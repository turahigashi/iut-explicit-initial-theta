#!/usr/bin/env python3
"""Regression gate newly written for the uploaded note6 v2 (not the missing old gate).

Every negative control must fail by an assertion, never by timeout or an unrelated
crash. Missing/ambiguous mutation targets are failures, not successful kills.
No mathematical conclusion is inferred from the mutation kill percentage.

Usage: python note6_regression_gate.py PATH/TO/costs.py --json evidence.json
"""
from __future__ import annotations
import argparse, concurrent.futures, difflib, json, os, pathlib, re, shutil, subprocess, sys, tempfile

CASES = [
 # Previously reported defects that the submitted v2 already rejects.
 ('old_height_denominator','den = mul(pw(a, 2), pw(b, 2))','den = mul(pw(a, 3), pw(b, 2))'),
 ('old_height_numerator','num = pw(t, 3);','num = pw(t, 4);'),
 ('old_nonprime_field','for p in (3, 5, 7):','for p in (4, 5, 7):'),
 ('old_unramified_index','index = 5**f','index = 6**f'),
 ('old_floor_leading_constant','good = 1 + F(math.floor(lam)) - lam','good = 2 + F(math.floor(lam)) - lam'),
 ('old_c4_printed_modulus','residue_173 = c4 % 173','residue_173 = c4 % 174'),
 ('old_full_mean','mean_full, mean_diag = F(sum(full),4), F(sum(diag),2)','mean_full, mean_diag = F(sum(full),5), F(sum(diag),2)'),
 ('old_diagonal_mean','mean_full, mean_diag = F(sum(full),4), F(sum(diag),2)','mean_full, mean_diag = F(sum(full),4), F(sum(diag),3)'),
 ('old_moderate_bound','p_minus_two = p_-2','p_minus_two = p_-3'),
 ('old_coarse_coefficient','coarse_coefficient = l+5','coarse_coefficient = l+6'),
 ('old_two_cb','two_cb = 2*cb_','two_cb = 3*cb_'),
 # Concrete residual failures in the submitted v2.
 ('cyclotomic_ramification','e, f, m = p - 1, 1, 1','e, f, m = p - 2, 1, 1'),
 ('floor_fixed_row','for lam in (F(3), F(472,157), F(627,157), F(4)):','for lam in (F(3), F(472,157), F(628,157), F(4)):'),
 ('residue_degree_rows','for f in (1, 2, 3):','for f in (1, 3, 3):'),
 ('ramification_rows','for N in (471, 472, 474, 475):','for N in (472, 472, 474, 475):'),
 ('two_adic_rows','for N in (199, 200, 201, 400):','for N in (200, 200, 201, 400):'),
 ('tuple_weight_dataflow','(("gg", F(1,4)), ("gb",','(("gg", F(1,5)), ("gb",'),
 ('two_adic_contribution_label','lab = "0" if m == 0 else','lab = "0" if m == 1 else'),
 ('statistic_additive_constant','return (1 + cg*t.count("g")','return (2 + cg*t.count("g")'),
 ('finite_check_all_skipped','k, v = pi(j, t), B(j, t, F(0), cb, s)','k, v = pi(j, t), B(j, t, F(1), cb, s)'),
 ('finite_check_wrong_counter_start','Em = E(3); mis = 0; n_tested = 0','Em = E(3); mis = 0; n_tested = 1'),
 ('finite_check_double_count','n_tested += 1','n_tested += 2'),
 ('finite_check_domain_shrink','for num in range(1, 40):','for num in range(2, 40):'),
 ('omitted_first_table','else range(1, len(TABLES)+1)','else range(2, len(TABLES)+1)'),
 ('wrong_table_order','TABLES[i-1]()','TABLES[i-2]()'),
 ('valuation_divisor','t //= 5; v5 += 1','t //= 6; v5 += 1'),
 ('tensor_order_generator','M = [[1, 0, 0, 5],','M = [[1, 1, 0, 5],'),
 ('two_adic_norm_object','B = Z[0]**2 + Z[1]**2','B = Z[1]**2 + Z[1]**2'),
]

def main() -> int:
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('script',type=pathlib.Path);ap.add_argument('--json',type=pathlib.Path)
 ap.add_argument('--timeout',type=float,default=25);ap.add_argument('--workers',type=int,default=4)
 a=ap.parse_args();script=a.script.resolve();src=script.read_text(encoding='utf-8')
 env=dict(os.environ);env.pop('PYTHONOPTIMIZE',None)
 def run(cmd, timeout=None):
  return subprocess.run([sys.executable,*map(str,cmd)],capture_output=True,text=True,env=env,timeout=timeout or a.timeout)
 try:base=run([script])
 except subprocess.TimeoutExpired:print('FAIL baseline timed out');return 2
 headers=[int(x) for x in re.findall(r'^Table (\d+)\.',base.stdout,re.M)]
 fixture=script.with_name('costs_output.txt')
 ok=base.returncode==0 and headers==list(range(1,13)) and fixture.exists() and base.stdout==fixture.read_text()
 records=[{'name':'baseline_12_tables_and_saved_output','status':'PASS' if ok else 'FAIL','returncode':base.returncode,'table_headers':headers}]
 if not ok:print('FAIL baseline',base.stderr);return 2
 with tempfile.TemporaryDirectory(prefix='note6-v2-gate-') as td:
  root=pathlib.Path(td)
  for f in script.parent.iterdir():
   if f.is_file() and f.suffix in {'.py','.json','.txt'}:shutil.copy2(f,root/f.name)
  def trial(case):
   name,before,after=case
   if src.count(before)!=1:return {'name':name,'status':'FAIL','reason':'missing or ambiguous target'}
   path=root/(name+'.py');path.write_text(src.replace(before,after,1))
   try:r=run([path])
   except subprocess.TimeoutExpired:return {'name':name,'status':'FAIL','reason':'timeout, not a verified rejection'}
   rejected=r.returncode!=0 and bool(re.search(r'^AssertionError(?::.*)?$',r.stderr,re.M))
   rec={'name':name,'status':'PASS' if rejected else 'FAIL','returncode':r.returncode,
        'reason':'assertion rejected' if rejected else ('all assertions passed' if r.returncode==0 else 'unrelated execution failure'),
        'line':src[:src.index(before)].count('\n')+1,'before':before,'after':after,
        'stdout_changed':r.stdout!=base.stdout,'stderr_tail':r.stderr[-1200:]}
   if r.returncode==0 and r.stdout!=base.stdout:
    rec['stdout_diff']=''.join(difflib.unified_diff(base.stdout.splitlines(True),r.stdout.splitlines(True),fromfile='baseline',tofile=name,n=2))
   return rec
  with concurrent.futures.ThreadPoolExecutor(max_workers=max(1,min(8,a.workers))) as pool:records.extend(pool.map(trial,CASES))
  # The distribution claims this named file is shipped. This checks presence, not provenance.
  shipped=script.with_name('note6_regression_gate.py').is_file()
  records.append({'name':'declared_gate_file_is_shipped','status':'PASS' if shipped else 'FAIL',
                  'reason':'named file exists' if shipped else 'scripts/note6_regression_gate.py is absent'})
  # The generic mutation harness must refuse *every* failing baseline invocation.
  # SIGTERM affects only the fixture's own child process.
  harness=script.with_name('mutation_test.py')
  if os.name=='posix' and harness.is_file():
   fixture_path=root/'signal_baseline.py'
   fixture_path.write_text('import os, signal, sys\nif "--signal" in sys.argv:\n    os.kill(os.getpid(), signal.SIGTERM)\nmarker = 7\nprint(marker)\n')
   r=run([harness,fixture_path,'--argv','','--argv','--signal'])
   rejected=r.returncode!=0 and 'does not pass unmutated' in r.stdout
   records.append({'name':'harness_rejects_signalled_baseline','status':'PASS' if rejected else 'FAIL','returncode':r.returncode,'stdout':r.stdout,'stderr':r.stderr})
  else:records.append({'name':'harness_rejects_signalled_baseline','status':'UNSUPPORTED','reason':'POSIX and mutation_test.py required'})
 counts={k:sum(x['status']==k for x in records) for k in ['PASS','FAIL','UNSUPPORTED']}
 for r in records:print(r['status'],r['name'],r.get('reason',''))
 print('RESULT:',json.dumps(counts))
 if a.json:
  a.json.parent.mkdir(parents=True,exist_ok=True)
  a.json.write_text(json.dumps({'python':sys.version,'script':str(script),'counts':counts,'records':records},ensure_ascii=False,indent=2)+'\n')
 return 1 if counts['FAIL'] or counts['UNSUPPORTED'] else 0
if __name__=='__main__':raise SystemExit(main())
