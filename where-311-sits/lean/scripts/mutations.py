#!/usr/bin/env python3
"""Reproduce the mutations reported in Section 11 of the paper.

Each mutation edits one file of the library, compiles that file alone against the already
built library (run `lake build` first), and records which declarations fail and, inside a
structure instance, which fields fail. It then compares the result with what the paper says.

  first         the first error lies in the named declaration (or field);
  exact_within  inside the named declarations, the set of failing fields is exactly the
                expected one (errors elsewhere are consequences and are not counted);
  exact         the set of failing declarations of the whole file is exactly the expected one.

Usage: python3 scripts/mutations.py [ID ...]
The environment variables LEAN (the lean binary) and LEAN_PATH may be set; otherwise
`lake env` is used.
"""
import json, os, re, shutil, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPECS = json.load(open(os.path.join(ROOT, 'scripts', 'mutations.json'), encoding='utf-8'))

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|example|inductive|class)\s+([^\s(:{\[]+)")
FIELD = re.compile(r"^  ([A-Za-z_][A-Za-z0-9_'.]*)\s*:=")
ERR = re.compile(r":(\d+):(\d+): error")


def lean_cmd():
    lean = os.environ.get('LEAN')
    lp = os.environ.get('LEAN_PATH')
    if lean and lp:
        return [lean], dict(os.environ)
    r = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT,
                       capture_output=True, text=True, check=True)
    env = dict(os.environ, LEAN_PATH=r.stdout.strip())
    return ['lake', 'env', 'lean'], env


def labels(lines):
    """For each line number (1-based), the enclosing declaration and field."""
    out, decl, field = {}, None, None
    for i, line in enumerate(lines, 1):
        m = DECL.match(line)
        if m:
            decl, field = m.group(1).split('.')[-1], None
        elif decl is not None and (line.startswith('end ') or line.startswith('namespace ')):
            decl, field = None, None
        else:
            f = FIELD.match(line)
            if f and decl is not None:
                field = f.group(1)
        out[i] = (decl, field)
    return out


def run(spec, cmd, env):
    src = os.path.join(ROOT, spec['file'])
    text = open(src, encoding='utf-8').read()
    for e in spec['edits']:
        n = text.count(e['old'])
        want = e.get('count', 1)
        if n != want:
            return {'id': spec['id'], 'ok': False, 'why': f"edit applies {n} times, expected {want}"}
        text = text.replace(e['old'], e['new'])
    tmp = tempfile.mkdtemp(prefix='mut_')
    try:
        dst = os.path.join(tmp, spec['file'])
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, 'w', encoding='utf-8').write(text)
        r = subprocess.run(cmd + ['-R', tmp, dst], env=env, capture_output=True, text=True,
                           cwd=ROOT, timeout=3600)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    out = r.stdout + r.stderr
    lab = labels(text.split('\n'))
    errs = []
    for m in ERR.finditer(out):
        d, f = lab.get(int(m.group(1)), (None, None))
        errs.append(d if f is None else f'{d}.{f}')
    exp = spec['expect']
    mode = exp['mode']
    if not errs:
        return {'id': spec['id'], 'ok': False, 'why': 'the mutated file compiles', 'errors': []}
    if mode == 'first':
        got = errs[0]
        want = exp['label']
        ok = got == want or ('.' not in want and got.split('.')[0] == want)
    elif mode == 'exact_within':
        scope = exp['scope']
        got = sorted({e for e in errs if e.split('.')[0] in scope})
        ok = got == sorted(exp['labels'])
    elif mode == 'exact':
        got = sorted({e.split('.')[0] for e in errs})
        ok = got == sorted(exp['labels'])
    else:
        raise ValueError(mode)
    return {'id': spec['id'], 'ok': ok, 'got': got, 'errors': errs[:12]}


def main():
    ids = sys.argv[1:]
    cmd, env = lean_cmd()
    results = []
    for spec in SPECS:
        if ids and spec['id'] not in ids:
            continue
        res = run(spec, cmd, env)
        res['paper'] = spec['paper']
        results.append(res)
        print(('PASS ' if res['ok'] else 'FAIL ') + spec['id'] + ': ' + spec['paper'])
        print('     got: ' + json.dumps(res.get('got', res.get('why'))), flush=True)
    bad = [r for r in results if not r['ok']]
    print(f"{len(results) - len(bad)}/{len(results)} mutations behave as the paper states")
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
