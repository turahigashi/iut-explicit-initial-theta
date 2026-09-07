#!/usr/bin/env python3
"""Mutation test for scripts/costs.py:  perturb every integer literal by +1 and
report the ones no assertion notices.  Standard library only.  Run:

    python3 scripts/mutation_test.py            # costs.py
    python3 scripts/mutation_test.py FILE ...
    python3 scripts/mutation_test.py FILE --argv "" --argv "--self-test" --argv "--json"

A script whose behaviour is gated on argv has more than one contract, and the paths
not exercised are exactly the ones that look best under this test.  Pass every
documented invocation with --argv; a mutant counts as killed if any of them notices
it.  The certificate's own negative control was reached only this way.

A surviving mutant is not automatically a defect -- a sample list, a search bound
or a coefficient multiplied by zero for the datum at hand can be perturbed without
changing any answer.  It is a defect when the mutated number is one the paper
prints.  The classification of the current residue is in plan/mutation-residue.md.

Positions come from `tokenize`, so literals inside strings and comments are never
touched; an earlier column-based version silently edited the wrong token.
"""
import io, pathlib, subprocess, sys, tokenize

def run(path, argvs):
    src = pathlib.Path(path).read_text(); lines = src.split("\n")
    # Every decimal integer literal, INCLUDING 0 and 1.  An earlier version skipped
    # values below 2 and still described itself as covering every integer literal;
    # that exclusion hid 228 targets in this file, one of which (the leading 1 of
    # "1 + floor(lambda) - lambda") changes a printed column of Table 4 (external
    # review, 2026-09-07).
    toks = [(t.start[0], t.start[1], t.end[1], t.string)
            for t in tokenize.generate_tokens(io.StringIO(src).readline)
            if t.type == tokenize.NUMBER and t.string.isdigit()]
    import time
    t0 = time.time()
    rcs0 = [subprocess.run([sys.executable, path, *a], capture_output=True).returncode
            for a in argvs]
    # A baseline killed by a signal reports a negative return code; treating that as
    # "non-zero, so nothing to test" is right, but treating it as a normal failure hid
    # the difference (external review, 2026-09-07).
    if any(rc < 0 for rc in rcs0):
        print(f"{path}: does not pass unmutated; nothing to test "
              f"(terminated by signal {[-rc for rc in rcs0 if rc < 0]})", flush=True)
        return 1
    base = max(rcs0, default=1)
    if base != 0:
        print(f"{path}: does not pass unmutated; nothing to test", flush=True); return 1
    # A mutant that runs far longer than the original has changed observable behaviour,
    # so it is killed, not survived; without a cap one widened search bound can stall
    # the whole run.  The cap is generous relative to the unmutated time.
    cap = max(15.0, 25 * (time.time() - t0))
    tmp = pathlib.Path(path).with_suffix(".mutant.tmp")
    surv, slow, byassert, byother = [], [], 0, 0
    try:
        for ln, c0, c1, v in toks:
            m = lines[:]; m[ln-1] = m[ln-1][:c0] + str(int(v)+1) + m[ln-1][c1:]
            tmp.write_text("\n".join(m))
            rcs, errs, timed_out = [], [], False
            for a in argvs:                      # a mutant is killed if ANY documented
                try:                             # invocation notices it: an argument-
                    r = subprocess.run(          # gated self-test is part of the
                        [sys.executable, str(tmp), *a],   # contract and was previously
                        capture_output=True, timeout=cap)  # never executed
                    rcs.append(r.returncode); errs.append(r.stderr)
                except subprocess.TimeoutExpired:
                    timed_out = True; break
            if timed_out:
                slow.append((ln, v)); continue
            if all(rc == 0 for rc in rcs):
                surv.append((ln, v, m[ln-1].strip()[:78]))
            elif any(b"AssertionError" in e for e in errs):
                byassert += 1                    # a check noticed it
            else:
                byother += 1                     # it merely failed to run
    finally:
        tmp.unlink(missing_ok=True)
    # tokenize reports numbers inside f-string replacement fields from Python 3.12
    # (PEP 701) and not before, so the mutant COUNT is version-dependent; the version
    # is printed with it.  An earlier version reported "killed by an assertion" for
    # every non-zero exit, which conflated a check noticing a defect with the mutant
    # merely failing to run (external review, 2026-09-07).
    print(f"{path}: mutants={len(toks)}  killed={len(toks)-len(surv)}  "
          f"survived={len(surv)}  (of the killed, {byassert} by an assertion, "
          f"{byother} by another error, {len(slow)} by exceeding {cap:.0f}s)"
          f"  [python {sys.version_info.major}.{sys.version_info.minor}]", flush=True)
    for ln, v, t in surv:
        print(f"    line {ln:4d}   {v} -> {int(v)+1}   {t}", flush=True)
    return 0

if __name__ == "__main__":
    argv = sys.argv[1:]
    argvs, files = [[]], []
    if "--argv" in argv:                          # --argv "" --argv "--self-test"
        argvs = [a.split() for i, a in enumerate(argv) if i and argv[i-1] == "--argv"]
        argv = [a for i, a in enumerate(argv)
                if a != "--argv" and not (i and argv[i-1] == "--argv")]
    files = argv or [str(pathlib.Path(__file__).with_name("costs.py"))]
    raise SystemExit(max(run(f, argvs) for f in files))
