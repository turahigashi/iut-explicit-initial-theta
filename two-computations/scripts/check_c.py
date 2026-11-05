#!/usr/bin/env python3
"""Compare the outputs of the C programs with those of the Python programs of reading-family/ (v0.17.0).

classical.c  against elementary_height.py   (log q, log f for all places and for the counted ones, log d, the
                                             right-hand side of Theorem 1.10)
iut.c        against iut_height.py          (-|log qq|, U(D) and its parts, Step (viii), Theorem 1.10)
             and iut_readings36.py           (-|log Theta| in the reading V, container, units, hull, small)
Relative tolerance 1e-9.

Usage: python3 check_c.py <scripts folder of reading-family> <folder with the C binaries> <data folder>
From the folder two-computations/, after make -C c:
    python3 scripts/check_c.py ../reading-family/scripts c data
"""
import math
import os
import re
import subprocess
import sys

scripts, cdir, ddir = sys.argv[1:4]
sys.path.insert(0, scripts)
import elementary_height as el  # noqa: E402
import iut_compute as ic  # noqa: E402
import iut_height as ih  # noqa: E402
import iut_readings36 as r36  # noqa: E402

NUM = r"(-?[0-9.]+(?:e[+-]?[0-9]+)?)"
bad = 0


def close(x, y):
    return abs(x - y) <= 1e-9 * max(1.0, abs(x), abs(y))


def check(name, what, c_value, py_value):
    global bad
    ok = close(c_value, py_value)
    bad += not ok
    print(f"  {'OK ' if ok else 'BAD'} {what:<34} C {c_value:.9g}   Python {py_value:.9g}")


def grab(text, pattern):
    m = re.search(pattern, text)
    if not m:
        raise SystemExit(f"pattern not found: {pattern}")
    return [float(g) for g in m.groups()]


for name in el.CURVES:
    path = os.path.join(ddir, name + ".txt")
    cl = subprocess.run([os.path.join(cdir, "classical"), path], capture_output=True, text=True, check=True).stdout
    iu = subprocess.run([os.path.join(cdir, "iut"), path], capture_output=True, text=True, check=True).stdout
    E = el.compute(name)
    H = ih.compute(name)
    R = r36.evaluate(ic.InitialThetaData(name, factor_seconds=1))
    MV = [r for r in R["rows"] if r["reading"] == ["V", "容器", "単数", "包", "小"]][0]
    print(name)
    lq_all, lf_all = grab(cl, r"all places of bad reduction: log q = " + NUM + r"\s+log f = " + NUM)
    lq, lf, ld = grab(cl, r"counted places:\s+log q = " + NUM + r"\s+log f = " + NUM + r"\s+log d = " + NUM)
    (rhs,) = grab(cl, r"<?=? " + NUM + r" = right-hand side")
    check(name, "classical: log q (all)", lq_all, E["全部"]["log_q"])
    check(name, "classical: log f (all)", lf_all, E["全部"]["log_f"])
    check(name, "classical: log q (counted)", lq, E["𝕍^bad 型"]["log_q"])
    check(name, "classical: log f (counted)", lf, E["𝕍^bad 型"]["log_f"])
    check(name, "classical: log d", ld, E["log_d"])
    check(name, "classical: Theorem 1.10, right side", rhs, E["𝕍^bad 型"]["rhs"])
    (mq,) = grab(iu, r"-\|log qq\|\s+= " + NUM)
    (M,) = grab(iu, r"-\|log Theta\| = " + NUM)
    U, Uk, Ucl, Ur, arch = grab(iu, r"U\(D\)\s+= " + NUM + r"\s+\(primes with theta values " + NUM + r", closed form "
                                + NUM + r"; 2, 3, 5, l " + NUM + r"; archimedean " + NUM)
    (viii,) = grab(iu, r"Step \(viii\): " + NUM)
    (trhs,) = grab(iu, r"Theorem 1.10: \(1/6\) log q = [0-9.]+ <?>?=? " + NUM)
    check(name, "iut: -|log qq|", mq, H["lhs"])
    check(name, "iut: -|log Theta| (reading V)", M, MV["lo"])
    if MV["extra"]:
        print(f"  note: iut_readings36.py adds {MV['extra']:.4f} for the places above the unfactored cofactor; iut.c does not count them")
    check(name, "iut: U(D)", U, H["U"])
    check(name, "iut: U at primes with theta values", Uk, H["U_known"])
    check(name, "iut: the same in closed form", Ucl, H["U_known"])
    check(name, "iut: U at 2, 3, 5, l", Ur, H["U_unknown"])
    check(name, "iut: archimedean part", arch, H["arch"])
    check(name, "iut: Step (viii)", viii, H["viii"])
    check(name, "iut: Theorem 1.10, right side", trhs, H["thm_rhs"])
    check(name, "ends: log q, classical vs iut", lq, 2 * E["ell"] * (-mq))
    check(name, "ends: right side, classical vs iut", rhs, trhs)
print(f"bad = {bad}")
sys.exit(1 if bad else 0)
