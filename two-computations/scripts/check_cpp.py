#!/usr/bin/env python3
"""Compare the C++ mockup (cpp/mockup) with the C programs (c/iut, c/classical) on the seven data, run its
selftests (non-interference) and the information-flow check, and scan the family q -> q^N.

The C programs agree with the Python programs of reading-family/ (v0.17.0) on 119 items (check_c.py), so agreement
with C is agreement with Python. Relative tolerance 1e-9.

Usage (from the folder two-computations/): python3 scripts/check_cpp.py
It builds the C programs (make -C c) and the mockup (make -C cpp), and writes outputs/check_cpp.txt.
"""
import os
import re
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = ["D211", "D109", "D2", "D3", "D18", "D15", "D2357"]
NUM = r"(-?[0-9.]+(?:e[+-]?[0-9]+)?)"
bad = 0
lines = []


def out(s=""):
    print(s)
    lines.append(s)


def run(*args):
    return subprocess.run(list(args), capture_output=True, text=True, check=True, cwd=ROOT).stdout


def grab(text, pattern):
    m = re.search(pattern, text)
    if not m:
        raise SystemExit(f"pattern not found: {pattern}")
    return [float(g) for g in m.groups()]


def close(x, y):
    return abs(x - y) <= 1e-9 * max(1.0, abs(x), abs(y))


def check(what, cpp, c):
    global bad
    ok = close(cpp, c)
    bad += not ok
    out(f"  {'OK ' if ok else 'BAD'} {what:<36} C++ {cpp:.10g}   C {c:.10g}")


PATTERNS = {
    "-|log qq|": r"q-pilot\s+-\|log qq\|\s+= " + NUM,
    "log q = 2 l |log qq|": r"\(log q = 2 l \|log qq\| = " + NUM,
    "-|log Theta|": r"Theta-pilot\s+-\|log Theta\| = " + NUM,
    "U(D)": r"U\(D\)\s+= " + NUM,
    "U: primes with theta values": r"primes with theta values " + NUM,
    "U: closed form": r"closed form " + NUM + r"; 2, 3, 5",
    "U: 2, 3, 5, l": r"2, 3, 5, l " + NUM,
    "U: archimedean": r"; archimedean " + NUM,
    "wall (k-1)|log qq|": r"\(k-1\)\|log qq\| = " + NUM,
    "C": r"<?=? " + NUM + r" = C",
    "Step (viii)": r"Step \(viii\): " + NUM,
    "Theorem 1.10: (1/6) log q": r"Theorem 1.10: \(1/6\) log q = " + NUM + r" <?=?>? [0-9.e+]+\n",
    "Theorem 1.10: right-hand side": r"Theorem 1.10: \(1/6\) log q = [0-9.]+ <?=?>? " + NUM + r"\n",
}
CLASSICAL = {
    "classical: log q (counted)": (r"classical\s+log q = " + NUM, r"counted places:\s+log q = " + NUM),
    "classical: log f (counted)": (r"classical\s+log q = [0-9.]+\s+log f = " + NUM, r"counted places:\s+log q = [0-9.]+\s+log f = " + NUM),
    "classical: log d": (r"log d = " + NUM + r"\s+\(all", r"log d = " + NUM),
    "classical: log q (all)": (r"all places of bad reduction: log q = " + NUM, r"all places of bad reduction: log q = " + NUM),
    "classical: log f (all)": (r"all places of bad reduction: log q = [0-9.]+\s+log f = " + NUM,
                               r"all places of bad reduction: log q = [0-9.]+\s+log f = " + NUM),
    "classical: right-hand side": (r"classical\s+Theorem 1.10: \(1/6\) log q = [0-9.]+ <?=?>? " + NUM, r"<?=? " + NUM + r" = right-hand side"),
}

run("make", "-C", "c", "-s")
run("make", "-C", "cpp", "-s", "mockup")
out("1. The C++ mockup against the C programs (the same seven data)")
items = 0
for d in DATA:
    path = os.path.join("data", d + ".txt")
    cpp = run("cpp/mockup", path)
    iu = run("c/iut", path)
    cl = run("c/classical", path)
    out(d)
    for what, pat in PATTERNS.items():
        check(what, grab(cpp, pat)[0], grab(iu, pat)[0])
        items += 1
    for what, (pc, pcl) in CLASSICAL.items():
        check(what, grab(cpp, pc)[0], grab(cl, pcl)[0])
        items += 1
    for m in re.finditer(r"hull " + NUM + r"  closed form " + NUM, cpp):   # enumeration = closed form, prime by prime
        check("hull of one prime: enumerated = closed", float(m.group(1)), float(m.group(2)))
        items += 1
    for tag in ("[implemented]", "[ORACLE ind3]", "[ORACLE step-xi]", "REVERSE-COMPUTED"):
        if tag not in cpp:
            bad += 1
            out(f"  BAD the report does not show {tag}")
out(f"items compared: {items}")
out()
out("2. Information flow and non-interference (make check)")
for s in run("make", "-C", "cpp", "-s", "check").splitlines():
    out("  " + s)
    if "FAILED" in s:
        bad += 1
out()
out("3. The family q -> q^N (N <= 40, N prime to l)")
for d in DATA[:6]:
    s = run("cpp/mockup", "--scan", os.path.join("data", d + ".txt"), "40")
    out(f"  {d}: " + s.strip().splitlines()[-2])
out()
out("all checks passed" if bad == 0 else f"{bad} checks FAILED")
os.makedirs(os.path.join(ROOT, "outputs"), exist_ok=True)
with open(os.path.join(ROOT, "outputs", "check_cpp.txt"), "w", encoding="utf-8") as fh:
    fh.write("\n".join(lines) + "\n")
raise SystemExit(1 if bad else 0)
