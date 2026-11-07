#!/usr/bin/env python3
"""Write generated.tex and the five excerpts of the note from ../c, ../cpp and ../outputs.

The numbers of Tables 2 and 6 and of the text (items compared, files and lines of the mockup, the value without
step (C), the values of C in the scan) are read from the outputs, so that the note shows what the programs print.

Usage (from the folder paper/, after ../scripts/run_all.sh):  python3 make_generated.py
"""
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DOI = "10.5281/zenodo.24039369"
DATA = ["D211", "D109", "D2", "D3", "D18", "D15", "D2357"]
CPP_FILES = ["common.hpp", "theater.hpp", "theater.cpp", "oracle.hpp", "oracle.cpp", "multiradial.hpp",
             "multiradial.cpp", "iv.hpp", "iv.cpp", "link.hpp", "link.cpp", "classical.hpp", "datum.hpp",
             "decimal.hpp", "main.cpp", "Makefile"]
NUM = r"(-?[0-9.]+(?:e[+-]?[0-9]+)?)"


def read(*parts):
    with open(os.path.join(ROOT, *parts), encoding="utf-8") as fh:
        return fh.read()


def write(name, text):
    with open(os.path.join(HERE, name), "w", encoding="utf-8") as fh:
        fh.write(text.rstrip("\n") + "\n")


def between(text, start, end):
    i = text.index(start)
    j = text.index(end, i) + len(end)
    return text[i:j]


def grab(text, pattern):
    m = re.search(pattern, text)
    if not m:
        raise SystemExit(f"pattern not found: {pattern}")
    return m.groups()


def number(x, digits):
    return f"${x:.{digits}f}$"


# the code excerpts
iut = read("c", "iut.c")
write("excerpt_iut_core.c", between(iut, "    /* 3. The primes that carry theta values", "        iv_sum += iv_p;\n    }\n"))
src = {f: read("cpp", f) for f in CPP_FILES}
listed = sorted(f for f in os.listdir(os.path.join(ROOT, "cpp")) if f.endswith((".hpp", ".cpp")) or f == "Makefile")
assert sorted(CPP_FILES) == listed, "the list of C++ files"
write("excerpt_box.hpp", between(src["common.hpp"], "// ORACLE [theta-group]. The theta group", "struct QPilotInput {")
      + "\n    ...\n};")
write("excerpt_rigidity.cpp",
      between(src["multiradial.cpp"], "// (C) cyclotomic rigidity at level N.", "    return c.c;\n}")
      + "\n\n    ...\n\n"
      + between(src["multiradial.cpp"], "    // (C)-(D) The theta values",
                "R.theta_ord[i] = (double)val[0] / R.local[i].e;   // ord_p(qq) = ord_{K_v}(qq) / e; the valuations are "
                "<< N\n    }"))
write("excerpt_stepxi.cpp", between(src["oracle.cpp"], "StepXiCertificate step_xi(", "    return X;\n}"))
write("excerpt_data_D211.txt", "".join(read("data", "D211.txt").splitlines(True)[:14]) + "...")

# Table 2
rows = []
for d in DATA:
    cl = read("outputs", f"classical_{d}.txt")
    iu = read("outputs", f"iut_{d}.txt")
    lq, lf = map(float, grab(cl, r"counted places:\s+log q = " + NUM + r"\s+log f = " + NUM))
    (a,) = map(float, grab(iu, r"-\|log qq\|\s+= " + NUM))
    (M,) = map(float, grab(iu, r"-\|log Theta\| = " + NUM))
    (U,) = map(float, grab(iu, r"U\(D\)\s+= " + NUM))
    wall, C = map(float, grab(iu, r"\(k-1\)\|log qq\| = " + NUM + r" [<>=]+ " + NUM))
    label = d + ("$^\\ast$" if d == "D2357" else "")
    cells = [number(lq, 2), number(lf, 2), number(a, 3), number(M, 2), number(U, 2), number(wall, 2), number(C, 2)]
    rows.append(label + " & " + " & ".join(cells) + "\\\\")
table2 = "\n".join(rows)

# Table 6
rows = []
for d in DATA[:6]:
    t = read("outputs", f"scan40_{d}.txt")
    a, b, c, e = grab(t, r"says yes up to N = (\d+), no from N = (\d+); the height inequality holds up to N = (\d+), "
                         r"fails from N = (\d+)")
    rows.append(f"{d} & $N\\le{a}$ (``no'' from $N={b}$) & $N\\le{c}$ (fails from $N={e}$)\\\\")
table6 = "\n".join(rows)

# numbers in the text
(items,) = grab(read("outputs", "check_cpp.txt"), r"items compared: (\d+)")
assert "all checks passed" in read("outputs", "check_cpp.txt")
nlines = sum(t.count("\n") for t in src.values())
(naive,) = grab(read("outputs", "selftest_D211.txt"), r"without step \(C\): -\|log Theta\| = " + NUM)
mant, expo = f"{float(naive):.1e}".split("e")
naive_tex = f"{mant}\\times10^{{{int(expo)}}}"
cvals = []
for m in re.finditer(r"^\s+\d+\s+" + r"\s+".join([NUM] * 5), read("outputs", "scan40_D211.txt"), re.M):
    v = f"{float(m.group(5)):.2f}"
    if v not in cvals:
        cvals.append(v)
assert len(cvals) == 2, cvals

out = [
    "% written by make_generated.py from ../c, ../cpp and ../outputs; do not edit",
    f"\\newcommand{{\\thedoi}}{{{DOI}}}",
    f"\\newcommand{{\\cppitems}}{{{items}}}",
    f"\\newcommand{{\\cppfiles}}{{{len(CPP_FILES)}}}",
    f"\\newcommand{{\\cpplines}}{{{nlines // 1000}{{,}}{nlines % 1000:03d}}}" if nlines >= 1000
    else f"\\newcommand{{\\cpplines}}{{{nlines}}}",
    f"\\newcommand{{\\selftestnaive}}{{{naive_tex}}}",
    f"\\newcommand{{\\scanCvalues}}{{{cvals[0]} and {cvals[1]}}}",
    "\\newcommand{\\tabletwo}{%\n" + table2 + "}",
    "\\newcommand{\\tablesix}{%\n" + table6 + "}",
    "\\newcommand{\\iutcore}{\\VerbatimInput{excerpt_iut_core.c}}",
    "\\newcommand{\\cppbox}{\\VerbatimInput{excerpt_box.hpp}}",
    "\\newcommand{\\cpprigidity}{\\VerbatimInput{excerpt_rigidity.cpp}}",
    "\\newcommand{\\cppstepxi}{\\VerbatimInput{excerpt_stepxi.cpp}}",
    "\\newcommand{\\datafile}{\\VerbatimInput{excerpt_data_D211.txt}}",
]
write("generated.tex", "\n".join(out))
print(f"wrote generated.tex and 5 excerpts: {items} items, {len(CPP_FILES)} C++ files, {nlines} lines; "
      f"without step (C) {naive_tex}; C in the scan {cvals}")
