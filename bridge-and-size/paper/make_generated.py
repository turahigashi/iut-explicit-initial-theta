#!/usr/bin/env python3
"""Write generated.tex: the DOI, Tables 4.1 and 7.1, and the numbers quoted in the text, all computed by
../scripts/bridge_lib.py (the same functions that print ../outputs/bridge.txt).

Usage (from the folder paper/):  python3 make_generated.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "scripts"))
import bridge_lib  # noqa: E402

DOI = "10.5281/zenodo.23984201"


def tex_factored(n):
    if n == 1:
        return "1"
    parts = []
    for p, e in sorted(bridge_lib.factor(n).items()):
        parts.append(f"{p}^{{{e}}}" if e > 1 else f"{p}")
    return "\\cdot ".join(parts)


def place(t):
    label = t["label"]
    sign = {"+": "+", "-": "-"}.get(label[-1], "")
    digits = len(str(t["p"]))
    if digits > 12:
        return f"a {digits}-digit prime (${sign}$)" if sign else f"a {digits}-digit prime"
    return f"${t['p']}{sign}$" if sign else f"${t['p']}$"


def num(x):
    return f"{x:,.2f}"


out = [f"\\newcommand{{\\thedoi}}{{{DOI}}}"]

rows = []
ratio_tex = {"b/c": "b/c", "a/c": "a/c", "−a/b": "-a/b"}
for r in bridge_lib.triples_rows():
    first = True
    for it in r["items"]:
        assert it["vlog"] == it["e"]
        triple = f"${tex_factored(r['a'])}+{tex_factored(r['b'])}={tex_factored(r['c'])}$" if first else ""
        qual = f"{r['quality']:.4f}" if first else ""
        first = False
        rows.append(f"{triple} & {qual} & ${it['p']}^{{{it['e']}}}$ & ${it['term']}$ & ${ratio_tex[it['ratio']]}$ & "
                    f"{it['vlog']} & {', '.join(str(q) for q in it['primes'])} \\\\")
out.append("\\newcommand{\\tabletriples}{%\n" + "\n".join(rows) + "}")

rows = []
d211 = None
for r in bridge_lib.data_rows():
    t = r["top"]
    js = sorted(r["gaps"])
    last = js[-1]
    assert abs(r["gap_total"] / r["wall"] - r["ell"]) < 1e-9
    name = r["name"] + ("$^{\\dagger}$" if r["unfactored"] else "")
    rows.append(f"{name} & {r['ell']} & {place(t)} & {t['oq']} & {t['d']} & {r['gaps'][2]:,} & "
                f"{r['gaps'][last]:,} ($j={last}$) & {num(r['gap_total'])} & {num(r['wall'])} \\\\")
    if r["name"] == "D211":
        d211 = r
out.append("\\newcommand{\\tabledata}{%\n" + "\n".join(rows) + "}")
t = d211["top"]
out += [f"\\newcommand{{\\dQ}}{{{d211['Q']:.4f}}}", f"\\newcommand{{\\dwall}}{{{d211['wall']:.4f}}}",
        f"\\newcommand{{\\dgap}}{{{d211['gap_total']:.4f}}}", f"\\newcommand{{\\dgaptwo}}{{{d211['gaps'][2]}}}",
        f"\\newcommand{{\\dgapthree}}{{{d211['gaps'][3]}}}", f"\\newcommand{{\\ddepth}}{{{t['d']}}}",
        f"\\newcommand{{\\dordq}}{{{t['oq']}}}", f"\\newcommand{{\\dnbad}}{{{d211['nbad']}}}"]
with open(os.path.join(HERE, "generated.tex"), "w", encoding="utf-8") as fh:
    fh.write("% written by make_generated.py from ../scripts/bridge_lib.py; do not edit by hand\n" + "\n".join(out) + "\n")
print("wrote generated.tex")
