#!/usr/bin/env python3
"""Fail if a retraction made in the paper has not reached the shipped artifacts.

Every round-3 and round-4 review, from three internal checks, gave the same
primary reason for withholding publication: the prose was corrected and the code,
the stored stdout, the run instructions or the audit scope were not.  Prose review
does not catch that reliably -- the corrected sentence reads fine and the stale
label sits in a different file.  So each retraction is recorded here as a string
that must not reappear, and the packager runs this before it builds a bundle.

Usage: python3 scripts/check_no_drift.py [root]     (exit 1 if anything drifted)
"""
from __future__ import annotations
import pathlib, subprocess, sys

# (retracted string, files it must not appear in, what replaced it)
RETRACTED = [
    ("e_b = 105/gcd(105, 44)", ["scripts/tables_output.txt"],
     "at p=3 the prime-to-p formula does not apply; mu_3 forces 2 | e"),
    # NOTE: the needle must be the retracted SENTENCE, not a fragment of it.  An
    # earlier version used "fails there" and flagged Table 5's correct "condition (4)
    # fails there" at N=116 -- a false positive, which is the dangerous kind: it sends
    # you to break text that was right.
    ("so [IUT4, Prop. 1.4(iii)] fails there", ["scripts/tables.py",
                                               "scripts/tables_output.txt"],
     "the proposition applies with the index placed in I*"),
    ("ord of q_{v_j}^{j^2}", ["scripts/tables.py", "scripts/tables_output.txt"],
     "qbb = q^(1/(2 ell)), the double-underlined q of [IUT1, Ex. 3.2(iv)]"),
    ("Thm 3.11(i)]: the number of direct summands", ["scripts/tables.py",
                                                     "scripts/tables_output.txt"],
     "[IUT3, Prop. 3.2]; Thm 3.11(i)(a) is cited only for the notation"),
    ("seed - bound", ["scripts/tables.py", "scripts/tables_output.txt"],
     "co(t), bd(t), co - bd"),
    ("Why the local discrepancy does not reach", ["scripts/tables.py",
                                                  "scripts/tables_output.txt"],
     "the ratio of two terms inside the same upper bound"),
    ("No log-volume is computed", ["paper/note5.tex"],
     "what is not computed is the hull of the actual Theta-pilot's possible images"),
    ("no log-volume is computed here", ["paper/note5.tex"],
     "same"),
    ("a comparison that this report does not make", ["scripts/imq_checks.py"],
     "same"),
    ("SELECTED bad places", ["scripts/tables.py", "scripts/tables_output.txt"],
     "H_all, over ALL bad places, as (C1) is stated"),
    ("opposite end of the same", ["paper/note5.tex"],
     "different and independent; no claim that LANA's targets coincide"),
    ("could not previously be asked", ["paper/note5.tex"],
     "evaluate, on these explicit inputs, three questions"),
    ("Neither point affects an estimate", ["paper/note5.tex"],
     "we do not consider what either point does to that paper's estimates"),
    ("external certificate of \\cite{First}", ["paper/note5.tex"],
     "computed in scripts/tables.py, Table 13"),
    ("and (5) are conditions imposed here", ["paper/note5.tex"],
     "(5) is [IUT1, Def. 3.1(c)]; (1) and (3) are imposed here"),
    # --- added after round 5 (two internal checks, same seven items) ---
    ("accumulated thm 7.42", ["scripts/tables.py", "scripts/tables_output.txt"],
     "row removed: the locator is not in this report's bibliography"),
    ("computed from scratch", ["scripts/tables.py"],
     "the Cremona counts and ord_3(q)=44 are inputs, and say so where printed"),
    ("in the accompanying certificate", ["scripts/tables.py",
                                         "scripts/tables_output.txt"],
     "the sieve is external; its inputs are in lean/LargeImaginaryDatum.lean"),
    ("its bound in \\S\\ref{s:fourteen}", ["paper/note5.tex"],
     "that reference pointed at the section it stood in"),
    ("valuations and\nresidue degrees", ["paper/note5.tex"],
     "the two named Lean files do not prove the residue degrees"),
    # NOT listed: lean/ModSevenImage.lean still says "give different traces".  That
    # file is pinned by SHA-256 to the first report's bytes, so the comment cannot be
    # corrected without giving up the pin; the paper discloses the discrepancy instead.
    ("makes unnecessary", ["paper/note5.tex"],
     "reduced by a cyclotomic factorisation to a finite blockwise sieve"),
    # --- added after round 7: the retracted BASIS-DEPENDENT argument, which had
    # survived in running code rather than in a label.  This is the class the earlier
    # needles missed, so all three of its surfaces are listed.
    ("witnesses generate SL_2(F_7), of order 336", ["scripts/imq_checks.py",
                                                    "scripts/imq_checks_output.txt"],
     "AUXILIARY ONLY on a chosen companion representative; the image argument is "
     "lean/BasisFreeImage.lean"),
    ("the Frobenius traces and the group generation", ["paper/note5.tex"],
     "the norms and the Frobenius traces; it does not reproduce the image argument"),
    # --- added after round 15: counts that had gone stale in three places at once
    ("thirteen", ["paper/note5.tex"], "fourteen (the audit covers 14 files)"),
    # --- added after round 19: this datum's torsion level was applied to other curves
    ("105/gcd(105,5) = 21", ["scripts/tables.py", "scripts/tables_output.txt"],
     "e_b >= 42/gcd(42,5) = 42; 105 is THIS datum's level, not 11a1's"),
    ("e_{\\mathrm b}=105/\\gcd(105,5)=21", ["paper/note5.tex"],
     "e_b >= 42 from [IUT1, Def 3.1(b)] making E[6] rational"),
    ("is external to this report", ["paper/note5.tex"],
     "carried out by scripts/powerfree_certificate.py, which ships here"),
]

def flatten(text: str) -> str:
    return " ".join(text.split())          # so a retraction cannot hide in a line break

def main() -> int:
    root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
    bad = []
    for needle, files, replacement in RETRACTED:
        for rel in files:
            f = root / rel
            if not f.is_file():
                continue
            if flatten(needle) in flatten(f.read_text()):
                bad.append((rel, needle, replacement))
    for rel, needle, repl in bad:
        print(f"DRIFT: {rel} still contains {needle!r}\n       should read: {repl}")
    print(f"checked {len(RETRACTED)} retractions -> "
          f"{'DRIFT FOUND' if bad else 'none reappeared'}")
    return 1 if bad else 0

if __name__ == "__main__":
    raise SystemExit(main())
