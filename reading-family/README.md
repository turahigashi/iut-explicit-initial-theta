# No reading avoids the height inequality: 36 readings of Corollary 3.12 and the conservation of the height load

Version 1.1.0, 8 November 2026 (17 pages). DOI [10.5281/zenodo.24039368](https://doi.org/10.5281/zenodo.24039368).
Version 1.0.0: [10.5281/zenodo.23965952](https://doi.org/10.5281/zenodo.23965952).

**Changes in 1.1.0.** Cites earlier work by Takkun-kohinata/IUT_LEAN (GitHub, 15 July 2026: in Lean, for one
reading, the containment of Step (v) together with Corollary 3.12 gives (ℓ(ℓ+1)/12 − 1)|log q| ≤ L, and conversely;
the case x = 1 of the note), and the statement of Mochizuki's report on formalization (§3) that the height is
unaffected, up to a mild error, by multiplication by N, with its Lean form in D. Richards' motizukipdf (October 2026). Narrows the novelty item on the split point: the condition for equality was stated earlier
in lana-agents/iut, `Iut/Concrete/Literal.lean` (revision 2b2190d, 11 October 2026), and in Proposition 13.2 of the
author's note on indexed identifications; what remains new is the condition for reading L and its validity in all 36
readings. Corrects §5.4 (at N = 3 the rounding term of the lattice group for D109 doubles, from Δ(D109) to 2Δ(D109);
it does not vanish), the range of the deficit of IV for D2357 in §5.5 (8362 to 10308 with the hull and the small
archimedean container, 8376 to 10321 with the large ball, at least 7775 without the hull), the name of the readings of
the catalogue ((M_b) and (M_g)), and the description of the note on indexed identifications (its companion is
*Segment or loop?*). Adds to Theorem 3.6 the hypothesis Θ_r ≥ −k·a that its part (ii) uses (the field `theta_ge` of
the Lean structure). Adds cross-references to the author's fourth report (§6, Proposition 9: (Ind2) acts by unit
scalars at a finite place; §6: fixing D_0 does not fix the label 0 inside the larger capsules), to the fifth report
(Proposition 3 is the height inequality in other variables) and to *Where Theorem 3.11 sits* (Theorems 14, 15 and 22
use the same family q → q^N). The results, the programs, their outputs and the Lean files are unchanged.

Corollary 3.12 of IUT III compares the log-volume −|log q| of the q-pilot object with the log-volume −|log Θ| of the
holomorphic hull of the union of the possible images of the Θ-pilot object, and Theorem 1.10 of IUT IV bounds −|log Θ|
from above; together they give the height inequality. The value of −|log Θ| depends on how the statement is read,
along five axes: the range of the label permutations of (Ind1), container or iteration for (Ind3), the group of (Ind2),
whether the hull is taken, and the archimedean container. Combining the axes found so far gives 36 readings.

The note shows that in each of the 36 readings, also with a bounded Kummer distortion added, Corollary 3.12 and the
upper bound of IV together give the same height inequality (k − 1)|log q| ≤ C, because |log q|, k and C are computed
by one procedure that takes no reading. A reading decides only how the wall (k − 1)|log q| is split between the two
statements: Corollary 3.12 carries (x − 1)|log q| and IV carries (k − x)|log q|, where the split point x is decided by
the (Ind1)-axis alone. No reading makes both loads nonpositive, and in the family obtained by replacing q with q^N, the
statement that holds for every N carries no positive load while the other carries at least the whole wall. These
statements are proved in Lean 4 for a component model, and the 36 readings are computed for the seven explicit initial
Θ-data of the catalogue in [`../initial-theta-catalogue/`](../initial-theta-catalogue/).

**No claim is made about the truth of Corollary 3.12, Theorem 1.10 of IUT IV, or the abc conjecture.** That each axis
other than (Ind1) changes only a bounded remainder rests on a paper argument and on the programs; Lean uses it as a
hypothesis. The 36 readings are the combinations of the axes found so far, not a classification of all readings.

## Files

```
paper/reading_family.pdf            the note
paper/reading_family.tex            its LaTeX source, bibliography included
lean/ReadingFamily.lean             the Lean 4 file of the note (1024 lines, 96 named declarations)
lean/ReadingFamilyAxiomCheck.lean   the same file followed by #print axioms for all 96 named declarations
lean/lakefile.toml                  Lake project file (Mathlib at tag v4.30.0)
lean/lean-toolchain                 leanprover/lean4:v4.30.0
lean/lake-manifest.json             exact revisions of Mathlib and its dependencies
logs/build.txt                      output of `lake env lean ReadingFamily.lean` and the exit code
logs/print_axioms.txt               output of `lake env lean ReadingFamilyAxiomCheck.lean` and the exit code
scripts/iut_compute.py              the program of the walkthrough, version 1.1.0, unchanged
                                    (the same file as ../iut-walkthrough/program/iut_compute.py)
scripts/iut_patterns.py             the hulls of the twelve readings with the hull; --check runs its self-checks
scripts/iut_readings36.py           the 36 readings: theta parts, remainders, split points, loads and verdicts;
                                    --scale N... checks the family q -> q^N
scripts/scan_scale.py               the remainders for N = 1, ..., 40
scripts/thresholds.py               Table 2 of the note
scripts/iut_height.py               U(D): Steps (iv)-(viii) of the proof of Theorem 1.10 of IUT IV, as written
scripts/elementary_height.py        an elementary computation from the statement of Theorem 1.10 alone
scripts/compare_elementary_iut.py   the comparison of the two computations
scripts/shell_lattice.py            exact log-shells of model fields (used by iut_patterns.py --check)
outputs/readings36_all.txt          python3 scripts/iut_readings36.py --all
outputs/readings36_scale.txt        python3 scripts/iut_readings36.py --all --scale 2 3 25
outputs/scan_scale.txt              cd outputs && python3 ../scripts/scan_scale.py D2,D211,D109 40
outputs/results36_scan.json         written by the same command
outputs/thresholds.txt              python3 scripts/thresholds.py
outputs/patterns_all.txt            python3 scripts/iut_patterns.py --all
outputs/patterns_check.txt          python3 scripts/iut_patterns.py --all --check
outputs/height.txt                  python3 scripts/iut_height.py
outputs/elementary.txt              python3 scripts/elementary_height.py
outputs/compare.txt                 python3 scripts/compare_elementary_iut.py
LICENSE                             Creative Commons Attribution 4.0 International (CC BY 4.0)
SHA256SUMS                          checksums of the files above
```

## Reproducing

From this folder, with Python 3.10 or later and sympy, run the commands listed above next to each output. The comments
and the output of the programs are in Japanese, as for the program of the walkthrough; `thresholds.py` prints in
English. The outputs are deterministic except for the computing times printed by `elementary_height.py` and
`compare_elementary_iut.py`. Together the programs take about four minutes on the author's machine.

For Lean:

```
cd lean
lake exe cache get
lake env lean ReadingFamily.lean
lake env lean ReadingFamilyAxiomCheck.lean
```

The logs in `logs/` were produced with the toolchain and Mathlib revision recorded in `lean/`. Every declaration
depends at most on `propext`, `Classical.choice` and `Quot.sound` (`Reading.Admissible` on none); there is no `sorry`
and no added axiom. The note builds with `pdflatex reading_family.tex` (run three times).
