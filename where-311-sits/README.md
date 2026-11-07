# Where Theorem 3.11 sits: the log-volume content of the results cited in the proof of IUT III, Corollary 3.12, does not imply its conclusion

Version 1.0.1, 7 November 2026 (23 pages). DOI [10.5281/zenodo.24030772](https://doi.org/10.5281/zenodo.24030772);
all versions: [10.5281/zenodo.24028832](https://doi.org/10.5281/zenodo.24028832).

The inequality of Corollary 3.12 of IUT III is obtained in Step (xi) of its proof, where the author states that he
will be concerned only with certain qualitative properties of the multiradial algorithm of Theorem 3.11. The note
lists every result that the corollary and its proof cite (152 citations of 61 targets), keeps the 22 that the proof
uses as definitions or premises, and states their content as axioms about normalized log-volumes of regions in
tensor packets with Haar measure, at the strength of the source. A weak reading of the property (SHE) follows from
these axioms. The conclusion of Corollary 3.12 fails in models of the axioms, one of which is built from the actual
local objects at a finite extension of Q_p. Two strong readings of (SHE), and the equality (9-1) that the interim
report of Project LANA identifies as the missing step, each imply the conclusion, and none of them follows from the
axioms.

A Venn diagram (Figure 1) displays the position: the models of the cited theory lie inside the class of weak (SHE)
and not inside that of the conclusion, and among them the conclusion holds exactly where strong (SHE) holds. The
statement "3.11.5" that Mochizuki isolates in his report on formalization corresponds to that intersection. For the
same passage, the public repository [lana-agents/iut](https://github.com/lana-agents/iut) of Project LANA proves in
Lean non-derivability from a package collecting what it proves at the level of Theorem 3.11; the results here were
obtained independently of it, and it was made public first.

**We do not claim that Corollary 3.12 is false, nor anything about abc.** The result concerns what follows from the
statements that the proof cites, including what Theorem 3.11 states about the output of its algorithm; whether the
construction of the algorithm itself supplies the missing membership is not decided here.

## Changes in 1.0.1

The disclosure now says what was done: the proofs were found with generative AI tools under the author's direction;
every statement marked [P] is checked in Lean; the correspondence between the axioms and the cited results is
checked against the source texts and not by Lean; the author's own reading of the proofs is still in progress; the
author takes full responsibility for the paper. Version 1.0.0 said instead that the author had checked every proof,
computation and reference, and that the author had checked each inclusion of Figure 1; those sentences are removed.
Section 10 now states that only Theorem 1 of the first report (the initial Θ-datum) is used, and not the source
application of its Theorems 5 and 6, which version 0.1.7 of that report withdrew. Nothing else changed; the Lean
sources are identical. Version 1.0.0: DOI [10.5281/zenodo.24028833](https://doi.org/10.5281/zenodo.24028833), tag
v0.23.0.

## Files

```
paper/where-311-sits.pdf     the note
paper/where-311-sits.tex     its LaTeX source (the figure is drawn with TikZ; bibliography included)
lean/                        the Lean 4 formalization of every statement marked [P] (Lean v4.30.0, Mathlib v4.30.0);
                             see lean/README.md for what Lean checks and what it does not
LICENSE                      Creative Commons Attribution 4.0 International (CC BY 4.0), for the paper and this README
lean/LICENSE                 Apache License 2.0, for the Lean sources
SHA256SUMS                   checksums of the files in this folder
```

## Checking

```
cd lean
lake exe cache get      # the compiled Mathlib
lake build              # the 222 modules of Cor312LogVolume
lake env lean Verify.lean
python3 scripts/mutations.py
```

Recorded on 7 November 2026 with Lean v4.30.0 and Mathlib v4.30.0: `lake build` built the 222 modules with no
errors and no `sorry`; `Verify.lean` checked 642 declarations in the 16 modules that carry the results, all of
which depend on at most `propext`, `Classical.choice` and `Quot.sound`; and `scripts/mutations.py` reported
"17/17 mutations behave as the paper states". The library declares no axioms and uses no `native_decide`. Lean
does not check that the axioms state the cited results correctly; see `lean/README.md` and Section 2 of the note.

The PDF is built with `pdflatex where-311-sits.tex` (three runs) in `paper/`. The quotations in the note are taken
from the English originals.
