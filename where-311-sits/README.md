# Where Theorem 3.11 sits: the log-volume content of the results cited in the proof of IUT III, Corollary 3.12, does not imply its conclusion

Version 1.2.0, 10 November 2026 (28 pages). DOI [10.5281/zenodo.24044582](https://doi.org/10.5281/zenodo.24044582) (version DOI to be assigned at upload);
all versions: [10.5281/zenodo.24028832](https://doi.org/10.5281/zenodo.24028832).

The inequality of Corollary 3.12 of IUT III is obtained in Step (xi) of its proof, where the author states that he
will be concerned only with certain qualitative properties of the multiradial algorithm of Theorem 3.11. The note
lists every target that the corollary and its proof cite (164 citations of 63 targets; full list in Appendix A of the paper and in `inventory_v120.csv`), keeps the 22 that the proof
uses as definitions or premises, and states their content as axioms about normalized log-volumes of regions in
tensor packets with Haar measure, at the strength of the source. A weak reading of the property (SHE) follows from
these axioms. The conclusion of Corollary 3.12 fails in models of the axioms, one of which is built from the actual
local objects at a finite extension of Q_p. Two strong readings of (SHE), and the equality (9-1) that the interim
report of Project LANA identifies as the missing step, each imply the conclusion, and none of them follows from the
axioms.

A Venn diagram (Figure 1) displays the position: the models of the cited theory lie inside the class of weak (SHE)
and not inside that of the conclusion, and among them the conclusion holds exactly where strong (SHE) holds. The
statement "3.11.5" that Mochizuki isolates in his report on formalization corresponds to that intersection. Results of
the same shape were proved earlier: for abstractions of the passage by Higuchi and Pajo, and in Lean by
Takkun-kohinata/IUT_LEAN (July 2026) and by [lana-agents/iut](https://github.com/lana-agents/iut) of Project LANA
(October 2026), which proves non-derivability from a package of what it proves at the level of Theorem 3.11 and
separates two readings of (SHE); Saito (July 2026) audits the passage against a registered inventory of the source,
and sfingali (August 2026) formalizes the core of the Scholze–Stix objection. The results here were obtained
independently of these Lean works, which were made public first. What this note adds is that the axioms are the
results that the proof actually cites, at the strength of the source, and that the models are built on actual local
objects.

**We do not claim that Corollary 3.12 is false, nor anything about abc.** The result concerns what follows from the
statements that the proof cites, including what Theorem 3.11 states about the output of its algorithm; whether the
construction of the algorithm itself supplies the missing membership is not decided here.

## Changes in 1.2.0

The citation inventory is corrected (independent recount, 10 November 2026): the earlier
"152 citations of 61 targets" came from an inventory extracted from a Japanese translation,
which grouped [IUTchI] §§4, 5, 6 as one target and missed twelve textual occurrences. The paper
now fixes the counting rule in §2 and reports 164 occurrences of 63 targets; the target set is
otherwise the same and no role assignment changes. Table 2 names all fifteen premise targets
(including the twelve remarks previously left unnamed), Appendix A lists every target with its
count and role, and §9 disposes of the five premise remarks it previously did not mention
(Rems. 1.5.2, 3.8.1, 3.9.2, 3.9.3, 3.12.2). The three sources not cited in Corollary 3.12 directly
([IUT III] Props. 3.5(ii), 3.2(ii) and Rem. 3.9.1) are marked † in §2. Consulted author versions
corrected to December 2020 for IUT II and April 2020 for IUT IV. No statement proved in the paper
and no Lean source (`.lean`) changes; the recorded runs of 7 November 2026 stand.

## Changes in 1.1.1

Section 11 now says which modules are named after the interim report of Project LANA (July 2026):
`independence/Cor312LanaTarget.lean` states its equality (9-1), and the twelve modules
`relative/LanaStep6*.lean` are named after Step 6 of its §6.2; they formalize the generic Kummer
construction of its §6.1 and the Kummer-log realization of that step, and are used by further models,
not by the statements of the paper. These modules were written by the author and contain no code from
the LANA repositories. Earlier versions did not say this, and the comments that gave the origin had been
removed from the published sources. `lean/README.md` says the same. The Lean sources are unchanged.

## Changes in 1.1.0

Cites earlier work that versions 1.0.0 and 1.0.1 did not: Takkun-kohinata/IUT_LEAN (July 2026), Saito (July 2026),
sfingali (August 2026), Geiger (August 2026), Zeng (October 2026), and the files `Iut/Wall/Constraints.lean` and
`Iut/Wall/EtaAlg.lean` of lana-agents/iut (October 2026), whose readings (C2) and (C3) of (SHE) correspond to the weak
reading and to (9-1) here. Corrects a date: versions 1.0.x said that the author learned of the non-derivability file
of lana-agents/iut on 4 November 2026; the author's records show that it was known by 1 November 2026. The text and
the Lean sources of the results were completed in September 2026. Describes the Lean port of D. Richards more fully,
and adds cross-references to the author's other notes (Two computations, Segment or loop?, Indexed identifications,
No reading avoids the height inequality, Bridge and size, the fourth and fifth reports) and a key to the notation
used for the degree scale across them. The Lean sources are unchanged.

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
