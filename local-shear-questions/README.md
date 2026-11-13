# Questions on the remaining value-group profile switch from Theorem 3.11 to Corollary 3.12

**Small questions bearing on the central residual in one route to Corollary 3.12 and ABC: globalization of local shears and object membership**

Version 1.0.1, 13 November 2026 (12 pages). DOI [10.5281/zenodo.24199344](https://doi.org/10.5281/zenodo.24199344);
all versions [10.5281/zenodo.24198744](https://doi.org/10.5281/zenodo.24198744).
Author: Toshihisa Urahigashi (independent researcher;
ORCID [0009-0004-0460-6242](https://orcid.org/0009-0004-0460-6242)).

This question note decomposes the remaining value-group profile switch in a conditional assembly from Theorem 3.11 to Corollary 3.12 into small anabelian questions. The questions are not addressed to any particular individual or project; they are addressed broadly to anyone with expertise in the relevant areas who may be able to supply references, corrections, counterexamples, or a better formulation. It asks in which categories degree-moving local shears occur, whether a local shear can be supported at one bad place as part of a global change of model, whether transported degree readouts are invariant under the standard difference of theta sections, what minimal category contains both sections and degree readouts, whether a global section difference exists in pre-IUT vocabulary, and what bridges are needed to return from readout compatibility to object-level membership.

A composite readout statement P′ is distinguished from the two outside bridges. For each question, the note records a complementary division-of-roles relation to Project LANA's (9-1), without presenting itself as an alternative or criticism.

Abstract implication cores used in the reduction map were checked in Lean; the questions themselves and their identification with the actual [EtTh] and IUT constructions are not formalized. The note does not claim a proof or disproof of Corollary 3.12, the ABC conjecture, or the value-group profile switch, and does not claim that the questions are globally unprecedented: the central difficulty is already public, related local claims exist in different frameworks, and the audited range is stated explicitly.

This is the English version of the Japanese preprint draft v0.2 (ronbun9810).

## Contents

- `paper/local-shear-questions.pdf` — the paper (12 pages).
- `paper/local-shear-questions.tex` — TeX source; build with `pdflatex local-shear-questions.tex` (twice).
- `lean/ActualValuePartQuestionImplications.lean` — the Lean-checked abstract implication cores.
- `lean/ActualValuePartProfileIndependence.lean` — the imported profile countermodel used by the transported-readout insufficiency check.
- `lean/Remark395HullIsAClosure.lean` — the defining hull module used by the two files above.
  These Lean files are excerpts of a larger Lean development and are **not standalone** in flattened form; the selected build closing over them (3 modules) was checked in that development. What is machine-checked is only the abstract implication cores listed in the paper — not Q0–Q7, P′, the [EtTh]/IUT constructions, or frame fidelity.
- `SHA256SUMS` — SHA-256 of the files above.

## Status

Question note only. The value-group profile switch H*val (R2V), the IUT black box (R1), inhabitation/frame fidelity (R2) and independent re-verification (R3) remain open, as stated in the paper.
