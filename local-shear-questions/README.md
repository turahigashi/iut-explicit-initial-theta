# Questions on the remaining value-group profile switch from Theorem 3.11 to Corollary 3.12

**Where is it supplied? A central question with a test, and component questions on local shears and object membership**

Version 2.0.0, 14 November 2026 (24 pages). DOI [10.5281/zenodo.24213391](https://doi.org/10.5281/zenodo.24213391);
all versions [10.5281/zenodo.24198744](https://doi.org/10.5281/zenodo.24198744); version 1.0.2: [10.5281/zenodo.24209905](https://doi.org/10.5281/zenodo.24209905).
Author: Toshihisa Urahigashi (independent researcher;
ORCID [0009-0004-0460-6242](https://orcid.org/0009-0004-0460-6242)).

Version 2.0.0 adds a central question and makes it the main question of the note. In Step (xi) of the proof of Corollary 3.12, the inequality is drawn from the property (SHE) in the form stated in Step (xi-e). The step is the value-group counterpart of a compatibility that is proved on the unit side; since the two profiles differ by the factors j² between the labels, the counterpart has to be an inclusion in the hull rather than an isomorphism. The note locates where the source divides the two sides (Step (i) of the proof splits the Θ-link into a unit part and a value part, and the compatibilities of Theorem 3.11(iii) concern the unit part), and finds no statement that carries the value part to regions in the common container. It reads five places that could supply that one edge (the family of possible images, the holomorphic hull, the identification of theta and Gaussian monoids, the compatibility statement of Theorem 3.11(iii)(c), and the global realified Frobenioids of Step (xii)) as holding in the author's own models of the cited statements, built from actual local objects and described in the note (a local model at a finite extension of Q_p, and a profile countermodel at ℓ = 7), in which the step fails. It asks which property of the actual construction excludes those models, that is, where the models fail to represent the construction, or which of the readings is wrong. This is a reading, not a claim that the construction does not supply the step. The note names five places where these readings are least certain (the internal structure of the value parts that Step (xi-b) sets aside, the size of the container, the family of possible images of Propositions 3.1–3.10, the global ingredients, and the consequences of categorical statements for regions), so that a pointer on any one of them is an answer. Several works show that this form does not follow from what the proof cites about the output of the multiradial algorithm of Theorem 3.11; whether the construction of the algorithm itself supplies the step, and if so where, is not decided by them. The note asks that question in a form that can be answered by pointing to a statement or to a passage of a proof. It states what the step must deliver in terms of local fields, log-shells and Haar measure; lists what is known not to suffice; gives a test that any candidate must pass, using models of the cited statements built from actual local objects; lists places in the source where one might look; and classifies the possible answers.

Together with IUT IV the step has the strength of an explicit height inequality. Every proof of such an inequality has a step of this strength where its content enters; the note uses the fact only as a criterion by which a supplier, once found, can be recognized, and not as evidence for or against its existence.

The questions are not addressed to any particular individual or project; they are addressed to anyone with relevant expertise who can supply a reference, a correction, a counterexample or a better formulation. Answers can be sent by e-mail (title page) or posted as an issue in this repository; one line in one of the forms of Section 1.7 is enough.

The small questions Q0–Q7 of version 1 (categories of local shears, their globalization, transported degree readouts, minimal categories, a global section difference, a Tate computation, and two return bridges) are kept, in appendices, as component questions about one route, through the difference of the theta and algebraic sections of [EtTh], and this version answers them provisionally: the difference of sections does not move degree readouts, a degree-moving freedom is one positive scalar common to all places, and the route does not carry the profile switch. Their statements and the composite Statement P′ are unchanged.

Earlier work on the same passage is cited: Higuchi; Pajo; Takkun-kohinata/IUT_LEAN; Saito; sfingali; Geiger; Project LANA's interim report and its Lean repository lana-agents/iut; Mochizuki's report on formalization; and D. Richards' motizukipdf.

Abstract implication cores used in the component questions were checked in Lean (unchanged from version 1), and a new standalone Lean file checks the elementary forms that the readings of the central question use; the readings themselves, the questions themselves and their identification with the actual [EtTh] and IUT constructions are not formalized. The note does not claim a proof or disproof of Corollary 3.12, the ABC conjecture, or the value-group profile switch, and it does not claim that the construction fails to supply the step.

This is the English version of an unpublished Japanese draft.

## Contents

- `paper/local-shear-questions.pdf` — the paper (24 pages).
- `paper/local-shear-questions.tex` — TeX source; build with `pdflatex local-shear-questions.tex` (three times).
- `lean/CentralQuestionReadings.lean` — new in version 2.0.0: the elementary forms that the readings (a)–(e) of the central question use (19 theorems). **Standalone**: it depends only on Mathlib; checked with Lean 4.30.0 against Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` (for instance `lake env lean CentralQuestionReadings.lean` inside a Lake project that requires that Mathlib revision), and `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`. Examples in the file show that the main hypotheses are needed. It checks the forms used by the readings, not the readings themselves.
- `lean/ActualValuePartQuestionImplications.lean` — the Lean-checked abstract implication cores.
- `lean/ActualValuePartProfileIndependence.lean` — the imported profile countermodel used by the transported-readout insufficiency check.
- `lean/Remark395HullIsAClosure.lean` — the defining hull module used by the two files above.
  These Lean files are excerpts of a larger Lean development and are **not standalone** in flattened form; the selected build closing over them (3 modules) was checked in that development. What is machine-checked is only the abstract implication cores listed in the paper — not the central question, Q0–Q7, P′, the [EtTh]/IUT constructions, or frame fidelity. These three excerpts are unchanged from version 1.0.2.
- `SHA256SUMS` — SHA-256 of the files above.

## Status

Question note only. The value-group profile switch H*val (R2V), the IUT black box (R1), inhabitation/frame fidelity (R2) and independent re-verification (R3) remain open, as stated in the paper.
