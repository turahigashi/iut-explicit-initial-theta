# Forgetting and completeness: the centre of the passage from Theorem 3.11 to Corollary 3.12 in inter-universal Teichmüller theory

Version 1.1.4, 14 November 2026 (13 pages; Appendix A added in 1.1.0, Disclosure and figure placement corrected in 1.1.1, open-interface count, audit-range wording and the c/s dictionary corrected in 1.1.2, terminology around scale clarified in 1.1.3: the defect Δ is an aggregate readout quantity, and identity of a chart calibration does not by itself identify pilot value-group profiles; in 1.1.4 the description of the Lean development and of the source audit is reworded and the comments of the Lean files are rewritten in English; no proposition, Lean statement, audit status or conclusion changed). DOI [10.5281/zenodo.24209901](https://doi.org/10.5281/zenodo.24209901);
all versions: [10.5281/zenodo.24135420](https://doi.org/10.5281/zenodo.24135420).

The passage from Theorem 3.11 to Corollary 3.12 in inter-universal
Teichmüller theory (IUT) is formulated as a problem of *completeness*
in the sense of abstract interpretation: a forgetful map is complete
for a query if the query factors through it. Sign abstraction
(complete for products, incomplete for sums) and the interval
dependency problem show that completeness is query-relative and that
local completeness at each interface does not compose. In the cited
theory of the preceding note (`where-311-sits`), the
Corollary 3.12-shaped conclusion follows once the scale defect
Δ = (s−1)·vol(θ) is nonpositive, and on extremal data with no slack
this is also necessary; preservation itself is Δ = 0, i.e. s = 1.
Relative to this route, a sufficient condition for the ABC-type
conclusion reduces to whether the aggregate real readout scale is
preserved through the whole transport; no unconditional equivalence
with the ABC conjecture is claimed, and neither Corollary 3.12 nor
ABC is decided. An audit of the interfaces in IUT I–IV and in the
Frobenioid, étale theta and absolute anabelian sources finds the
other audited interfaces locally closed, with two items open: on the
input side, the lift of the Θ-link from bare to marked prime-strips;
on the output side, the identification of the source's holomorphic
hull family with the same-run full-image family. The reduction to a scale
defect itself is credited to Scholze–Stix and to Project LANA's
`xi_iff` (the reciprocal parameterization); what is added here is
the completeness language, the interface-wise localization, and the
consequent shrinking of the formalization target to the interfaces
needed to decide the sign of Δ.

## Contents

- `paper/forgetting-completeness.pdf` — the paper.
- `paper/forgetting-completeness.tex` — its source
  (`pdflatex` twice; TeX Live packages `geometry`, `amsmath`,
  `amssymb`, `amsthm`, `enumitem`, `booktabs`, `longtable`, `array`,
  `tikz`, `hyperref`).
- `lean/CompletenessFrameCore.lean` — the standalone abstract core
  of §3 of the paper (Definition 3.1, Propositions 3.2–3.4 and the
  examples of §2). It depends only on Mathlib and was checked with
  Lean 4.30.0 against Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`,
  within the standard axioms `propext`, `Classical.choice`,
  `Quot.sound` (the restoration lemma and the fibre direction use
  none); the `#print axioms` commands are at the end of the file,
  and their recorded output is in
  `lean/CompletenessFrameCore.check.log`.
- `lean/ActualValuePartCompletenessFrame.lean` — the frame file of
  the author's larger Lean development, including the
  instantiation on value-part classes, reproduced for reference. It
  is not standalone: it is module
  `M3.relative.ActualValuePartCompletenessFrame` of that development
  (commit
  `1e144663259ff07329f2158b3e2043d396fa4d54`), where its selected
  build (341 modules) was verified within the standard three
  axioms.

To check the standalone core in a Lake project with a Mathlib
dependency:

```sh
lake env lean lean/CompletenessFrameCore.lean
```

Independent review has not been received.
