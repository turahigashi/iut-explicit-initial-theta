# Scale preservation is not enough: a profile-level independence countermodel for the Corollary 3.12 assembly inputs

Version 1.0.1, 14 November 2026 (9 pages; v1.0.1 adds a remark relating the removed hypothesis (Hloc) to the Lean counterpart of H*val in the assembly note, rewords the description of the Lean build, and rewrites the comments of the Lean files in English with the root namespace of the excerpts renamed — no theorem or conclusion changed). DOI [10.5281/zenodo.24209904](https://doi.org/10.5281/zenodo.24209904);
all versions [10.5281/zenodo.24195283](https://doi.org/10.5281/zenodo.24195283).
Author: Toshihisa Urahigashi (independent researcher;
ORCID [0009-0004-0460-6242](https://orcid.org/0009-0004-0460-6242)).

We exhibit a concrete profile-valued countermodel showing that the
remaining value-group profile switch in a conditional assembly from
Theorem 3.11 to Corollary 3.12 in inter-universal Teichmuller theory
is logically independent of the other assembly inputs. At l=7, with
labels j=1,2,3 at one bad place and normalized unit u=1, the
theta-side readouts are -j^2 and the q-side readouts are -1, with
equal procession weights 1/3. The normalized generator and unit-side
readouts agree, membership, monotonicity, hull domain and both
volume decompositions hold, but the aggregates are -14/3 and -1,
the aggregate scale is forced to 3/14, and the
Corollary-3.12-shaped conclusion fails. For general odd primes
l>=5 the aggregate scale is 12/(l(l+1)).

The countermodel and independence corollary are formalized in Lean 4;
the recorded selected build passes with only the standard three
axioms. The profile and normalizations are the source readouts
(theta values q^{j^2}, plain procession averaging, and the
coefficient comparison in IUT IV Theorem 1.10), not arbitrary
choices.

This note does not claim that Mochizuki's actual construction is
this model, nor that Theorem 3.11, Corollary 3.12, the ABC
conjecture or H*val is false. It proves only that no derivation
exists from the listed inputs once labelwise profile equality is
removed. Further progress requires a genuinely profile-level input
or a richer formalization of the actual construction.

This is the English version of an unpublished Japanese draft.

## Contents

- `paper/profile-independence.pdf` — the paper (9 pages).
- `paper/profile-independence.tex` — TeX source; build with
  `pdflatex profile-independence.tex` (twice).
- `lean/ActualValuePartProfileIndependence.lean` — the countermodel
  and independence theorems.
- `lean/Remark395HullIsAClosure.lean` — defining module for the
  `HullOperator` type and the identity hull `trivialHull` used above.
  These Lean files are excerpts of a larger Lean development and are
  **not standalone** in flattened form; the selected build closing
  over them (2 modules) was checked in that development. What is
  machine-checked is the independence theorem of this note — not the
  assembly paper as a whole, not frame fidelity, and not the actual
  IUT construction.
- `SHA256SUMS` — SHA-256 of the files above.

## Status

Independence result only. The value-group profile switch H*val
(preprint R2V), the IUT black box (R1), inhabitation/frame fidelity
(R2) and independent re-verification (R3) remain open, as stated at
the outset of the paper.
