# A conditional assembly from Theorem 3.11 to Corollary 3.12: decomposition of the scalar layer, a semantic principle, and isolation of the value-group profile switch

Version 1.0.3, 14 November 2026 (16 pages; v1.0.3 rewrites the comments of the Lean files in English and renames the root namespace of the excerpts; v1.0.2 redraws Figure 1 and its caption, checks in Lean the relations drawn for the assembly range B (`lean/VennRegionB.lean`), and corrects the Lean counterpart of H*val in the table of §1 from `hmem` alone to `hmem` and `hlocal` — no result or conclusion changed). DOI [10.5281/zenodo.24209900](https://doi.org/10.5281/zenodo.24209900);
all versions [10.5281/zenodo.24166924](https://doi.org/10.5281/zenodo.24166924).
Author: Toshihisa Urahigashi (independent researcher;
ORCID [0009-0004-0460-6242](https://orcid.org/0009-0004-0460-6242)).

This note reports a conditional assembly of the passage from Theorem 3.11
to Corollary 3.12 in inter-universal Teichmüller theory, expanding the
seams treated in the source by abbreviation conventions and citations to
numbered results. It does not claim an unconditional proof of
Corollary 3.12 or of the ABC conjecture. Accepting the numbered
statements of IUT I–IV as black boxes, Mochizuki's non-IUT papers and
classical results as known inputs, a semantic Principle S, and the
value-group switch H*val as an explicit input, each step of the passage
is filled by named grounds. Of what was underivable in the preceding
note *Where Theorem 3.11 sits*, the scalar layer (chart calibration,
generator scalars, transport distortion) is supplied at the statement
level; what remains at the centre is the profile layer: identity of
chart calibration does not imply equality of pilot value-group profiles,
and the switch from a Gaussian $j^2$ profile to an actual $q$-pilot
representation (H*val), together with frame fidelity, is open.

This is the English version of the Japanese preprint draft v0.4
(summary and main proofs). The detailed working draft is cited as [W].

## Contents

- `paper/cor312-assembly.pdf` — the paper (16 pages).
- `paper/cor312-assembly.tex` — TeX source; build with
  `pdflatex cor312-assembly.tex` (twice).
- `lean/*.lean` — Lean excerpts referred to in the text, reproduced for
  reference: the capstone `Cor312Assembly.lean`, the arithmetic
  inhabitation `FVdashArithmeticInstance.lean`, the prime-strip skeleton
  `FVdashPrimeStripSkeleton.lean`, the square-independence audit
  `ShapeDoesNotDecide.lean`, the Tate model-pair file
  `ActualValuePartLocalCancellationTate.lean`, and the check of Figure 1
  `VennRegionB.lean` (relations drawn for the assembly range B, for each
  reading of H*val; it imports two modules of the same development and
  was compiled with Lean 4.30.0 against the same Mathlib pin). These are
  excerpts of a
  larger Lean development and are **not standalone**; the selected build
  closing over them (353 modules) was checked in that development.
  What is machine-checked is sufficiency of the assembly and the
  model-level statements named in the text — not the paper proof as a
  whole, and not frame fidelity or the value-group switch.
- `SHA256SUMS` — SHA-256 of the files above.

## Status

Conditional assembly only. Remaining items are listed at the outset of
the paper: (R1) the IUT black box, (R2V) the value-group switch H*val,
(R2) inhabitation of Principle S in the actual construction (frame
fidelity), (R3) independent re-verification, and (R4) explicit
constants only.

## Disclosure

Generative AI was used, under the author's direction, in the proofs,
assembly, audit, formalization, and preparation of the Japanese and
English drafts. The author bears responsibility for the contents. The
author's own complete reading of the sources is in progress.
