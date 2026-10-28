# A local non-containment in Step (v) of IUT IV, Theorem 1.10

Version 2.0.0, 29 October 2026 (7 pages).
This version: DOI [10.5281/zenodo.23737179](https://doi.org/10.5281/zenodo.23737179).
Archived at DOI [10.5281/zenodo.23166432](https://doi.org/10.5281/zenodo.23166432) (all versions).

This note presents an explicit local non-containment calculation for a datum with two places of
multiplicative reduction above the prime 30965771. A pure tensor obtained from a theta value by a label
permutation remains outside the comparison module under every factorwise log-shell-preserving
automorphism. Its application to the possible-image union in Step (v) of IUT IV, Theorem 1.10 is
conditional on the membership and orbit-closure readings (M) and (R) in Section 4, including the
compatibility with the cited constructions of the local-coordinate descriptions used in Lemmas 3
and 4. Under those assumptions, the corresponding hull component has larger log-volume than the
displayed bound. A complete identification with the source construction is not established in this note.

No assertion is made about Corollary 3.12 itself, the final global inequality of Theorem 1.10, or the
abc conjecture. This is a preprint; it has not been refereed.

The first report in this repository compared a different datum, at the prime 211, with the local
estimates of IUT IV; the source application of that comparison was withdrawn in its version 0.1.7. This
note is a separate paper, not a revision of the first report: its datum has two places above the prime,
both of multiplicative reduction, and it neither cites nor relies on the first report.

## Changes in version 2.0.0

The revised note makes the conditional scope of the application explicit, adds discussion of the
choice of theta representative and related expositions, and clarifies that the simplified example
in Dupuy–Hilado, Section 6.2, omits the tensor-factor permutations present in the actual (Ind1).

## Files

```
paper/stepv_local_noncontainment.pdf   the note (7 pages)
paper/stepv_local_noncontainment.tex   its LaTeX source, bibliography included
LICENSE                                Creative Commons Attribution 4.0 International (CC BY 4.0)
SHA256SUMS                             SHA-256 checksums of the files above
```

## Building the PDF

```
cd paper
pdflatex -interaction=nonstopmode -halt-on-error stepv_local_noncontainment.tex
pdflatex -interaction=nonstopmode -halt-on-error stepv_local_noncontainment.tex
```

The supplied PDF has seven pages. Rebuilding may change PDF metadata and byte checksums even when the
pages are unchanged.

## Use of generative AI

Generative AI tools (large language models: Claude by Anthropic, and ChatGPT and Codex by OpenAI) were
used extensively in this work, under the author's direction: in finding the example and its proofs, in
the computations, in checking the statements against the cited sources, and in writing the text. The
author takes full responsibility for the contents of this note.

Copyright 2026 Toshihisa Urahigashi. The files in this folder are licensed under the Creative Commons
Attribution 4.0 International License (CC BY 4.0); see `LICENSE`. The rest of this repository remains
under the Apache License, Version 2.0.
