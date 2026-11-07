# A local non-containment in Step (v) of IUT IV, Theorem 1.10

Version 3.1.0, 8 November 2026 (9 pages).
This version: DOI [10.5281/zenodo.24039373](https://doi.org/10.5281/zenodo.24039373). Version 3.0.0:
[10.5281/zenodo.23852752](https://doi.org/10.5281/zenodo.23852752).
Archived at DOI [10.5281/zenodo.23166432](https://doi.org/10.5281/zenodo.23166432) (all versions).

This note presents an explicit local non-containment calculation for a datum with two places of
multiplicative reduction above the prime 30965771. A pure tensor obtained from a theta value by a label
permutation remains outside the comparison module under every factorwise log-shell-preserving
automorphism. Its application to the possible-image union in Step (v) of IUT IV, Theorem 1.10 is
conditional on the membership and orbit-closure readings (M) and (R) in Section 4, including the
compatibility with the cited constructions of the local-coordinate descriptions used in Lemmas 3
and 4. Under those assumptions, the corresponding hull component has larger log-volume than the
displayed bound. A complete identification with the source construction is not established in this note.

Section 6 relates the reading (R) to the literal reading of Corollary 3.12 and to the reading with the
theta value at the label j used in Step (v), as formalized in the public Lean repository
[lana-agents/iut](https://github.com/lana-agents/iut), and, using the distinctions recorded there, places the example in a two-by-two
classification by reading and by whether the orders of the q-parameters at the places above p agree.

No assertion is made about Corollary 3.12 itself, the final global inequality of Theorem 1.10, or the
abc conjecture. This is a preprint; it has not been refereed.

The first report in this repository compared a different datum, at the prime 211, with the local
estimates of IUT IV; the source application of that comparison was withdrawn in its version 0.1.7. This
note is a separate paper, not a revision of the first report: its datum has two places above the prime,
both of multiplicative reduction, and it neither cites nor relies on the first report.

## Changes in version 3.1.0

Cites earlier work. The public Lean repository
[Takkun-kohinata/IUT_LEAN](https://github.com/Takkun-kohinata/IUT_LEAN) (15 July 2026) singled out the
containment tested here, with λ = ord(q^{j²}), as the one input of the chain from Theorem 3.11 to the height
inequality that its formalization could not confirm; its route is different (volume preservation, without label
permutations or explicit data). Version 1.0.0 of this note was audited publicly in
[Luminescence10086/Inter-universal-Teichmuller-Theory](https://github.com/Luminescence10086/Inter-universal-Teichmuller-Theory)
(first commits 20 October 2026), which computed the exponent 107/35, listed the membership and closure conditions,
and pointed to IUT III, Remark 3.11.4(i), before version 2.0.0 added these points; earlier versions did not cite
either. A sentence cites Zeng (Zenodo, first version 29 October 2026) on the hull of IUT III, Remark 3.9.5.
Section 6 gains a pointer to the treatment of primes with a good and a bad place in the catalogue
([`../initial-theta-catalogue/`](../initial-theta-catalogue/), Proposition 1 (GB), Theorem 3) and, in models, in
Indexed identifications (Proposition 13.3, Theorem 14.3(iv)) and Reading family (Example 3.7). The title page now
prints the version and the DOI, and its dates agree with the Dates paragraph (version 2.0.0: 29 October 2026).
The mathematical statements, proofs and numbers are unchanged.

## Changes in version 3.0.0

A new Section 6 cites the public Lean repository lana-agents/iut, whose file
`Iut/Concrete/Literal.lean` (added on 11 October 2026, UTC) formalizes the literal reading of
Corollary 3.12 and IUT IV's reading with the label j. It shows that the reading (R) of this note
corresponds to the literal reading, adds Proposition 6 (the elements of Lemmas 3 and 4 lie in the
comparison module unless the reading is (R) and two bad places above p have different orders of the
q-parameter), and places the datum D2 in a two-by-two classification (Table 2), noting that for D2 the difference between the two readings exceeds the allowance in the bound of Step (v). The abstract mentions
this comparison, and Section 4 gains a pointer to Section 6; Sections 1-5 are otherwise unchanged.

## Changes in version 2.0.0

The revised note makes the conditional scope of the application explicit, adds discussion of the
choice of theta representative and related expositions, and clarifies that the simplified example
in Dupuy–Hilado, Section 6.2, omits the tensor-factor permutations present in the actual (Ind1).

## Files

```
paper/stepv_local_noncontainment.pdf   the note (9 pages)
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

The supplied PDF has nine pages. Rebuilding may change PDF metadata and byte checksums even when the
pages are unchanged.

## Use of generative AI

Generative AI tools (large language models: Claude by Anthropic, and ChatGPT and Codex by OpenAI) were
used extensively in this work, under the author's direction: in finding the example and its proofs, in
the computations, in checking the statements against the cited sources, and in writing the text. The
author takes full responsibility for the contents of this note.

Copyright 2026 Toshihisa Urahigashi. The files in this folder are licensed under the Creative Commons
Attribution 4.0 International License (CC BY 4.0); see `LICENSE`. The rest of this repository remains
under the Apache License, Version 2.0.
