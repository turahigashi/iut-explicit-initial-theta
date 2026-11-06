# Segment or loop? A homotopy-type-theoretic overview of the dispute over Corollary 3.12 of inter-universal Teichmüller theory

Version 1.3.0, 6 November 2026 (26 pages). DOI [10.5281/zenodo.23991545](https://doi.org/10.5281/zenodo.23991545).
Version 1.2.0: [10.5281/zenodo.23991368](https://doi.org/10.5281/zenodo.23991368); version 1.1.0: [10.5281/zenodo.23933109](https://doi.org/10.5281/zenodo.23933109);
version 1.0.0: [10.5281/zenodo.23931344](https://doi.org/10.5281/zenodo.23931344). Version 1.1.0 added pointers to Part II of the
companion note (its version 2.0.0). Version 1.2.0 cites the earlier general framework of R. Laniewski
(arXiv:2608.13609), which the author learned of after version 1.1.0 was posted, and claims no priority for it
(abstract and §1.4). Version 1.3.0 also cites the Lean files `Iut/WallEquiv/Basic.lean` and
`Iut/WallEquiv/NonDerivable.lean` of lana-agents/iut (added 13 October 2026), which prove, in models, statements of the
same shape as Theorems 5.3 and 5.7; neither is claimed as new. Both versions update the companion's version and DOI.
The results and the Lean files are unchanged.

The dispute over Corollary 3.12 of IUT III has been conducted in many vocabularies: the identification and labelling
of isomorphic copies, monodromy, segment, loop and universal cover, the properties IPL, SHE and APT, logical AND and
logical OR, descent, commutativity up to indeterminacies, the size of the blurring. The paper states them as
propositions of homotopy type theory about families of ordered real lines over graphs. Identifying copies along one
path loses nothing; two paths make a loop whose monodromy is a complete invariant; Corollary 3.12 is equivalent to a
lax 2-cell between the two paths, an inequality that has the shape of a height bound; a hull taken along the whole
loop says nothing; and IPL, SHE and APT are compatible with any size of the blurring. Applied one level down, to
presented reals and locators, the same tools show no monodromy. None of the results is new mathematically: the
contribution is the formulation and the correspondences. A general semantics for comparison problems in arithmetic
geometry, with labelled presentations and transports carrying costs, appears earlier, without reference to IUT, in
R. Laniewski, *Intensional semantics for comparison problems in arithmetic geometry* (arXiv:2608.13609); no priority
is claimed for that idea. Statements of the same shape as Theorems 5.3 and 5.7 were proved earlier, in models, in the
Lean repository lana-agents/iut (`Iut/WallEquiv/`). Each statement carries a label (S, X, P, R, N, H), and each
proposition gives the source of the underlying mathematics. The quantitative core is checked in Lean 4.

**No claim is made about the truth of Corollary 3.12, Theorem 1.10 of IUT IV, or the abc conjecture.**

A companion note in undergraduate mathematics, *Reading the IUT dispute through indexed identifications*, is in
[`../indexed-identifications/`](../indexed-identifications/) (version 2.2.0, DOI
[10.5281/zenodo.23991546](https://doi.org/10.5281/zenodo.23991546)). Its Part II extends the model to the components
of tensor packets and the label permutations of (Ind1).

## Files

```
paper/segment_or_loop.pdf    the paper
paper/segment_or_loop.tex    its LaTeX source, bibliography included
lean/SegmentOrLoop.lean      the Lean 4 file of Appendix A
lean/lakefile.toml           Lake project file (Mathlib at tag v4.30.0)
lean/lean-toolchain          leanprover/lean4:v4.30.0
lean/lake-manifest.json      exact revisions of Mathlib and its dependencies
logs/print_axioms.txt        output of `lake env lean SegmentOrLoop.lean`: the #print axioms lines and the exit code
LICENSE                      Creative Commons Attribution 4.0 International (CC BY 4.0)
SHA256SUMS                   checksums of the files above
```

## Reproducing

```
cd lean
lake exe cache get
lake env lean SegmentOrLoop.lean
```

The log in `logs/` was produced with the toolchain and Mathlib revision recorded in `lean/`. Every declaration
depends at most on `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry` and no added axiom. The paper
builds with `pdflatex segment_or_loop.tex` (run three times).
