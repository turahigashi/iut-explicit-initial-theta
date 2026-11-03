# Segment or loop? A homotopy-type-theoretic overview of the dispute over Corollary 3.12 of inter-universal Teichmüller theory

Version 1.0.0, 4 November 2026 (24 pages). DOI [10.5281/zenodo.23931344](https://doi.org/10.5281/zenodo.23931344).

The dispute over Corollary 3.12 of IUT III has been conducted in many vocabularies: the identification and labelling
of isomorphic copies, monodromy, segment, loop and universal cover, the properties IPL, SHE and APT, logical AND and
logical OR, descent, commutativity up to indeterminacies, the size of the blurring. The paper states them as
propositions of homotopy type theory about families of ordered real lines over graphs. Identifying copies along one
path loses nothing; two paths make a loop whose monodromy is a complete invariant; Corollary 3.12 is equivalent to a
lax 2-cell between the two paths, an inequality that has the shape of a height bound; a hull taken along the whole
loop says nothing; and IPL, SHE and APT are compatible with any size of the blurring. Applied one level down, to
presented reals and locators, the same tools show no monodromy. None of the results is new mathematically: the
contribution is the formulation and the correspondences. Each statement carries a label (S, X, P, R, N, H), and each
proposition gives the source of the underlying mathematics. The quantitative core is checked in Lean 4.

**No claim is made about the truth of Corollary 3.12, Theorem 1.10 of IUT IV, or the abc conjecture.**

A companion note in undergraduate mathematics, *Reading the IUT dispute through indexed identifications*, is in
[`../indexed-identifications/`](../indexed-identifications/) (DOI
[10.5281/zenodo.23931346](https://doi.org/10.5281/zenodo.23931346)).

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
