# Reading the IUT dispute through indexed identifications: an educational model in undergraduate mathematics

Version 2.2.0, 6 November 2026 (26 pages). DOI [10.5281/zenodo.23991546](https://doi.org/10.5281/zenodo.23991546).
Version 2.1.0: [10.5281/zenodo.23991371](https://doi.org/10.5281/zenodo.23991371); version 2.0.0: [10.5281/zenodo.23933108](https://doi.org/10.5281/zenodo.23933108);
version 1.0.0: [10.5281/zenodo.23931346](https://doi.org/10.5281/zenodo.23931346). Version 2.1.0 cites the earlier general notation of
R. Laniewski (arXiv:2608.13609), which the author learned of after version 2.0.0 was posted, and claims no priority
for it (abstract and §1.4). Version 2.2.0 also cites the Lean files `Iut/WallEquiv/Basic.lean` and
`Iut/WallEquiv/NonDerivable.lean` of lana-agents/iut (added 13 October 2026), which prove, in models, that Step (xi) is
equivalent to the inequality of Part I. Both versions update the companion's version and DOI. The results and the
Lean files are unchanged.

An educational model that states the shape of the dispute over Corollary 3.12 of IUT III using only undergraduate
mathematics: sets and maps, multiplication of positive real numbers, graphs and inequalities. Instead of the equality
sign it uses a symbol x ≈_f y that records which identification is used, with four rules declared at the outset.
Mochizuki's own elementary numerical model and the three options described by Scholze–Stix then sit on one
inequality, (k−1)Q ≤ E.

Part II, new in version 2.0.0, opens the single number E. Read backwards from the public Lean formalization
lana-agents/iut, the notation gains values on the components of tensor packets, indices that pair a permutation of the
factors with identifications on the components, a declared order for hulls and averages, and a record of provenance.
In a model with one prime and the label permutations of (Ind1), the two readings of the union in Corollary 3.12 differ
by an expected order statistic, which vanishes exactly when all places above the prime have the same q-order; for
either reading, Corollary 3.12 and the upper bound of IV together imply the height bound. The note separates what is
agreed from what is disputed, and does not decide the latter. It ends with exercises and their answers. Each statement
carries a label (S, P, R, N, H).

**No claim is made about the truth of Corollary 3.12, Theorem 1.10 of IUT IV, or the abc conjecture.**

The companion paper, which states the model of Part I in homotopy type theory and checks its quantitative core in
Lean, is in [`../segment-or-loop/`](../segment-or-loop/) (version 1.3.0, DOI
[10.5281/zenodo.23991545](https://doi.org/10.5281/zenodo.23991545)).

## Files

```
paper/indexed_identifications.pdf    the note
paper/indexed_identifications.tex    its LaTeX source, bibliography included
lean/Components.lean                 the Lean 4 file of Appendix A (Part II)
lean/lakefile.toml                   Lake project file (Mathlib at tag v4.30.0)
lean/lean-toolchain                  leanprover/lean4:v4.30.0
lean/lake-manifest.json              exact revisions of Mathlib and its dependencies
logs/print_axioms.txt                output of `lake env lean Components.lean`: the #print axioms lines and the exit code
LICENSE                              Creative Commons Attribution 4.0 International (CC BY 4.0)
SHA256SUMS                           checksums of the files above
```

## Reproducing

```
cd lean
lake exe cache get
lake env lean Components.lean
```

The log in `logs/` was produced with the toolchain and Mathlib revision recorded in `lean/`. Every declaration
depends at most on `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry` and no added axiom. The note
builds with `pdflatex indexed_identifications.tex` (run three times).
