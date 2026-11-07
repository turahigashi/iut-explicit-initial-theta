# Segment or loop? A homotopy-type-theoretic overview of the dispute over Corollary 3.12 of inter-universal Teichmüller theory

Version 1.4.0, 8 November 2026 (28 pages). DOI [10.5281/zenodo.24039360](https://doi.org/10.5281/zenodo.24039360).
Version 1.3.0: [10.5281/zenodo.23991545](https://doi.org/10.5281/zenodo.23991545); version 1.2.0: [10.5281/zenodo.23991368](https://doi.org/10.5281/zenodo.23991368);
version 1.1.0: [10.5281/zenodo.23933109](https://doi.org/10.5281/zenodo.23933109); version 1.0.0: [10.5281/zenodo.23931344](https://doi.org/10.5281/zenodo.23931344);
all versions: [10.5281/zenodo.23931343](https://doi.org/10.5281/zenodo.23931343). Version 1.1.0 added pointers to Part II of the
companion note (its version 2.0.0). Version 1.2.0 cites the earlier general framework of R. Laniewski
(arXiv:2608.13609), which the author learned of after version 1.1.0 was posted, and claims no priority for it
(abstract and §1.4). Version 1.3.0 also cites the Lean files `Iut/WallEquiv/Basic.lean` and
`Iut/WallEquiv/NonDerivable.lean` of lana-agents/iut (added 13 October 2026), which prove, in models, statements of the
same shape as Theorems 5.3 and 5.7; neither is claimed as new. Both versions update the companion's version and DOI.
The results and the Lean files are unchanged. For version 1.4.0 see "Changes in 1.4.0" below.

The dispute over Corollary 3.12 of IUT III has been conducted in many vocabularies: the identification and labelling
of isomorphic copies, monodromy, segment, loop and universal cover, the properties IPL, SHE and APT, logical AND and
logical OR, descent, commutativity up to indeterminacies, the size of the blurring. The paper states them as
propositions of homotopy type theory about families of ordered real lines over graphs. Identifying copies along one
path loses nothing; two paths make a loop whose monodromy is a complete invariant; Corollary 3.12 is equivalent to a
lax 2-cell between the two paths, an inequality that has the shape of a height bound; a hull taken along the whole
loop says nothing; and IPL, SHE and APT are compatible with any size of the blurring. Applied one level down, to
presented reals and locators, the same tools show no monodromy. None of the results is new mathematically: the
contribution is the formulation and the correspondences. An earlier reading of the dispute in homotopy type theory,
in which the Θ-link is a path in the type of prime-strips that does not lift to the full ring structures, is due to
J. Whaley Jr (*The Theta-link as a path in homotopy type theory*, Zenodo, 15 October 2026). A general semantics for
comparison problems in arithmetic geometry, with labelled presentations and transports carrying costs, appears
earlier, without reference to IUT, in R. Laniewski, *Intensional semantics for comparison problems in arithmetic
geometry* (arXiv:2608.13609); no priority is claimed for that idea. Statements of the same shape as Theorems 5.2, 5.3
and 5.7 and Corollary 5.4 were formalized earlier in Lean, in Takkun-kohinata/IUT_LEAN (July 2026), by sfingali
(Zenodo, August 2026) and, in models, in lana-agents/iut (`Iut/Wall/`, `Iut/WallEquiv/`, October 2026). Each
statement carries a label (S, X, P, R, N, H), and each proposition gives the source of the underlying mathematics.
The quantitative core is checked in Lean 4.

**No claim is made about the truth of Corollary 3.12, Theorem 1.10 of IUT IV, or the abc conjecture.**

A companion note in undergraduate mathematics, *Reading the IUT dispute through indexed identifications*, is in
[`../indexed-identifications/`](../indexed-identifications/) (version 2.3.0; all versions: DOI
[10.5281/zenodo.23931345](https://doi.org/10.5281/zenodo.23931345)). Its Part II extends the model to the components
of tensor packets and the label permutations of (Ind1).

## Changes in 1.4.0

- Cites earlier work that versions up to 1.3.0 did not cite. J. Whaley Jr, *The Theta-link as a path in homotopy type
  theory* (Zenodo, 10.5281/zenodo.23403323, 15 October 2026), an earlier reading of the dispute in homotopy type
  theory, replaces the sentence "As far as the author has checked, no earlier work reads the dispute over Corollary
  3.12 itself through homotopy type theory" (§1.4). Earlier Lean formalizations of statements of the same shape:
  Takkun-kohinata/IUT_LEAN (`slack_lower_bound`, `strict_collapse`; 15 July 2026), sfingali, *The Scholze–Stix
  objection, formally* (Zenodo, 10.5281/zenodo.21757640, 2 August 2026), and Gogopex/iut-lean (labelled copies of the
  real line with positive-scale transports; repository created 29 May 2026) (abstract, §1.4, and the sources of
  Theorems 5.2, 5.3, Corollary 5.4 and Proposition 6.1). Also C. Lando Mills, *Inter-universal Teichmüller theory comes
  home* (Zenodo, 21 September 2026, §18), and, next to Corollary 5.4, Mochizuki's report on formalization (§3) with
  the toy form `height_bounded_of_dilation` of D. Richards' motizukipdf.
- Cites the files `Iut/Wall/Pilots.lean` (`hexagon_commutes_iff`, 11 October 2026) and `Iut/Wall/Constraints.lean`
  (`EtaAlg.sheq_iff_wall`, `EtaAlg.SHESides`, 12 October 2026) of lana-agents/iut, next to Theorem 5.2 and Remark 5.8,
  and says in §1.4 which versions cite which files of lana-agents/iut.
- Narrows the sentence after Corollary 5.4: Theorem 5.3 gives *a* precise form of the sentence of Scholze–Stix on the
  blurring, and sfingali's earlier formalization of that sentence is credited there.
- Remark 5.4′ quotes the sentence of Scholze–Stix (§2.2) on consistent identification instead of a paraphrase in
  quotation marks, and its title says that the identification is not needed in the model.
- Remark 5.8 no longer puts the author's own phrase for the strong reading of SHE in quotation marks; the remark after
  Proposition 6.1 states LANA's reading of (9-1) without quotation marks.
- The "empty inequality" of Scholze–Stix is now paired with the case m = 1 of Theorem 5.2 (in the table of Section 6
  and in the remark after Theorem 5.5), as in the companion note (Proposition 5.3(b)) and in *Where Theorem 3.11 sits*
  (Proposition 26(b)); Theorem 5.5 stays paired with the trivial multiradial representation.
- The key [DH] is renamed [DH1]: it is arXiv:2004.13228v1, whose §1 and §4.6 are cited, and the companion note uses
  [DH] for arXiv:2004.13108v2.
- Adds cross-references to the author's later notes *Where Theorem 3.11 sits* (concept DOI 10.5281/zenodo.24028832),
  *No reading avoids the height inequality*, *Two computations of the height inequality* and *Bridge and size*, and a
  sentence on how the ratio m of this paper is written in each of them and in lana-agents/iut.
- Cites the companion's version 2.3.0 by its concept DOI.

The results, the proofs and the Lean files are unchanged.

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
