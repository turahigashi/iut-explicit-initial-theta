# Reading the IUT dispute through indexed identifications: an educational model in undergraduate mathematics

Version 2.3.0, 8 November 2026 (28 pages). DOI [10.5281/zenodo.24039367](https://doi.org/10.5281/zenodo.24039367).
Version 2.2.0: [10.5281/zenodo.23991546](https://doi.org/10.5281/zenodo.23991546); version 2.1.0: [10.5281/zenodo.23991371](https://doi.org/10.5281/zenodo.23991371);
version 2.0.0: [10.5281/zenodo.23933108](https://doi.org/10.5281/zenodo.23933108); version 1.0.0: [10.5281/zenodo.23931346](https://doi.org/10.5281/zenodo.23931346);
all versions: [10.5281/zenodo.23931345](https://doi.org/10.5281/zenodo.23931345). Version 2.1.0 cites the earlier general notation of
R. Laniewski (arXiv:2608.13609), which the author learned of after version 2.0.0 was posted, and claims no priority
for it (abstract and §1.4). Version 2.2.0 also cites the Lean files `Iut/WallEquiv/Basic.lean` and
`Iut/WallEquiv/NonDerivable.lean` of lana-agents/iut (added 13 October 2026), which prove, in models, that Step (xi) is
equivalent to the inequality of Part I. Both versions update the companion's version and DOI. The results and the
Lean files are unchanged. For version 2.3.0 see "Changes in 2.3.0" below.

An educational model that states the shape of the dispute over Corollary 3.12 of IUT III using only undergraduate
mathematics: sets and maps, multiplication of positive real numbers, graphs and inequalities. Instead of the equality
sign it uses a symbol x ≈_f y that records which identification is used, with four rules declared at the outset.
Mochizuki's own elementary numerical model and the three options described by Scholze–Stix then sit on one
inequality, (k−1)Q ≤ E. Labelled copies of the real line with named transports (Gogopex/iut-lean, May 2026) and the
options of Scholze–Stix (Takkun-kohinata/IUT_LEAN, July 2026; sfingali, Zenodo, August 2026) were formalized earlier
in Lean by others; no priority is claimed for them.

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
Lean, is in [`../segment-or-loop/`](../segment-or-loop/) (version 1.4.0; all versions: DOI
[10.5281/zenodo.23931343](https://doi.org/10.5281/zenodo.23931343)).

## Changes in 2.3.0

- Rephrases the opening of §1.4 ("Elementary explanations of the dispute have been given by the parties themselves").
  After the parties' own explanations it now credits earlier Lean models of the same identification problem by
  others: Gogopex/iut-lean (labelled copies of the real line with positive-scale transports, file
  `Iut/Foundations/RealLineCopy.lean`; repository created 29 May 2026), Takkun-kohinata/IUT_LEAN (`strict_collapse`,
  `relabeling_vacuous`; 15 July 2026) and sfingali, *The Scholze–Stix objection, formally* (Zenodo,
  10.5281/zenodo.21757640, 2 August 2026). The clause "what this note adds is the use of such a notation for the
  explanations of the two sides" is replaced by one plain sentence on what the note adds, and no priority is claimed
  for labelled real lines with named transports. The abstract mentions these works in one sentence.
- Says which versions cite which files: version 1.0.0 cited no file of lana-agents/iut, and versions 1.0.0–2.1.0 did not
  cite the files of `Iut/WallEquiv/` (cited from 2.2.0).
- Defines, next to the quoted inequality (s−1)a ≤ V of lana-agents/iut, its letters in lana's sense: s = l(l+1)/12 is
  the k of this note, a = |log q| is the Q of this note (not its a = −Q), and V is the log-volume of the hull of the
  container VC(I) (not the set of places of Setup 12.1).
- Adds cross-references to the author's later notes *Where Theorem 3.11 sits* (concept DOI 10.5281/zenodo.24028832),
  *No reading avoids the height inequality* (concept DOI 10.5281/zenodo.23965951; its Theorem 3.2 extends Theorem
  14.3(ii) here), *The gap between the two walls is positive* (concept DOI 10.5281/zenodo.23954193; its (Ind2)-terms
  relate to the E of Setup 12.1(f)), *Two computations of the height inequality* and *Bridge and size*, and a sentence
  on how the number k is written in each of them, in the companion paper and in lana-agents/iut.
- Also cites J. Whaley Jr, *The Theta-link as a path in homotopy type theory* (Zenodo, 15 October 2026), as an earlier
  reading of the dispute in homotopy type theory; Higuchi (31 March 2026) and Pajo (26 April 2026), next to the remark
  that the model admits both kinds of model; and, next to Corollary 7.2, Mochizuki's report on formalization (§3) with
  the toy form `height_bounded_of_dilation` of D. Richards' motizukipdf.
- The entry [DH] (arXiv:2004.13108v2, whose §6.2, footnote 7, is cited) now says which version is cited; the companion
  paper now uses [DH1] for arXiv:2004.13228v1, so that the two notes no longer use one key for two papers.
- Cites the companion's version 1.4.0 by its concept DOI.

The results, the proofs and the Lean files are unchanged.

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
