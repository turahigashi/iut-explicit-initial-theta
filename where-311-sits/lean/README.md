# Lean formalization for *Where Theorem 3.11 sits*

This folder contains the Lean 4 formalization that accompanies

> T. Urahigashi, *Where Theorem 3.11 sits: the log-volume content of the results cited in the
> proof of IUT III, Corollary 3.12, does not imply its conclusion*, version 1.2.1, Zenodo, 2026 (Lean sources unchanged from version 1.1.1).
> DOI [10.5281/zenodo.24044582](https://doi.org/10.5281/zenodo.24044582) (all versions:
> [10.5281/zenodo.24028832](https://doi.org/10.5281/zenodo.24028832)).

Every statement that the paper marks [P] is proved here. The paper states the axioms, the
models and the theorems in ordinary mathematical language, and says what is and what is
not claimed; this README only explains how to check the Lean side.

## What Lean checks, and what it does not

Lean checks that the theorems follow from the definitions and axioms written in these
files: that the models satisfy every axiom of Definition 2 of the paper, that the conclusion
of IUT III, Corollary 3.12, fails in them, that the weak reading of (SHE) follows from the
axioms while the strong readings do not, and that identifying the two pilots, or a degree
scale 1 together with an image of the Θ-pilot of nonzero measure, gives the conclusion.

Lean does not check that the axioms state the cited results of the source correctly. That
correspondence is the inventory of citations in Section 2 of the paper (Table 2) and the
source attached to each axiom of Definition 2, whose strength is discussed in Remark 3; it
is checked against the source, not by Lean. Nothing here claims that IUT III, Corollary 3.12,
is false.

## Requirements

* Lean `v4.30.0` (installed by `elan` from `lean-toolchain`)
* Mathlib `v4.30.0` (pinned in `lake-manifest.json`)

## Build

```sh
lake exe cache get   # downloads the compiled Mathlib
lake build           # builds the 222 modules of Cor312LogVolume
```

## Check the axioms

```sh
lake env lean Verify.lean
```

`Verify.lean` collects, for every declaration defined in the sixteen modules
`Cor312LogVolume/independence/*.lean`, the axioms that it depends on, and fails unless they
are among `propext`, `Classical.choice` and `Quot.sound`. A proof that used `sorry` would
depend on `sorryAx` and fail this check. The library declares no axioms and uses no
`native_decide`.

## Reproduce the mutations of Section 11

```sh
python3 scripts/mutations.py        # all seventeen
python3 scripts/mutations.py m01 m09  # some of them
```

Each mutation edits one file, compiles that file against the built library, and compares
the declarations (and, inside a structure instance, the fields) that fail with what the
paper says. The edits are listed in `scripts/mutations.json`. Where a changed value makes an
unchanged proof fail for a reason that has nothing to do with the property under test (for
instance, a proof that unfolds the old value), the edit also adapts that proof, so that only
the properties that are mathematically broken can fail.

## Where the results of the paper are

All modules are under `Cor312LogVolume/`. The results of the paper are in
`Cor312LogVolume/independence/`; the other directories contain the development they use
(tensor packets with Haar measure, log-shells, theta values, indeterminacies), and
`Cor312LogVolume/Src/` contains statements and constructions taken from the source and
general p-adic lemmas.

Namespaces below are abbreviated: `Cited` is `CitedLV.Independence.Cor312Cited`, `Fam` is
`CitedLV.Independence.Cor312CitedFamily`, `Ramp` is
`CitedLV.Independence.Cor312RamifiedBadPlace`, `Shell` is
`CitedLV.Independence.Cor312RamifiedLogShell`.

| Paper | Lean |
|---|---|
| Definition 2 (cited theory) | `Cited.CitedTheory`; over several places `Fam.CitedTheoryFam` |
| Definition 4 (readings of (SHE)) | `Cited.CitedTheory.WeakSHE`, `StrongSHECarrier`, `StrongSHEValue` |
| Proposition 5 (weak (SHE) holds) | `Cited.CitedTheory.weakSHE_holds`, `Fam.CitedTheoryFam.weakSHE_holds` |
| Proposition 6 (strong readings and (9-1) give the conclusion) | `Cited.CitedTheory.strongValue_iff_conclusion`, `strongCarrier_implies_pilotVolumeMatch`, `pilotVolumeMatch_implies_conclusion` |
| Remark 7 (approximation) | `Cited.approx_le_iff`, `Cited.CitedTheory.approx_iff_conclusion`, `Cited.approx_not_derivable` |
| Definition 8, Lemma 9, Theorem 10 (one place) | `Cited.modelTheory`, `model_weakSHE`, `model_not_conclusion`, `model_linkScale`, `strongCarrier_not_derivable`, `strongValue_not_derivable`, `pilotVolumeMatch_not_derivable` |
| Corollary 11 (where the gap lies) | `Cited.gap_between_readings`, `Fam.gap_between_readings_fam` |
| Theorem 14 (any number of places) | `Fam.robust`, `Fam.concrete`, `Fam.strongCarrier_not_derivable_fam`, `Fam.strongValue_not_derivable_fam`, `Fam.pilotVolumeMatch_not_derivable_fam` |
| Theorem 15 (enlarged container) | `Fam.robust_enlarged`, `Fam.concrete_enlarged`, `Fam.strongCarrier_not_derivable_enlarged`, `Fam.strongValue_not_derivable_enlarged`, `Fam.approx_not_derivable_enlarged` |
| Lemmas 16–18, Definitions 19–20, Lemma 21, Theorem 22 (actual local objects) | `Ramp.ThetaDatum`, `Ramp.rampTheory`, `Ramp.exists_ramified_counterexample`, `Ramp.FB_ramified`, `Ramp.concrete_ramified`; `Shell.logShellSystem`, `Shell.packetLogVolume_eq`, `Shell.stage_hull_le`, `Shell.enlargementL_bounded`, `Shell.logShellTheory`, `Shell.exists_logShell_counterexample`, `Shell.concrete_logShell`, `Shell.robust_logShell`, `Shell.concrete_family`, `Shell.ind2_nontrivial`, `Shell.label_swap_ne`, `Shell.ind1_nontrivial`, `Shell.ind1_strip_nontrivial`, `Shell.ind1_nontrivial_FB` |
| Theorem 24, Proposition 25 (the layer of Step (xi)) | `Cited.CitedTheory.layer_on_every_cited_theory`, `layer_holonomy_trivial`, `restriction_cannot_rescue`, `Cited.layer_does_not_produce_q_value`, and the same in `Fam` |
| Proposition 26 (the two horns) | (a) `Fam.CitedTheoryFam.negLogTheta_le_containers`, `not_conclusion_of_container_gap`; (b) `erased_gives_conclusion`, `erased_linkScale`; (c) `Cited.CitedTheory.conclusion_of_linkScale_one`, `linkScale_ne_one` |

The files `Cor312SourceBound*.lean` in the same directory contain further models built from
source-derived data; they are checked by `Verify.lean` as well.

Two groups of modules are named after the interim report of Project LANA (July 2026).
`Cor312LanaTarget.lean` in this directory states its equality (9-1) (Proposition 6 of the paper). The
twelve modules `Cor312LogVolume/relative/LanaStep6*.lean` are named after Step 6 of its §6.2: they
formalize the generic Kummer construction of its §6.1 and the Kummer-log realization of that step, and
are used by some modules in `Cor312LogVolume/theorem311/` and by the files `Cor312SourceBound*.lean`, not by
the results listed above. These modules were written by the author and contain no code from the LANA repositories.

The source files carry no comments; the paper documents them.

## License

Apache License 2.0; see `LICENSE`.
