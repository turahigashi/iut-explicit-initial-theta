# Lean formalization for *How far automorphisms move the ring of integers*

This folder contains the Lean 4 formalization that accompanies version 1.1.0 of

> T. Urahigashi, *How far automorphisms of a p-adic absolute Galois group move the ring of integers:
> to the edge of the log-shell, with an application to Step (v) of IUT IV*, Zenodo, 2026.

The note marks the statements it proves with [P]. This folder checks most of those proofs from
explicit hypotheses: the results the note cites ([S]), and some classical facts about local fields that
are not in Mathlib, are hypotheses of the theorems (fields of structures), never axioms. The tables below
say what is checked, what is assumed, and what is not formalized. Section 12 of the note says the same in
ordinary language.

## What Lean checks, and what it does not

Lean checks that the conclusions follow from the hypotheses written in these files. It does not check
that the hypotheses state the cited results correctly; that is checked against the cited texts.

In most files the field `K` is replaced by a model: a `ℚ_p`-vector space `V` with the lattices
`L j = 𝔪^j` (`Filtration`: `L (j + e) = p L j`, strictly decreasing), a basis `y` of `Λ = L 1`, the
linear form `τ = Tr/p`, and a subgroup `Γ` of linear automorphisms (the maps `α₊`). The multiplication
of `K`, the group `G_K` and the reciprocity map are not formalized; what the proofs use about them
enters through the hypotheses listed below. `SmallLog.lean` works with an actual complete ultrametric
normed field.

## Requirements and build

* Lean `v4.30.0` (installed by `elan` from `lean-toolchain`)
* Mathlib `v4.30.0` (pinned in `lake-manifest.json`)

```sh
lake exe cache get   # downloads the compiled Mathlib
lake build           # builds the library LogShellEdge
lake env lean Verify.lean
```

`Verify.lean` prints the axioms of the main results. Each depends only on (a subset of) `propext`,
`Classical.choice` and `Quot.sound`. The library declares no axioms and uses no `sorry` and no
`native_decide`.

## Hypotheses

| Structure / hypothesis | Fields | Source in the note |
|---|---|---|
| `Filtration` | `L`, `shift`, `strict` | `𝔪^(j+e) = p 𝔪^j` |
| `SmallField` | `Γ`, `y`, `hΛ` | `Λ = log U¹ = 𝔪` with `Z_p`-basis `y` (Lemmas 2.2(b), 3.2) |
| | `f`, `hdeg`, `hcard` | `d = e f`; `dim_{F_p} 𝔪^r/p𝔪 = f(e+1-r)` |
| | `hΓ1`, `hΓ2` | Proposition 2.3 ([Hoshi], [HN, Lemma 2.3(ii)]) |
| | `pc`, `hpc`, `hpcτ` | Lemma 2.2(d) |
| `OddSmall`, `EvenSmall` | `hker` | [Kondo, Theorem 1.3] |
| | `hτ0`, `hτ1` | Lemma 3.4 (`lemma34` proves it from `hker` and Lemma 2.2(d)) |
| | `moveU`, `moveV`, `swap`, `moveT` | derived from `RealizesOdd`/`RealizesEven` (`Assemble.lean`) |
| `RealizesOdd`, `RealizesEven` | | Lemma 4.1 with Theorem 3.1: an automorphism of the free group on `z_1, …, z_d` fixing `z_1` and the boundary word is realized in `Γ` by its abelianization in the basis `y` |
| `OddTR` | `pv`, `hpv`, `hpvτ`, `hLe` | `p ∈ ℚ_p ⊂ K`; `Tr(p) = pd`, `p ∤ d`; `𝔪^e/p𝔪 = F_p p̄` when `f = 1` |
| | `s`, `hs`, `lift` | `s(K) = 1` and Theorem 6.5 |
| `OddLattice` | `lift` | Theorem 6.5 (Corollary 6.8, `k` not necessarily small) |
| `CycloData` | `hL2`, `hL1`, `hcardR`, `hcard`, `hw1`, `hw2`, `htr`, `htrp`, `hΓm` | Lemma 8.5 |
| | `hΓΛ`, `hΓ2` | Proposition 2.3 |
| | `b`, `α`, `y`, `hy0`, `hyj`, `hker`, `hτ1` | Lemma 8.6 ([HN, Proposition 1.1, Lemma 1.3], [Kondo, Theorem 1.3]) |
| | `kondoT`, `kondoNeg` | [Kondo26, Lemma 3.3] |
| | `hR` | Lemma 4.1 (`moveM` is derived from it, `RealizeCyclo.lean`) |
| `OddKondo` | `kondoT`; `s`, `hs`, `lift` | [Kondo26, Lemma 3.3]; Theorem 6.5 |
| `SmallLog` | `hρe`, `hep`, `hdisc` | `ρ = ‖π‖`, `ρ^e = ‖p‖`, `e ≤ p-2`; the open unit ball of `K` is the closed ball of radius `ρ` |
| `prop83`, `thm811` | `hC`, `h2` | the invariance of `log C_K` (Lemmas 8.1, 8.2) |

## Where the results are

| Note | Lean |
|---|---|
| Lemma 2.2(a)(b) | `SmallLog.mu_p_not_subset`, `SmallLog.eq_one_of_pow_eq_one`, `SmallLog.log1p_bijOn`, `SmallLog.norm_log1p_eq`, `SmallLog.log_hom_on_ball` |
| Proposition 2.5 | `upper`, `S_le_lo`, `S_shift`, `reaches_shift` |
| Lemma 3.2 (module computation) | `lemma32_core`, `ShearRelation.isUnit_of_relation` |
| Lemma 3.4 | `lemma34` |
| Lemma 4.1 (group-theoretic part) | `lemma41_descends`, `fixes_relation` |
| Lemmas 4.2, 4.3 | `FG.mulAE_cmt`, `FG.mulBE_cmt`, `FG.pairSwap_delta`, `ShearFreeGroup.Z_delta`, `H_delta`, `J_delta`, `M_a`, `M_delta`, `M_ab` |
| Proposition 4.4 | `oddMoves_of_realizes`, `evenMoves_of_realizes` |
| Lemmas 5.2, 5.3, 5.4 | `EvenSmall.lemma52`, `OddSmall.lemma53`, `OddSmall.lemma54` |
| Theorem 5.1 | `EvenSmall.thm51_even`, `OddSmall.thm51_odd`, `thm51c_of_inputs` |
| Theorem 6.1, Proposition 6.2 | `OddTR.thm61_i`, `OddTR.thm61_ii`, `OddTR.prop62` (the main implication) |
| Theorem 6.5 (group-ring identities of steps (2)–(4), (6)) | `GroupRing.adjRule_of_unit`, `adjRule_of_mem_adjoin`, `c_spec`, `c_mem_ker`, `eps_mu`, `eps_nu`, `E_mem`, `exists_zeta`, `coinv_action_basis`, `relCoinv_action_basis` |
| Corollary 6.6 | `OddTR.cor66` |
| Theorem 6.7 | `main_even_of_inputs`, `main_odd_f2_of_inputs`, `main_odd_tr_of_inputs` |
| Corollary 6.8, Remark 6.9 | `OddLattice.cor68`, `OddLattice.rem69` |
| Theorem 7.1 (the orders; the hull of a unit) | `ord_identity`, `lo_div`, `unit_smul_subset_hull` |
| Corollary 7.2 | `cor72_even`, `cor72_odd_f2`, `cor72_odd_tr` |
| Lemmas 8.1, 8.2 (cores), Proposition 8.3 | `lemma81`, `lemma82_core`, `prop83` |
| Lemma 8.6 (module computation) | `lemma86_span` |
| Lemmas 8.7, 8.8, Theorem 8.9 | `CycloData.lemma87`, `CycloData.lemma88`, `CycloData.thm89` |
| Theorem 8.11 | `thm811` |
| Proposition 8.13 | `OddKondo.prop813a_full`, `OddKondo.prop813a_tr`, `OddKondo.prop813c_a_not_add`, `CycloData.prop813b`, `CycloData.prop813c_b_not_add`, `card_union_a`, `card_union_b` |

All names are in the namespace `LogShellEdge`.

## Not formalized

* Lemma 2.2(c) and the proof of 2.2(d) (the element `pc` is a hypothesis), Remark 5.5, Lemma 8.5 (its
  statements are hypotheses of `CycloData`), Examples 7.3 and 8.10, Remark 10.2.
* In Lemma 4.1, the identification of `α₊` on `Λ` with the abelianization (through the reciprocity map
  and `log`); Lemma 3.2 beyond the module computation.
* In Theorem 6.5, the computation in the free pro-`p` operator group and the lifting (Theorem 6.3); also
  `θR = I₀` (assumed in `exists_zeta`) and Proposition 6.4.
* In Theorem 7.1, the passage from the orders to the holomorphic hull of [Tiers].
* In Lemmas 8.1 and 8.2, the identification of the groups with the unit groups and the transfer.

## Consistency of the hypotheses

`Consistency.lean` checks that the maps that the proofs put into `Γ` (the maps of Proposition 4.4, the
map `M`, the map of Theorem 6.5, Kondo's transvections) preserve `τ`, so that they do not contradict
(Γ2). This is not checked for the realization hypothesis for every free-group automorphism.

## Reused code

The files in `LogShellEdge/Reuse/` (the automorphisms `Z`, `H`, `J`, `M` of the free group on four
letters, two module lemmas, and the logarithm series over `ℚ_p` and over complete ultrametric normed
fields) are adapted from an earlier, unpublished Lean development of the author: comments were
rewritten, namespaces renamed and a few unused statements removed.

## Files

| File | Contents |
|---|---|
| `Basic.lean` | `lo`, `Filtration`, `S`, `Reaches`, Proposition 2.5 |
| `Small.lean`, `Coord.lean` | `SmallField`; coordinates and norms |
| `SmallLog.lean` | Lemma 2.2(a)(b) |
| `Presentation.lean` | Lemma 4.1 (group-theoretic part), Lemma 3.2 (module computation), Lemma 3.4 |
| `FreeGroupMoves.lean` | the free-group automorphisms of Section 4 and their abelianizations |
| `Realize.lean`, `RealizeCyclo.lean`, `Assemble.lean` | Proposition 4.4 and the map `M` from Lemma 4.1; the main results from the hypotheses |
| `Odd.lean`, `Even.lean`, `OddMain.lean`, `Extra.lean`, `MainTheorem.lean` | Sections 5 and 6 |
| `GroupRing.lean` | the group-ring identities in the proof of Theorem 6.5 |
| `StepV.lean` | Theorem 7.1 (the orders) |
| `Radical.lean` | Lemmas 8.1, 8.2 (cores), Proposition 8.3, Theorem 8.11 |
| `Symplectic.lean`, `Residue.lean`, `Cyclo.lean`, `Unions.lean` | Section 8 |
| `Consistency.lean` | the maps put into `Γ` preserve `τ` |
| `Reuse/` | reused files (see above) |
| `Verify.lean` | axiom check |
