import LogShellEdge.Unions

/-!
# Consistency of the hypotheses on `Γ`

The hypotheses put explicit maps into `Γ` (the maps of Proposition 4.4 and the map `M`, which follow from
the realization of Lemma 4.1; the map of Theorem 6.5; Kondo's transvections) and also require every
element of `Γ` to preserve the trace (Γ2). If one of these maps changed the trace, the hypotheses would
be contradictory and every theorem would hold vacuously. The lemmas below show, from Kondo's
description of `ker Tr` alone, that each of these maps does preserve the trace on the basis (hence
everywhere, by linearity). This is checked for the maps that the proofs use, not for the realization
hypothesis of Lemma 4.1 for every free-group automorphism.
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge

variable {p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]

/-- A linear map that preserves `τ` on a basis preserves `τ`. -/
theorem tau_comp_of_basis {ι : Type} [Fintype ι] [DecidableEq ι] (y : Module.Basis ι ℚ_[p] V)
    (τ : V →ₗ[ℚ_[p]] ℚ_[p]) (γ : V →ₗ[ℚ_[p]] V) (h : ∀ i, τ (γ (y i)) = τ (y i)) (x : V) :
    τ (γ x) = τ x := by
  conv_lhs => rw [← y.sum_repr x]
  conv_rhs => rw [← y.sum_repr x]
  simp only [map_sum, map_smul, smul_eq_mul, h]

namespace OddSmall

variable {g : ℕ} (K : OddSmall p V g)

theorem uIdx_ne_zero (k : Fin g) : uIdx k ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp [uIdx] at this

theorem vIdx_ne_zero (k : Fin g) : vIdx k ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp [vIdx] at this

/-- the moves `u ↦ u + v`, `v ↦ v + u` of Proposition 4.4(b) preserve the trace on the basis -/
theorem moveU_tau (k : Fin g) (i : Fin (2 * g + 1)) :
    K.τ (if i = uIdx k then K.y (uIdx k) + K.y (vIdx k) else K.y i) = K.τ (K.y i) := by
  split_ifs with h
  · subst h; rw [map_add, K.hker _ (vIdx_ne_zero k), add_zero]
  · rfl

theorem moveV_tau (k : Fin g) (i : Fin (2 * g + 1)) :
    K.τ (if i = vIdx k then K.y (vIdx k) + K.y (uIdx k) else K.y i) = K.τ (K.y i) := by
  split_ifs with h
  · subst h; rw [map_add, K.hker _ (uIdx_ne_zero k), add_zero]
  · rfl

/-- the swaps of adjacent pairs fix index `0`, hence preserve the trace on the basis -/
theorem swap_tau (k : ℕ) (hk : k + 1 < g) (i : Fin (2 * g + 1)) :
    K.τ (K.y (swapIdx k hk i)) = K.τ (K.y i) := by
  by_cases h0 : i = 0
  · subst h0
    have : swapIdx k hk (0 : Fin (2 * g + 1)) = 0 := by
      apply Fin.ext; simp only [swapIdx]; split_ifs <;> simp_all <;> omega
    rw [this]
  · have hs : swapIdx k hk i ≠ 0 := by
      intro h; apply h0; apply Fin.ext
      have := congrArg Fin.val h
      simp only [swapIdx] at this
      split_ifs at this <;> simp_all <;> omega
    rw [K.hker _ hs, K.hker _ h0]

end OddSmall

namespace EvenSmall

variable {g : ℕ} (K : EvenSmall p V g)

theorem moveT_tau (i : Fin (2 * g)) :
    K.τ (if i = ⟨1, by have := K.hg; omega⟩ then K.y ⟨1, by have := K.hg; omega⟩ +
      K.y ⟨0, by have := K.hg; omega⟩ else K.y i) = K.τ (K.y i) := by
  split_ifs with h
  · subst h; rw [map_add, K.hker ⟨0, by have := K.hg; omega⟩ (by simp), add_zero]
  · rfl

theorem moveU_tau (j : Fin (2 * g)) (hj : 2 ≤ j.val) (i : Fin (2 * g)) :
    K.τ (K.y i + ((formQ i ⟨0, by have := K.hg; omega⟩ : ℤ) : ℚ_[p]) • K.y j +
      ((formQ i j : ℤ) : ℚ_[p]) • K.y ⟨0, by have := K.hg; omega⟩) = K.τ (K.y i) := by
  rw [map_add, map_add, map_smul, map_smul, K.hker j (by omega),
    K.hker ⟨0, by have := K.hg; omega⟩ (by simp)]
  simp

end EvenSmall

namespace CycloData

variable {g : ℕ} (K : CycloData p V g)

/-- the map `M` preserves the trace on the basis -/
theorem moveM_tau (hg2 : 2 ≤ g) (i : Fin (2 * g)) :
    K.τ (if i.val = 1 then K.b i + (K.α : ℚ_[p]) • K.b ⟨0, by omega⟩ + K.b ⟨3, by omega⟩
      else if i.val = 2 then K.b i - (K.α : ℚ_[p]) • K.b ⟨0, by omega⟩ - K.b ⟨3, by omega⟩ else K.b i) =
      K.τ (K.b i) := by
  have h0 : K.τ (K.b ⟨0, by omega⟩) = 0 := K.hker _ (by simp)
  have h3 : K.τ (K.b ⟨3, by omega⟩) = 0 := K.hker _ (by simp)
  split_ifs with h1 h2
  · rw [map_add, map_add, map_smul, h0, h3]; simp
  · rw [map_sub, map_sub, map_smul, h0, h3]; simp
  · rfl

/-- `-1` on the pair `(b 2, b 3)` preserves the trace on the basis -/
theorem kondoNeg_tau (i : Fin (2 * g)) :
    K.τ (if i.val = 2 ∨ i.val = 3 then -K.b i else K.b i) = K.τ (K.b i) := by
  split_ifs with h
  · have : i.val ≠ 1 := by omega
    rw [map_neg, K.hker i this, neg_zero]
  · rfl

/-- a block transvection preserves the trace (its direction `v` lies in `ker τ`) -/
theorem kondoT_tau (v : V) (hv : ∀ i : Fin (2 * g), i.val < 2 → K.b.repr v i = 0) (a : ℤ_[p]) (x : V) :
    K.τ (x + ((a : ℚ_[p]) * blockForm K.b x v) • v) = K.τ x := by
  have hτv : K.τ v = 0 := by
    conv_lhs => rw [← K.b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [map_smul, smul_eq_mul]
    by_cases h : i.val = 1
    · rw [hv i (by omega), zero_mul]
    · rw [K.hker i h, mul_zero]
  rw [map_add, map_smul, hτv, smul_zero, add_zero]

end CycloData


namespace OddKondo

variable {g : ℕ} (K : OddKondo p V g)

/-- a transvection of `W` preserves the trace (its direction lies in `ker τ`) -/
theorem kondoT_tau (v : V) (hv : K.y.repr v 0 = 0) (a : ℤ_[p]) (x : V) :
    K.τ (x + ((a : ℚ_[p]) * oddForm K.y x v) • v) = K.τ x := by
  have hτv : K.τ v = 0 := by rw [K.toOddSmall.tau_eq, hv, zero_mul]
  rw [map_add, map_smul, hτv, smul_zero, add_zero]

/-- the mod-`p` action of Theorem 6.5 is compatible with the trace: `τ(y₁ + y₂) = τ(y₁)` -/
theorem lift_tau (i : Fin (2 * g + 1)) :
    K.τ (if i = 0 then K.y 0 + K.y ⟨1, by have := K.hg; omega⟩ else K.y i) = K.τ (K.y i) := by
  split_ifs with h
  · subst h
    rw [map_add, K.hker ⟨1, by have := K.hg; omega⟩ (by intro h; have := congrArg Fin.val h; simp at this),
      add_zero]
  · rfl

end OddKondo

end LogShellEdge
