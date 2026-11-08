import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.Span.Basic

/-!
# A relation whose quotient is torsion-free

`exists_isUnit_coord_of_torsionFree`: if `v ≠ 0` and `ℤ_p^ι / ℤ_p v` is torsion-free, some coordinate
of `v` is a unit. `isUnit_of_relation`: for `v = h e_{i₀} - p^s e_{i₁}` with `s ≥ 1`, `h` is a unit.
Used in Lemma 3.2 (`lemma32_core`).

Adapted from an earlier, unpublished Lean development of the author: the comments were
rewritten, the namespace was renamed and a few unused summary statements were removed; the
remaining definitions and proofs are unchanged.
-/

set_option autoImplicit false

namespace LogShellEdge.ShearRelation

variable {p : ℕ} [Fact p.Prime] {ι : Type*}

theorem exists_isUnit_coord_of_torsionFree (v : ι → ℤ_[p]) (hv : v ≠ 0)
    (htf : ∀ (c : ℤ_[p]) (w : ι → ℤ_[p]), c ≠ 0 →
      c • w ∈ Submodule.span ℤ_[p] {v} → w ∈ Submodule.span ℤ_[p] {v}) :
    ∃ i, IsUnit (v i) := by
  by_contra hno
  rw [not_exists] at hno
  have hdvd : ∀ i, (p : ℤ_[p]) ∣ v i := fun i => by
    rw [← PadicInt.norm_lt_one_iff_dvd]
    exact lt_of_le_of_ne (PadicInt.norm_le_one _) fun h => hno i (PadicInt.isUnit_iff.2 h)
  choose w hw using hdvd
  have hpw : (p : ℤ_[p]) • w = v := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, hw i]
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hwv := htf p w hp0 (by rw [hpw]; exact Submodule.mem_span_singleton_self v)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hwv
  have h1 : (1 - c * (p : ℤ_[p])) • w = 0 := by
    rw [sub_smul, one_smul, mul_smul, hpw, hc, sub_self]
  have hunit : IsUnit (1 - c * (p : ℤ_[p])) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (mul_mem_nonunits_right PadicInt.p_nonunit)
  have hw0 : w = 0 := hunit.smul_eq_zero.1 h1
  exact hv (by rw [← hpw, hw0, smul_zero])

theorem isUnit_of_relation [DecidableEq ι] (i₀ i₁ : ι) (h01 : i₀ ≠ i₁) (h : ℤ_[p]) (s : ℕ) (hs : 1 ≤ s)
    (htf : ∀ (c : ℤ_[p]) (w : ι → ℤ_[p]), c ≠ 0 →
      c • w ∈ Submodule.span ℤ_[p] {Pi.single i₀ h - Pi.single i₁ ((p : ℤ_[p]) ^ s)} →
      w ∈ Submodule.span ℤ_[p] {Pi.single i₀ h - Pi.single i₁ ((p : ℤ_[p]) ^ s)}) :
    IsUnit h := by
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hps : ¬ IsUnit ((p : ℤ_[p]) ^ s) := fun hu =>
    PadicInt.p_nonunit ((isUnit_pow_iff (by omega : s ≠ 0)).1 hu)
  have hv1 : (Pi.single i₀ h - Pi.single i₁ ((p : ℤ_[p]) ^ s) : ι → ℤ_[p]) i₁ = -((p : ℤ_[p]) ^ s) := by
    rw [Pi.sub_apply, Pi.single_eq_of_ne h01.symm, Pi.single_eq_same, zero_sub]
  have hv0 : (Pi.single i₀ h - Pi.single i₁ ((p : ℤ_[p]) ^ s) : ι → ℤ_[p]) ≠ 0 := by
    intro hz
    have := congrFun hz i₁
    rw [hv1, Pi.zero_apply, neg_eq_zero] at this
    exact pow_ne_zero s hp0 this
  obtain ⟨i, hi⟩ := exists_isUnit_coord_of_torsionFree _ hv0 htf
  by_cases h0 : i = i₀
  · subst h0
    rwa [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h01, sub_zero] at hi
  · by_cases h1 : i = i₁
    · subst h1
      rw [hv1] at hi
      exact absurd ((IsUnit.neg_iff _).1 hi) hps
    · rw [Pi.sub_apply, Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h1, sub_zero] at hi
      exact absurd hi not_isUnit_zero

end LogShellEdge.ShearRelation
