import Mathlib

namespace SrcLib.PadicLog

open Polynomial

variable (p : ℕ) [hp : Fact p.Prime]
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]

theorem norm_algebraMap_padicInt (r : ℤ_[p]) : ‖algebraMap ℤ_[p] K r‖ = ‖r‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K, norm_algebraMap', PadicInt.algebraMap_apply,
    PadicInt.norm_def]

theorem norm_padicInt_smul (r : ℤ_[p]) (y : K) : ‖r • y‖ = ‖r‖ * ‖y‖ := by
  rw [Algebra.smul_def, norm_mul, norm_algebraMap_padicInt]

variable {p}

theorem norm_le_one_of_isIntegral {x : K} (hx : IsIntegral ℤ_[p] x) : ‖x‖ ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨g, hmonic, hg⟩ := hx
  have hg' : aeval x g = 0 := by rwa [aeval_def]
  set n := g.natDegree with hn
  rw [aeval_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree, one_smul] at hg'
  have hxn : x ^ n = -∑ i ∈ Finset.range n, g.coeff i • x ^ i := eq_neg_of_add_eq_zero_right hg'
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero, Finset.range_zero, Finset.sum_empty, neg_zero] at hxn
    exact one_ne_zero hxn
  have hx0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hbound : ‖∑ i ∈ Finset.range n, g.coeff i • x ^ i‖ ≤ ‖x‖ ^ (n - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hx0 _)
    intro i hi
    rw [norm_padicInt_smul, norm_pow]
    have hi' : i ≤ n - 1 := by have := Finset.mem_range.mp hi; omega
    calc ‖g.coeff i‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i :=
          mul_le_mul_of_nonneg_right (g.coeff i).norm_le_one (pow_nonneg hx0 _)
      _ = ‖x‖ ^ i := one_mul _
      _ ≤ ‖x‖ ^ (n - 1) := pow_le_pow_right₀ h.le hi'
  have hlhs : ‖x ^ n‖ ≤ ‖x‖ ^ (n - 1) := by rw [hxn, norm_neg]; exact hbound
  rw [norm_pow] at hlhs
  have : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ h (by omega)
  linarith

variable [FiniteDimensional ℚ_[p] K]

theorem isIntegral_of_norm_le_one {x : K} (hx : ‖x‖ ≤ 1) : IsIntegral ℤ_[p] x := by
  classical
  have hball : ∀ y ∈ Algebra.adjoin ℤ_[p] {x}, ‖y‖ ≤ 1 := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact hx
    | algebraMap r => rw [norm_algebraMap_padicInt]; exact r.norm_le_one
    | add y z _ _ hy hz => exact (IsUltrametricDist.norm_add_le_max y z).trans (max_le hy hz)
    | mul y z _ _ hy hz =>
      exact (norm_mul_le y z).trans (by nlinarith [norm_nonneg y, norm_nonneg z])
  let b := Module.finBasis ℚ_[p] K
  let f : K →L[ℚ_[p]] (Fin (Module.finrank ℚ_[p] K) → ℚ_[p]) :=
    LinearMap.toContinuousLinearMap b.equivFun.toLinearMap
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt ‖f‖ hp1
  let N : Submodule ℤ_[p] K := Submodule.span ℤ_[p] (Set.range fun j => ((p : ℚ_[p]) ^ M)⁻¹ • b j)
  have hN : ∀ y : K, ‖y‖ ≤ 1 → y ∈ N := by
    intro y hy
    rw [← b.sum_equivFun y]
    refine Submodule.sum_mem _ fun j _ => ?_
    set c := b.equivFun y j with hcdef
    have hcf : ‖c‖ ≤ ‖f‖ := by
      have h1 : ‖c‖ ≤ ‖f y‖ := norm_le_pi_norm (f y) j
      have h2 : ‖f y‖ ≤ ‖f‖ * ‖y‖ := f.le_opNorm y
      have h3 : ‖f‖ * ‖y‖ ≤ ‖f‖ := by nlinarith [norm_nonneg f, norm_nonneg y]
      linarith
    have hpM : (0 : ℝ) < (p : ℝ) ^ M := pow_pos (by linarith) M
    have hc : ‖(p : ℚ_[p]) ^ M * c‖ ≤ 1 := by
      rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
      rw [inv_mul_le_iff₀ hpM, mul_one]
      linarith
    let r : ℤ_[p] := ⟨(p : ℚ_[p]) ^ M * c, hc⟩
    have hpM0 : ((p : ℚ_[p]) ^ M) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    have hr : c • b j = r • (((p : ℚ_[p]) ^ M)⁻¹ • b j) := by
      rw [← algebraMap_smul ℚ_[p] r, PadicInt.algebraMap_apply, smul_smul]
      congr 1
      change c = ((p : ℚ_[p]) ^ M * c) * ((p : ℚ_[p]) ^ M)⁻¹
      field_simp
    rw [hr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hfg : (Algebra.adjoin ℤ_[p] {x}).toSubmodule.FG :=
    Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) (fun y hy => hN y (hball y hy))
  exact IsIntegral.of_mem_of_fg _ hfg x (Algebra.self_mem_adjoin_singleton ℤ_[p] x)

theorem isIntegral_iff_norm_le_one (x : K) : IsIntegral ℤ_[p] x ↔ ‖x‖ ≤ 1 :=
  ⟨norm_le_one_of_isIntegral, isIntegral_of_norm_le_one⟩

end SrcLib.PadicLog

section Model

example (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) : IsIntegral ℤ_[p] x ↔ ‖x‖ ≤ 1 :=
  SrcLib.PadicLog.isIntegral_iff_norm_le_one x

end Model

section Check
end Check
