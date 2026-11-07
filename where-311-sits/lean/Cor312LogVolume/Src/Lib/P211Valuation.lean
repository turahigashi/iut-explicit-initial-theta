import Mathlib

noncomputable section
namespace Src.Lib.P211Valuation

instance fact211 : Fact (Nat.Prime 211) := ⟨by norm_num⟩

def pC : ℂ_[211] := ((211 : ℚ_[211]) : ℂ_[211])

lemma norm_pC : ‖pC‖ = (211 : ℝ)⁻¹ := by
  rw [pC, PadicComplex.norm_extends']
  exact_mod_cast Padic.norm_p (p := 211)

lemma norm_pC_lt_one : ‖pC‖ < 1 := by
  rw [norm_pC]; norm_num

theorem exists_qb :
    ∃ q : ℂ_[211], q ^ 7 = pC ^ 29 ∧ ‖q‖ ^ 7 = ‖pC‖ ^ 29 ∧ ‖q‖ < 1 := by
  obtain ⟨q, hq⟩ := IsAlgClosed.exists_pow_nat_eq (pC ^ 29) (n := 7) (by norm_num)
  have hnorm : ‖q‖ ^ 7 = ‖pC‖ ^ 29 := by
    rw [← norm_pow, hq, norm_pow]
  refine ⟨q, hq, hnorm, ?_⟩
  by_contra h
  push_neg at h
  have h1 : (1 : ℝ) ≤ ‖q‖ ^ 7 := one_le_pow₀ h
  rw [hnorm, norm_pC] at h1
  have : ((211 : ℝ)⁻¹) ^ 29 < 1 := by
    apply pow_lt_one₀ (by positivity) (by norm_num) (by norm_num)
  linarith

end Src.Lib.P211Valuation
end
