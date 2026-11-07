import Cor312LogVolume.Src.Lib.P211Datum

noncomputable section
namespace Src.Lib.P211LogVolume

open Src.Lib.P211Datum Src.Lib.P211Valuation

theorem qb_log :
    Real.log ‖((qb : ℂ_[211]))‖ = -(29 / 7) * Real.log 211 := by
  have h7 : Real.log (‖((qb : ℂ_[211]))‖ ^ 7) = 7 * Real.log ‖((qb : ℂ_[211]))‖ := by
    simp [Real.log_pow]
  have h29 : Real.log (‖pC‖ ^ 29) = 29 * Real.log ‖pC‖ := by
    simp [Real.log_pow]
  have hpc : Real.log ‖pC‖ = -Real.log 211 := by
    rw [norm_pC, Real.log_inv]
  have := congrArg Real.log qb_ord
  rw [h7, h29, hpc] at this
  linarith

theorem qb_neg_abs_log :
    -|Real.log ‖((qb : ℂ_[211]))‖| = -(29 / 7) * Real.log 211 := by
  have hlt : Real.log ‖((qb : ℂ_[211]))‖ < 0 := by
    rw [qb_log]
    have : (0 : ℝ) < Real.log 211 := Real.log_pos (by norm_num)
    nlinarith
  rw [abs_of_neg hlt, neg_neg, qb_log]

theorem obligationE_target_value_at_p211 :
    ∃ r : ℝ, r = -(29 / 7) * Real.log 211 ∧
      r = -|Real.log ‖((qb : ℂ_[211]))‖| ∧ r < 0 :=
  ⟨-(29 / 7) * Real.log 211, rfl, qb_neg_abs_log.symm, by
    have : (0 : ℝ) < Real.log 211 := Real.log_pos (by norm_num)
    nlinarith⟩

end Src.Lib.P211LogVolume
end
