import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Positivity

namespace CitedLV.PadicLogSummable

open Filter

variable (p : ℕ) [hp : Fact p.Prime]

theorem norm_natCast_ge (n : ℕ) (hn : n ≠ 0) :
    (1 : ℝ) / (n : ℝ) ≤ ‖((n : ℚ_[p]))‖ := by
  have hdvd : p ^ padicValNat p n ∣ n := (padicValNat_dvd_iff_le hn).mpr le_rfl
  have hle : p ^ padicValNat p n ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have hcast : ((n : ℚ_[p])) = (((n : ℚ)) : ℚ_[p]) := by push_cast; ring
  have hne : ((n : ℚ)) ≠ 0 := by exact_mod_cast hn
  have hnorm : ‖((n : ℚ_[p]))‖ = ((padicNorm p (n : ℚ) : ℚ) : ℝ) := by
    rw [hcast]; exact_mod_cast Padic.eq_padicNorm (p := p) (n : ℚ)
  have hval : padicNorm p (n : ℚ) = (p : ℚ) ^ (-(padicValNat p n : ℤ)) := by
    rw [padicNorm, if_neg hne, padicValRat.of_nat]
  rw [hnorm, hval]
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hpowR : ((p : ℝ)) ^ (padicValNat p n) ≤ (n : ℝ) := by exact_mod_cast hle
  have hpowpos : (0 : ℝ) < ((p : ℝ)) ^ (padicValNat p n) := by positivity
  have hcv : (((p : ℚ) ^ (-(padicValNat p n : ℤ)) : ℚ) : ℝ)
       = ((p : ℝ)) ^ (-(padicValNat p n : ℤ)) := by push_cast; ring
  rw [hcv, zpow_neg, zpow_natCast, ← one_div]
  exact one_div_le_one_div_of_le hpowpos hpowR

theorem norm_term_le (x : ℚ_[p]) (n : ℕ) (hn : n ≠ 0) :
    ‖x ^ n / (n : ℚ_[p])‖ ≤ (n : ℝ) * ‖x‖ ^ n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hnorm : (1 : ℝ) / (n : ℝ) ≤ ‖((n : ℚ_[p]))‖ := norm_natCast_ge p n hn
  have hne : ‖((n : ℚ_[p]))‖ ≠ 0 := by
    have : (0:ℝ) < 1 / (n:ℝ) := by positivity
    linarith
  rw [norm_div, norm_pow]
  rw [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne))]
  have h1 : ‖x‖ ^ n * 1 ≤ ‖x‖ ^ n * ((n : ℝ) * ‖((n : ℚ_[p]))‖) := by
    have : (1 : ℝ) ≤ (n : ℝ) * ‖((n : ℚ_[p]))‖ := by
      have := (div_le_iff₀ hnpos).mp hnorm
      linarith [this]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  calc ‖x‖ ^ n = ‖x‖ ^ n * 1 := by ring
    _ ≤ ‖x‖ ^ n * ((n : ℝ) * ‖((n : ℚ_[p]))‖) := h1
    _ = (n : ℝ) * ‖x‖ ^ n * ‖((n : ℚ_[p]))‖ := by ring

theorem summable_log_series (x : ℚ_[p]) (hx : ‖x‖ < 1) :
    Summable (fun n : ℕ => x ^ (n + 1) / ((n + 1 : ℕ) : ℚ_[p])) := by
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => ((n : ℝ) + 1) * ‖x‖ ^ (n + 1))
  · have hgeo : Summable (fun n : ℕ => (n : ℝ) ^ 1 * ‖x‖ ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by simpa using hx)
    have h2 : Summable (fun n : ℕ => ((n : ℝ) + 1) * ‖x‖ ^ (n + 1)) := by
      have := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (r := ‖x‖) (by simpa using hx))
      have hshift : Summable (fun n : ℕ => (((n+1 : ℕ)) : ℝ) ^ 1 * ‖x‖ ^ (n+1)) :=
        (summable_nat_add_iff 1).mpr this
      simpa [pow_one] using hshift
    exact h2
  · intro n
    have hne : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
    have := norm_term_le p x (n + 1) hne
    simpa using this

end CitedLV.PadicLogSummable
