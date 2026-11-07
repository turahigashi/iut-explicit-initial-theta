import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Src.CoreLayer.LogVol

open Real Finset

theorem one_div_sub_two_le_four_div (p : ℝ) (hp : 3 ≤ p) : 1 / (p - 2) ≤ 4 / p := by
  have h2 : (0:ℝ) < p - 2 := by linarith
  have hp0 : (0:ℝ) < p := by linarith
  rw [div_le_div_iff₀ h2 hp0]
  linarith

theorem p_div_sub_one_le_two (p : ℝ) (hp : 2 ≤ p) : p / (p - 1) ≤ 2 := by
  have h1 : (0:ℝ) < p - 1 := by linarith
  rw [div_le_iff₀ h1]
  linarith

theorem two_log_le_self (p : ℝ) (hp : 2 ≤ p) : 2 * Real.log p ≤ p := by
  have hp0 : (0:ℝ) < p := by linarith
  have hs0 : (0:ℝ) ≤ p := le_of_lt hp0
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hs0
  have hsn : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hspos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0

  have h1 : Real.log (Real.sqrt p) ≤ Real.sqrt p - 1 := Real.log_le_sub_one_of_pos hspos

  have h2 : Real.log p = 2 * Real.log (Real.sqrt p) := by
    rw [Real.log_sqrt hs0]; ring

  have h3 : 4 * Real.sqrt p - 4 ≤ p := by
    have : 0 ≤ (Real.sqrt p - 2) ^ 2 := sq_nonneg _
    nlinarith [hsq]
  calc 2 * Real.log p = 4 * Real.log (Real.sqrt p) := by rw [h2]; ring
    _ ≤ 4 * (Real.sqrt p - 1) := by linarith
    _ = 4 * Real.sqrt p - 4 := by ring
    _ ≤ p := h3

theorem two_div_le_inv_log (p : ℝ) (hp : 2 ≤ p) : 2 / p ≤ 1 / Real.log p := by
  have hp0 : (0:ℝ) < p := by linarith
  have hl : 0 < Real.log p := Real.log_pos (by linarith)
  rw [div_le_div_iff₀ hp0 hl]
  have := two_log_le_self p hp
  linarith

theorem four_div_mul_log_le_two (p : ℝ) (hp : 2 ≤ p) : (4 / p) * Real.log p ≤ 2 := by
  have hp0 : (0:ℝ) < p := by linarith
  have := two_log_le_self p hp
  rw [div_mul_eq_mul_div, div_le_iff₀ hp0]
  linarith

theorem log_two_mul_le (e : ℝ) (he : 0 < e) : Real.log (2 * e) ≤ 1 + Real.log e := by
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  rw [Real.log_mul (by norm_num) (ne_of_gt he)]
  linarith

theorem index_contribution (p e a b : ℝ) (hp : 2 ≤ p) (he : 0 < e)
    (ha : a - 1 / e ≤ 4 / p)
    (hb : (b + 1 / e) * Real.log p ≤ Real.log (2 * e)) :
    (a + b) * Real.log p ≤ 3 + Real.log e := by
  have hl : 0 < Real.log p := Real.log_pos (by linarith)
  have hsplit : (a + b) * Real.log p
      = (a - 1 / e) * Real.log p + (b + 1 / e) * Real.log p := by ring
  have h1 : (a - 1 / e) * Real.log p ≤ (4 / p) * Real.log p :=
    mul_le_mul_of_nonneg_right ha (le_of_lt hl)
  have h2 : (4 / p) * Real.log p ≤ 2 := four_div_mul_log_le_two p hp
  have h3 : Real.log (2 * e) ≤ 1 + Real.log e := log_two_mul_le e he
  rw [hsplit]
  linarith

theorem neg_floor_le (x : ℝ) : -(⌊x⌋ : ℝ) ≤ -x + 1 := by
  have := Int.sub_one_lt_floor x
  linarith

theorem floor_scaled_volume_bound (p x baseVol : ℝ) (hp : 2 ≤ p) :
    baseVol - (⌊x⌋ : ℝ) * Real.log p ≤ baseVol + (-x + 1) * Real.log p := by
  have hl : 0 < Real.log p := Real.log_pos (by linarith)
  have := neg_floor_le x
  nlinarith [hl]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_ab_le (Istar : Finset ι) (p : ℝ) (hp : 2 ≤ p)
    (e a b : ι → ℝ) (he : ∀ i, 0 < e i)
    (ha : ∀ i ∈ Istar, a i - 1 / e i ≤ 4 / p)
    (hb : ∀ i ∈ Istar, (b i + 1 / e i) * Real.log p ≤ Real.log (2 * e i))
    (hout : ∀ i ∉ Istar, a i + b i = 0) :
    ((∑ i, a i) + (∑ i, b i)) * Real.log p ≤ ∑ i ∈ Istar, (3 + Real.log (e i)) := by
  have hsum : (∑ i, a i) + (∑ i, b i) = ∑ i ∈ Istar, (a i + b i) := by
    rw [← Finset.sum_add_distrib]
    exact (Finset.sum_subset (Finset.subset_univ Istar)
      (fun x _ hx => hout x hx)).symm
  rw [hsum, Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro i hi
  exact index_contribution p (e i) (a i) (b i) hp (he i) (ha i hi) (hb i hi)

theorem second_inequality (Istar : Finset ι) (p : ℝ) (hp : 2 ≤ p)
    (e a b d : ι → ℝ) (lam : ℝ) (he : ∀ i, 0 < e i)
    (ha : ∀ i ∈ Istar, a i - 1 / e i ≤ 4 / p)
    (hb : ∀ i ∈ Istar, (b i + 1 / e i) * Real.log p ≤ Real.log (2 * e i))
    (hout : ∀ i ∉ Istar, a i + b i = 0) :
    -((⌊lam - (∑ i, d i) - (∑ i, a i)⌋ : ℝ) - (∑ i, b i)) * Real.log p
      ≤ (-lam + (∑ i, d i) + 1) * Real.log p + ∑ i ∈ Istar, (3 + Real.log (e i)) := by
  set dI := ∑ i, d i
  set aI := ∑ i, a i
  set bI := ∑ i, b i
  have hl : 0 < Real.log p := Real.log_pos (by linarith)

  have hfl : -(⌊lam - dI - aI⌋ : ℝ) ≤ -(lam - dI - aI) + 1 := neg_floor_le _
  have step1 : -((⌊lam - dI - aI⌋ : ℝ) - bI) * Real.log p
      ≤ (-lam + dI + aI + bI + 1) * Real.log p := by
    have : -((⌊lam - dI - aI⌋ : ℝ) - bI) ≤ -lam + dI + aI + bI + 1 := by linarith
    exact mul_le_mul_of_nonneg_right this (le_of_lt hl)

  have step2 : (aI + bI) * Real.log p ≤ ∑ i ∈ Istar, (3 + Real.log (e i)) :=
    sum_ab_le Istar p hp e a b he ha hb hout
  have hexp : (-lam + dI + aI + bI + 1) * Real.log p
      = (-lam + dI + 1) * Real.log p + (aI + bI) * Real.log p := by ring
  linarith [step1, step2, hexp.le, hexp.ge]

theorem sum_a_sub_le (Istar : Finset ι) (p : ℝ) (hp : 2 ≤ p)
    (e a : ι → ℝ)
    (ha : ∀ i ∈ Istar, a i - 1 / e i ≤ 4 / p)
    (hout : ∀ i ∉ Istar, a i - 1 / e i = 0) :
    ∑ i, (a i - 1 / e i) ≤ (Istar.card : ℝ) * (4 / p) := by
  have hsum : ∑ i, (a i - 1 / e i) = ∑ i ∈ Istar, (a i - 1 / e i) :=
    (Finset.sum_subset (Finset.subset_univ Istar) (fun x _ hx => hout x hx)).symm
  rw [hsum]
  calc ∑ i ∈ Istar, (a i - 1 / e i) ≤ ∑ _i ∈ Istar, (4 / p) := Finset.sum_le_sum ha
    _ = (Istar.card : ℝ) * (4 / p) := by rw [Finset.sum_const, nsmul_eq_mul]

theorem first_inequality (Istar : Finset ι) (p : ℝ) (hp : 2 ≤ p)
    (e a d : ι → ℝ) (lam : ℝ) (logVolUnit : ι → ℝ) (logVolRI : ℝ)
    (hunit : ∀ i, logVolUnit i ≤ -(1 / e i) * Real.log p)
    (hRI : logVolRI ≤ 0)
    (ha : ∀ i ∈ Istar, a i - 1 / e i ≤ 4 / p)
    (hout : ∀ i ∉ Istar, a i - 1 / e i = 0) :
    -((⌊lam - (∑ i, d i) - (∑ i, a i)⌋ : ℝ)) * Real.log p
        + ((∑ i, logVolUnit i) + logVolRI)
      ≤ (-lam + (∑ i, d i) + 1 + (Istar.card : ℝ) * (4 / p)) * Real.log p := by
  set dI := ∑ i, d i
  set aI := ∑ i, a i
  have hl : 0 < Real.log p := Real.log_pos (by linarith)

  have step1 : -((⌊lam - dI - aI⌋ : ℝ)) * Real.log p
      ≤ (-lam + dI + aI + 1) * Real.log p := by
    have h := neg_floor_le (lam - dI - aI)
    have : -((⌊lam - dI - aI⌋ : ℝ)) ≤ -lam + dI + aI + 1 := by linarith
    exact mul_le_mul_of_nonneg_right this (le_of_lt hl)

  have step2 : (∑ i, logVolUnit i) ≤ (∑ i, -(1 / e i)) * Real.log p := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => hunit i)

  have step3 : ∑ i, (a i - 1 / e i) ≤ (Istar.card : ℝ) * (4 / p) :=
    sum_a_sub_le Istar p hp e a ha hout
  have hsplit : aI + (∑ i, -(1 / e i)) = ∑ i, (a i - 1 / e i) := by
    simp only [aI, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  nlinarith [step1, step2, step3, hRI, hl, hsplit.le, hsplit.ge]

theorem index_contribution_strict :
    (2 : ℝ) * Real.log 2 < 3 := by
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  linarith

end Src.CoreLayer.LogVol
