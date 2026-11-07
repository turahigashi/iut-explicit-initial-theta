import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Src.CoreLayer.Elementary

open Finset

theorem sum_id (n : ℕ) : 2 * (∑ m ∈ range (n + 1), m) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

theorem sum_sq (n : ℕ) :
    6 * (∑ m ∈ range (n + 1), m ^ 2) = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

theorem E1 (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n : ℝ)) * (∑ m ∈ range (n + 1), (m : ℝ)) = (1 / 2) * ((n : ℝ) + 1) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have h : (2 : ℝ) * (∑ m ∈ range (n + 1), (m : ℝ)) = (n : ℝ) * ((n : ℝ) + 1) := by
    have hN := congrArg (fun x : ℕ => (x : ℝ)) (sum_id n)
    push_cast [Nat.cast_sum] at hN
    linarith [hN]
  have hS : (∑ m ∈ range (n + 1), (m : ℝ)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by linarith
  rw [hS]
  field_simp

theorem E2 (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n : ℝ)) * (∑ m ∈ range (n + 1), (m : ℝ) ^ 2)
      = (1 / 6) * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have h : (6 : ℝ) * (∑ m ∈ range (n + 1), (m : ℝ) ^ 2)
      = (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) := by
    have hN := congrArg (fun x : ℕ => (x : ℝ)) (sum_sq n)
    push_cast [Nat.cast_sum] at hN
    linarith [hN]
  have hS : (∑ m ∈ range (n + 1), (m : ℝ) ^ 2)
      = (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by linarith
  rw [hS]
  field_simp

theorem main_term_equals_l_plus_one_over_24 (l : ℝ) (hl : 0 < l) :
    (2 * ((l - 1) / 2) + 1) * (((l - 1) / 2) + 1) / (12 * l) = (l + 1) / 24 := by
  field_simp
  ring

theorem main_term_at_seven :
    (2 * (((7:ℝ) - 1) / 2) + 1) * ((((7:ℝ) - 1) / 2) + 1) / (12 * 7) = 1 / 3 := by
  norm_num

theorem main_term_pos (l : ℝ) (hl : 5 ≤ l) : 0 < (l + 1) / 24 := by
  linarith

theorem stage_viii_first (l : ℝ) (hl : 1 ≤ l) :
    1 / (2 * l) ≤ (l + 1) / 4 * (1 / 6) * (12 / l ^ 2) := by
  have hl0 : (0:ℝ) < l := by linarith
  have e : (l + 1) / 4 * (1 / 6) * (12 / l ^ 2) = (l + 1) / (2 * l ^ 2) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hl0, hl]

theorem stage_viii_last : ((20:ℝ) + 1) / 3 * (4 / 3) ≤ 10 := by
  norm_num

theorem stage_viii_constant : (56:ℕ) ≤ 2 ^ 12 * 3 * 5 := by
  norm_num

end Src.CoreLayer.Elementary
