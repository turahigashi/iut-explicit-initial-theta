import Cor312LogVolume.ElementaryIdentitiesE1E6
import Cor312LogVolume.logshell.StepXConcrete
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace CitedLV.Procession

open Finset Src.CoreLayer.Elementary

def sqScaled (c : ℝ) (j : ℕ) : ℝ := (j : ℝ) ^ 2 * c

noncomputable def processionAvg (c : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * (∑ m ∈ range (n + 1), sqScaled c m)

theorem processionAvg_eq (c : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    processionAvg c n = (1 / 6) * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) * c := by
  simp only [processionAvg, sqScaled]
  rw [← Finset.sum_mul, ← mul_assoc]
  rw [E2 n hn]

theorem procession_over_two_l (l : ℝ) (hl : 0 < l) :
    (2 * ((l - 1) / 2) + 1) * (((l - 1) / 2) + 1) / (12 * l) = (l + 1) / 24 :=
  main_term_equals_l_plus_one_over_24 l hl

theorem procession_normalized_value (c : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    processionAvg c n / (2 * (2 * (n : ℝ) + 1))
      = ((2 * (n : ℝ) + 1) + 1) / 24 * c := by
  rw [processionAvg_eq c n hn]
  have hpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  field_simp
  ring

theorem main_term_positive (l : ℝ) (hl : 5 ≤ l) : 0 < (l + 1) / 24 :=
  main_term_pos l hl

theorem sqScaled_le (c : ℝ) (hc : 0 ≤ c) (n j : ℕ) (hj : j ≤ n) :
    sqScaled c j ≤ sqScaled c n := by
  simp only [sqScaled]
  apply mul_le_mul_of_nonneg_right _ hc
  have : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
  have hj0 : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith

theorem grounded_procession (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (hn : 1 ≤ n)
    (l : ℝ) (hl : 5 ≤ l) (j : ℕ) (hj : j ≤ n) :
    (processionAvg c n = (1 / 6) * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) * c) ∧
    (processionAvg c n / (2 * (2 * (n : ℝ) + 1)) = ((2 * (n : ℝ) + 1) + 1) / 24 * c) ∧
    (0 < (l + 1) / 24) ∧
    (sqScaled c j ≤ sqScaled c n) :=
  ⟨processionAvg_eq c n hn,
   procession_normalized_value c n hn,
   main_term_positive l hl,
   sqScaled_le c hc n j hj⟩

end CitedLV.Procession
