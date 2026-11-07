import Mathlib.Algebra.Ring.GeomSum
import Cor312LogVolume.Src.Lib.PadicLog.LocalFieldLogIsometry

namespace SrcLib.LocalFieldLogContraction

open SrcLib.LocalFieldLogIsometry

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_pow_sub_pow_le (x y : K) (m : ℕ) (hm : 1 ≤ m)
    (M : ℝ) (hM : 0 ≤ M) (hxM : ‖x‖ ≤ M) (hyM : ‖y‖ ≤ M) :
    ‖x ^ m - y ^ m‖ ≤ ‖x - y‖ * M ^ (m - 1) := by
  have hfac := geom_sum₂_mul x y m
  have hsum : ‖∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)‖ ≤ M ^ (m - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty
    · exact Finset.nonempty_range_iff.mpr (by omega)
    · intro i hi
      have hilt : i < m := Finset.mem_range.mp hi
      have hidx : i + (m - 1 - i) = m - 1 := by omega
      rw [norm_mul, norm_pow, norm_pow]
      calc
        ‖x‖ ^ i * ‖y‖ ^ (m - 1 - i)
            ≤ M ^ i * M ^ (m - 1 - i) := by
              apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) hxM i)
                (pow_le_pow_left₀ (norm_nonneg y) hyM _) (by positivity) (by positivity)
        _ = M ^ (m - 1) := by rw [← pow_add, hidx]
  calc
    ‖x ^ m - y ^ m‖
        = ‖(∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)) * (x - y)‖ := by rw [hfac]
    _ = ‖∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)‖ * ‖x - y‖ := norm_mul _ _
    _ ≤ M ^ (m - 1) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
    _ = ‖x - y‖ * M ^ (m - 1) := by ring

variable (p : ℕ) [hp : Fact p.Prime]
variable [NormedAlgebra ℚ_[p] K] [CompleteSpace K]

include p hp

theorem norm_term_sub_le (x y : K) (n : ℕ)
    (M : ℝ) (hM : 0 ≤ M) (hM4 : M ≤ 1 / 4) (hxM : ‖x‖ ≤ M) (hyM : ‖y‖ ≤ M) :
    ‖term x (n + 1) - term y (n + 1)‖ ≤ (1 / 2) * ‖x - y‖ := by
  have hne : (n + 2 : ℕ) ≠ 0 := by omega
  have hrwx : term x (n + 1)
      = (-1 : K) ^ (n + 1) * (x ^ (n + 2) / ((n + 2 : ℕ) : K)) := rfl
  have hrwy : term y (n + 1)
      = (-1 : K) ^ (n + 1) * (y ^ (n + 2) / ((n + 2 : ℕ) : K)) := rfl
  have hcomb : term x (n + 1) - term y (n + 1)
      = (-1 : K) ^ (n + 1) * ((x ^ (n + 2) - y ^ (n + 2)) / ((n + 2 : ℕ) : K)) := by
    rw [hrwx, hrwy]
    ring
  rw [hcomb, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div]
  have hden : (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ≤ ‖((n + 2 : ℕ) : K)‖ :=
    norm_natCast_ge_extension (p := p) (K := K) (n + 2) hne
  have hdpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hdnorm : (0 : ℝ) < ‖((n + 2 : ℕ) : K)‖ := by
    have : (0 : ℝ) < 1 / ((n + 2 : ℕ) : ℝ) := by positivity
    linarith
  have hnum : ‖x ^ (n + 2) - y ^ (n + 2)‖ ≤ ‖x - y‖ * M ^ (n + 1) := by
    simpa using norm_pow_sub_pow_le x y (n + 2) (by omega) M hM hxM hyM
  rw [div_le_iff₀ hdnorm]
  have hcoef : ((n : ℝ) + 2) * M ^ (n + 1) ≤ 1 / 2 :=
    SrcLib.PadicLogIsometry.coeff_bound hM hM4 n
  have hcast : (((n + 2 : ℕ)) : ℝ) = (n : ℝ) + 2 := by
    push_cast
    ring
  have hd1 : (1 : ℝ) ≤ (((n + 2 : ℕ)) : ℝ) * ‖((n + 2 : ℕ) : K)‖ := by
    have := (div_le_iff₀ hdpos).mp hden
    linarith
  calc
    ‖x ^ (n + 2) - y ^ (n + 2)‖
        ≤ ‖x - y‖ * M ^ (n + 1) := hnum
    _ = (‖x - y‖ * M ^ (n + 1)) * 1 := by ring
    _ ≤ (‖x - y‖ * M ^ (n + 1)) *
        ((((n + 2 : ℕ)) : ℝ) * ‖((n + 2 : ℕ) : K)‖) := by
          apply mul_le_mul_of_nonneg_left hd1 (by positivity)
    _ = ((((n : ℝ) + 2) * M ^ (n + 1)) * ‖x - y‖) * ‖((n + 2 : ℕ) : K)‖ := by
          rw [hcast]
          ring
    _ ≤ ((1 / 2) * ‖x - y‖) * ‖((n + 2 : ℕ) : K)‖ := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hdnorm)
          exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

theorem norm_tail_sub_le (x y : K) (hx : ‖x‖ ≤ 1 / 4) (hy : ‖y‖ ≤ 1 / 4) :
    ‖(log1p x - x) - (log1p y - y)‖ ≤ (1 / 2) * ‖x - y‖ := by
  have hxlt : ‖x‖ < 1 := lt_of_le_of_lt hx (by norm_num)
  have hylt : ‖y‖ < 1 := lt_of_le_of_lt hy (by norm_num)
  let M : ℝ := max ‖x‖ ‖y‖
  have hM : 0 ≤ M := le_trans (norm_nonneg x) (le_max_left _ _)
  have hM4 : M ≤ 1 / 4 := max_le hx hy
  have hxM : ‖x‖ ≤ M := le_max_left _ _
  have hyM : ‖y‖ ≤ M := le_max_right _ _
  have hex := log_eq_head_add_tail (p := p) x hxlt
  have hey := log_eq_head_add_tail (p := p) y hylt
  have htx : log1p x - x = ∑' n : ℕ, term x (n + 1) := by
    rw [hex]
    ring
  have hty : log1p y - y = ∑' n : ℕ, term y (n + 1) := by
    rw [hey]
    ring
  have hsx : Summable (fun n : ℕ => term x (n + 1)) :=
    ((summable_signed (p := p) x hxlt).comp_injective (add_left_injective 1))
  have hsy : Summable (fun n : ℕ => term y (n + 1)) :=
    ((summable_signed (p := p) y hylt).comp_injective (add_left_injective 1))
  rw [htx, hty, ← hsx.tsum_sub hsy]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  exact norm_term_sub_le (p := p) x y n M hM hM4 hxM hyM

theorem small_ball_has_distinct_pair :
    ∃ x y : K, x ≠ y ∧ ‖x‖ ≤ 1 / 4 ∧ ‖y‖ ≤ 1 / 4 := by
  rcases small_ball_has_nonzero (p := p) (K := K) with ⟨x, hx0, hx⟩
  exact ⟨x, 0, hx0, hx, by simp⟩

theorem summary_extension_contraction (x y : K)
    (hx : ‖x‖ ≤ 1 / 4) (hy : ‖y‖ ≤ 1 / 4) :
    ‖(log1p x - x) - (log1p y - y)‖ ≤ (1 / 2) * ‖x - y‖ :=
  norm_tail_sub_le (p := p) x y hx hy

end SrcLib.LocalFieldLogContraction
