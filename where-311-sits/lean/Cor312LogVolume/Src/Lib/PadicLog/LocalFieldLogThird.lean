import Mathlib.Topology.MetricSpace.Contracting
import Cor312LogVolume.Src.Lib.PadicLog.LocalFieldLogContraction

namespace SrcLib.LocalFieldLogThird

open SrcLib.LocalFieldLogIsometry SrcLib.LocalFieldLogContraction

theorem coeff_bound_third {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 3) (n : ℕ) :
    ((n : ℝ) + 2) * t ^ (n + 1) ≤ 2 / 3 := by
  have hq : t ^ (n + 1) ≤ (1 / 3 : ℝ) ^ (n + 1) := pow_le_pow_left₀ ht0 ht _
  have hnat : ∀ k : ℕ, 3 * (k + 2) ≤ 2 * 3 ^ (k + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have h3 : 3 ^ (k + 1 + 1) = 3 * 3 ^ (k + 1) := by ring
      have hpos : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
      omega
  have hr : (3 : ℝ) * ((n : ℝ) + 2) ≤ 2 * (3 : ℝ) ^ (n + 1) := by
    have hc : ((3 * (n + 2) : ℕ) : ℝ) ≤ ((2 * 3 ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast hnat n
    push_cast at hc
    linarith
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (n + 1) := by positivity
  have hthird : ((1 : ℝ) / 3) ^ (n + 1) = 1 / (3 : ℝ) ^ (n + 1) := by
    rw [div_pow, one_pow]
  have hstep : ((n : ℝ) + 2) * t ^ (n + 1) ≤ ((n : ℝ) + 2) * (1 / (3 : ℝ) ^ (n + 1)) := by
    rw [← hthird]
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  have hfin : ((n : ℝ) + 2) * (1 / (3 : ℝ) ^ (n + 1)) ≤ 2 / 3 := by
    rw [mul_one_div, div_le_div_iff₀ h3pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  linarith

variable (p : ℕ) [hp : Fact p.Prime]
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

include p hp

theorem norm_tail_le_third (x : K) (hx : ‖x‖ ≤ 1 / 3) :
    ‖∑' n : ℕ, term x (n + 1)‖ ≤ (2 / 3) * ‖x‖ := by
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  have hterm := norm_tail_term_le (p := p) x n
  have hcoeff := coeff_bound_third (norm_nonneg x) hx n
  have hchain : ((n : ℝ) + 2) * ‖x‖ ^ (n + 2) = (((n : ℝ) + 2) * ‖x‖ ^ (n + 1)) * ‖x‖ := by ring
  have hfin : (((n : ℝ) + 2) * ‖x‖ ^ (n + 1)) * ‖x‖ ≤ (2 / 3) * ‖x‖ :=
    mul_le_mul_of_nonneg_right hcoeff (norm_nonneg x)
  rw [hchain] at hterm
  linarith

theorem norm_log1p_eq_third (x : K) (hx : ‖x‖ ≤ 1 / 3) : ‖log1p x‖ = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [log1p_zero (p := p) (K := K)]
  · have hlt : ‖x‖ < 1 := lt_of_le_of_lt hx (by norm_num)
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have htail := norm_tail_le_third (p := p) x hx
    have hstrict : ‖∑' n : ℕ, term x (n + 1)‖ < ‖x‖ := by linarith
    rw [log_eq_head_add_tail (p := p) x hlt,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hstrict)]
    exact max_eq_left hstrict.le

theorem norm_term_sub_le_third (x y : K) (n : ℕ)
    (M : ℝ) (hM : 0 ≤ M) (hM3 : M ≤ 1 / 3) (hxM : ‖x‖ ≤ M) (hyM : ‖y‖ ≤ M) :
    ‖term x (n + 1) - term y (n + 1)‖ ≤ (2 / 3) * ‖x - y‖ := by
  have hne : (n + 2 : ℕ) ≠ 0 := by omega
  have hcomb : term x (n + 1) - term y (n + 1)
      = (-1 : K) ^ (n + 1) * ((x ^ (n + 2) - y ^ (n + 2)) / ((n + 2 : ℕ) : K)) := by
    show (-1 : K) ^ (n + 1) * (x ^ (n + 2) / ((n + 2 : ℕ) : K)) -
        (-1 : K) ^ (n + 1) * (y ^ (n + 2) / ((n + 2 : ℕ) : K)) = _
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
  have hcoef := coeff_bound_third hM hM3 n
  have hcast : (((n + 2 : ℕ)) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  have hd1 : (1 : ℝ) ≤ (((n + 2 : ℕ)) : ℝ) * ‖((n + 2 : ℕ) : K)‖ := by
    have := (div_le_iff₀ hdpos).mp hden
    linarith
  calc
    ‖x ^ (n + 2) - y ^ (n + 2)‖ ≤ ‖x - y‖ * M ^ (n + 1) := hnum
    _ = (‖x - y‖ * M ^ (n + 1)) * 1 := by ring
    _ ≤ (‖x - y‖ * M ^ (n + 1)) * ((((n + 2 : ℕ)) : ℝ) * ‖((n + 2 : ℕ) : K)‖) :=
          mul_le_mul_of_nonneg_left hd1 (by positivity)
    _ = ((((n : ℝ) + 2) * M ^ (n + 1)) * ‖x - y‖) * ‖((n + 2 : ℕ) : K)‖ := by rw [hcast]; ring
    _ ≤ ((2 / 3) * ‖x - y‖) * ‖((n + 2 : ℕ) : K)‖ := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hdnorm)
          exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

theorem norm_tail_sub_le_third (x y : K) (hx : ‖x‖ ≤ 1 / 3) (hy : ‖y‖ ≤ 1 / 3) :
    ‖(log1p x - x) - (log1p y - y)‖ ≤ (2 / 3) * ‖x - y‖ := by
  have hxlt : ‖x‖ < 1 := lt_of_le_of_lt hx (by norm_num)
  have hylt : ‖y‖ < 1 := lt_of_le_of_lt hy (by norm_num)
  have hM : 0 ≤ max ‖x‖ ‖y‖ := le_trans (norm_nonneg x) (le_max_left _ _)
  have htx : log1p x - x = ∑' n : ℕ, term x (n + 1) := by
    rw [log_eq_head_add_tail (p := p) x hxlt]; ring
  have hty : log1p y - y = ∑' n : ℕ, term y (n + 1) := by
    rw [log_eq_head_add_tail (p := p) y hylt]; ring
  have hsx : Summable (fun n : ℕ => term x (n + 1)) :=
    (summable_signed (p := p) x hxlt).comp_injective (add_left_injective 1)
  have hsy : Summable (fun n : ℕ => term y (n + 1)) :=
    (summable_signed (p := p) y hylt).comp_injective (add_left_injective 1)
  rw [htx, hty, ← hsx.tsum_sub hsy]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  exact norm_term_sub_le_third (p := p) x y n _ hM (max_le hx hy) (le_max_left _ _) (le_max_right _ _)

omit hp in

def B3 (K : Type*) [NormedField K] : Set K := Metric.closedBall (0 : K) (1 / 3)

omit [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] hp in
theorem mem_B3_iff {x : K} : x ∈ B3 K ↔ ‖x‖ ≤ 1 / 3 := by
  simp [B3]

omit hp in
instance instNonemptyB3 : Nonempty (B3 K) := ⟨⟨0, by simp [B3]⟩⟩

omit hp in
instance instCompleteB3 : CompleteSpace (B3 K) :=
  (Metric.isClosed_closedBall : IsClosed (B3 K)).completeSpace_coe

noncomputable def F3 (y : K) (hy : ‖y‖ ≤ 1 / 3) (x : B3 K) : B3 K :=
  ⟨y - (log1p (x : K) - (x : K)), by
    rw [mem_B3_iff (p := p)]
    have hx : ‖(x : K)‖ ≤ 1 / 3 := (mem_B3_iff (p := p)).mp x.2
    have hlt : ‖(x : K)‖ < 1 := lt_of_le_of_lt hx (by norm_num)
    have hg : ‖log1p (x : K) - (x : K)‖ ≤ 1 / 3 := by
      rw [show log1p (x : K) - (x : K) = ∑' n : ℕ, term (x : K) (n + 1) by
        rw [log_eq_head_add_tail (p := p) _ hlt]; ring]
      have := norm_tail_le_third (p := p) (x : K) hx
      nlinarith [norm_nonneg (x : K)]
    have hmax : ‖y - (log1p (x : K) - (x : K))‖ ≤ max ‖y‖ ‖log1p (x : K) - (x : K)‖ := by
      rw [sub_eq_add_neg]
      have h := IsUltrametricDist.norm_add_le_max (x := y) (y := -(log1p (x : K) - (x : K)))
      rwa [norm_neg] at h
    exact hmax.trans (max_le hy hg)⟩

theorem contracting_F3 (y : K) (hy : ‖y‖ ≤ 1 / 3) :
    ContractingWith (2 / 3 : NNReal) (F3 (p := p) y hy) := by
  refine ⟨by rw [show (2 / 3 : NNReal) = ((2 : NNReal) / 3) from rfl]; norm_num, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have ha : ‖(a : K)‖ ≤ 1 / 3 := (mem_B3_iff (p := p)).mp a.2
  have hb : ‖(b : K)‖ ≤ 1 / 3 := (mem_B3_iff (p := p)).mp b.2
  have hcon := norm_tail_sub_le_third (p := p) (a : K) (b : K) ha hb
  have hdist : dist (F3 (p := p) y hy a) (F3 (p := p) y hy b)
      = ‖(log1p (a : K) - (a : K)) - (log1p (b : K) - (b : K))‖ := by
    rw [Subtype.dist_eq, dist_eq_norm]
    simp only [F3]
    rw [show y - (log1p (a : K) - (a : K)) - (y - (log1p (b : K) - (b : K))) =
        -((log1p (a : K) - (a : K)) - (log1p (b : K) - (b : K))) by ring, norm_neg]
  rw [hdist, Subtype.dist_eq, dist_eq_norm]
  have hcast : ((2 / 3 : NNReal) : ℝ) = 2 / 3 := by norm_num
  rw [hcast]
  exact hcon

theorem log1p_surjOn_third (y : K) (hy : ‖y‖ ≤ 1 / 3) :
    ∃ x : K, ‖x‖ ≤ 1 / 3 ∧ log1p x = y := by
  have hc := contracting_F3 (p := p) y hy
  let xs : B3 K := hc.fixedPoint (F3 (p := p) y hy)
  have hfix : F3 (p := p) y hy xs = xs := hc.fixedPoint_isFixedPt
  refine ⟨(xs : K), (mem_B3_iff (p := p)).mp xs.2, ?_⟩
  have hval : y - (log1p (xs : K) - (xs : K)) = (xs : K) := by
    have h := congrArg (fun z : B3 K => (z : K)) hfix
    simpa [F3] using h
  linear_combination -hval

end SrcLib.LocalFieldLogThird

section Check
open SrcLib.LocalFieldLogThird
end Check
