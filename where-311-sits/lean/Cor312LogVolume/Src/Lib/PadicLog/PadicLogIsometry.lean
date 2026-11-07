import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Cor312LogVolume.Src.Lib.PadicLog.PadicLogDef

namespace SrcLib.PadicLogIsometry

open SrcLib.PadicLogSummable SrcLib.PadicLogDef

variable (p : ℕ) [hp : Fact p.Prime]

theorem two_mul_add_two_le_four_pow (n : ℕ) : 2 * (n + 2) ≤ 4 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have h4 : (4 : ℕ) ^ (k + 1 + 1) = 4 * 4 ^ (k + 1) := by ring
    have hpos : 1 ≤ 4 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    omega

theorem coeff_bound {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) (n : ℕ) :
    ((n : ℝ) + 2) * t ^ (n + 1) ≤ 1 / 2 := by
  have hq : t ^ (n + 1) ≤ (1 / 4 : ℝ) ^ (n + 1) := pow_le_pow_left₀ ht0 ht _
  have hnat : (2 : ℝ) * ((n : ℝ) + 2) ≤ (4 : ℝ) ^ (n + 1) := by
    have := two_mul_add_two_le_four_pow n
    have hc : ((2 * (n + 2) : ℕ) : ℝ) ≤ ((4 ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hc; linarith
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ (n + 1) := by positivity
  have hquarter : ((1 : ℝ) / 4) ^ (n + 1) = 1 / (4 : ℝ) ^ (n + 1) := by
    rw [div_pow, one_pow]
  have hstep : ((n : ℝ) + 2) * t ^ (n + 1) ≤ ((n : ℝ) + 2) * (1 / (4 : ℝ) ^ (n + 1)) := by
    rw [← hquarter]
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  have hfin : ((n : ℝ) + 2) * (1 / (4 : ℝ) ^ (n + 1)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ h4pos (by norm_num : (0:ℝ) < 2)]
    linarith
  linarith

noncomputable def term (x : ℚ_[p]) (n : ℕ) : ℚ_[p] :=
  (-1 : ℚ_[p]) ^ n * (x ^ (n + 1) / ((n + 1 : ℕ) : ℚ_[p]))

theorem norm_tail_term_le (x : ℚ_[p]) (n : ℕ) :
    ‖term p x (n + 1)‖ ≤ ((n : ℝ) + 2) * ‖x‖ ^ (n + 2) := by
  have hne : ((n + 2 : ℕ)) ≠ 0 := by omega
  have hbase := norm_term_le p x (n + 2) hne
  have hrw : term p x (n + 1)
      = (-1 : ℚ_[p]) ^ (n + 1) * (x ^ (n + 2) / ((n + 2 : ℕ) : ℚ_[p])) := rfl
  rw [hrw, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hcast : (((n + 2 : ℕ)) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hbase
  exact hbase

theorem norm_tail_le (x : ℚ_[p]) (hx : ‖x‖ ≤ 1 / 4) :
    ‖∑' n : ℕ, term p x (n + 1)‖ ≤ ‖x‖ / 2 := by
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  have hterm := norm_tail_term_le p x n
  have hcoeff := coeff_bound (norm_nonneg x) hx n
  have hsplit : ‖x‖ ^ (n + 2) = ‖x‖ ^ (n + 1) * ‖x‖ := by ring
  have hchain : ((n : ℝ) + 2) * ‖x‖ ^ (n + 2)
      = (((n : ℝ) + 2) * ‖x‖ ^ (n + 1)) * ‖x‖ := by rw [hsplit]; ring
  have hfin : (((n : ℝ) + 2) * ‖x‖ ^ (n + 1)) * ‖x‖ ≤ (1 / 2) * ‖x‖ :=
    mul_le_mul_of_nonneg_right hcoeff (norm_nonneg x)
  have : ((n : ℝ) + 2) * ‖x‖ ^ (n + 2) ≤ ‖x‖ / 2 := by
    rw [hchain]; linarith
  linarith

theorem log_eq_head_add_tail (x : ℚ_[p]) (hx : ‖x‖ < 1) :
    padicLog1p p x = x + ∑' n : ℕ, term p x (n + 1) := by
  have hsum : Summable (term p x) := summable_signed p x hx
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have hzero : term p x 0 = x := by simp [term]
  have hdef : padicLog1p p x = ∑' n : ℕ, term p x n := rfl
  rw [hdef, ← hsplit, Finset.sum_range_one, hzero]

theorem norm_padicLog1p_eq (x : ℚ_[p]) (hx : ‖x‖ ≤ 1 / 4) :
    ‖padicLog1p p x‖ = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [padicLog1p_zero]
  · have hlt : ‖x‖ < 1 := lt_of_le_of_lt hx (by norm_num)
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have htail := norm_tail_le p x hx
    have hstrict : ‖∑' n : ℕ, term p x (n + 1)‖ < ‖x‖ := by linarith
    have hne : ‖x‖ ≠ ‖∑' n : ℕ, term p x (n + 1)‖ := ne_of_gt hstrict
    rw [log_eq_head_add_tail p x hlt,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne]
    exact max_eq_left (le_of_lt hstrict)

theorem padicLog1p_eq_zero_iff (x : ℚ_[p]) (hx : ‖x‖ ≤ 1 / 4) :
    padicLog1p p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have : ‖x‖ = 0 := by rw [← norm_padicLog1p_eq p x hx, h, norm_zero]
    exact norm_eq_zero.mp this
  · rintro rfl; exact padicLog1p_zero p

theorem norm_one_add (y : ℚ_[p]) (hy : ‖y‖ < 1) : ‖(1 : ℚ_[p]) + y‖ = 1 := by
  have hne : ‖(1 : ℚ_[p])‖ ≠ ‖y‖ := by rw [norm_one]; exact ne_of_gt hy
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]
  exact max_eq_left (le_of_lt hy)

theorem one_add_ne_zero (y : ℚ_[p]) (hy : ‖y‖ < 1) : (1 : ℚ_[p]) + y ≠ 0 := by
  intro h
  have := norm_one_add p y hy
  rw [h, norm_zero] at this
  norm_num at this

theorem padicLog1p_injOn_small_ball :
    Set.InjOn (padicLog1p p) {x : ℚ_[p] | ‖x‖ ≤ 1 / 4} := by
  intro x hxmem y hymem hxy
  have hx : ‖x‖ ≤ 1 / 4 := hxmem
  have hy : ‖y‖ ≤ 1 / 4 := hymem
  have hxlt : ‖x‖ < 1 := lt_of_le_of_lt hx (by norm_num)
  have hylt : ‖y‖ < 1 := lt_of_le_of_lt hy (by norm_num)
  have hden : (1 : ℚ_[p]) + y ≠ 0 := one_add_ne_zero p y hylt
  set z : ℚ_[p] := (x - y) / (1 + y) with hz

  have hkey : y + z + y * z = x := by
    have : y + z + y * z = y + z * (1 + y) := by ring
    rw [this, hz, div_mul_cancel₀ _ hden]; ring

  have hnormz : ‖z‖ = ‖x - y‖ := by
    rw [hz, norm_div, norm_one_add p y hylt, div_one]
  have hsub : ‖x - y‖ ≤ 1 / 4 := by
    have hmax : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
      have h := IsUltrametricDist.norm_add_le_max (x := x) (y := -y)
      simpa [sub_eq_add_neg] using h
    exact le_trans hmax (max_le hx hy)
  have hzsmall : ‖z‖ ≤ 1 / 4 := by rw [hnormz]; exact hsub
  have hzlt : ‖z‖ < 1 := lt_of_le_of_lt hzsmall (by norm_num)

  have hadd := padicLog1p_add p y z hylt hzlt
  rw [hkey, hxy] at hadd
  have hlogz : padicLog1p p z = 0 := by
    have : padicLog1p p y = padicLog1p p y + padicLog1p p z := hadd
    linear_combination -this

  have hz0 : z = 0 := (padicLog1p_eq_zero_iff p z hzsmall).mp hlogz

  rw [hz0] at hkey
  simp only [add_zero, mul_zero] at hkey
  exact hkey.symm

theorem dist_padicLog1p_eq (x y : ℚ_[p]) (hx : ‖x‖ ≤ 1 / 4) (hy : ‖y‖ ≤ 1 / 4) :
    ‖padicLog1p p x - padicLog1p p y‖ = ‖x - y‖ := by
  have hxlt : ‖x‖ < 1 := lt_of_le_of_lt hx (by norm_num)
  have hylt : ‖y‖ < 1 := lt_of_le_of_lt hy (by norm_num)
  have hden : (1 : ℚ_[p]) + y ≠ 0 := one_add_ne_zero p y hylt
  set z : ℚ_[p] := (x - y) / (1 + y) with hz
  have hkey : y + z + y * z = x := by
    have : y + z + y * z = y + z * (1 + y) := by ring
    rw [this, hz, div_mul_cancel₀ _ hden]; ring
  have hnormz : ‖z‖ = ‖x - y‖ := by
    rw [hz, norm_div, norm_one_add p y hylt, div_one]
  have hsub : ‖x - y‖ ≤ 1 / 4 := by
    have hmax : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
      have h := IsUltrametricDist.norm_add_le_max (x := x) (y := -y)
      simpa [sub_eq_add_neg] using h
    exact le_trans hmax (max_le hx hy)
  have hzsmall : ‖z‖ ≤ 1 / 4 := by rw [hnormz]; exact hsub
  have hzlt : ‖z‖ < 1 := lt_of_le_of_lt hzsmall (by norm_num)
  have hadd := padicLog1p_add p y z hylt hzlt
  rw [hkey] at hadd
  have hdiff : padicLog1p p x - padicLog1p p y = padicLog1p p z := by
    rw [hadd]; ring
  rw [hdiff, norm_padicLog1p_eq p z hzsmall, hnormz]

theorem isometry_padicLog1p_on_ball (x y : ℚ_[p]) (hx : ‖x‖ ≤ 1 / 4) (hy : ‖y‖ ≤ 1 / 4) :
    dist (padicLog1p p x) (padicLog1p p y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  exact dist_padicLog1p_eq p x y hx hy

theorem injOn_of_isometry :
    Set.InjOn (padicLog1p p) {x : ℚ_[p] | ‖x‖ ≤ 1 / 4} := by
  intro x hx y hy hxy
  have h := dist_padicLog1p_eq p x y hx hy
  rw [hxy, sub_self, norm_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)

theorem minus_two_norm_exceeds_quarter :
    ¬ (‖((-1 : ℚ_[2]) - 1)‖ ≤ 1 / 4) := by
  have harg : ((-1 : ℚ_[2]) - 1) = -(2 : ℚ_[2]) := by ring
  have hval : ‖((-1 : ℚ_[2]) - 1)‖ = 1 / 2 := by
    rw [harg, norm_neg]
    have h2 : ((2 : ℚ_[2])) = ((2 : ℕ) : ℚ_[2]) := by norm_num
    rw [h2, Padic.norm_p (p := 2)]
    norm_num
  rw [hval]; norm_num

theorem small_ball_nontrivial :
    ∃ x : ℚ_[2], x ≠ 0 ∧ ‖x‖ ≤ 1 / 4 := by
  refine ⟨((4 : ℕ) : ℚ_[2]), ?_, ?_⟩
  · have : ‖((4 : ℕ) : ℚ_[2])‖ = 1 / 4 := by
      have : ((4 : ℕ) : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) ^ 2 := by push_cast; ring
      rw [this, norm_pow, Padic.norm_p (p := 2)]; norm_num
    intro h; rw [h, norm_zero] at this; norm_num at this
  · have : ‖((4 : ℕ) : ℚ_[2])‖ = 1 / 4 := by
      have : ((4 : ℕ) : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) ^ 2 := by push_cast; ring
      rw [this, norm_pow, Padic.norm_p (p := 2)]; norm_num
    rw [this]

theorem summary_isometry_and_injectivity (x : ℚ_[p]) (hx : ‖x‖ ≤ 1 / 4) :
    (‖padicLog1p p x‖ = ‖x‖) ∧
    (padicLog1p p x = 0 ↔ x = 0) ∧
    Set.InjOn (padicLog1p p) {z : ℚ_[p] | ‖z‖ ≤ 1 / 4} :=
  ⟨norm_padicLog1p_eq p x hx,
   padicLog1p_eq_zero_iff p x hx,
   padicLog1p_injOn_small_ball p⟩

end SrcLib.PadicLogIsometry
