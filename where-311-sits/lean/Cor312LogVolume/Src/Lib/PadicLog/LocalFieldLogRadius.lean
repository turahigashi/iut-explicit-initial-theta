import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Cor312LogVolume.Src.Lib.PadicLog.LocalFieldLogContraction

namespace SrcLib.LocalFieldLogRadius

open SrcLib.LocalFieldLogIsometry SrcLib.LocalFieldLogContraction

section Padic

variable (p : ℕ) [hp : Fact p.Prime]

include hp

theorem padicValNat_mul_le (m : ℕ) (hm : 1 ≤ m) :
    ((padicValNat p m : ℕ) : ℝ) * ((p : ℝ) - 1) ≤ (m : ℝ) - 1 := by
  set v := padicValNat p m
  have hdvd : p ^ v ∣ m := pow_padicValNat_dvd
  have hle : p ^ v ≤ m := Nat.le_of_dvd (by omega) hdvd
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hbern := one_add_mul_le_pow (a := (p : ℝ) - 1) (by linarith) v
  have hle' : ((p : ℝ)) ^ v ≤ (m : ℝ) := by exact_mod_cast hle
  have : (1 : ℝ) + (p - 1) = p := by ring
  rw [this] at hbern
  linarith

theorem norm_natCast_eq (m : ℕ) (hm : m ≠ 0) :
    ‖((m : ℕ) : ℚ_[p])‖ = (p : ℝ) ^ (-((padicValNat p m : ℕ) : ℤ)) := by
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hm), Padic.valuation_natCast]

theorem coeffBound_of_rpow {r c : ℝ} (hr0 : 0 ≤ r)
    (hrc : r * (p : ℝ) ^ ((1 : ℝ) / ((p : ℝ) - 1)) ≤ c)
    (hc1 : r * (p : ℝ) ^ ((1 : ℝ) / ((p : ℝ) - 1)) ≤ 1) (n : ℕ) :
    r ^ (n + 1) ≤ c * ‖((n + 2 : ℕ) : ℚ_[p])‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  set v := padicValNat p (n + 2)
  have hval := padicValNat_mul_le p (n + 2) (by omega)
  have hvle : (v : ℝ) ≤ ((n : ℝ) + 1) * (1 / ((p : ℝ) - 1)) := by
    rw [mul_one_div, le_div_iff₀ hpm1]
    push_cast at hval
    linarith
  rw [norm_natCast_eq p (n + 2) (by omega)]
  set s := (p : ℝ) ^ ((1 : ℝ) / ((p : ℝ) - 1)) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hp0 _

  have hpv : (p : ℝ) ^ (v : ℝ) ≤ s ^ (n + 1) := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    apply Real.rpow_le_rpow_of_exponent_le hp1.le
    push_cast
    linarith
  have hzpow : (p : ℝ) ^ (-((v : ℕ) : ℤ)) = ((p : ℝ) ^ (v : ℝ))⁻¹ := by
    rw [zpow_neg, zpow_natCast, Real.rpow_natCast]
  rw [hzpow]
  have hpvpos : 0 < (p : ℝ) ^ (v : ℝ) := Real.rpow_pos_of_pos hp0 _
  rw [← div_eq_mul_inv, le_div_iff₀ hpvpos]
  have hrs : (r * s) ^ (n + 1) ≤ r * s := by
    exact pow_le_of_le_one (by positivity) hc1 (by omega)
  calc r ^ (n + 1) * (p : ℝ) ^ (v : ℝ) ≤ r ^ (n + 1) * s ^ (n + 1) :=
        mul_le_mul_of_nonneg_left hpv (by positivity)
    _ = (r * s) ^ (n + 1) := by ring
    _ ≤ r * s := hrs
    _ ≤ c := hrc

end Padic

variable (p : ℕ) [hp : Fact p.Prime]
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

include p hp

def CoeffBound (r c : ℝ) : Prop :=
  ∀ n : ℕ, r ^ (n + 1) ≤ c * ‖((n + 2 : ℕ) : ℚ_[p])‖

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem norm_natCast_K (m : ℕ) : ‖((m : ℕ) : K)‖ = ‖((m : ℕ) : ℚ_[p])‖ := by
  have := norm_algebraMap' K ((m : ℕ) : ℚ_[p])
  simpa using this

omit [IsUltrametricDist K] [CompleteSpace K] in

theorem norm_tail_term_le_radius {r c : ℝ} (hc : CoeffBound p r c) (hc0 : 0 ≤ c) (x : K)
    (hx : ‖x‖ ≤ r) (n : ℕ) : ‖term x (n + 1)‖ ≤ c * ‖x‖ := by
  have hne : ((n + 2 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  have hdpos : 0 < ‖((n + 2 : ℕ) : ℚ_[p])‖ := norm_pos_iff.mpr hne
  rw [term, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div, norm_pow,
    norm_natCast_K (p := p) (K := K), div_le_iff₀ hdpos]
  have hxr : ‖x‖ ^ (n + 1) ≤ r ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg x) hx _
  calc ‖x‖ ^ (n + 1 + 1) = ‖x‖ ^ (n + 1) * ‖x‖ := by ring
    _ ≤ r ^ (n + 1) * ‖x‖ := mul_le_mul_of_nonneg_right hxr (norm_nonneg x)
    _ ≤ (c * ‖((n + 2 : ℕ) : ℚ_[p])‖) * ‖x‖ := mul_le_mul_of_nonneg_right (hc n) (norm_nonneg x)
    _ = c * ‖x‖ * ‖((n + 2 : ℕ) : ℚ_[p])‖ := by ring

omit [CompleteSpace K] in
theorem norm_tail_le_radius {r c : ℝ} (hc : CoeffBound p r c) (hc0 : 0 ≤ c) (x : K) (hx : ‖x‖ ≤ r) :
    ‖∑' n : ℕ, term x (n + 1)‖ ≤ c * ‖x‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le fun n => norm_tail_term_le_radius p hc hc0 x hx n

theorem norm_log1p_eq_radius {r c : ℝ} (hc : CoeffBound p r c) (hc0 : 0 ≤ c) (hc1 : c < 1) (hr1 : r < 1)
    (x : K) (hx : ‖x‖ ≤ r) : ‖log1p x‖ = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [log1p_zero (p := p) (K := K)]
  · have hlt : ‖x‖ < 1 := lt_of_le_of_lt hx hr1
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have htail := norm_tail_le_radius p hc hc0 x hx
    have hstrict : ‖∑' n : ℕ, term x (n + 1)‖ < ‖x‖ := by nlinarith
    rw [log_eq_head_add_tail (p := p) x hlt,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hstrict)]
    exact max_eq_left hstrict.le

omit [CompleteSpace K] in
theorem norm_term_sub_le_radius {r c : ℝ} (hc : CoeffBound p r c) (hc0 : 0 ≤ c) (hr0 : 0 ≤ r)
    (x y : K) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
    ‖term x (n + 1) - term y (n + 1)‖ ≤ c * ‖x - y‖ := by
  have hne : ((n + 2 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  have hdpos : 0 < ‖((n + 2 : ℕ) : ℚ_[p])‖ := norm_pos_iff.mpr hne
  have hcomb : term x (n + 1) - term y (n + 1)
      = (-1 : K) ^ (n + 1) * ((x ^ (n + 2) - y ^ (n + 2)) / ((n + 2 : ℕ) : K)) := by
    show (-1 : K) ^ (n + 1) * (x ^ (n + 1 + 1) / ((n + 1 + 1 : ℕ) : K)) -
        (-1 : K) ^ (n + 1) * (y ^ (n + 1 + 1) / ((n + 1 + 1 : ℕ) : K)) = _
    ring
  rw [hcomb, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div,
    norm_natCast_K (p := p) (K := K), div_le_iff₀ hdpos]
  have hnum : ‖x ^ (n + 2) - y ^ (n + 2)‖ ≤ ‖x - y‖ * r ^ (n + 1) := by
    simpa using norm_pow_sub_pow_le x y (n + 2) (by omega) r hr0 hx hy
  calc ‖x ^ (n + 2) - y ^ (n + 2)‖ ≤ ‖x - y‖ * r ^ (n + 1) := hnum
    _ ≤ ‖x - y‖ * (c * ‖((n + 2 : ℕ) : ℚ_[p])‖) := mul_le_mul_of_nonneg_left (hc n) (norm_nonneg _)
    _ = c * ‖x - y‖ * ‖((n + 2 : ℕ) : ℚ_[p])‖ := by ring

theorem norm_tail_sub_le_radius {r c : ℝ} (hc : CoeffBound p r c) (hc0 : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x y : K) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖(log1p x - x) - (log1p y - y)‖ ≤ c * ‖x - y‖ := by
  have hxlt : ‖x‖ < 1 := lt_of_le_of_lt hx hr1
  have hylt : ‖y‖ < 1 := lt_of_le_of_lt hy hr1
  have htx : log1p x - x = ∑' n : ℕ, term x (n + 1) := by
    rw [log_eq_head_add_tail (p := p) x hxlt]; ring
  have hty : log1p y - y = ∑' n : ℕ, term y (n + 1) := by
    rw [log_eq_head_add_tail (p := p) y hylt]; ring
  have hsx : Summable (fun n : ℕ => term x (n + 1)) :=
    (summable_signed (p := p) x hxlt).comp_injective (add_left_injective 1)
  have hsy : Summable (fun n : ℕ => term y (n + 1)) :=
    (summable_signed (p := p) y hylt).comp_injective (add_left_injective 1)
  rw [htx, hty, ← hsx.tsum_sub hsy]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le fun n =>
    norm_term_sub_le_radius p hc hc0 hr0 x y hx hy n

omit hp in

def Ball (K : Type*) [NormedField K] (r : ℝ) : Set K := Metric.closedBall (0 : K) r

omit [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] hp in
theorem mem_Ball_iff {r : ℝ} {x : K} : x ∈ Ball K r ↔ ‖x‖ ≤ r := by
  simp [Ball]

omit [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] hp in
instance instCompleteBall (r : ℝ) [CompleteSpace K] : CompleteSpace (Ball K r) :=
  (Metric.isClosed_closedBall : IsClosed (Ball K r)).completeSpace_coe

noncomputable def F {r c : ℝ} (hc : CoeffBound p r c) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hr1 : r < 1)
    (y : K) (hy : ‖y‖ ≤ r) (x : Ball K r) : Ball K r :=
  ⟨y - (log1p (x : K) - (x : K)), by
    rw [mem_Ball_iff (p := p)]
    have hx : ‖(x : K)‖ ≤ r := (mem_Ball_iff (p := p)).mp x.2
    have hlt : ‖(x : K)‖ < 1 := lt_of_le_of_lt hx hr1
    have hg : ‖log1p (x : K) - (x : K)‖ ≤ r := by
      rw [show log1p (x : K) - (x : K) = ∑' n : ℕ, term (x : K) (n + 1) by
        rw [log_eq_head_add_tail (p := p) _ hlt]; ring]
      have := norm_tail_le_radius p hc hc0 (x : K) hx
      nlinarith [norm_nonneg (x : K)]
    have hmax : ‖y - (log1p (x : K) - (x : K))‖ ≤ max ‖y‖ ‖log1p (x : K) - (x : K)‖ := by
      rw [sub_eq_add_neg]
      have h := IsUltrametricDist.norm_add_le_max (x := y) (y := -(log1p (x : K) - (x : K)))
      rwa [norm_neg] at h
    exact hmax.trans (max_le hy hg)⟩

theorem contracting_F {r c : ℝ} (hc : CoeffBound p r c) (hc0 : 0 ≤ c) (hc1 : c < 1) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (y : K) (hy : ‖y‖ ≤ r) :
    ContractingWith ⟨c, hc0⟩ (F p hc hc0 hc1.le hr1 y hy) := by
  refine ⟨by exact_mod_cast hc1, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have ha : ‖(a : K)‖ ≤ r := (mem_Ball_iff (p := p)).mp a.2
  have hb : ‖(b : K)‖ ≤ r := (mem_Ball_iff (p := p)).mp b.2
  have hcon := norm_tail_sub_le_radius p hc hc0 hr0 hr1 (a : K) (b : K) ha hb
  have hdist : dist (F p hc hc0 hc1.le hr1 y hy a) (F p hc hc0 hc1.le hr1 y hy b)
      = ‖(log1p (a : K) - (a : K)) - (log1p (b : K) - (b : K))‖ := by
    rw [Subtype.dist_eq, dist_eq_norm]
    simp only [F]
    rw [show y - (log1p (a : K) - (a : K)) - (y - (log1p (b : K) - (b : K))) =
        -((log1p (a : K) - (a : K)) - (log1p (b : K) - (b : K))) by ring, norm_neg]
  rw [hdist, Subtype.dist_eq, dist_eq_norm]
  exact hcon

theorem log1p_surjOn_radius {r c : ℝ} (hc : CoeffBound p r c) (hc0 : 0 ≤ c) (hc1 : c < 1) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (y : K) (hy : ‖y‖ ≤ r) :
    ∃ x : K, ‖x‖ ≤ r ∧ log1p x = y := by
  haveI : Nonempty (Ball K r) := ⟨⟨0, by simp [Ball, hr0]⟩⟩
  have hcw := contracting_F p hc hc0 hc1 hr0 hr1 y hy
  let xs : Ball K r := hcw.fixedPoint (F p hc hc0 hc1.le hr1 y hy)
  have hfix : F p hc hc0 hc1.le hr1 y hy xs = xs := hcw.fixedPoint_isFixedPt
  refine ⟨(xs : K), (mem_Ball_iff (p := p)).mp xs.2, ?_⟩
  have hval : y - (log1p (xs : K) - (xs : K)) = (xs : K) := by
    have h := congrArg (fun z : Ball K r => (z : K)) hfix
    simpa [F] using h
  linear_combination -hval

end SrcLib.LocalFieldLogRadius

section Check
open SrcLib.LocalFieldLogRadius
end Check
