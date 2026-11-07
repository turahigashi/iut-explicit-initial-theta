import Mathlib
import Cor312LogVolume.Src.IUT3.Section3Proposition35iiUpperSemiCompat
import Cor312LogVolume.Src.Lib.PadicLog.LocalFieldLogRadius
import Cor312LogVolume.Src.IUT4.Section1Proposition14iiLogUnitsVolumeQp

namespace Src.IUT4.Proposition12i

open Metric Set SrcLib.LocalFieldLogIsometry Src.IUT3.Proposition39iv Src.IUT3.Proposition35ii

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable def aExp (e : ℕ) : ℝ :=
  if p = 2 then 2 else 1 / (e : ℝ) * (⌈(e : ℝ) / ((p : ℝ) - 2)⌉ : ℝ)

noncomputable def bExp (e : ℕ) : ℝ :=
  (⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ : ℝ) - 1 / (e : ℝ)

structure RamificationData (K : Type*) [NormedField K] where
  e : ℕ
  e_pos : 0 < e
  pi : K
  norm_pi : ‖pi‖ = (p : ℝ) ^ (-(1 : ℝ) / (e : ℝ))
  valueGroup : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖pi‖ ^ n

def logUnitsSet (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K] [CompleteSpace K] [IsUltrametricDist K] :
    Set K :=
  {x | ∃ u : K, LogRel p u x}

include hp

theorem one_div_lt_aExp (e : ℕ) (he : 0 < e) : 1 / ((p : ℝ) - 1) < aExp p e := by
  have hp2 : 2 ≤ p := hp.out.two_le
  unfold aExp
  split_ifs with h
  · subst h; norm_num
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
    have hpm2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have he0 : (0 : ℝ) < e := by exact_mod_cast he
    have hceil : (e : ℝ) / ((p : ℝ) - 2) ≤ (⌈(e : ℝ) / ((p : ℝ) - 2)⌉ : ℝ) := Int.le_ceil _
    have h1 : 1 / ((p : ℝ) - 2) ≤ 1 / (e : ℝ) * (⌈(e : ℝ) / ((p : ℝ) - 2)⌉ : ℝ) := by
      calc 1 / ((p : ℝ) - 2) = 1 / (e : ℝ) * ((e : ℝ) / ((p : ℝ) - 2)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hceil (by positivity)
    have h2 : 1 / ((p : ℝ) - 1) < 1 / ((p : ℝ) - 2) := one_div_lt_one_div_of_lt hpm2 (by linarith)
    linarith

theorem exponent_le (e m : ℕ) (he : 0 < e) (hm : 0 < m) :
    ((padicValNat p m : ℕ) : ℝ) - (m : ℝ) / e ≤
      (⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ : ℝ) - 1 / e := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have he0 : (0 : ℝ) < e := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  set q : ℝ := (p : ℝ) * e / ((p : ℝ) - 1) with hq
  set L : ℤ := ⌊Real.log q / Real.log p⌋ with hLdef
  set v := padicValNat p m with hv
  have hq1 : 1 ≤ q := by
    rw [hq, le_div_iff₀ hpm1]; nlinarith
  have hq0 : 0 < q := by linarith
  have hL0 : 0 ≤ L := Int.floor_nonneg.mpr (div_nonneg (Real.log_nonneg hq1) hlogp.le)
  set Ln := L.toNat with hLn
  have hLcast : (L : ℝ) = (Ln : ℝ) := by
    rw [hLn]; exact_mod_cast (Int.toNat_of_nonneg hL0).symm
  have hqlt : q < (p : ℝ) ^ (Ln + 1) := by
    have h1 : Real.log q / Real.log p < L + 1 := Int.lt_floor_add_one _
    have h2 : Real.log q < ((Ln : ℝ) + 1) * Real.log p := by
      rw [div_lt_iff₀ hlogp, hLcast] at h1; exact h1
    have h3 : ((Ln : ℝ) + 1) * Real.log p = Real.log ((p : ℝ) ^ (Ln + 1)) := by
      rw [Real.log_pow]; push_cast; ring
    rw [h3] at h2
    exact (Real.log_lt_log_iff hq0 (by positivity)).mp h2
  have hpv : (p : ℝ) ^ v ≤ m := by exact_mod_cast Nat.le_of_dvd hm pow_padicValNat_dvd
  rw [hLcast]
  by_cases hvL : v ≤ Ln
  · have h1 : (v : ℝ) ≤ Ln := by exact_mod_cast hvL
    have h2 : (1 : ℝ) / e ≤ (m : ℝ) / e := div_le_div_of_nonneg_right hm1 he0.le
    linarith
  · push_neg at hvL
    obtain ⟨j, hj⟩ : ∃ j : ℕ, v = Ln + j := ⟨v - Ln, by omega⟩
    have hj1 : 1 ≤ j := by omega
    suffices hsuff : (e : ℝ) * j ≤ (m : ℝ) - 1 by
      rw [hj]; push_cast
      have : (j : ℝ) ≤ ((m : ℝ) - 1) / e := by rw [le_div_iff₀ he0]; linarith
      have hsplit : ((m : ℝ) - 1) / e = (m : ℝ) / e - 1 / e := by ring
      linarith
    have hbern := one_add_mul_le_pow (a := (p : ℝ) - 1) (by linarith) j
    rw [show (1 : ℝ) + ((p : ℝ) - 1) = p by ring] at hbern
    by_cases hep : (p : ℝ) - 1 ≤ e
    ·
      have hpLn : (e : ℝ) / ((p : ℝ) - 1) < (p : ℝ) ^ Ln := by
        have : q = (p : ℝ) * ((e : ℝ) / ((p : ℝ) - 1)) := by rw [hq]; ring
        rw [this, pow_succ'] at hqlt
        exact lt_of_mul_lt_mul_left hqlt (by linarith)
      have hpvj : (p : ℝ) ^ v = (p : ℝ) ^ Ln * (p : ℝ) ^ j := by rw [hj, pow_add]
      have hmain : (e : ℝ) / ((p : ℝ) - 1) * (1 + j * ((p : ℝ) - 1)) < (m : ℝ) := by
        calc (e : ℝ) / ((p : ℝ) - 1) * (1 + j * ((p : ℝ) - 1))
            ≤ (e : ℝ) / ((p : ℝ) - 1) * (p : ℝ) ^ j := mul_le_mul_of_nonneg_left hbern (by positivity)
          _ < (p : ℝ) ^ Ln * (p : ℝ) ^ j := mul_lt_mul_of_pos_right hpLn (by positivity)
          _ = (p : ℝ) ^ v := hpvj.symm
          _ ≤ m := hpv
      have hexp : (e : ℝ) / ((p : ℝ) - 1) * (1 + j * ((p : ℝ) - 1)) = (e : ℝ) / ((p : ℝ) - 1) + e * j := by
        field_simp
      have hge1 : (1 : ℝ) ≤ (e : ℝ) / ((p : ℝ) - 1) := by rw [le_div_iff₀ hpm1]; linarith
      linarith
    · push_neg at hep

      have hqp : q < p := by
        rw [hq, div_lt_iff₀ hpm1]; nlinarith
      have hL : L ≤ 0 := by
        have hlt : Real.log q / Real.log p < 1 := by
          rw [div_lt_one hlogp]; exact Real.log_lt_log hq0 hqp
        have := Int.floor_le (Real.log q / Real.log p)
        have hLlt : (L : ℝ) < 1 := lt_of_le_of_lt (hLdef ▸ this) hlt
        exact Int.lt_add_one_iff.mp (by exact_mod_cast hLlt)
      have hLn0 : Ln = 0 := by rw [hLn]; omega
      have hvj : v = j := by rw [hj, hLn0, zero_add]
      have hpj : (p : ℝ) ^ j ≤ m := by rw [← hvj]; exact hpv
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hej : (e : ℝ) * j ≤ ((p : ℝ) - 1) * j := mul_le_mul_of_nonneg_right hep.le hj0
      nlinarith

section Inclusions

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [CompleteSpace K] [IsUltrametricDist K]

omit [CompleteSpace K] in
theorem primeToPRoot_one : PrimeToPRoot p (1 : K) :=
  ⟨1, one_pos, hp.out.not_dvd_one, one_pow 1⟩

theorem lower_inclusion (e : ℕ) (he : 0 < e) :
    closedBall (0 : K) ((p : ℝ) ^ (-(aExp p e))) ⊆ logUnitsSet p K := by
  intro x hx
  rw [mem_closedBall_zero_iff] at hx
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have ha := one_div_lt_aExp p e he
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hapos : 0 < aExp p e := lt_trans (by positivity) ha
  set r := (p : ℝ) ^ (-(aExp p e)) with hr
  set c := r * (p : ℝ) ^ ((1 : ℝ) / ((p : ℝ) - 1)) with hcdef
  have hr0 : 0 ≤ r := Real.rpow_nonneg hp0.le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hc1 : c < 1 := by
    rw [hcdef, hr, ← Real.rpow_add hp0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hc0 : 0 ≤ c := mul_nonneg hr0 (Real.rpow_nonneg hp0.le _)
  have hbound : SrcLib.LocalFieldLogRadius.CoeffBound p r c :=
    SrcLib.LocalFieldLogRadius.coeffBound_of_rpow p hr0 le_rfl hc1.le
  obtain ⟨z, hz, hzx⟩ := SrcLib.LocalFieldLogRadius.log1p_surjOn_radius (K := K) p hbound hc0 hc1 hr0 hr1 x hx
  have hzlt : ‖z‖ < 1 := lt_of_le_of_lt hz hr1
  refine ⟨1 + z, ?_, 1, primeToPRoot_one p, ?_, ?_⟩
  · have hne : ‖(1 : K)‖ ≠ ‖z‖ := by rw [norm_one]; exact ne_of_gt hzlt
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]
    exact max_eq_left hzlt.le
  · simpa using hzlt
  · simp [logUnit, hzx]

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] [IsUltrametricDist K] hp in
theorem norm_pi_lt_one (R : RamificationData p K) (hp1 : (1 : ℝ) < p) : ‖R.pi‖ < 1 := by
  rw [R.norm_pi]
  have he0 : (0 : ℝ) < R.e := by exact_mod_cast R.e_pos
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by rw [neg_div]; exact neg_neg_of_pos (by positivity))

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] [IsUltrametricDist K] in

theorem norm_le_of_lt_one (R : RamificationData p K) (y : K) (hy : ‖y‖ < 1) :
    ‖y‖ ≤ (p : ℝ) ^ (-(1 : ℝ) / (R.e : ℝ)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [← R.norm_pi]
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  obtain ⟨n, hn⟩ := R.valueGroup y hy0
  have hpi1 := norm_pi_lt_one p R hp1
  have hpi0 : 0 < ‖R.pi‖ := by
    rw [R.norm_pi]; exact Real.rpow_pos_of_pos (by linarith) _
  have hn1 : 1 ≤ n := by
    by_contra h
    push_neg at h
    have : 1 ≤ ‖R.pi‖ ^ n := one_le_zpow_of_nonpos₀ hpi0 hpi1.le (by omega)
    linarith
  rw [hn]
  calc ‖R.pi‖ ^ n ≤ ‖R.pi‖ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hpi0 hpi1.le hn1
    _ = ‖R.pi‖ := zpow_one _

omit [CompleteSpace K] in

theorem norm_term_le (R : RamificationData p K) (y : K) (hy : ‖y‖ < 1) (n : ℕ) :
    ‖term y n‖ ≤ (p : ℝ) ^ (bExp p R.e) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have he0 : (0 : ℝ) < R.e := by exact_mod_cast R.e_pos
  set v := padicValNat p (n + 1)
  have hyle := norm_le_of_lt_one p R y hy
  rw [term, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div, norm_pow,
    SrcLib.LocalFieldLogRadius.norm_natCast_K (p := p) (K := K),
    SrcLib.LocalFieldLogRadius.norm_natCast_eq p (n + 1) (by omega)]
  have hzpow : (p : ℝ) ^ (-((v : ℕ) : ℤ)) = ((p : ℝ) ^ (v : ℝ))⁻¹ := by
    rw [zpow_neg, zpow_natCast, Real.rpow_natCast]
  rw [hzpow, div_inv_eq_mul]
  have hpow : ‖y‖ ^ (n + 1) ≤ (p : ℝ) ^ (-(((n + 1 : ℕ) : ℝ)) / (R.e : ℝ)) := by
    calc ‖y‖ ^ (n + 1) ≤ ((p : ℝ) ^ (-(1 : ℝ) / (R.e : ℝ))) ^ (n + 1) :=
          pow_le_pow_left₀ (norm_nonneg y) hyle _
      _ = (p : ℝ) ^ (-(((n + 1 : ℕ) : ℝ)) / (R.e : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; congr 1; push_cast; ring
  calc ‖y‖ ^ (n + 1) * (p : ℝ) ^ (v : ℝ)
      ≤ (p : ℝ) ^ (-(((n + 1 : ℕ) : ℝ)) / (R.e : ℝ)) * (p : ℝ) ^ (v : ℝ) :=
        mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hp0.le _)
    _ = (p : ℝ) ^ ((v : ℝ) - ((n + 1 : ℕ) : ℝ) / (R.e : ℝ)) := by
        rw [← Real.rpow_add hp0]; congr 1; ring
    _ ≤ (p : ℝ) ^ (bExp p R.e) := by
        apply Real.rpow_le_rpow_of_exponent_le hp1.le
        unfold bExp
        exact exponent_le p R.e (n + 1) R.e_pos (by omega)

theorem upper_inclusion (R : RamificationData p K) :
    logUnitsSet p K ⊆ closedBall (0 : K) ((p : ℝ) ^ (bExp p R.e)) := by
  rintro _ ⟨u, _, ζ, _, hprin, rfl⟩
  rw [mem_closedBall_zero_iff]
  unfold logUnit log1p
  exact IsUltrametricDist.norm_tsum_le_of_forall_le fun n => norm_term_le p R _ hprin n

theorem inclusions (R : RamificationData p K) :
    closedBall (0 : K) ((p : ℝ) ^ (-(aExp p R.e))) ⊆ logUnitsSet p K ∧
      logUnitsSet p K ⊆ closedBall (0 : K) ((p : ℝ) ^ (bExp p R.e)) :=
  ⟨lower_inclusion p R.e R.e_pos, upper_inclusion p R⟩

theorem aExp_eq_of_small (e : ℕ) (he : 0 < e) (hp2 : p ≠ 2) (hep : e + 2 ≤ p) : aExp p e = 1 / (e : ℝ) := by
  unfold aExp
  rw [if_neg hp2]
  have hpm2 : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (e : ℝ) + 2 ≤ p := by exact_mod_cast hep
    have : (0 : ℝ) < e := by exact_mod_cast he
    linarith
  have hceil : ⌈(e : ℝ) / ((p : ℝ) - 2)⌉ = 1 := by
    rw [Int.ceil_eq_iff]
    constructor
    · push_cast; norm_num; positivity
    · push_cast
      rw [div_le_one hpm2]
      have : (e : ℝ) + 2 ≤ p := by exact_mod_cast hep
      linarith
  rw [hceil]; push_cast; ring

theorem bExp_eq_of_small (e : ℕ) (he : 0 < e) (hep : e + 2 ≤ p) : bExp p e = -(1 / (e : ℝ)) := by
  unfold bExp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hep' : (e : ℝ) + 2 ≤ p := by exact_mod_cast hep
  have hq1 : 1 ≤ (p : ℝ) * e / ((p : ℝ) - 1) := by rw [le_div_iff₀ hpm1]; nlinarith
  have hqp : (p : ℝ) * e / ((p : ℝ) - 1) < p := by rw [div_lt_iff₀ hpm1]; nlinarith
  have hfloor : ⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    constructor
    · exact div_nonneg (Real.log_nonneg hq1) hlogp.le
    · rw [div_lt_one hlogp]; exact Real.log_lt_log (by linarith) hqp
  rw [hfloor]; push_cast; ring

theorem logUnitsSet_eq_of_small_ramification (R : RamificationData p K) (hp2 : p ≠ 2) (hep : R.e + 2 ≤ p) :
    logUnitsSet p K = closedBall (0 : K) ((p : ℝ) ^ (-(1 / (R.e : ℝ)))) := by
  have h := inclusions p R
  rw [aExp_eq_of_small p R.e R.e_pos hp2 hep] at h
  rw [bExp_eq_of_small p R.e R.e_pos hep] at h
  exact Set.Subset.antisymm h.2 h.1

end Inclusions

section Model

noncomputable def qpRamification : RamificationData p ℚ_[p] where
  e := 1
  e_pos := one_pos
  pi := (p : ℚ_[p])
  norm_pi := by
    rw [Padic.norm_p]; push_cast
    rw [show (-(1 : ℝ) / 1) = -1 by norm_num, Real.rpow_neg_one]
  valueGroup := fun x hx => ⟨x.valuation, by
    rw [Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_p, inv_zpow', zpow_neg]⟩

theorem qp_logUnits (hp2 : p ≠ 2) :
    logUnitsSet p ℚ_[p] = closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-(1 : ℝ))) ∧
      logUnitsSet p ℚ_[p] = Src.IUT4.Proposition14ii.logUnits p := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  refine ⟨?_, rfl⟩
  have h := logUnitsSet_eq_of_small_ramification p (qpRamification p) hp2 (by change 1 + 2 ≤ p; omega)
  rw [h]
  change closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-(1 / ((1 : ℕ) : ℝ)))) = _
  norm_num

end Model

end Src.IUT4.Proposition12i

section Check
open Src.IUT4.Proposition12i
end Check
