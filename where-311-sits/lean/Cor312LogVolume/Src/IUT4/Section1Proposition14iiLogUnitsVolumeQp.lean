import Mathlib
import Cor312LogVolume.Src.IUT3.Section3Proposition35iiUpperSemiCompat
import Cor312LogVolume.Src.IUT3.Section3Theorem311Indeterminacies

namespace Src.IUT4.Proposition14ii

open Metric Set MeasureTheory SrcLib.LocalFieldLogIsometry Src.IUT3.Proposition39iv
  Src.IUT3.Proposition35ii

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable instance : MeasurableSpace ℚ_[p] := borel _

instance : BorelSpace ℚ_[p] := ⟨rfl⟩

def logUnits : Set ℚ_[p] := {x | ∃ u : ℚ_[p], LogRel p u x}

noncomputable def haarQp : Measure ℚ_[p] :=
  Measure.addHaarMeasure
    ⟨⟨closedBall (0 : ℚ_[p]) 1, isCompact_closedBall 0 1⟩,
      ⟨0, Metric.ball_subset_interior_closedBall (mem_ball_self one_pos)⟩⟩

instance : (haarQp p).IsAddHaarMeasure := by
  unfold haarQp; infer_instance

variable {p}

theorem norm_le_inv_of_lt_one {x : ℚ_[p]} (hx : ‖x‖ < 1) : ‖x‖ ≤ (p : ℝ)⁻¹ := by
  let z : ℤ_[p] := ⟨x, le_of_lt hx⟩
  have hz : ‖z‖ < 1 := hx
  obtain ⟨y, hy⟩ := (PadicInt.norm_lt_one_iff_dvd z).mp hz
  have : ‖z‖ = ‖(p : ℤ_[p])‖ * ‖y‖ := by rw [hy, norm_mul]
  change ‖x‖ = _ at this
  rw [this, PadicInt.norm_p]
  have hy1 : ‖y‖ ≤ 1 := y.norm_le_one
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  nlinarith

theorem inv_p_le_third (hp2 : p ≠ 2) : (p : ℝ)⁻¹ ≤ 1 / 3 := by
  have h3 : 3 ≤ p := by have := hp.out.two_le; omega
  have : (3 : ℝ) ≤ p := by exact_mod_cast h3
  rw [one_div]
  exact inv_anti₀ (by norm_num) this

theorem logUnits_eq_odd (hp2 : p ≠ 2) : logUnits p = closedBall (0 : ℚ_[p]) (p : ℝ)⁻¹ := by
  ext x
  constructor
  · rintro ⟨u, _, ζ, _, hprin, rfl⟩
    rw [mem_closedBall_zero_iff]
    have hsmall := norm_le_inv_of_lt_one hprin
    have hiso : ‖logUnit (u * ζ⁻¹)‖ = ‖u * ζ⁻¹ - 1‖ :=
      SrcLib.LocalFieldLogThird.norm_log1p_eq_third (p := p) _ (hsmall.trans (inv_p_le_third hp2))
    rw [hiso]
    exact hsmall
  · intro hx
    rw [mem_closedBall_zero_iff] at hx
    obtain ⟨z, hz, hzx⟩ :=
      SrcLib.LocalFieldLogThird.log1p_surjOn_third (p := p) x (hx.trans (inv_p_le_third hp2))
    have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    have hnorm : ‖(1 : ℚ_[p]) + z‖ = 1 := by
      have hne : ‖(1 : ℚ_[p])‖ ≠ ‖z‖ := by rw [norm_one]; exact ne_of_gt hz1
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]
      exact max_eq_left (le_of_lt hz1)
    refine ⟨1 + z, hnorm, 1, ⟨1, one_pos, ?_, one_pow 1⟩, ?_, ?_⟩
    · intro hdvd
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp hdvd)
    · rw [inv_one, mul_one, add_sub_cancel_left]; exact hz1
    · rw [inv_one, mul_one]
      unfold logUnit
      rw [add_sub_cancel_left, hzx]

theorem natCast_mem_closedBall (k : ℕ) : (k : ℚ_[p]) ∈ closedBall (0 : ℚ_[p]) 1 := by
  rw [mem_closedBall_zero_iff]
  simpa using Padic.norm_int_le_one (p := p) (k : ℤ)

theorem closedBall_one_eq_iUnion :
    closedBall (0 : ℚ_[p]) 1 = ⋃ k ∈ Finset.range p, closedBall (k : ℚ_[p]) (p : ℝ)⁻¹ := by
  ext x
  simp only [mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · intro hx
    rw [mem_closedBall_zero_iff] at hx
    let z : ℤ_[p] := ⟨x, hx⟩
    have hspec := PadicInt.toZMod_spec z
    refine ⟨(PadicInt.toZMod z).val, ZMod.val_lt _, ?_⟩
    rw [mem_closedBall, dist_eq_norm]
    have hmem : ‖z - ((PadicInt.toZMod z).val : ℤ_[p])‖ < 1 := by
      rw [ZMod.natCast_val]
      exact PadicInt.mem_nonunits.mp hspec
    have : ‖x - ((PadicInt.toZMod z).val : ℚ_[p])‖ < 1 := by simpa [z] using hmem
    exact norm_le_inv_of_lt_one this
  · rintro ⟨k, _, hk⟩
    rw [mem_closedBall_zero_iff]
    rw [mem_closedBall, dist_eq_norm] at hk
    have hx : x = (k : ℚ_[p]) + (x - k) := by ring
    rw [hx]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact mem_closedBall_zero_iff.mp (natCast_mem_closedBall k)
    · exact hk.trans (by
        have : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
        exact inv_le_one_of_one_le₀ this)

theorem closedBall_pairwiseDisjoint :
    (↑(Finset.range p) : Set ℕ).PairwiseDisjoint (fun k : ℕ => closedBall (k : ℚ_[p]) (p : ℝ)⁻¹) := by
  intro k hk k' hk' hne
  simp only [Finset.coe_range, mem_Iio] at hk hk'
  rw [Function.onFun, Set.disjoint_left]
  intro y hy hy'
  rw [mem_closedBall, dist_eq_norm] at hy hy'
  have hkk : ‖((k : ℤ) - (k' : ℤ) : ℚ_[p])‖ < 1 := by
    have : ((k : ℤ) - (k' : ℤ) : ℚ_[p]) = (y - k') + -(y - k) := by push_cast; ring
    rw [this]
    refine lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_neg])) ?_
    have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    exact max_lt (lt_of_le_of_lt hy' hlt) (lt_of_le_of_lt hy hlt)
  have hdvd : (p : ℤ) ∣ (k : ℤ) - k' := by
    have := (Padic.norm_intCast_lt_one_iff (p := p) (k := (k : ℤ) - k')).mp (by push_cast at hkk ⊢; exact hkk)
    exact this
  have habs : ((k : ℤ) - k').natAbs < p := by omega
  have hzero := Int.eq_zero_of_abs_lt_dvd hdvd (by
    rw [abs_lt]; constructor <;> omega)
  exact hne (by omega)

theorem closedBall_translate (k : ℚ_[p]) (r : ℝ) :
    closedBall k r = (fun w => k + w) '' closedBall (0 : ℚ_[p]) r := by
  ext y
  constructor
  · intro hy
    refine ⟨y - k, ?_, by ring⟩
    rw [mem_closedBall_zero_iff]
    rwa [mem_closedBall, dist_eq_norm] at hy
  · rintro ⟨w, hw, rfl⟩
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact mem_closedBall_zero_iff.mp hw

theorem haarQp_closedBall_inv : haarQp p (closedBall (0 : ℚ_[p]) (p : ℝ)⁻¹) = (p : ENNReal)⁻¹ := by
  have hone : haarQp p (closedBall (0 : ℚ_[p]) 1) = 1 := by
    unfold haarQp
    exact Measure.addHaarMeasure_self
  rw [closedBall_one_eq_iUnion, measure_biUnion_finset closedBall_pairwiseDisjoint
    (fun k _ => measurableSet_closedBall)] at hone
  have heach : ∀ k ∈ Finset.range p,
      haarQp p (closedBall (k : ℚ_[p]) (p : ℝ)⁻¹) = haarQp p (closedBall (0 : ℚ_[p]) (p : ℝ)⁻¹) := by
    intro k _
    rw [closedBall_translate]
    exact measure_translate (haarQp p) _ _
  rw [Finset.sum_congr rfl heach, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hone
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hone)

theorem logVolume_logUnits_odd (hp2 : p ≠ 2) :
    Src.IUT3.Theorem311.logVolume (haarQp p) (closedBall (0 : ℚ_[p]) 1) (logUnits p) =
      -Real.log p := by
  unfold Src.IUT3.Theorem311.logVolume
  rw [logUnits_eq_odd hp2, haarQp_closedBall_inv]
  have hone : haarQp p (closedBall (0 : ℚ_[p]) 1) = 1 := by
    unfold haarQp
    exact Measure.addHaarMeasure_self
  rw [hone, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_one, Real.log_one, sub_zero,
    Real.log_inv]

theorem logVolume_normalization :
    Src.IUT3.Theorem311.logVolume (haarQp p) (closedBall (0 : ℚ_[p]) 1) (closedBall (0 : ℚ_[p]) 1) = 0 ∧
      Src.IUT3.Theorem311.logVolume (haarQp p) (closedBall (0 : ℚ_[p]) 1)
        (closedBall (0 : ℚ_[p]) (p : ℝ)⁻¹) = -Real.log p := by
  refine ⟨Src.IUT3.Theorem311.logVolume_self _ _, ?_⟩
  unfold Src.IUT3.Theorem311.logVolume
  have hone : haarQp p (closedBall (0 : ℚ_[p]) 1) = 1 := by
    unfold haarQp
    exact Measure.addHaarMeasure_self
  rw [haarQp_closedBall_inv, hone, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_one, Real.log_one,
    sub_zero, Real.log_inv]

section Scaling

noncomputable def scaleEquiv (c : ℚ_[p]) (hc : c ≠ 0) : ℚ_[p] ≃+ ℚ_[p] where
  toFun x := c * x
  invFun x := c⁻¹ * x
  left_inv x := by simp [hc]
  right_inv x := by simp [hc]
  map_add' x y := mul_add c x y

theorem haarQp_mul_p (A : Set ℚ_[p]) (hA : MeasurableSet A) :
    haarQp p ((fun x => (p : ℚ_[p]) * x) '' A) = (p : ENNReal)⁻¹ * haarQp p A := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set e := scaleEquiv (p : ℚ_[p])⁻¹ (inv_ne_zero hp0) with he
  have hcont : Continuous e := continuous_const.mul continuous_id
  have hcont' : Continuous e.symm := continuous_const.mul continuous_id
  haveI : (Measure.map e (haarQp p)).IsAddHaarMeasure := e.isAddHaarMeasure_map (haarQp p) hcont hcont'
  set K₀ : TopologicalSpace.PositiveCompacts ℚ_[p] :=
    ⟨⟨closedBall (0 : ℚ_[p]) 1, isCompact_closedBall 0 1⟩,
      ⟨0, Metric.ball_subset_interior_closedBall (mem_ball_self one_pos)⟩⟩ with hK₀
  have huniq := Measure.addHaarMeasure_unique (Measure.map e (haarQp p)) K₀
  have hhaar : haarQp p = Measure.addHaarMeasure K₀ := rfl
  have hpre : ∀ S : Set ℚ_[p], e ⁻¹' S = (fun x => (p : ℚ_[p]) * x) '' S := by
    intro S; ext x
    simp only [mem_preimage, mem_image, he, scaleEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]
    constructor
    · intro hx; exact ⟨(p : ℚ_[p])⁻¹ * x, hx, by field_simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa [hp0] using hy
  have hK : Measure.map e (haarQp p) (K₀ : Set ℚ_[p]) = (p : ENNReal)⁻¹ := by
    have : e ⁻¹' (closedBall (0 : ℚ_[p]) 1) = closedBall (0 : ℚ_[p]) (p : ℝ)⁻¹ := by
      ext x
      simp only [mem_preimage, mem_closedBall_zero_iff, he, scaleEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, norm_mul,
        norm_inv, Padic.norm_p]
      constructor
      · intro h; have hp1 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
        rw [inv_inv] at h
        calc ‖x‖ = (p : ℝ)⁻¹ * ((p : ℝ) * ‖x‖) := by field_simp
          _ ≤ (p : ℝ)⁻¹ * 1 := by gcongr
          _ = (p : ℝ)⁻¹ := mul_one _
      · intro h; have hp1 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
        rw [inv_inv]
        calc (p : ℝ) * ‖x‖ ≤ (p : ℝ) * (p : ℝ)⁻¹ := by gcongr
          _ = 1 := by field_simp
    change Measure.map e (haarQp p) (closedBall (0 : ℚ_[p]) 1) = _
    rw [Measure.map_apply hcont.measurable isClosed_closedBall.measurableSet, this, haarQp_closedBall_inv]
  have key := congrArg (fun ν : Measure ℚ_[p] => ν A) huniq
  simp only at key
  rw [Measure.map_apply hcont.measurable hA, hpre, hK, Measure.smul_apply, smul_eq_mul, ← hhaar] at key
  exact key

theorem logVolume_mul_p (A : Set ℚ_[p]) (hA : MeasurableSet A) (hpos : 0 < haarQp p A) (hfin : haarQp p A < ⊤) :
    Src.IUT3.Theorem311.logVolume (haarQp p) (closedBall (0 : ℚ_[p]) 1) ((fun x => (p : ℚ_[p]) * x) '' A) =
      Src.IUT3.Theorem311.logVolume (haarQp p) (closedBall (0 : ℚ_[p]) 1) A - Real.log p := by
  unfold Src.IUT3.Theorem311.logVolume
  rw [haarQp_mul_p A hA, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hp1 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have ha : 0 < (haarQp p A).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  rw [Real.log_mul (inv_ne_zero hp1.ne') ha.ne', Real.log_inv]
  ring

end Scaling

section Two

theorem two_unit_add_one {b : ℚ_[2]} (hb : ‖b‖ = 1) : ‖b + 1‖ < 1 := by
  let z : ℤ_[2] := ⟨b, le_of_eq hb⟩
  have hspec := PadicInt.toZMod_spec z
  have hne : PadicInt.toZMod z ≠ 0 := by
    intro h0
    rw [h0, ZMod.cast_zero, sub_zero] at hspec
    have : ‖z‖ < 1 := PadicInt.mem_nonunits.mp hspec
    change ‖b‖ < 1 at this
    linarith
  have h1 : PadicInt.toZMod z = 1 := by
    have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact this _ hne
  have hc : (ZMod.cast (1 : ZMod 2) : ℤ_[2]) = 1 := by
    rw [← ZMod.natCast_val]
    have : (1 : ZMod 2).val = 1 := rfl
    rw [this, Nat.cast_one]
  rw [h1, hc] at hspec
  have hlt : ‖z - 1‖ < 1 := PadicInt.mem_nonunits.mp hspec
  change ‖b - 1‖ < 1 at hlt
  have h2 : ‖(2 : ℚ_[2])‖ < 1 := by
    have := Padic.norm_p (p := 2); simp only [Nat.cast_ofNat] at this; rw [this]; norm_num
  rw [show b + 1 = (b - 1) + 2 by ring]
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hlt h2)

theorem norm_two_Q2 : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
  have := Padic.norm_p (p := 2); simp only [Nat.cast_ofNat] at this; rw [this, one_div]

theorem two_principal_sq {w : ℚ_[2]} (hw : ‖w - 1‖ < 1) : ‖w * w - 1‖ ≤ 1 / 8 := by
  have ha : ‖w - 1‖ ≤ 1 / 2 := by
    have := norm_le_inv_of_lt_one (p := 2) hw; simpa using this

  set b := (w - 1) / 2 with hbdef
  have hwb : w - 1 = 2 * b := by rw [hbdef]; ring
  have hb : ‖b‖ ≤ 1 := by
    rw [hbdef, norm_div, norm_two_Q2]; linarith
  have hsq : w * w - 1 = (2 * b) * (2 * (b + 1)) := by
    have : w = 2 * b + 1 := by linear_combination hwb
    rw [this]; ring
  rw [hsq, norm_mul, norm_mul, norm_mul, norm_two_Q2]
  rcases lt_or_eq_of_le hb with hlt | heq
  · have hb2 : ‖b‖ ≤ 1 / 2 := by have := norm_le_inv_of_lt_one (p := 2) hlt; simpa using this
    have hb1 : ‖b + 1‖ ≤ 1 := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb ?_); rw [norm_one]
    nlinarith [norm_nonneg b, norm_nonneg (b + 1)]
  · have hb1 : ‖b + 1‖ ≤ 1 / 2 := by
      have := norm_le_inv_of_lt_one (p := 2) (two_unit_add_one heq); simpa using this
    rw [heq]
    nlinarith [norm_nonneg (b + 1)]

theorem logUnits_eq_two : logUnits 2 = closedBall (0 : ℚ_[2]) (1 / 4) := by
  ext x
  constructor
  · rintro ⟨u, _, ζ, _, hprin, rfl⟩
    rw [mem_closedBall_zero_iff]
    set w := u * ζ⁻¹
    have hsq := two_principal_sq hprin
    have hmul : logUnit (w * w) = logUnit w + logUnit w :=
      Src.IUT3.Remark122.logUnit_mul (p := 2) hprin hprin
    have hiso : ‖logUnit (w * w)‖ = ‖w * w - 1‖ :=
      SrcLib.LocalFieldLogThird.norm_log1p_eq_third (p := 2) _ (hsq.trans (by norm_num))
    have h2 : logUnit w + logUnit w = 2 * logUnit w := by ring
    rw [hmul, h2, norm_mul, norm_two_Q2] at hiso
    linarith
  · intro hx
    rw [mem_closedBall_zero_iff] at hx
    obtain ⟨z, hz, hzx⟩ :=
      SrcLib.LocalFieldLogThird.log1p_surjOn_third (p := 2) x (hx.trans (by norm_num))
    have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    have hnorm : ‖(1 : ℚ_[2]) + z‖ = 1 := by
      have hne : ‖(1 : ℚ_[2])‖ ≠ ‖z‖ := by rw [norm_one]; exact ne_of_gt hz1
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]
      exact max_eq_left (le_of_lt hz1)
    refine ⟨1 + z, hnorm, 1, ⟨1, one_pos, by norm_num, one_pow 1⟩, ?_, ?_⟩
    · rw [inv_one, mul_one, add_sub_cancel_left]; exact hz1
    · rw [inv_one, mul_one]
      unfold logUnit
      rw [add_sub_cancel_left, hzx]

theorem closedBall_half_eq_union :
    closedBall (0 : ℚ_[2]) (1 / 2) = closedBall (0 : ℚ_[2]) (1 / 4) ∪ closedBall (2 : ℚ_[2]) (1 / 4) := by
  ext x
  simp only [mem_union]
  constructor
  · intro hx
    rw [mem_closedBall_zero_iff] at hx
    have hy : x / 2 ∈ closedBall (0 : ℚ_[2]) 1 := by
      rw [mem_closedBall_zero_iff, norm_div, norm_two_Q2]; linarith
    rw [closedBall_one_eq_iUnion] at hy
    simp only [mem_iUnion, Finset.mem_range, exists_prop] at hy
    obtain ⟨k, hk, hyk⟩ := hy
    rw [mem_closedBall, dist_eq_norm] at hyk
    have hyk' : ‖x / 2 - k‖ ≤ 1 / 2 := by simpa using hyk
    have hxk : ‖x - 2 * k‖ ≤ 1 / 4 := by
      have : x - 2 * k = 2 * (x / 2 - k) := by ring
      rw [this, norm_mul, norm_two_Q2]; linarith
    interval_cases k
    · left; rw [mem_closedBall_zero_iff]; simpa using hxk
    · right; rw [mem_closedBall, dist_eq_norm]; simpa using hxk
  · rintro (h | h)
    · rw [mem_closedBall_zero_iff] at h ⊢; linarith
    · rw [mem_closedBall, dist_eq_norm] at h
      rw [mem_closedBall_zero_iff]
      rw [show x = (x - 2) + 2 by ring]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by linarith) (by rw [norm_two_Q2]))

theorem haarQp_two_quarter : haarQp 2 (closedBall (0 : ℚ_[2]) (1 / 4)) = 4⁻¹ := by
  have hhalf := haarQp_closedBall_inv (p := 2)
  have hdisj : Disjoint (closedBall (0 : ℚ_[2]) (1 / 4)) (closedBall (2 : ℚ_[2]) (1 / 4)) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    rw [mem_closedBall_zero_iff] at hy
    rw [mem_closedBall, dist_eq_norm] at hy'
    have : ‖(2 : ℚ_[2])‖ ≤ 1 / 4 := by
      rw [show (2 : ℚ_[2]) = y + -(y - 2) by ring]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy ?_)
      rw [norm_neg]; exact hy'
    rw [norm_two_Q2] at this; norm_num at this
  have htrans : haarQp 2 (closedBall (2 : ℚ_[2]) (1 / 4)) = haarQp 2 (closedBall (0 : ℚ_[2]) (1 / 4)) := by
    rw [closedBall_translate]
    exact measure_translate (haarQp 2) _ _
  have hcast : closedBall (0 : ℚ_[2]) ((2 : ℕ) : ℝ)⁻¹ = closedBall (0 : ℚ_[2]) (1 / 2) := by norm_num
  rw [hcast, closedBall_half_eq_union, measure_union hdisj measurableSet_closedBall, htrans] at hhalf
  have h2 : (2 : ENNReal) * haarQp 2 (closedBall (0 : ℚ_[2]) (1 / 4)) = 2⁻¹ := by
    rw [two_mul]; simpa using hhalf
  have hne : haarQp 2 (closedBall (0 : ℚ_[2]) (1 / 4)) = 2⁻¹ / 2 := by
    rw [← h2, mul_comm, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
  rw [hne, ENNReal.div_eq_inv_mul, ← ENNReal.mul_inv (by norm_num) (by norm_num)]
  norm_num

theorem logVolume_logUnits_two :
    Src.IUT3.Theorem311.logVolume (haarQp 2) (closedBall (0 : ℚ_[2]) 1) (logUnits 2) =
      -(2 * Real.log 2) := by
  unfold Src.IUT3.Theorem311.logVolume
  rw [logUnits_eq_two, haarQp_two_quarter]
  have hone : haarQp 2 (closedBall (0 : ℚ_[2]) 1) = 1 := by
    unfold haarQp
    exact Measure.addHaarMeasure_self
  rw [hone, ENNReal.toReal_inv, ENNReal.toReal_one, Real.log_one, sub_zero, Real.log_inv]
  have : ((4 : ENNReal)).toReal = (2 : ℝ) ^ 2 := by norm_num
  rw [this, Real.log_pow]
  push_cast; ring

end Two

section Prop12

noncomputable def aIdx (e p : ℕ) : ℝ :=
  if p = 2 then 2 else (1 / (e : ℝ)) * ⌈(e : ℝ) / ((p : ℝ) - 2)⌉

noncomputable def bIdx (e p : ℕ) : ℝ :=
  ⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ - 1 / (e : ℝ)

theorem aIdx_one_odd (hp2 : p ≠ 2) : aIdx 1 p = 1 := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.out.two_le; omega)
  unfold aIdx
  rw [if_neg hp2, Nat.cast_one, div_one, one_mul]
  have hceil : ⌈(1 : ℝ) / ((p : ℝ) - 2)⌉ = 1 := by
    rw [Int.ceil_eq_iff]
    constructor
    · push_cast; rw [sub_self]; exact div_pos one_pos (by linarith)
    · rw [div_le_iff₀ (by linarith)]; push_cast; linarith
  rw [hceil]; norm_num

theorem aIdx_one_two : aIdx 1 2 = 2 := by
  simp [aIdx]

theorem bIdx_one_odd (hp2 : p ≠ 2) : bIdx 1 p = -1 := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.out.two_le; omega)
  unfold bIdx
  rw [Nat.cast_one, mul_one, div_one]
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  have hfl : ⌊Real.log ((p : ℝ) / ((p : ℝ) - 1)) / Real.log p⌋ = 0 := by
    rw [Int.floor_eq_iff]
    constructor
    · push_cast
      apply div_nonneg _ hlogp.le
      apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith)]; linarith
    · push_cast
      rw [zero_add, div_lt_one hlogp]
      apply Real.log_lt_log (div_pos (by linarith) (by linarith))
      rw [div_lt_iff₀ (by linarith)]; nlinarith
  rw [hfl]; norm_num

theorem bIdx_one_two : bIdx 1 2 = 0 := by
  unfold bIdx
  have hlog : Real.log ((2 : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_ofNat]; exact (Real.log_pos (by norm_num)).ne'
  have : Real.log (((2 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1)) / Real.log ((2 : ℕ) : ℝ) = 1 := by
    rw [show ((2 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1) = ((2 : ℕ) : ℝ) by norm_num]
    exact div_self hlog
  rw [this]; norm_num

theorem prop12i_Qp :
    closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-aIdx 1 p)) ⊆ logUnits p ∧
      logUnits p ⊆ closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (bIdx 1 p)) ∧
      (p ≠ 2 → closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-aIdx 1 p)) = logUnits p ∧
        logUnits p = closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (bIdx 1 p))) := by
  by_cases hp2 : p = 2
  · subst hp2
    rw [aIdx_one_two, bIdx_one_two, logUnits_eq_two]
    refine ⟨?_, ?_, fun h => absurd rfl h⟩
    · rw [show ((2 : ℕ) : ℝ) ^ (-(2 : ℝ)) = 1 / 4 by
        rw [Real.rpow_neg (by norm_num), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num]
    · rw [Real.rpow_zero]
      exact closedBall_subset_closedBall (by norm_num)
  · have hpow1 : (p : ℝ) ^ (-aIdx 1 p) = (p : ℝ)⁻¹ := by
      rw [aIdx_one_odd hp2, Real.rpow_neg (by positivity), Real.rpow_one]
    have hpow2 : (p : ℝ) ^ (bIdx 1 p) = (p : ℝ)⁻¹ := by
      rw [bIdx_one_odd hp2, Real.rpow_neg (by positivity), Real.rpow_one]
    rw [hpow1, hpow2, logUnits_eq_odd hp2]
    exact ⟨subset_rfl, subset_rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem prop14iv_Qp (hp2 : p ≠ 2) (φ : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) (hφ : φ '' logUnits p ⊆ logUnits p) :
    φ '' closedBall (0 : ℚ_[p]) 1 ⊆ closedBall (0 : ℚ_[p]) 1 ∧
      Src.IUT3.Theorem311.logVolume (haarQp p) (closedBall (0 : ℚ_[p]) 1) (closedBall (0 : ℚ_[p]) 1) = 0 := by
  refine ⟨?_, Src.IUT3.Theorem311.logVolume_self _ _⟩
  rw [logUnits_eq_odd hp2] at hφ
  have hlin : ∀ x : ℚ_[p], φ x = x * φ 1 := by
    intro x
    have := φ.map_smul x 1
    simpa [smul_eq_mul] using this
  have hp_mem : (p : ℚ_[p]) ∈ closedBall (0 : ℚ_[p]) (p : ℝ)⁻¹ := by
    rw [mem_closedBall_zero_iff, Padic.norm_p]
  have hc : ‖φ 1‖ ≤ 1 := by
    have h := hφ ⟨p, hp_mem, rfl⟩
    rw [mem_closedBall_zero_iff, hlin, norm_mul, Padic.norm_p] at h
    have hp1 : (0 : ℝ) < (p : ℝ)⁻¹ := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
      positivity
    nlinarith [norm_nonneg (φ 1)]
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closedBall_zero_iff] at hx ⊢
  rw [hlin, norm_mul]
  nlinarith [norm_nonneg x, norm_nonneg (φ 1)]

end Prop12

section Remark397

theorem principal_logRel {u : ℚ_[p]} (hu : ‖u - 1‖ < 1) : LogRel p u (logUnit u) := by
  have hnorm : ‖u‖ = 1 := by
    have hu' : u = 1 + (u - 1) := by ring
    have hne : ‖(1 : ℚ_[p])‖ ≠ ‖u - 1‖ := by rw [norm_one]; exact ne_of_gt hu
    rw [hu', IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]
    exact max_eq_left (le_of_lt hu)
  refine ⟨hnorm, 1, ⟨1, one_pos, ?_, one_pow 1⟩, ?_, ?_⟩
  · intro hdvd; exact hp.out.one_lt.ne' (Nat.dvd_one.mp hdvd)
  · rw [inv_one, mul_one]; exact hu
  · rw [inv_one, mul_one]

theorem logShell_Qp_eq : Src.IUT3.Remark122.logShell (K := ℚ_[p]) p = closedBall (0 : ℚ_[p]) 1 := by
  apply Set.Subset.antisymm
  · rintro x ⟨u, hu, hux⟩
    have hu' : ‖u - 1‖ < 1 := hu
    have hmem : logUnit u ∈ logUnits p := ⟨u, principal_logRel hu'⟩
    rw [mem_closedBall_zero_iff]
    have hx := congrArg norm hux
    rw [norm_mul] at hx
    by_cases hp2 : p = 2
    · subst hp2
      rw [logUnits_eq_two, mem_closedBall_zero_iff] at hmem
      have h4 : ‖((Src.IUT3.Remark122.pStar 2 : ℕ) : ℚ_[2])‖ = 1 / 4 := by
        rw [Src.IUT3.Remark122.pStar_two]
        have : ((4 : ℕ) : ℚ_[2]) = 2 * 2 := by norm_num
        rw [this, norm_mul, norm_two_Q2]; norm_num
      rw [h4] at hx
      linarith
    · rw [logUnits_eq_odd hp2, mem_closedBall_zero_iff] at hmem
      have hps : ‖((Src.IUT3.Remark122.pStar p : ℕ) : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
        rw [Src.IUT3.Remark122.pStar_odd hp2]; exact Padic.norm_p
      rw [hps] at hx
      have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := by
        have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
        positivity
      nlinarith [norm_nonneg x]
  · exact Src.IUT3.Remark122.intO_subset_logShell (p := p)

theorem logShell_eq_intO_of_unramified {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [CompleteSpace K]
    [IsUltrametricDist K] (hp2 : p ≠ 2) (hunr : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ (p : ℝ)⁻¹) :
    Src.IUT3.Remark122.logShell (K := K) p = Src.IUT3.Remark122.intO := by
  apply Set.Subset.antisymm
  · rintro x ⟨u, hu, hux⟩
    have hu' : ‖u - 1‖ < 1 := hu
    have hsmall := hunr _ hu'
    have hlog : ‖logUnit u‖ = ‖u - 1‖ :=
      SrcLib.LocalFieldLogThird.norm_log1p_eq_third (p := p) _ (hsmall.trans (inv_p_le_third hp2))
    have hps : ‖((Src.IUT3.Remark122.pStar p : ℕ) : K)‖ = (p : ℝ)⁻¹ := by
      rw [Src.IUT3.Remark122.pStar_odd hp2, Src.IUT3.Remark122.norm_natCast_K (p := p)]
      exact Padic.norm_p
    have hx := congrArg norm hux
    rw [norm_mul, hps, hlog] at hx
    rw [Src.IUT3.Remark122.intO, mem_closedBall_zero_iff]
    have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
      positivity
    nlinarith [norm_nonneg x]
  · exact Src.IUT3.Remark122.intO_subset_logShell (p := p)

theorem remark397i_Qp :
    Src.IUT3.Remark122.logShell (K := ℚ_[p]) p = closedBall (0 : ℚ_[p]) 1 ∧
      Src.IUT3.Theorem311.logVolume (haarQp p) (closedBall (0 : ℚ_[p]) 1)
        (Src.IUT3.Remark122.logShell (K := ℚ_[p]) p) = 0 := by
  refine ⟨logShell_Qp_eq, ?_⟩
  rw [logShell_Qp_eq]
  exact Src.IUT3.Theorem311.logVolume_self _ _

end Remark397

end Src.IUT4.Proposition14ii

section Check
open Src.IUT4.Proposition14ii
end Check
