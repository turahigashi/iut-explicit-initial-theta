import Cor312LogVolume.theorem311.LocalScalarHaarCore
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Algebra.Module.Compact

open Set TopologicalSpace MeasureTheory IsLocalRing
open scoped ENNReal NNReal Pointwise Topology

namespace CitedLV.Theorem311

theorem maximalIdeal_index_eq_residue_card
    {R : Type*} [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).toAddSubgroup.index = Nat.card (ResidueField R) := by
  rw [AddSubgroup.index_eq_card]
  rfl

theorem padicInt_maximalIdeal_index (p : ℕ) [Fact p.Prime] :
    (maximalIdeal ℤ_[p]).toAddSubgroup.index = p := by
  rw [maximalIdeal_index_eq_residue_card]
  rw [Nat.card_congr (PadicInt.residueField (p := p)).toEquiv]
  exact Nat.card_zmod p

def padicQpUnitRegion (p : ℕ) [Fact p.Prime] :
    NormalizedHaarRegion ℚ_[p] where
  val := Metric.closedBall 0 1
  property :=
    ⟨⟨ProperSpace.isCompact_closedBall 0 1,
      IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero⟩,
      ⟨0, by simp⟩⟩

noncomputable def padicPrimeUnit (p : ℕ) [Fact p.Prime] : ℚ_[p]ˣ :=
  Units.mk0 (p : ℚ_[p]) (by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)

theorem padicPrime_smul_unitBall_eq_image_maximalIdeal
    (p : ℕ) [Fact p.Prime] :
    (padicPrimeUnit p) • (padicQpUnitRegion p).1 =
      ((↑) : ℤ_[p] → ℚ_[p]) '' (maximalIdeal ℤ_[p] : Set ℤ_[p]) := by
  ext x
  constructor
  · rw [Set.mem_smul_set]
    rintro ⟨y, hy, rfl⟩
    have hy' : ‖y‖ ≤ 1 := by
      simpa [padicQpUnitRegion, Metric.mem_closedBall] using hy
    let z : ℤ_[p] := ⟨y, hy'⟩
    refine ⟨(p : ℤ_[p]) * z, ?_, ?_⟩
    · change (p : ℤ_[p]) * z ∈ maximalIdeal ℤ_[p]
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
    · simp [padicPrimeUnit, z]
  · rintro ⟨z, hz, rfl⟩
    have hzspan : z ∈ Ideal.span {(p : ℤ_[p])} := by
      rw [← PadicInt.maximalIdeal_eq_span_p]
      exact hz
    have hzdiv : (p : ℤ_[p]) ∣ z := Ideal.mem_span_singleton.mp hzspan
    rcases hzdiv with ⟨w, rfl⟩
    rw [Set.mem_smul_set]
    refine ⟨(w : ℚ_[p]), ?_, ?_⟩
    · simpa [padicQpUnitRegion, Metric.mem_closedBall] using w.2
    · simp [padicPrimeUnit]

theorem padicInt_comap_normalizedQpHaar_maximalIdeal_mul
    (p : ℕ) [Fact p.Prime] :
    let _ : MeasurableSpace ℚ_[p] := borel ℚ_[p]
    let _ : BorelSpace ℚ_[p] := ⟨rfl⟩
    let _ : MeasurableSpace ℤ_[p] := borel ℤ_[p]
    let _ : BorelSpace ℤ_[p] := ⟨rfl⟩
    let μ := normalizedAddHaar (padicQpUnitRegion p)
    let ν := Measure.comap
      (PadicInt.Coe.ringHom (p := p)).toAddMonoidHom μ
    (p : ENNReal) * ν (maximalIdeal ℤ_[p] : Set ℤ_[p]) = 1 := by
  letI mQ : MeasurableSpace ℚ_[p] := borel ℚ_[p]
  letI bQ : BorelSpace ℚ_[p] := ⟨rfl⟩
  letI mZ : MeasurableSpace ℤ_[p] := borel ℤ_[p]
  letI bZ : BorelSpace ℤ_[p] := ⟨rfl⟩
  letI : MeasurableAdd ℚ_[p] := ContinuousAdd.measurableAdd
  letI : MeasurableAdd ℤ_[p] := ContinuousAdd.measurableAdd
  let μ := normalizedAddHaar (padicQpUnitRegion p)
  let ν : Measure ℤ_[p] := Measure.comap
    (PadicInt.Coe.ringHom (p := p)).toAddMonoidHom μ
  let H : AddSubgroup ℤ_[p] := (maximalIdeal ℤ_[p]).toAddSubgroup
  letI : Finite (ℤ_[p] ⧸ H) :=
    Finite.of_injective (PadicInt.residueField (p := p))
      (PadicInt.residueField (p := p)).injective
  letI : H.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  haveI : ν.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.comap μ
      (mH := (ContinuousAdd.measurableAdd : MeasurableAdd ℚ_[p]))
      (f := (PadicInt.Coe.ringHom (p := p)).toAddMonoidHom)
      PadicInt.isOpenEmbedding_coe
  have hH : MeasurableSet (H : Set ℤ_[p]) :=
    (IsNoetherianRing.isClosed_ideal (maximalIdeal ℤ_[p])).measurableSet
  have h := MeasureTheory.AddSubgroup.index_mul_measure H hH ν
  have hindex : H.index = p := padicInt_maximalIdeal_index p
  have hf : MeasurableEmbedding
      ((PadicInt.Coe.ringHom (p := p)).toAddMonoidHom : ℤ_[p] → ℚ_[p]) :=
    @Topology.IsOpenEmbedding.measurableEmbedding (PadicInt p) (Padic p)
      _ mZ bZ _ mQ bQ _ PadicInt.isOpenEmbedding_coe
  rw [hindex] at h
  calc
    (p : ENNReal) * ν (maximalIdeal ℤ_[p] : Set ℤ_[p]) = ν Set.univ := h
    _ = μ (padicQpUnitRegion p).1 := by
      have hu := hf.comap_apply μ (Set.univ : Set ℤ_[p])
      change ν Set.univ = _
      rw [show ν Set.univ = μ
        ((PadicInt.Coe.ringHom (p := p)).toAddMonoidHom '' Set.univ) from hu]
      congr
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        simpa [padicQpUnitRegion, Metric.mem_closedBall] using y.2
      · intro hx
        have hx' : ‖x‖ ≤ 1 := by
          simpa [padicQpUnitRegion, Metric.mem_closedBall] using hx
        exact ⟨⟨x, hx'⟩, Set.mem_univ _, rfl⟩
    _ = 1 := normalizedAddHaar_anchor (padicQpUnitRegion p)

theorem normalizedQpHaar_padicPrime_unitBall
    (p : ℕ) [Fact p.Prime] :
    let _ : MeasurableSpace ℚ_[p] := borel ℚ_[p]
    let _ : BorelSpace ℚ_[p] := ⟨rfl⟩
    normalizedAddHaar (padicQpUnitRegion p)
        ((padicPrimeUnit p) • (padicQpUnitRegion p).1) =
      (p : ENNReal)⁻¹ := by
  letI mQ : MeasurableSpace ℚ_[p] := borel ℚ_[p]
  letI bQ : BorelSpace ℚ_[p] := ⟨rfl⟩
  letI mZ : MeasurableSpace ℤ_[p] := borel ℤ_[p]
  letI bZ : BorelSpace ℤ_[p] := ⟨rfl⟩
  letI : MeasurableAdd ℚ_[p] := ContinuousAdd.measurableAdd
  letI : MeasurableAdd ℤ_[p] := ContinuousAdd.measurableAdd
  let μ := normalizedAddHaar (padicQpUnitRegion p)
  let ν : Measure ℤ_[p] := Measure.comap
    (PadicInt.Coe.ringHom (p := p)).toAddMonoidHom μ
  have hmul := padicInt_comap_normalizedQpHaar_maximalIdeal_mul p
  have hf : MeasurableEmbedding
      ((PadicInt.Coe.ringHom (p := p)).toAddMonoidHom : ℤ_[p] → ℚ_[p]) :=
    @Topology.IsOpenEmbedding.measurableEmbedding (PadicInt p) (Padic p)
      _ mZ bZ _ mQ bQ _ PadicInt.isOpenEmbedding_coe
  have hcomap :
      ν (maximalIdeal ℤ_[p] : Set ℤ_[p]) =
        μ (((↑) : ℤ_[p] → ℚ_[p]) ''
          (maximalIdeal ℤ_[p] : Set ℤ_[p])) := by
    exact hf.comap_apply _ _
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [padicPrime_smul_unitBall_eq_image_maximalIdeal]
  rw [← hcomap]
  simpa [mul_comm] using hmul

theorem distribHaarChar_padicPrime
    (p : ℕ) [Fact p.Prime] :
    MeasureTheory.distribHaarChar ℚ_[p] (padicPrimeUnit p) =
      (p : NNReal)⁻¹ := by
  letI : MeasurableSpace ℚ_[p] := borel ℚ_[p]
  letI : BorelSpace ℚ_[p] := ⟨rfl⟩
  have hmul := MeasureTheory.distribHaarChar_mul
    (normalizedAddHaar (padicQpUnitRegion p))
    (padicPrimeUnit p) (padicQpUnitRegion p).1
  rw [normalizedAddHaar_anchor, normalizedQpHaar_padicPrime_unitBall] at hmul
  apply ENNReal.coe_injective
  simpa [ENNReal.coe_inv (show (p : NNReal) ≠ 0 by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)] using hmul

theorem realLog_distribHaarChar_padicPrime
    (p : ℕ) [Fact p.Prime] :
    Real.log
        (MeasureTheory.distribHaarChar ℚ_[p] (padicPrimeUnit p) : Real) =
      -Real.log (p : Real) := by
  rw [distribHaarChar_padicPrime]
  rw [NNReal.coe_inv]
  exact Real.log_inv (p : Real)

theorem normalizedQpHaarLogVolume_padicPrime_shift
    (p : ℕ) [Fact p.Prime] :
    let _ : MeasurableSpace ℚ_[p] := borel ℚ_[p]
    let _ : BorelSpace ℚ_[p] := ⟨rfl⟩
    normalizedHaarLogVolume (padicQpUnitRegion p)
        (localScalarHaarRegion (padicPrimeUnit p) (padicQpUnitRegion p)) =
      normalizedHaarLogVolume (padicQpUnitRegion p) (padicQpUnitRegion p) -
        Real.log (p : Real) := by
  letI : MeasurableSpace ℚ_[p] := borel ℚ_[p]
  letI : BorelSpace ℚ_[p] := ⟨rfl⟩
  change normalizedHaarLogVolume (padicQpUnitRegion p)
      (localScalarHaarRegion (padicPrimeUnit p) (padicQpUnitRegion p)) =
    normalizedHaarLogVolume (padicQpUnitRegion p) (padicQpUnitRegion p) -
      Real.log (p : Real)
  rw [normalizedHaarLogVolume_localScalarRegion]
  rw [realLog_distribHaarChar_padicPrime]
  ring

theorem normalizedQpHaarLogVolume_padicPrime_eq_neg_log
    (p : ℕ) [Fact p.Prime] :
    let _ : MeasurableSpace ℚ_[p] := borel ℚ_[p]
    let _ : BorelSpace ℚ_[p] := ⟨rfl⟩
    normalizedHaarLogVolume (padicQpUnitRegion p)
        (localScalarHaarRegion (padicPrimeUnit p) (padicQpUnitRegion p)) =
      -Real.log (p : Real) := by
  letI : MeasurableSpace ℚ_[p] := borel ℚ_[p]
  letI : BorelSpace ℚ_[p] := ⟨rfl⟩
  change normalizedHaarLogVolume (padicQpUnitRegion p)
      (localScalarHaarRegion (padicPrimeUnit p) (padicQpUnitRegion p)) =
    -Real.log (p : Real)
  rw [normalizedQpHaarLogVolume_padicPrime_shift]
  rw [normalizedHaarLogVolume_anchor]
  ring

theorem distribHaarChar_padicPrime_lt_one
    (p : ℕ) [Fact p.Prime] :
    MeasureTheory.distribHaarChar ℚ_[p] (padicPrimeUnit p) < 1 := by
  rw [distribHaarChar_padicPrime]
  exact inv_lt_one_of_one_lt₀ (by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt)

theorem distribHaarChar_padicPrime_ne_one
    (p : ℕ) [Fact p.Prime] :
    MeasureTheory.distribHaarChar ℚ_[p] (padicPrimeUnit p) ≠ 1 :=
  ne_of_lt (distribHaarChar_padicPrime_lt_one p)

theorem padicPrime_log_shift_ne_zero
    (p : ℕ) [Fact p.Prime] :
    -Real.log (p : Real) ≠ 0 := by
  have hp : (1 : Real) < p := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  exact neg_ne_zero.mpr (ne_of_gt (Real.log_pos hp))

theorem padicPrime_scaled_unitRegion_ne_anchor
    (p : ℕ) [Fact p.Prime] :
    let _ : MeasurableSpace ℚ_[p] := borel ℚ_[p]
    let _ : BorelSpace ℚ_[p] := ⟨rfl⟩
    localScalarHaarRegion (padicPrimeUnit p) (padicQpUnitRegion p) ≠
      padicQpUnitRegion p := by
  letI : MeasurableSpace ℚ_[p] := borel ℚ_[p]
  letI : BorelSpace ℚ_[p] := ⟨rfl⟩
  change localScalarHaarRegion (padicPrimeUnit p) (padicQpUnitRegion p) ≠
    padicQpUnitRegion p
  intro hregion
  have hlog := normalizedQpHaarLogVolume_padicPrime_eq_neg_log p
  dsimp only at hlog
  rw [hregion, normalizedHaarLogVolume_anchor] at hlog
  exact padicPrime_log_shift_ne_zero p hlog.symm

theorem padicPrime_scalar_action_is_not_noop
    (p : ℕ) [Fact p.Prime] :
    localScalarAddEquiv (padicPrimeUnit p) ≠
      ContinuousAddEquiv.refl ℚ_[p] := by
  intro h
  have hzero := congrArg (fun e : ℚ_[p] ≃ₜ+ ℚ_[p] => e 1) h
  have hpone : (p : ℚ_[p]) = 1 := by
    simpa [localScalarAddEquiv, padicPrimeUnit] using hzero
  have hpNat : p = 1 := by
    exact_mod_cast hpone
  exact (Fact.out : Nat.Prime p).ne_one hpNat

end CitedLV.Theorem311
