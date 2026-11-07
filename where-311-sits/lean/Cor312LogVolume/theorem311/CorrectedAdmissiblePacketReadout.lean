import Cor312LogVolume.theorem311.CompatibleTwoOrbitPacketChain

namespace CitedLV.Theorem311

universe uX uY

noncomputable def correctAdmissibleSourceReadout
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    {kind : PacketPlaceKind}
    {H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY}
    (rawSource : HeterogeneousSourceAdmissibleReadout kind H)
    (correction : Fin n -> Real) :
    HeterogeneousSourceAdmissibleReadout kind H :=
  fun j R => rawSource j R + correction j

def AdmissibleAnchorCorrectionCalibrated
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (rawSource : HeterogeneousSourceAdmissibleReadout kind H)
    (targetReadout : HeterogeneousTargetAdmissibleReadout kind H)
    (anchor : HeterogeneousSourceAdmissibleProfile kind H)
    (correction : Fin n -> Real) : Prop :=
  ∀ j,
    rawSource j (anchor j) + correction j =
      targetReadout j
        (transportHeterogeneousAdmissibleRegion kind H j (anchor j))

def RelativeAdmissibleReadoutCompatible
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (rawSource : HeterogeneousSourceAdmissibleReadout kind H)
    (targetReadout : HeterogeneousTargetAdmissibleReadout kind H)
    (anchor : HeterogeneousSourceAdmissibleProfile kind H) : Prop :=
  ∀ j R,
    targetReadout j (transportHeterogeneousAdmissibleRegion kind H j R) -
        targetReadout j
          (transportHeterogeneousAdmissibleRegion kind H j (anchor j)) =
      rawSource j R - rawSource j (anchor j)

theorem anchor_and_relative_laws_give_corrected_compatibility
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (rawSource : HeterogeneousSourceAdmissibleReadout kind H)
    (targetReadout : HeterogeneousTargetAdmissibleReadout kind H)
    (anchor : HeterogeneousSourceAdmissibleProfile kind H)
    (correction : Fin n -> Real)
    (hanchor : AdmissibleAnchorCorrectionCalibrated kind H rawSource
      targetReadout anchor correction)
    (hrelative : RelativeAdmissibleReadoutCompatible kind H rawSource
      targetReadout anchor) :
    HeterogeneousAdmissibleReadoutCompatible kind H
      (correctAdmissibleSourceReadout rawSource correction) targetReadout := by
  intro j R
  unfold correctAdmissibleSourceReadout
  have hcal := hanchor j
  have hrel := hrelative j R
  linarith

theorem anchor_and_relative_laws_give_corrected_mean_equality
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (rawSource : HeterogeneousSourceAdmissibleReadout kind H)
    (targetReadout : HeterogeneousTargetAdmissibleReadout kind H)
    (anchor : HeterogeneousSourceAdmissibleProfile kind H)
    (correction : Fin n -> Real)
    (hanchor : AdmissibleAnchorCorrectionCalibrated kind H rawSource
      targetReadout anchor correction)
    (hrelative : RelativeAdmissibleReadoutCompatible kind H rawSource
      targetReadout anchor)
    (profile : HeterogeneousSourceAdmissibleProfile kind H) :
    heterogeneousTargetNormalizedMean targetReadout
        (transportHeterogeneousAdmissibleProfile kind H profile) =
      heterogeneousSourceNormalizedMean
        (correctAdmissibleSourceReadout rawSource correction) profile :=
  heterogeneous_compatible_normalized_means kind H
    (correctAdmissibleSourceReadout rawSource correction) targetReadout
      (anchor_and_relative_laws_give_corrected_compatibility kind H rawSource
        targetReadout anchor correction hanchor hrelative) profile

noncomputable def nonarchLogUnitImageLogVolume
    (p e f m : Nat) : Real :=
  -((1 / (e : Real)) + (m : Real) / ((e : Real) * (f : Real))) *
    Real.log (p : Real)

noncomputable def nonarchMonoIntegralLogVolume
    (p s e f m : Nat) : Real :=
  ((s : Real) - (1 / (e : Real)) -
      (m : Real) / ((e : Real) * (f : Real))) * Real.log (p : Real)

theorem nonarch_mono_integral_is_scaled_log_unit_image
    (p s e f m : Nat) :
    nonarchMonoIntegralLogVolume p s e f m =
      nonarchLogUnitImageLogVolume p e f m +
        (s : Real) * Real.log (p : Real) := by
  unfold nonarchMonoIntegralLogVolume nonarchLogUnitImageLogVolume
  ring

noncomputable def nonarchMonoIntegralAnchorCorrection
    (p s e f m : Nat) : Real :=
  -nonarchMonoIntegralLogVolume p s e f m

theorem nonarch_single_factor_correction_calibrates_zero
    (p s e f m : Nat) :
    nonarchMonoIntegralLogVolume p s e f m +
      nonarchMonoIntegralAnchorCorrection p s e f m = 0 := by
  unfold nonarchMonoIntegralAnchorCorrection
  ring

theorem bool_false_singleton_ne_univ :
    ({false} : Set Bool) ≠ Set.univ := by
  intro h
  have : true ∈ ({false} : Set Bool) := by rw [h]; trivial
  simp at this

theorem bool_fin_two_singleton_image_ne_univ (j : Fin 2) :
    boolFinTwoTopologicalTransport.packetHomeomorph j ''
        ({false} : Set Bool) ≠ Set.univ := by
  intro h
  exact bool_false_singleton_ne_univ
    ((heterogeneous_equiv_image_eq_univ_iff
      (boolFinTwoTopologicalTransport.packetHomeomorph j).toEquiv
        ({false} : Set Bool)).mp h)

theorem bool_fin_two_univ_image_eq_univ (j : Fin 2) :
    boolFinTwoTopologicalTransport.packetHomeomorph j ''
        (Set.univ : Set Bool) = Set.univ :=
  (heterogeneous_equiv_image_eq_univ_iff
    (boolFinTwoTopologicalTransport.packetHomeomorph j).toEquiv
      (Set.univ : Set Bool)).mpr rfl

noncomputable def shiftedBoolSourceReadout :
    HeterogeneousSourceAdmissibleReadout .nonarch
      boolFinTwoTopologicalTransport := by
  classical
  exact fun _ R => if R.1 = Set.univ then -2 else -4

noncomputable def shiftedFinTwoTargetReadout :
    HeterogeneousTargetAdmissibleReadout .nonarch
      boolFinTwoTopologicalTransport := by
  classical
  exact fun _ R => if R.1 = Set.univ then 3 else 1

def shiftedReadoutCorrection : Fin 2 -> Real :=
  fun _ => 5

theorem shifted_source_readout_nonconstant :
    shiftedBoolSourceReadout 0 (boolSingletonSourceRegion 0) ≠
      shiftedBoolSourceReadout 0 (boolUnivSourceRegion 0) := by
  unfold shiftedBoolSourceReadout
  dsimp [boolSingletonSourceRegion, boolUnivSourceRegion]
  rw [if_neg bool_false_singleton_ne_univ, if_pos rfl]
  norm_num

theorem shifted_anchor_calibrated :
    AdmissibleAnchorCorrectionCalibrated .nonarch
      boolFinTwoTopologicalTransport shiftedBoolSourceReadout
        shiftedFinTwoTargetReadout boolSingletonSourceProfile
          shiftedReadoutCorrection := by
  intro j
  unfold shiftedBoolSourceReadout shiftedFinTwoTargetReadout
  dsimp [
    shiftedReadoutCorrection, boolSingletonSourceProfile,
    boolSingletonSourceRegion, transportHeterogeneousAdmissibleRegion]
  rw [if_neg bool_false_singleton_ne_univ,
    if_neg (bool_fin_two_singleton_image_ne_univ j)]
  norm_num

theorem shifted_relative_readouts_compatible :
    RelativeAdmissibleReadoutCompatible .nonarch
      boolFinTwoTopologicalTransport shiftedBoolSourceReadout
        shiftedFinTwoTargetReadout boolSingletonSourceProfile := by
  classical
  intro j R
  have himage := heterogeneous_equiv_image_eq_univ_iff
    (boolFinTwoTopologicalTransport.packetHomeomorph j).toEquiv R.1
  have htargetAnchor := bool_fin_two_singleton_image_ne_univ j
  by_cases hR : R.1 = Set.univ
  · have hRI : boolFinTwoTopologicalTransport.packetHomeomorph j '' R.1 =
        Set.univ := himage.mpr hR
    unfold shiftedBoolSourceReadout shiftedFinTwoTargetReadout
    dsimp [
      boolSingletonSourceProfile, boolSingletonSourceRegion,
      transportHeterogeneousAdmissibleRegion]
    rw [if_pos hRI, if_neg htargetAnchor, if_pos hR,
      if_neg bool_false_singleton_ne_univ]
    norm_num
  · have hRI : boolFinTwoTopologicalTransport.packetHomeomorph j '' R.1 ≠
        Set.univ := fun h => hR (himage.mp h)
    unfold shiftedBoolSourceReadout shiftedFinTwoTargetReadout
    dsimp [
      boolSingletonSourceProfile, boolSingletonSourceRegion,
      transportHeterogeneousAdmissibleRegion]
    rw [if_neg hRI, if_neg htargetAnchor, if_neg hR,
      if_neg bool_false_singleton_ne_univ]
    norm_num

theorem shifted_readouts_correct_to_full_compatibility :
    HeterogeneousAdmissibleReadoutCompatible .nonarch
      boolFinTwoTopologicalTransport
        (correctAdmissibleSourceReadout shiftedBoolSourceReadout
          shiftedReadoutCorrection)
        shiftedFinTwoTargetReadout :=
  anchor_and_relative_laws_give_corrected_compatibility .nonarch
    boolFinTwoTopologicalTransport shiftedBoolSourceReadout
      shiftedFinTwoTargetReadout boolSingletonSourceProfile
        shiftedReadoutCorrection shifted_anchor_calibrated
          shifted_relative_readouts_compatible

noncomputable def variableGapBoolSourceReadout :
    HeterogeneousSourceAdmissibleReadout .nonarch
      boolFinTwoTopologicalTransport := by
  classical
  exact fun _ R => if R.1 = Set.univ then 2 else 1

noncomputable def variableGapFinTwoTargetReadout :
    HeterogeneousTargetAdmissibleReadout .nonarch
      boolFinTwoTopologicalTransport := by
  classical
  exact fun _ R => if R.1 = Set.univ then 7 else 3

def variableGapAnchorCorrection : Fin 2 -> Real :=
  fun _ => 2

theorem variable_gap_anchor_is_calibrated :
    AdmissibleAnchorCorrectionCalibrated .nonarch
      boolFinTwoTopologicalTransport variableGapBoolSourceReadout
        variableGapFinTwoTargetReadout boolSingletonSourceProfile
          variableGapAnchorCorrection := by
  intro j
  unfold variableGapBoolSourceReadout variableGapFinTwoTargetReadout
  dsimp [variableGapAnchorCorrection, boolSingletonSourceProfile,
    boolSingletonSourceRegion, transportHeterogeneousAdmissibleRegion]
  rw [if_neg bool_false_singleton_ne_univ,
    if_neg (bool_fin_two_singleton_image_ne_univ j)]
  norm_num

theorem variable_gap_has_no_stagewise_additive_correction :
    ¬ ∃ correction : Fin 2 -> Real,
      HeterogeneousAdmissibleReadoutCompatible .nonarch
        boolFinTwoTopologicalTransport
          (correctAdmissibleSourceReadout variableGapBoolSourceReadout
            correction)
          variableGapFinTwoTargetReadout := by
  rintro ⟨correction, hcompat⟩
  have hsingle := hcompat 0 (boolSingletonSourceRegion 0)
  have huniv := hcompat 0 (boolUnivSourceRegion 0)
  unfold correctAdmissibleSourceReadout variableGapBoolSourceReadout
    variableGapFinTwoTargetReadout at hsingle huniv
  dsimp [boolSingletonSourceRegion,
    transportHeterogeneousAdmissibleRegion] at hsingle
  rw [if_neg bool_false_singleton_ne_univ,
    if_neg (bool_fin_two_singleton_image_ne_univ 0)] at hsingle
  dsimp [boolUnivSourceRegion,
    transportHeterogeneousAdmissibleRegion] at huniv
  simp only [if_pos (bool_fin_two_univ_image_eq_univ 0)] at huniv
  have hsingle' : 3 = 1 + correction 0 := by exact_mod_cast hsingle
  have huniv' : 7 = 2 + correction 0 := by exact_mod_cast huniv
  linarith

theorem variable_gap_relative_law_fails :
    ¬ RelativeAdmissibleReadoutCompatible .nonarch
      boolFinTwoTopologicalTransport variableGapBoolSourceReadout
        variableGapFinTwoTargetReadout boolSingletonSourceProfile := by
  intro hrelative
  apply variable_gap_has_no_stagewise_additive_correction
  exact ⟨variableGapAnchorCorrection,
    anchor_and_relative_laws_give_corrected_compatibility .nonarch
      boolFinTwoTopologicalTransport variableGapBoolSourceReadout
        variableGapFinTwoTargetReadout boolSingletonSourceProfile
          variableGapAnchorCorrection variable_gap_anchor_is_calibrated
            hrelative⟩

end CitedLV.Theorem311
