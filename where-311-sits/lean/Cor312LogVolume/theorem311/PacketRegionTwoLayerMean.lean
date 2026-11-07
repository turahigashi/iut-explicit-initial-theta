import Cor312LogVolume.theorem311.PacketChoiceDegreeTransport
import Cor312LogVolume.theorem311.ProcessionNormalizedLogVolume

namespace CitedLV.Theorem311

open scoped BigOperators TensorProduct

universe uBase uAbove uDegreeBase uLabel uK uPacket

noncomputable def decompositionChoiceRegion
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (region : Set (SourceSpanTensorPacketQ P j vQ))
    (choice : SourcePacketChoice Above arity j vQ) :
    Set (SourceSpanChoiceTensor P j vQ choice) :=
  (fun z => (sourceSpanTensorDecomposition P j vQ z) choice) '' region

theorem decomposition_choice_region_empty
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (choice : SourcePacketChoice Above arity j vQ) :
    decompositionChoiceRegion P j vQ ∅ choice = ∅ := by
  simp [decompositionChoiceRegion]

theorem decomposition_choice_region_singleton
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (z : SourceSpanTensorPacketQ P j vQ)
    (choice : SourcePacketChoice Above arity j vQ) :
    decompositionChoiceRegion P j vQ {z} choice =
      {(sourceSpanTensorDecomposition P j vQ z) choice} := by
  simp [decompositionChoiceRegion]

theorem different_components_give_different_singleton_regions
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (z₁ z₂ : SourceSpanTensorPacketQ P j vQ)
    (choice : SourcePacketChoice Above arity j vQ)
    (hcomponent :
      (sourceSpanTensorDecomposition P j vQ z₁) choice ≠
        (sourceSpanTensorDecomposition P j vQ z₂) choice) :
    decompositionChoiceRegion P j vQ {z₁} choice ≠
      decompositionChoiceRegion P j vQ {z₂} choice := by
  simpa [decompositionChoiceRegion] using hcomponent

theorem zero_visible_decomposition_choice_profile :
    decompositionChoiceProfile visibleUnitSourceSpan () () 0
      unitChoiceTensorScalar unitPacketChoice = 0 := by
  norm_num [decompositionChoiceProfile, unitChoiceTensorScalar,
    unitPacketChoice]

theorem visible_pure_and_zero_components_differ :
    (sourceSpanTensorDecomposition visibleUnitSourceSpan () ()
        visibleUnitPurePacket) unitPacketChoice ≠
      (sourceSpanTensorDecomposition visibleUnitSourceSpan () () 0)
        unitPacketChoice := by
  intro h
  have hvalue := congrArg (unitChoiceTensorScalar unitPacketChoice) h
  have hpure := visible_decomposition_choice_profile_is_one
  unfold decompositionChoiceProfile at hpure
  have hzero := zero_visible_decomposition_choice_profile
  unfold decompositionChoiceProfile at hzero
  rw [hpure, hzero] at hvalue
  norm_num at hvalue

theorem visible_pure_and_zero_singleton_regions_differ :
    decompositionChoiceRegion visibleUnitSourceSpan () ()
        {visibleUnitPurePacket} unitPacketChoice ≠
      decompositionChoiceRegion visibleUnitSourceSpan () ()
        {0} unitPacketChoice :=
  different_components_give_different_singleton_regions
    visibleUnitSourceSpan () () visibleUnitPurePacket 0 unitPacketChoice
    visible_pure_and_zero_components_differ

noncomputable def sourceSpanRegionDegreeWeightedMean
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [Fintype (Above vQ)]
    (region : Set (SourceSpanTensorPacketQ P j vQ))
    (degree : Above vQ -> Real)
    (componentLogVolume :
      (choice : SourcePacketChoice Above arity j vQ) ->
      Set (SourceSpanChoiceTensor P j vQ choice) -> Real) : Real :=
  fullChoiceNormalizedMean (arity j + 1) degree
    (fun choice => componentLogVolume choice
      (decompositionChoiceRegion P j vQ region choice))

noncomputable def sourceSpanBaseIndexedRegionDegreeWeightedMean
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {DegreeBase : Type uDegreeBase}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [Fintype (Above vQ)] [Fintype DegreeBase]
    (D : RawPacketDegreeData (Above vQ) DegreeBase)
    (T : LiftBaseTransportCandidate D)
    (region : Set (SourceSpanTensorPacketQ P j vQ))
    (componentLogVolume :
      (choice : SourcePacketChoice Above arity j vQ) ->
      Set (SourceSpanChoiceTensor P j vQ choice) -> Real) : Real :=
  fullChoiceNormalizedMean (arity j + 1) D.baseDegree
    (pushChoiceProfileToBase T (arity j + 1)
      (fun choice => componentLogVolume choice
        (decompositionChoiceRegion P j vQ region choice)))

theorem sourceSpan_region_mean_reindexes_to_base
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {DegreeBase : Type uDegreeBase}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [Fintype (Above vQ)] [Fintype DegreeBase]
    (D : RawPacketDegreeData (Above vQ) DegreeBase)
    (T : LiftBaseTransportCandidate D)
    (region : Set (SourceSpanTensorPacketQ P j vQ))
    (componentLogVolume :
      (choice : SourcePacketChoice Above arity j vQ) ->
      Set (SourceSpanChoiceTensor P j vQ choice) -> Real) :
    sourceSpanRegionDegreeWeightedMean P j vQ region
        (transportedBaseDegree T) componentLogVolume =
      sourceSpanBaseIndexedRegionDegreeWeightedMean P j vQ D T
        region componentLogVolume := by
  exact full_choice_normalized_mean_transport T (arity j + 1)
    (fun choice => componentLogVolume choice
      (decompositionChoiceRegion P j vQ region choice))

noncomputable def sourceProcessionChoiceWeightedLogVolumeRaw
    {Strip : Type uLabel} {n : Nat}
    (Prc : DPrimeStripProcessionCandidate Strip (n + 1))
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {DegreeBase : Type uDegreeBase}
    {arity : Strip -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (Q : SourceShapedLocalMonoanalyticQSpanRaw Base Above Strip arity K)
    (vQ : Base) [Fintype (Above vQ)] [Fintype DegreeBase]
    (D : RawPacketDegreeData (Above vQ) DegreeBase)
    (T : LiftBaseTransportCandidate D)
    (region : (j : Fin n) -> Set (SourceProcessionPacketQ Prc Q vQ j))
    (componentLogVolume :
      (j : Fin n) ->
      (choice : SourcePacketChoice Above arity
        (finalNonzeroProcessionLabel Prc j) vQ) ->
      Set (SourceSpanChoiceTensor Q
        (finalNonzeroProcessionLabel Prc j) vQ choice) -> Real) :
    ProcessionPacketLogVolumeRaw (SourceProcessionPacketQ Prc Q vQ) :=
  sourceProcessionPacketLogVolumeRaw Prc Q vQ region
    (fun j S => sourceSpanRegionDegreeWeightedMean Q
      (finalNonzeroProcessionLabel Prc j) vQ S
      (transportedBaseDegree T) (componentLogVolume j))

noncomputable def sourceProcessionTwoLayerDegreeMean
    {Strip : Type uLabel} {n : Nat}
    (Prc : DPrimeStripProcessionCandidate Strip (n + 1))
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {DegreeBase : Type uDegreeBase}
    {arity : Strip -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (Q : SourceShapedLocalMonoanalyticQSpanRaw Base Above Strip arity K)
    (vQ : Base) [Fintype (Above vQ)] [Fintype DegreeBase]
    (D : RawPacketDegreeData (Above vQ) DegreeBase)
    (T : LiftBaseTransportCandidate D)
    (region : (j : Fin n) -> Set (SourceProcessionPacketQ Prc Q vQ j))
    (componentLogVolume :
      (j : Fin n) ->
      (choice : SourcePacketChoice Above arity
        (finalNonzeroProcessionLabel Prc j) vQ) ->
      Set (SourceSpanChoiceTensor Q
        (finalNonzeroProcessionLabel Prc j) vQ choice) -> Real) : Real :=
  processionNormalizedLogVolume
    (sourceProcessionChoiceWeightedLogVolumeRaw Prc Q vQ D T
      region componentLogVolume)

theorem source_procession_two_layer_is_one_composition
    {Strip : Type uLabel} {n : Nat}
    (Prc : DPrimeStripProcessionCandidate Strip (n + 1))
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {DegreeBase : Type uDegreeBase}
    {arity : Strip -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (Q : SourceShapedLocalMonoanalyticQSpanRaw Base Above Strip arity K)
    (vQ : Base) [Fintype (Above vQ)] [Fintype DegreeBase]
    (D : RawPacketDegreeData (Above vQ) DegreeBase)
    (T : LiftBaseTransportCandidate D)
    (region : (j : Fin n) -> Set (SourceProcessionPacketQ Prc Q vQ j))
    (componentLogVolume :
      (j : Fin n) ->
      (choice : SourcePacketChoice Above arity
        (finalNonzeroProcessionLabel Prc j) vQ) ->
      Set (SourceSpanChoiceTensor Q
        (finalNonzeroProcessionLabel Prc j) vQ choice) -> Real) :
    sourceProcessionTwoLayerDegreeMean Prc Q vQ D T
        region componentLogVolume =
      ordinaryFinMean (fun j =>
        fullChoiceNormalizedMean
          (arity (finalNonzeroProcessionLabel Prc j) + 1)
          (transportedBaseDegree T)
          (fun choice => componentLogVolume j choice
            (decompositionChoiceRegion Q
              (finalNonzeroProcessionLabel Prc j) vQ
              (region j) choice))) := by
  rfl

noncomputable def nestedFiniteChoiceMean
    {n : Nat} (Choice : Fin n -> Type uPacket)
    [finiteChoice : forall j, Fintype (Choice j)]
    (weight : (j : Fin n) -> Choice j -> Real)
    (profile : (j : Fin n) -> Choice j -> Real) : Real :=
  ordinaryFinMean (fun j =>
    (∑ c : Choice j, weight j c * profile j c) /
      (∑ c : Choice j, weight j c))

noncomputable def stageMassFlattenedMean
    {n : Nat} (stageMass stageValue : Fin n -> Real) : Real :=
  (∑ j, stageMass j * stageValue j) / (∑ j, stageMass j)

def cardinalityCheckStageValue (j : Fin 2) : Real :=
  if j = 0 then 0 else 3

def cardinalityCheckStageMass (j : Fin 2) : Real :=
  if j = 0 then 1 else 3

theorem equal_outer_mean_ignores_inner_choice_cardinality :
    ordinaryFinMean cardinalityCheckStageValue = 3 / 2 := by
  norm_num [ordinaryFinMean, cardinalityCheckStageValue, Fin.sum_univ_two]

theorem flattened_mean_biases_by_inner_choice_cardinality :
    stageMassFlattenedMean cardinalityCheckStageMass
      cardinalityCheckStageValue = 9 / 4 := by
  norm_num [stageMassFlattenedMean, cardinalityCheckStageMass,
    cardinalityCheckStageValue, Fin.sum_univ_two]

theorem nested_and_flattened_means_are_distinct :
    ordinaryFinMean cardinalityCheckStageValue ≠
      stageMassFlattenedMean cardinalityCheckStageMass
        cardinalityCheckStageValue := by
  rw [equal_outer_mean_ignores_inner_choice_cardinality,
    flattened_mean_biases_by_inner_choice_cardinality]
  norm_num

def ComponentRegionReadoutSensitive
    {C : Type uPacket} (readout : Set C -> Real) : Prop :=
  exists S T, readout S ≠ readout T

noncomputable def containsTrueRegionReadout (S : Set Bool) : Real :=
  by
    classical
    exact if true ∈ S then 1 else 0

def hardCodedComponentRegionReadout (_S : Set Bool) : Real := 1

theorem contains_true_region_readout_is_sensitive :
    ComponentRegionReadoutSensitive containsTrueRegionReadout := by
  refine ⟨∅, {true}, ?_⟩
  norm_num [containsTrueRegionReadout]

theorem hard_coded_component_region_readout_is_not_sensitive :
    ¬ ComponentRegionReadoutSensitive hardCodedComponentRegionReadout := by
  rintro ⟨S, T, h⟩
  exact h rfl

theorem zero_stage_nested_mean_collapses
    (Choice : Fin 0 -> Type uPacket)
    [forall j, Fintype (Choice j)]
    (weight : (j : Fin 0) -> Choice j -> Real)
    (profile : (j : Fin 0) -> Choice j -> Real) :
    nestedFiniteChoiceMean Choice weight profile = 0 := by
  simp [nestedFiniteChoiceMean, ordinaryFinMean]

theorem empty_inner_choice_mean_collapses
    (weight profile : Fin 0 -> Real) :
    ((∑ c : Fin 0, weight c * profile c) /
      (∑ c : Fin 0, weight c)) = 0 := by
  simp

end CitedLV.Theorem311
