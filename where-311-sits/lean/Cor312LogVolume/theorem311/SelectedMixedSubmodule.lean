import Cor312LogVolume.theorem311.SourceSpanTensorPacket

namespace CitedLV.Theorem311

open scoped TensorProduct

universe uBase uAbove uLabel uK

abbrev SourceSpanChoiceTensor
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (choice : Fin (arity j + 1) -> Above vQ) :=
  PiTensorProduct ℚ (fun alpha : Fin (arity j + 1) =>
    P.rationalSpan
      { label := j, base := vQ, tensorFactor := alpha,
        directSummand := choice alpha })

abbrev SourceSpanChoiceDirectSum
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) :=
  DirectSum (Fin (arity j + 1) -> Above vQ)
    (fun choice => SourceSpanChoiceTensor P j vQ choice)

def selectedChoiceSupportSubmodule
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (alpha0 : Fin (arity j + 1)) (v0 : Above vQ) :
    Submodule ℚ (SourceSpanChoiceDirectSum P j vQ) where
  carrier := {z | forall choice, choice alpha0 ≠ v0 -> z choice = 0}
  zero_mem' := by intro choice hwrong; rfl
  add_mem' := by
    intro x y hx hy choice hwrong
    simp [hx choice hwrong, hy choice hwrong]
  smul_mem' := by
    intro c x hx choice hwrong
    change c • x choice = 0
    rw [hx choice hwrong, smul_zero]

noncomputable def selectedMixedSubmodule
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (alpha0 : Fin (arity j + 1)) (v0 : Above vQ) :
    Submodule ℚ (SourceSpanTensorPacketQ P j vQ) :=
  (selectedChoiceSupportSubmodule P j vQ alpha0 v0).comap
    (sourceSpanTensorDecomposition P j vQ).toLinearMap

def ChosenPureLands
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [DecidableEq (Above vQ)]
    (alpha0 : Fin (arity j + 1)) (v0 : Above vQ)
    (S : Submodule ℚ (SourceSpanTensorPacketQ P j vQ)) : Prop :=
  forall (choice : Fin (arity j + 1) -> Above vQ),
    choice alpha0 = v0 ->
    forall x : (alpha : Fin (arity j + 1)) ->
      P.rationalSpan
        { label := j, base := vQ, tensorFactor := alpha,
          directSummand := choice alpha },
      sourceSpanPurePacket P j vQ choice x ∈ S

def WrongNonzeroPureExcluded
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [DecidableEq (Above vQ)]
    (alpha0 : Fin (arity j + 1)) (v0 : Above vQ)
    (S : Submodule ℚ (SourceSpanTensorPacketQ P j vQ)) : Prop :=
  forall (choice : Fin (arity j + 1) -> Above vQ),
    choice alpha0 ≠ v0 ->
    forall x : (alpha : Fin (arity j + 1)) ->
      P.rationalSpan
        { label := j, base := vQ, tensorFactor := alpha,
          directSummand := choice alpha },
      PiTensorProduct.tprod ℚ x ≠ 0 ->
      sourceSpanPurePacket P j vQ choice x ∉ S

theorem selected_mixed_chosen_pure_lands
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [DecidableEq (Above vQ)]
    (alpha0 : Fin (arity j + 1)) (v0 : Above vQ) :
    ChosenPureLands P j vQ alpha0 v0
      (selectedMixedSubmodule P j vQ alpha0 v0) := by
  intro choice hselected x
  change sourceSpanTensorDecomposition P j vQ
      (sourceSpanPurePacket P j vQ choice x) ∈
    selectedChoiceSupportSubmodule P j vQ alpha0 v0
  rw [sourceSpanTensorDecomposition_maps_pure]
  intro other hwrong
  by_cases hEq : other = choice
  · subst other
    exact (hwrong hselected).elim
  · rw [DirectSum.lof_eq_of]
    exact DFinsupp.single_eq_of_ne hEq

theorem selected_mixed_wrong_nonzero_pure_excluded
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [DecidableEq (Above vQ)]
    (alpha0 : Fin (arity j + 1)) (v0 : Above vQ) :
    WrongNonzeroPureExcluded P j vQ alpha0 v0
      (selectedMixedSubmodule P j vQ alpha0 v0) := by
  intro choice hwrong x hnonzero hmem
  change sourceSpanTensorDecomposition P j vQ
      (sourceSpanPurePacket P j vQ choice x) ∈
    selectedChoiceSupportSubmodule P j vQ alpha0 v0 at hmem
  have hzero := hmem choice hwrong
  rw [sourceSpanTensorDecomposition_maps_pure] at hzero
  apply hnonzero
  simpa using hzero

theorem sourceSpanPurePacket_ne_zero_of_choiceTensor_ne_zero
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [DecidableEq (Above vQ)]
    (choice : Fin (arity j + 1) -> Above vQ)
    (x : (alpha : Fin (arity j + 1)) ->
      P.rationalSpan
        { label := j, base := vQ, tensorFactor := alpha,
          directSummand := choice alpha })
    (hnonzero : PiTensorProduct.tprod ℚ x ≠ 0) :
    sourceSpanPurePacket P j vQ choice x ≠ 0 := by
  intro hpure
  have hmapped := congrArg
    (sourceSpanTensorDecomposition P j vQ) hpure
  rw [sourceSpanTensorDecomposition_maps_pure] at hmapped
  have hlof :
      DirectSum.lof ℚ (Fin (arity j + 1) -> Above vQ)
        (fun selected => SourceSpanChoiceTensor P j vQ selected)
        choice (PiTensorProduct.tprod ℚ x) = 0 := by
    simpa using hmapped
  apply hnonzero
  have hsingle := hlof
  change DFinsupp.single
      (β := fun selected => SourceSpanChoiceTensor P j vQ selected)
      choice (PiTensorProduct.tprod ℚ x) = 0 at hsingle
  exact DFinsupp.single_eq_zero.mp hsingle

theorem top_chosen_pure_lands
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [DecidableEq (Above vQ)]
    (alpha0 : Fin (arity j + 1)) (v0 : Above vQ) :
    ChosenPureLands P j vQ alpha0 v0 ⊤ := by
  intro choice hchoice x
  simp

theorem bottom_wrong_nonzero_pure_excluded
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [DecidableEq (Above vQ)]
    (alpha0 : Fin (arity j + 1)) (v0 : Above vQ) :
    WrongNonzeroPureExcluded P j vQ alpha0 v0 ⊥ := by
  intro choice hwrong x hinner hpure
  have hpureZero : sourceSpanPurePacket P j vQ choice x = 0 := by
    simpa only [Submodule.mem_bot] using hpure
  exact (sourceSpanPurePacket_ne_zero_of_choiceTensor_ne_zero
    P j vQ choice x hinner) hpureZero

def boolPlaceSourceSpan :
    SourceShapedLocalMonoanalyticQSpanRaw Unit (fun _ => Bool)
      Unit unitArity ℚ where
  integral := fun _ => {1}
  rationalSpan := fun _ => ⊤

theorem bool_place_span_correct :
    RationalSpanCorrect boolPlaceSourceSpan := by
  intro i
  simp [boolPlaceSourceSpan]

abbrev boolPlaceChoice (v : Bool) : Fin 1 -> Bool := fun _ => v

def boolPlaceFiberOne (alpha : Fin 1) (v : Bool) :
    boolPlaceSourceSpan.rationalSpan
      { label := (), base := (), tensorFactor := alpha,
        directSummand := v } :=
  ⟨1, by simp [boolPlaceSourceSpan]⟩

theorem bool_place_fiber_one_ne_zero (alpha : Fin 1) (v : Bool) :
    boolPlaceFiberOne alpha v ≠ 0 := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [boolPlaceFiberOne] at hv

noncomputable def boolPlaceChoiceTensor (v : Bool) :
    SourceSpanChoiceTensor boolPlaceSourceSpan () ()
      (boolPlaceChoice v) :=
  PiTensorProduct.tprod ℚ (fun alpha => boolPlaceFiberOne alpha v)

theorem bool_place_choice_tensor_ne_zero (v : Bool) :
    boolPlaceChoiceTensor v ≠ 0 := by
  intro h
  let e := PiTensorProduct.subsingletonEquiv
      (R := ℚ)
      (s := fun alpha : Fin 1 =>
        boolPlaceSourceSpan.rationalSpan
          { label := (), base := (), tensorFactor := alpha,
            directSummand := v })
      (0 : Fin 1)
  have hmapped := congrArg e h
  apply bool_place_fiber_one_ne_zero 0 v
  simpa [e, boolPlaceChoiceTensor] using hmapped

noncomputable def boolPlacePurePacket (v : Bool) :
    SourceSpanTensorPacketQ boolPlaceSourceSpan () () :=
  sourceSpanPurePacket boolPlaceSourceSpan () ()
    (boolPlaceChoice v) (fun alpha => boolPlaceFiberOne alpha v)

theorem bool_place_pure_packet_ne_zero (v : Bool) :
    boolPlacePurePacket v ≠ 0 :=
  sourceSpanPurePacket_ne_zero_of_choiceTensor_ne_zero
    boolPlaceSourceSpan () () (boolPlaceChoice v)
      (fun alpha => boolPlaceFiberOne alpha v)
      (bool_place_choice_tensor_ne_zero v)

theorem top_fails_wrong_nonzero_pure_excluded :
    ¬ WrongNonzeroPureExcluded boolPlaceSourceSpan () () 0 false ⊤ := by
  intro h
  have hnot := h (boolPlaceChoice true)
    (by simp [boolPlaceChoice])
    (fun alpha => boolPlaceFiberOne alpha true)
    (bool_place_choice_tensor_ne_zero true)
  apply hnot
  simp

theorem bottom_fails_chosen_pure_lands :
    ¬ ChosenPureLands boolPlaceSourceSpan () () 0 false ⊥ := by
  intro h
  have hmem := h (boolPlaceChoice false)
    (by simp [boolPlaceChoice])
    (fun alpha => boolPlaceFiberOne alpha false)
  have hzero : boolPlacePurePacket false = 0 := by
    simpa only [Submodule.mem_bot] using hmem
  exact bool_place_pure_packet_ne_zero false hzero

theorem selected_mixed_conditions_are_not_baked_in :
    ChosenPureLands boolPlaceSourceSpan () () 0 false
        (selectedMixedSubmodule boolPlaceSourceSpan () () 0 false) /\
      WrongNonzeroPureExcluded boolPlaceSourceSpan () () 0 false
        (selectedMixedSubmodule boolPlaceSourceSpan () () 0 false) /\
      ChosenPureLands boolPlaceSourceSpan () () 0 false ⊤ /\
      ¬ WrongNonzeroPureExcluded boolPlaceSourceSpan () () 0 false ⊤ /\
      WrongNonzeroPureExcluded boolPlaceSourceSpan () () 0 false ⊥ /\
      ¬ ChosenPureLands boolPlaceSourceSpan () () 0 false ⊥ :=
  ⟨selected_mixed_chosen_pure_lands _ _ _ _ _,
    selected_mixed_wrong_nonzero_pure_excluded _ _ _ _ _,
    top_chosen_pure_lands _ _ _ _ _,
    top_fails_wrong_nonzero_pure_excluded,
    bottom_wrong_nonzero_pure_excluded _ _ _ _ _,
    bottom_fails_chosen_pure_lands⟩

end CitedLV.Theorem311
