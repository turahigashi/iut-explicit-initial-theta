import Cor312LogVolume.theorem311.IndeterminacyQuotientTransport
import Cor312LogVolume.theorem311.SourceSpanTensorPacket

namespace CitedLV.Theorem311

open scoped TensorProduct

universe uBase uAbove uLabel uK uAllowed

structure SourceSpanInd2Realization
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) where
  Allowed : (alpha : Fin (arity j + 1)) -> Above vQ -> Type uAllowed
  fiberEquiv : (alpha : Fin (arity j + 1)) -> (v : Above vQ) ->
    Allowed alpha v ->
      P.rationalSpan
          { label := j, base := vQ, tensorFactor := alpha,
            directSummand := v } ≃ₗ[ℚ]
        P.rationalSpan
          { label := j, base := vQ, tensorFactor := alpha,
            directSummand := v }

abbrev SourceSpanInd2Choice
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    {P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K}
    {j : Label} {vQ : Base}
    (R : SourceSpanInd2Realization.{uBase, uAbove, uLabel, uK, uAllowed}
      P j vQ) :=
  (alpha : Fin (arity j + 1)) -> (v : Above vQ) -> R.Allowed alpha v

noncomputable def sourceSpanInd2PacketEquiv
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (R : SourceSpanInd2Realization.{uBase, uAbove, uLabel, uK, uAllowed}
      P j vQ)
    (a : SourceSpanInd2Choice R) :
    SourceSpanTensorPacketQ P j vQ ≃ₗ[ℚ] SourceSpanTensorPacketQ P j vQ :=
  PiTensorProduct.congr (fun alpha =>
    DirectSum.congrLinearEquiv (fun v => R.fiberEquiv alpha v (a alpha v)))

theorem sourceSpanInd2PacketEquiv_maps_pure
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [DecidableEq (Above vQ)]
    (R : SourceSpanInd2Realization.{uBase, uAbove, uLabel, uK, uAllowed}
      P j vQ)
    (a : SourceSpanInd2Choice R)
    (choice : Fin (arity j + 1) -> Above vQ)
    (x : (alpha : Fin (arity j + 1)) ->
      P.rationalSpan
        { label := j, base := vQ, tensorFactor := alpha,
          directSummand := choice alpha }) :
    sourceSpanInd2PacketEquiv P j vQ R a
        (sourceSpanPurePacket P j vQ choice x) =
      sourceSpanPurePacket P j vQ choice
        (fun alpha => R.fiberEquiv alpha (choice alpha)
          (a alpha (choice alpha)) (x alpha)) := by
  simp [sourceSpanInd2PacketEquiv, sourceSpanPurePacket,
    DirectSum.coe_congrLinearEquiv]

def sourceSpanInd2Step
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (R : SourceSpanInd2Realization.{uBase, uAbove, uLabel, uK, uAllowed}
      P j vQ)
    (x y : SourceSpanTensorPacketQ P j vQ) : Prop :=
  exists a : SourceSpanInd2Choice R,
    y = sourceSpanInd2PacketEquiv P j vQ R a x

abbrev sourceSpanInd2Setoid
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (R : SourceSpanInd2Realization.{uBase, uAbove, uLabel, uK, uAllowed}
      P j vQ) : Setoid (SourceSpanTensorPacketQ P j vQ) :=
  Relation.EqvGen.setoid (sourceSpanInd2Step P j vQ R)

abbrev SourceSpanInd2Quotient
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (R : SourceSpanInd2Realization.{uBase, uAbove, uLabel, uK, uAllowed}
      P j vQ) :=
  Quotient (sourceSpanInd2Setoid P j vQ R)

def sourceSpanPacketVisible
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) (x : SourceSpanTensorPacketQ P j vQ) : Prop :=
  x ≠ 0

theorem sourceSpan_ind2_step_preserves_visibility
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (R : SourceSpanInd2Realization.{uBase, uAbove, uLabel, uK, uAllowed}
      P j vQ)
    {x y : SourceSpanTensorPacketQ P j vQ}
    (hxy : sourceSpanInd2Step P j vQ R x y) :
    sourceSpanPacketVisible P j vQ x ↔ sourceSpanPacketVisible P j vQ y := by
  rcases hxy with ⟨a, rfl⟩
  constructor
  · intro hx hzero
    apply hx
    apply (sourceSpanInd2PacketEquiv P j vQ R a).injective
    simpa using hzero
  · intro hy hx
    exact hy (by simpa [hx])

theorem sourceSpan_ind2_relation_preserves_visibility
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (R : SourceSpanInd2Realization.{uBase, uAbove, uLabel, uK, uAllowed}
      P j vQ)
    {x y : SourceSpanTensorPacketQ P j vQ}
    (hxy : Relation.EqvGen (sourceSpanInd2Step P j vQ R) x y) :
    sourceSpanPacketVisible P j vQ x ↔ sourceSpanPacketVisible P j vQ y := by
  induction hxy with
  | rel x y h => exact sourceSpan_ind2_step_preserves_visibility P j vQ R h
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ hxy hyz => exact hxy.trans hyz

def sourceSpanInd2OnlyGenerators
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (R : SourceSpanInd2Realization.{uBase, uAbove, uLabel, uK, uAllowed}
      P j vQ) :
    AmbiguityGenerators
      (fun _ : Unit => SourceSpanTensorPacketQ P j vQ) where
  ind1Step := fun _ _ _ => False
  ind2Step := fun _ => sourceSpanInd2Step P j vQ R

theorem sourceSpan_ind2_step_enters_generic_ambiguity
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (R : SourceSpanInd2Realization.{uBase, uAbove, uLabel, uK, uAllowed}
      P j vQ)
    {x y : SourceSpanTensorPacketQ P j vQ}
    (hxy : sourceSpanInd2Step P j vQ R x y) :
    Relation.EqvGen
      (ambiguityStep (sourceSpanInd2OnlyGenerators P j vQ R) ()) x y :=
  ind2_step_enters_ambiguity (sourceSpanInd2OnlyGenerators P j vQ R) hxy

noncomputable def visibleBoolInd2Realization :
    SourceSpanInd2Realization visibleUnitSourceSpan () () where
  Allowed := fun _ _ => Bool
  fiberEquiv := fun _ _ b =>
    if b then LinearEquiv.neg ℚ else LinearEquiv.refl ℚ _

def visibleNegInd2Choice : SourceSpanInd2Choice visibleBoolInd2Realization :=
  fun _ _ => true

theorem visible_neg_ind2_moves_packet :
    sourceSpanInd2PacketEquiv visibleUnitSourceSpan () ()
        visibleBoolInd2Realization visibleNegInd2Choice
        visibleUnitPurePacket ≠ visibleUnitPurePacket := by
  intro h
  unfold visibleUnitPurePacket at h
  rw [sourceSpanInd2PacketEquiv_maps_pure] at h
  let e := PiTensorProduct.subsingletonEquiv
      (R := ℚ)
      (s := fun alpha : Fin 1 =>
        DirectSum Unit (fun v =>
          visibleUnitSourceSpan.rationalSpan
            { label := (), base := (), tensorFactor := alpha,
              directSummand := v }))
      (0 : Fin 1)
  have he := congrArg e h
  simp [e, sourceSpanPurePacket, visibleBoolInd2Realization,
    visibleNegInd2Choice] at he
  have hc := congrArg (fun z => z ()) he
  have hf : -visibleUnitFiberOne 0 = visibleUnitFiberOne 0 := by
    simpa using hc
  have hv := congrArg Subtype.val hf
  norm_num [visibleUnitFiberOne] at hv

def SourceSpanHasMovingInd2
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (R : SourceSpanInd2Realization.{uBase, uAbove, uLabel, uK, uAllowed}
      P j vQ) : Prop :=
  exists (a : SourceSpanInd2Choice R) (x : SourceSpanTensorPacketQ P j vQ),
    sourceSpanInd2PacketEquiv P j vQ R a x ≠ x

theorem visible_bool_has_moving_ind2 :
    SourceSpanHasMovingInd2 visibleUnitSourceSpan () ()
      visibleBoolInd2Realization :=
  ⟨visibleNegInd2Choice, visibleUnitPurePacket,
    visible_neg_ind2_moves_packet⟩

theorem visible_ind2_action_rejects_constant_witness
    (a : SourceSpanInd2Choice visibleBoolInd2Realization) :
    sourceSpanInd2PacketEquiv visibleUnitSourceSpan () ()
        visibleBoolInd2Realization a 0 ≠
      sourceSpanInd2PacketEquiv visibleUnitSourceSpan () ()
        visibleBoolInd2Realization a visibleUnitPurePacket := by
  intro h
  apply visible_unit_pure_packet_ne_zero
  exact ((sourceSpanInd2PacketEquiv visibleUnitSourceSpan () ()
    visibleBoolInd2Realization a).injective h).symm

noncomputable def visibleEmptyInd2Realization :
    SourceSpanInd2Realization visibleUnitSourceSpan () () where
  Allowed := fun _ _ => Fin 0
  fiberEquiv := fun _ _ a => Fin.elim0 a

theorem visible_empty_ind2_has_no_choice :
    ¬ Nonempty (SourceSpanInd2Choice visibleEmptyInd2Realization) := by
  rintro ⟨a⟩
  exact Fin.elim0 (a 0 ())

theorem visible_empty_fails_moving_ind2 :
    ¬ SourceSpanHasMovingInd2 visibleUnitSourceSpan () ()
      visibleEmptyInd2Realization := by
  rintro ⟨a, x, hx⟩
  exact visible_empty_ind2_has_no_choice ⟨a⟩

theorem closed_packet_fails_moving_ind2
    (R : SourceSpanInd2Realization
      closedUnitSourceSpan () ()) :
    ¬ SourceSpanHasMovingInd2 closedUnitSourceSpan () () R := by
  rintro ⟨a, x, hx⟩
  exact hx (closed_unit_packet_subsingleton
    (sourceSpanInd2PacketEquiv closedUnitSourceSpan () () R a x) x)

theorem visible_zero_not_ind2_related :
    ¬ Relation.EqvGen
      (sourceSpanInd2Step visibleUnitSourceSpan () ()
        visibleBoolInd2Realization)
      0 visibleUnitPurePacket := by
  intro h
  have hvis := sourceSpan_ind2_relation_preserves_visibility
    visibleUnitSourceSpan () () visibleBoolInd2Realization h
  have hpacket : sourceSpanPacketVisible visibleUnitSourceSpan () ()
      visibleUnitPurePacket := visible_unit_pure_packet_ne_zero
  have hzero := hvis.mpr hpacket
  exact hzero rfl

theorem visible_zero_class_ne_packet_class :
    (Quotient.mk (sourceSpanInd2Setoid visibleUnitSourceSpan () ()
        visibleBoolInd2Realization) 0 :
      SourceSpanInd2Quotient visibleUnitSourceSpan () ()
        visibleBoolInd2Realization) ≠
    Quotient.mk (sourceSpanInd2Setoid visibleUnitSourceSpan () ()
      visibleBoolInd2Realization) visibleUnitPurePacket := by
  intro h
  exact visible_zero_not_ind2_related (Quotient.exact h)

end CitedLV.Theorem311
