import Cor312LogVolume.theorem311.LocalMonoanalyticQSpan
import Cor312LogVolume.theorem311.AlgebraicLocalTensorPacket
import Mathlib.LinearAlgebra.PiTensorProduct.DirectSum

namespace CitedLV.Theorem311

open scoped TensorProduct

universe uBase uAbove uLabel uK

abbrev SourceSpanOneFactorQ
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) (alpha : Fin (arity j + 1)) :=
  DirectSum (Above vQ) (fun v =>
    P.rationalSpan
      { label := j, base := vQ, tensorFactor := alpha,
        directSummand := v })

abbrev SourceSpanTensorPacketQ
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) :=
  PiTensorProduct ℚ
    (fun alpha : Fin (arity j + 1) =>
      SourceSpanOneFactorQ P j vQ alpha)

noncomputable def sourceSpanPurePacket
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [DecidableEq (Above vQ)]
    (choice : Fin (arity j + 1) -> Above vQ)
    (x : (alpha : Fin (arity j + 1)) ->
      P.rationalSpan
        { label := j, base := vQ, tensorFactor := alpha,
          directSummand := choice alpha }) :
    SourceSpanTensorPacketQ P j vQ := by
  exact PiTensorProduct.tprod ℚ (fun alpha =>
    DirectSum.lof ℚ (Above vQ)
      (fun v => P.rationalSpan
        { label := j, base := vQ, tensorFactor := alpha,
          directSummand := v })
      (choice alpha) (x alpha))

noncomputable def sourceSpanTensorDecomposition
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) :
    SourceSpanTensorPacketQ P j vQ ≃ₗ[ℚ]
      DirectSum (Fin (arity j + 1) -> Above vQ)
        (fun choice => PiTensorProduct ℚ
          (fun alpha : Fin (arity j + 1) =>
            P.rationalSpan
              { label := j, base := vQ, tensorFactor := alpha,
                directSummand := choice alpha })) :=
  PiTensorProduct.ofDirectSumEquiv

theorem sourceSpanTensorDecomposition_maps_pure
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [DecidableEq (Above vQ)]
    (choice : Fin (arity j + 1) -> Above vQ)
    (x : (alpha : Fin (arity j + 1)) ->
      P.rationalSpan
        { label := j, base := vQ, tensorFactor := alpha,
          directSummand := choice alpha }) :
    sourceSpanTensorDecomposition P j vQ
        (sourceSpanPurePacket P j vQ choice x) =
      DirectSum.lof ℚ (Fin (arity j + 1) -> Above vQ)
        (fun selected => PiTensorProduct ℚ
          (fun alpha : Fin (arity j + 1) =>
            P.rationalSpan
              { label := j, base := vQ, tensorFactor := alpha,
                directSummand := selected alpha }))
        choice (PiTensorProduct.tprod ℚ x) := by
  unfold sourceSpanTensorDecomposition sourceSpanPurePacket
  exact PiTensorProduct.ofDirectSumEquiv_tprod_lof
    (R := ℚ)
    (M := fun alpha v =>
      P.rationalSpan
        { label := j, base := vQ, tensorFactor := alpha,
          directSummand := v })
    choice x

def SourceSpanHasPlace
    {Base : Type uBase} (Above : Base -> Type uAbove) (vQ : Base) : Prop :=
  Nonempty (Above vQ)

def SourceSpanCoordinateVisible
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) : Prop :=
  exists (alpha : Fin (arity j + 1)) (v : Above vQ)
      (x : P.rationalSpan
        { label := j, base := vQ, tensorFactor := alpha,
          directSummand := v }),
    x ≠ 0

abbrev unitArity : Unit -> Nat := fun _ => 0

def visibleUnitSourceSpan :
    SourceShapedLocalMonoanalyticQSpanRaw Unit (fun _ => Unit)
      Unit unitArity ℚ where
  integral := fun _ => {1}
  rationalSpan := fun _ => ⊤

def closedUnitSourceSpan :
    SourceShapedLocalMonoanalyticQSpanRaw Unit (fun _ => Unit)
      Unit unitArity ℚ where
  integral := fun _ => {0}
  rationalSpan := fun _ => ⊥

theorem visible_unit_span_correct :
    RationalSpanCorrect visibleUnitSourceSpan := by
  intro i
  simp [visibleUnitSourceSpan]

theorem closed_unit_span_correct :
    RationalSpanCorrect closedUnitSourceSpan := by
  intro i
  simp [closedUnitSourceSpan]

theorem visible_unit_has_place :
    SourceSpanHasPlace (fun _ : Unit => Unit) () :=
  ⟨()⟩

def visibleUnitFiberOne (alpha : Fin 1) :
    visibleUnitSourceSpan.rationalSpan
      { label := (), base := (), tensorFactor := alpha,
        directSummand := () } :=
  ⟨1, by simp [visibleUnitSourceSpan]⟩

theorem visible_unit_fiber_one_ne_zero (alpha : Fin 1) :
    visibleUnitFiberOne alpha ≠ 0 := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [visibleUnitFiberOne] at hv

theorem visible_unit_coordinate_visible :
    SourceSpanCoordinateVisible visibleUnitSourceSpan () () :=
  ⟨0, (), visibleUnitFiberOne 0, visible_unit_fiber_one_ne_zero 0⟩

noncomputable def visibleUnitPurePacket :
    SourceSpanTensorPacketQ visibleUnitSourceSpan () () :=
  sourceSpanPurePacket visibleUnitSourceSpan () ()
    (fun _ => ()) visibleUnitFiberOne

theorem visible_unit_one_factor_ne_zero :
    DirectSum.lof ℚ Unit
      (fun v => visibleUnitSourceSpan.rationalSpan
        { label := (), base := (), tensorFactor := (0 : Fin 1),
          directSummand := v })
      () (visibleUnitFiberOne 0) ≠ 0 := by
  simpa [visibleUnitSourceSpan] using
    (singleton_directSum_lof_ne_zero
      (visibleUnitFiberOne 0) (visible_unit_fiber_one_ne_zero 0))

theorem visible_unit_pure_packet_ne_zero : visibleUnitPurePacket ≠ 0 := by
  intro h
  let e := PiTensorProduct.subsingletonEquiv
      (R := ℚ)
      (s := fun alpha : Fin 1 =>
        DirectSum Unit (fun v =>
          visibleUnitSourceSpan.rationalSpan
            { label := (), base := (), tensorFactor := alpha,
              directSummand := v }))
      (0 : Fin 1)
  have hOuter := congrArg e h
  simp [e, visibleUnitPurePacket, sourceSpanPurePacket] at hOuter
  have hComponent := congrArg (fun z => z ()) hOuter
  apply visible_unit_fiber_one_ne_zero 0
  simpa using hComponent

theorem visible_unit_packet_visible :
    AlgebraicPacketVisible
      (SourceSpanTensorPacketQ visibleUnitSourceSpan () ()) :=
  ⟨visibleUnitPurePacket, visible_unit_pure_packet_ne_zero⟩

theorem closed_unit_coordinate_fails_visibility :
    ¬ SourceSpanCoordinateVisible closedUnitSourceSpan () () := by
  rintro ⟨alpha, v, x, hx⟩
  apply hx
  apply Subtype.ext
  have hxmem := x.property
  change (x : ℚ) ∈ (⊥ : Submodule ℚ ℚ) at hxmem
  simpa only [Submodule.mem_bot] using hxmem

theorem closed_unit_fiber_subsingleton
    (alpha : Fin 1) (v : Unit)
    (x y : closedUnitSourceSpan.rationalSpan
      { label := (), base := (), tensorFactor := alpha,
        directSummand := v }) : x = y := by
  apply Subtype.ext
  have hxmem := x.property
  have hymem := y.property
  change (x : ℚ) ∈ (⊥ : Submodule ℚ ℚ) at hxmem
  change (y : ℚ) ∈ (⊥ : Submodule ℚ ℚ) at hymem
  have hxzero : (x : ℚ) = 0 := by
    simpa only [Submodule.mem_bot] using hxmem
  have hyzero : (y : ℚ) = 0 := by
    simpa only [Submodule.mem_bot] using hymem
  exact hxzero.trans hyzero.symm

theorem closed_unit_packet_subsingleton
    (x y : SourceSpanTensorPacketQ closedUnitSourceSpan () ()) : x = y := by
  let e := PiTensorProduct.subsingletonEquiv
    (R := ℚ)
    (s := fun alpha : Fin 1 =>
      SourceSpanOneFactorQ closedUnitSourceSpan () () alpha)
    (0 : Fin 1)
  apply e.injective
  apply DirectSum.ext_component ℚ
  intro v
  exact closed_unit_fiber_subsingleton 0 v (e x v) (e y v)

theorem closed_unit_packet_fails_visibility :
    ¬ AlgebraicPacketVisible
      (SourceSpanTensorPacketQ closedUnitSourceSpan () ()) := by
  rintro ⟨x, hx⟩
  exact hx (closed_unit_packet_subsingleton x 0)

def emptyAboveSourceSpan :
    SourceShapedLocalMonoanalyticQSpanRaw Unit (fun _ => Fin 0)
      Unit unitArity ℚ :=
  sourceShapedSpanFromIntegral (fun i => Fin.elim0 i.directSummand)

theorem empty_above_span_correct :
    RationalSpanCorrect emptyAboveSourceSpan :=
  sourceShapedSpanFromIntegral_correct _

theorem empty_above_fails_has_place :
    ¬ SourceSpanHasPlace (fun _ : Unit => Fin 0) () := by
  rintro ⟨v⟩
  exact Fin.elim0 v

theorem span_correctness_does_not_bake_in_packet_content :
    RationalSpanCorrect visibleUnitSourceSpan /\
      SourceSpanCoordinateVisible visibleUnitSourceSpan () () /\
      AlgebraicPacketVisible
        (SourceSpanTensorPacketQ visibleUnitSourceSpan () ()) /\
      RationalSpanCorrect closedUnitSourceSpan /\
      ¬ SourceSpanCoordinateVisible closedUnitSourceSpan () () /\
      ¬ AlgebraicPacketVisible
        (SourceSpanTensorPacketQ closedUnitSourceSpan () ()) /\
      RationalSpanCorrect emptyAboveSourceSpan /\
      ¬ SourceSpanHasPlace (fun _ : Unit => Fin 0) () :=
  ⟨visible_unit_span_correct,
    visible_unit_coordinate_visible,
    visible_unit_packet_visible,
    closed_unit_span_correct,
    closed_unit_coordinate_fails_visibility,
    closed_unit_packet_fails_visibility,
    empty_above_span_correct,
    empty_above_fails_has_place⟩

end CitedLV.Theorem311
