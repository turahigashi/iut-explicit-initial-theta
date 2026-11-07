import Cor312LogVolume.logshell.PadicLogDef
import Mathlib.LinearAlgebra.Span.Basic

namespace CitedLV.Theorem311

universe uBase uAbove uLabel uIndex uK

structure LocalPacketCoordinate
    (Base : Type uBase) (Above : Base -> Type uAbove)
    (Label : Type uLabel) (arity : Label -> Nat) where
  label : Label
  base : Base
  tensorFactor : Fin (arity label + 1)
  directSummand : Above base

structure LocalMonoanalyticQSpanRaw
    (Index : Type uIndex) (K : Type uK)
    [AddCommGroup K] [Module ℚ K] where
  integral : Index -> Set K
  rationalSpan : Index -> Submodule ℚ K

abbrev SourceShapedLocalMonoanalyticQSpanRaw
    (Base : Type uBase) (Above : Base -> Type uAbove)
    (Label : Type uLabel) (arity : Label -> Nat)
    (K : Type uK) [AddCommGroup K] [Module ℚ K] :=
  LocalMonoanalyticQSpanRaw
    (LocalPacketCoordinate Base Above Label arity) K

def RationalSpanCorrect
    {Index : Type uIndex} {K : Type uK}
    [AddCommGroup K] [Module ℚ K]
    (P : LocalMonoanalyticQSpanRaw Index K) : Prop :=
  forall i, P.rationalSpan i = Submodule.span ℚ (P.integral i)

def spanFromIntegral
    {Index : Type uIndex} {K : Type uK}
    [AddCommGroup K] [Module ℚ K]
    (I : Index -> Set K) : LocalMonoanalyticQSpanRaw Index K where
  integral := I
  rationalSpan := fun i => Submodule.span ℚ (I i)

theorem spanFromIntegral_correct
    {Index : Type uIndex} {K : Type uK}
    [AddCommGroup K] [Module ℚ K]
    (I : Index -> Set K) :
    RationalSpanCorrect (spanFromIntegral I) := by
  intro i
  rfl

theorem integral_subset_rationalSpan
    {Index : Type uIndex} {K : Type uK}
    [AddCommGroup K] [Module ℚ K]
    (P : LocalMonoanalyticQSpanRaw Index K)
    (hP : RationalSpanCorrect P) (i : Index) :
    P.integral i ⊆ P.rationalSpan i := by
  intro x hx
  rw [hP i]
  exact Submodule.subset_span hx

def sourceShapedSpanFromIntegral
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (I : LocalPacketCoordinate Base Above Label arity -> Set K) :
    SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K :=
  spanFromIntegral I

theorem sourceShapedSpanFromIntegral_correct
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (I : LocalPacketCoordinate Base Above Label arity -> Set K) :
    RationalSpanCorrect (sourceShapedSpanFromIntegral I) :=
  spanFromIntegral_correct _

def PacketIndexNonempty
    {Index : Type uIndex} {K : Type uK}
    [AddCommGroup K] [Module ℚ K]
    (_P : LocalMonoanalyticQSpanRaw Index K) : Prop :=
  Nonempty Index

def IntegralValueVisible
    {Index : Type uIndex} {K : Type uK}
    [AddCommGroup K] [Module ℚ K]
    (P : LocalMonoanalyticQSpanRaw Index K) : Prop :=
  exists i x, x ∈ P.integral i /\ x ≠ 0

def RationalSpanVisible
    {Index : Type uIndex} {K : Type uK}
    [AddCommGroup K] [Module ℚ K]
    (P : LocalMonoanalyticQSpanRaw Index K) : Prop :=
  exists i x, x ∈ P.rationalSpan i /\ x ≠ 0

def IntegralCoordinateVisible
    {Index : Type uIndex} {K : Type uK}
    [AddCommGroup K] [Module ℚ K]
    (P : LocalMonoanalyticQSpanRaw Index K) : Prop :=
  exists i j, P.integral i ≠ P.integral j

noncomputable def padicLogShellQSpan
    (p : Nat) [Fact p.Prime]
    {Index : Type uIndex} (S : Index -> Set ℚ_[p]) :
    LocalMonoanalyticQSpanRaw Index ℚ_[p] :=
  spanFromIntegral
    (fun i => (CitedLV.PadicLogDef.logShell p (S i) : Set ℚ_[p]))

theorem padicLogShellQSpan_correct
    (p : Nat) [Fact p.Prime]
    {Index : Type uIndex} (S : Index -> Set ℚ_[p]) :
    RationalSpanCorrect (padicLogShellQSpan p S) :=
  spanFromIntegral_correct _

theorem padic_log_image_lands_in_integral
    (p : Nat) [Fact p.Prime]
    {Index : Type uIndex} (S : Index -> Set ℚ_[p]) (i : Index) :
    CitedLV.PadicLogDef.padicLog1p p '' S i ⊆
      (padicLogShellQSpan p S).integral i :=
  CitedLV.PadicLogDef.logImage_subset_logShell p (S i)

noncomputable def padicCoordinateLogShellQSpan
    (p : Nat) [Fact p.Prime]
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    (S : LocalPacketCoordinate Base Above Label arity -> Set ℚ_[p]) :
    SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity ℚ_[p] :=
  padicLogShellQSpan p S

theorem padicCoordinateLogShellQSpan_correct
    (p : Nat) [Fact p.Prime]
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    (S : LocalPacketCoordinate Base Above Label arity -> Set ℚ_[p]) :
    RationalSpanCorrect (padicCoordinateLogShellQSpan p S) :=
  padicLogShellQSpan_correct p S

def boolIntegral : Bool -> Set ℚ
  | false => {0}
  | true => {1}

def goodBoolQSpan : LocalMonoanalyticQSpanRaw Bool ℚ :=
  spanFromIntegral boolIntegral

def badBoolQSpan : LocalMonoanalyticQSpanRaw Bool ℚ where
  integral := boolIntegral
  rationalSpan := fun _ => ⊤

def closedBoolQSpan : LocalMonoanalyticQSpanRaw Bool ℚ :=
  spanFromIntegral (fun _ => {0})

def emptyQSpan : LocalMonoanalyticQSpanRaw (Fin 0) ℚ :=
  spanFromIntegral (fun i => Fin.elim0 i)

theorem good_bool_span_correct : RationalSpanCorrect goodBoolQSpan :=
  spanFromIntegral_correct _

theorem good_bool_index_nonempty : PacketIndexNonempty goodBoolQSpan :=
  ⟨false⟩

theorem good_bool_integral_visible : IntegralValueVisible goodBoolQSpan := by
  exact ⟨true, 1, by simp [goodBoolQSpan, spanFromIntegral, boolIntegral]⟩

theorem good_bool_rational_span_visible : RationalSpanVisible goodBoolQSpan := by
  refine ⟨true, 1, ?_, by norm_num⟩
  apply Submodule.subset_span
  simp [boolIntegral]

theorem good_bool_coordinate_visible : IntegralCoordinateVisible goodBoolQSpan := by
  refine ⟨false, true, ?_⟩
  intro h
  have hone : (1 : ℚ) ∈ (goodBoolQSpan.integral true) := by
    simp [goodBoolQSpan, spanFromIntegral, boolIntegral]
  rw [← h] at hone
  simpa [goodBoolQSpan, spanFromIntegral, boolIntegral] using hone

theorem bad_bool_keeps_integral_input :
    badBoolQSpan.integral = goodBoolQSpan.integral :=
  rfl

theorem bad_bool_integral_visible : IntegralValueVisible badBoolQSpan := by
  exact ⟨true, 1, by simp [badBoolQSpan, boolIntegral]⟩

theorem bad_bool_rational_span_visible : RationalSpanVisible badBoolQSpan := by
  exact ⟨true, 1, by simp [badBoolQSpan]⟩

theorem bad_bool_span_incorrect : ¬ RationalSpanCorrect badBoolQSpan := by
  intro h
  have hfalse := h false
  have hone : (1 : ℚ) ∈ badBoolQSpan.rationalSpan false := by
    simp [badBoolQSpan]
  rw [hfalse] at hone
  simpa [badBoolQSpan, boolIntegral] using hone

theorem closed_bool_span_correct : RationalSpanCorrect closedBoolQSpan :=
  spanFromIntegral_correct _

theorem closed_bool_fails_integral_visibility :
    ¬ IntegralValueVisible closedBoolQSpan := by
  rintro ⟨i, x, hx, hne⟩
  have : x = 0 := by
    simpa [closedBoolQSpan, spanFromIntegral] using hx
  exact hne this

theorem closed_bool_fails_rational_span_visibility :
    ¬ RationalSpanVisible closedBoolQSpan := by
  rintro ⟨i, x, hx, hne⟩
  have hspan :
      Submodule.span ℚ ({0} : Set ℚ) = (⊥ : Submodule ℚ ℚ) := by
    simp
  have : x = 0 := by
    simpa [closedBoolQSpan, spanFromIntegral, hspan] using hx
  exact hne this

theorem empty_span_correct : RationalSpanCorrect emptyQSpan :=
  spanFromIntegral_correct _

theorem empty_span_fails_index_nonempty :
    ¬ PacketIndexNonempty emptyQSpan := by
  rintro ⟨i⟩
  exact Fin.elim0 i

theorem span_correctness_and_visibility_are_not_baked_in :
    RationalSpanCorrect goodBoolQSpan /\
      ¬ RationalSpanCorrect badBoolQSpan /\
      RationalSpanCorrect closedBoolQSpan /\
      ¬ IntegralValueVisible closedBoolQSpan /\
      RationalSpanCorrect emptyQSpan /\
      ¬ PacketIndexNonempty emptyQSpan :=
  ⟨good_bool_span_correct,
    bad_bool_span_incorrect,
    closed_bool_span_correct,
    closed_bool_fails_integral_visibility,
    empty_span_correct,
    empty_span_fails_index_nonempty⟩

end CitedLV.Theorem311
