import Cor312LogVolume.theorem311.SelectedMixedSubmodule
import Cor312LogVolume.WeightedAverageProp17
import Mathlib.Tactic.FinCases

namespace CitedLV.Theorem311

open scoped BigOperators TensorProduct

universe uBase uAbove uLabel uK uLift uDegreeBase

abbrev SourcePacketChoice
    {Base : Type uBase} (Above : Base -> Type uAbove)
    {Label : Type uLabel} (arity : Label -> Nat)
    (j : Label) (vQ : Base) :=
  Fin (arity j + 1) -> Above vQ

noncomputable def decompositionChoiceProfile
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (z : SourceSpanTensorPacketQ P j vQ)
    (readout : (choice : SourcePacketChoice Above arity j vQ) ->
      SourceSpanChoiceTensor P j vQ choice -> ℝ)
    (choice : SourcePacketChoice Above arity j vQ) : ℝ :=
  readout choice ((sourceSpanTensorDecomposition P j vQ z) choice)

def choiceDegreeProduct
    {E : Type uAbove} (n : Nat) (degree : E -> ℝ)
    (choice : Fin n -> E) : ℝ :=
  Src.CoreLayer.WeightedAvg.lamProd n degree choice

noncomputable def choiceDegreeMass
    {E : Type uAbove} [Fintype E]
    (n : Nat) (degree : E -> ℝ) : ℝ :=
  ∑ choice : Fin n -> E, choiceDegreeProduct n degree choice

noncomputable def thm110NormalizedChoiceWeight
    {E : Type uAbove} [Fintype E]
    (n : Nat) (degree : E -> ℝ) (choice : Fin n -> E) : ℝ :=
  choiceDegreeProduct n degree choice / choiceDegreeMass n degree

def PlaceDegreesPositive {E : Type uAbove} (degree : E -> ℝ) : Prop :=
  forall e, 0 < degree e

theorem choice_degree_product_pos
    {E : Type uAbove} (n : Nat) (degree : E -> ℝ)
    (hdegree : PlaceDegreesPositive degree) (choice : Fin n -> E) :
    0 < choiceDegreeProduct n degree choice := by
  unfold choiceDegreeProduct Src.CoreLayer.WeightedAvg.lamProd
  exact Finset.prod_pos (fun alpha _ => hdegree (choice alpha))

theorem choice_degree_mass_pos
    {E : Type uAbove} [Fintype E] [Nonempty E]
    (n : Nat) (degree : E -> ℝ)
    (hdegree : PlaceDegreesPositive degree) :
    0 < choiceDegreeMass n degree := by
  classical
  unfold choiceDegreeMass
  apply Finset.sum_pos
  · intro choice _
    exact choice_degree_product_pos n degree hdegree choice
  · exact Finset.univ_nonempty

theorem choice_degree_mass_eq_sum_pow
    {E : Type uAbove} [Fintype E] [DecidableEq E] [Nonempty E]
    (n : Nat) (degree : E -> ℝ) :
    choiceDegreeMass n degree =
      (Src.CoreLayer.WeightedAvg.lamE degree) ^ n := by
  exact (Src.CoreLayer.WeightedAvg.lamE_pow n degree).symm

theorem thm110_normalized_weights_sum_one
    {E : Type uAbove} [Fintype E] [Nonempty E]
    (n : Nat) (degree : E -> ℝ)
    (hdegree : PlaceDegreesPositive degree) :
    (∑ choice : Fin n -> E,
      thm110NormalizedChoiceWeight n degree choice) = 1 := by
  have hmass := choice_degree_mass_pos n degree hdegree
  unfold thm110NormalizedChoiceWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hmass)

structure RawPacketDegreeData (Lift : Type uLift) (DegreeBase : Type uDegreeBase) where
  toBase : Lift -> DegreeBase
  relativeDegree : Lift -> ℝ
  baseDegree : DegreeBase -> ℝ

def LiftToBaseBijective
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    (D : RawPacketDegreeData Lift DegreeBase) : Prop :=
  Function.Bijective D.toBase

def RawRelativeDegreesPositive
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    (D : RawPacketDegreeData Lift DegreeBase) : Prop :=
  PlaceDegreesPositive D.relativeDegree

def RawBaseDegreesPositive
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    (D : RawPacketDegreeData Lift DegreeBase) : Prop :=
  PlaceDegreesPositive D.baseDegree

def baseChoiceOfLift
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    (D : RawPacketDegreeData Lift DegreeBase) {n : Nat}
    (choice : Fin n -> Lift) : Fin n -> DegreeBase :=
  fun alpha => D.toBase (choice alpha)

noncomputable def iut3RawChoiceWeight
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    [Fintype DegreeBase]
    (D : RawPacketDegreeData Lift DegreeBase) (n : Nat)
    (choice : Fin n -> Lift) : ℝ :=
  1 / (choiceDegreeProduct n D.relativeDegree choice *
    choiceDegreeMass n D.baseDegree)

theorem iut3_raw_choice_weight_pos
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    [Fintype DegreeBase] [Nonempty DegreeBase]
    (D : RawPacketDegreeData Lift DegreeBase) (n : Nat)
    (hrel : RawRelativeDegreesPositive D)
    (hbase : RawBaseDegreesPositive D)
    (choice : Fin n -> Lift) :
    0 < iut3RawChoiceWeight D n choice := by
  have hprod := choice_degree_product_pos n D.relativeDegree hrel choice
  have hmass := choice_degree_mass_pos n D.baseDegree hbase
  unfold iut3RawChoiceWeight
  positivity

noncomputable def sourceSpanThm110DegreeWeightedMean
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [Fintype (Above vQ)]
    (z : SourceSpanTensorPacketQ P j vQ)
    (degree : Above vQ -> ℝ)
    (readout : (choice : SourcePacketChoice Above arity j vQ) ->
      SourceSpanChoiceTensor P j vQ choice -> ℝ) : ℝ :=
  (∑ choice : SourcePacketChoice Above arity j vQ,
      choiceDegreeProduct (arity j + 1) degree choice *
        decompositionChoiceProfile P j vQ z readout choice) /
    choiceDegreeMass (arity j + 1) degree

noncomputable def sourceSpanIUT3RawDegreeWeightedValue
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {DegreeBase : Type uDegreeBase}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [Fintype (Above vQ)] [Fintype DegreeBase]
    (D : RawPacketDegreeData (Above vQ) DegreeBase)
    (z : SourceSpanTensorPacketQ P j vQ)
    (readout : (choice : SourcePacketChoice Above arity j vQ) ->
      SourceSpanChoiceTensor P j vQ choice -> ℝ) : ℝ :=
  ∑ choice : SourcePacketChoice Above arity j vQ,
    iut3RawChoiceWeight D (arity j + 1) choice *
      decompositionChoiceProfile P j vQ z readout choice

abbrev unitPacketChoice :
    SourcePacketChoice (fun _ : Unit => Unit) unitArity () () :=
  fun _ => ()

noncomputable def unitChoiceTensorScalar
    (_choice : SourcePacketChoice (fun _ : Unit => Unit) unitArity () ())
    (t : SourceSpanChoiceTensor visibleUnitSourceSpan () () unitPacketChoice) : ℝ :=
  ((((PiTensorProduct.subsingletonEquiv
      (R := ℚ)
      (s := fun alpha : Fin 1 =>
        visibleUnitSourceSpan.rationalSpan
          { label := (), base := (), tensorFactor := alpha,
            directSummand := () })
      (0 : Fin 1)) t) :
    visibleUnitSourceSpan.rationalSpan
      { label := (), base := (), tensorFactor := (0 : Fin 1),
        directSummand := () }) : ℚ)

def unitDegreeTwo (_ : Unit) : ℝ := 2

theorem unit_degree_two_positive : PlaceDegreesPositive unitDegreeTwo := by
  intro v
  norm_num [unitDegreeTwo]

theorem visible_decomposition_choice_profile_is_one :
    decompositionChoiceProfile visibleUnitSourceSpan () ()
      visibleUnitPurePacket unitChoiceTensorScalar unitPacketChoice = 1 := by
  unfold decompositionChoiceProfile visibleUnitPurePacket
  rw [sourceSpanTensorDecomposition_maps_pure]
  norm_num [unitChoiceTensorScalar, unitPacketChoice, visibleUnitFiberOne]

theorem visible_thm110_degree_weighted_mean_is_one :
    sourceSpanThm110DegreeWeightedMean visibleUnitSourceSpan () ()
      visibleUnitPurePacket unitDegreeTwo unitChoiceTensorScalar = 1 := by
  norm_num [sourceSpanThm110DegreeWeightedMean, choiceDegreeProduct,
    choiceDegreeMass, Src.CoreLayer.WeightedAvg.lamProd,
    visible_decomposition_choice_profile_is_one, unitDegreeTwo]

theorem zero_packet_thm110_degree_weighted_mean_is_zero :
    sourceSpanThm110DegreeWeightedMean visibleUnitSourceSpan () ()
      0 unitDegreeTwo unitChoiceTensorScalar = 0 := by
  norm_num [sourceSpanThm110DegreeWeightedMean, decompositionChoiceProfile,
    choiceDegreeProduct, choiceDegreeMass, Src.CoreLayer.WeightedAvg.lamProd,
    unitChoiceTensorScalar, unitDegreeTwo]

def boolDegreePositive : Bool -> ℝ
  | false => 1
  | true => 3

def boolDegreeZero : Bool -> ℝ
  | false => 1
  | true => 0

theorem bool_degree_positive_passes : PlaceDegreesPositive boolDegreePositive := by
  intro v
  cases v <;> norm_num [boolDegreePositive]

theorem bool_degree_zero_fails : ¬ PlaceDegreesPositive boolDegreeZero := by
  intro h
  have hz := h true
  norm_num [boolDegreeZero] at hz

theorem empty_place_degrees_vacuously_positive (degree : Fin 0 -> ℝ) :
    PlaceDegreesPositive degree := by
  intro v
  exact Fin.elim0 v

theorem empty_place_choice_degree_mass_zero (degree : Fin 0 -> ℝ) :
    choiceDegreeMass 1 degree = 0 := by
  simp [choiceDegreeMass]

def zeroBaseDegreeData : RawPacketDegreeData Unit Unit where
  toBase := id
  relativeDegree := fun _ => 1
  baseDegree := fun _ => 0

theorem zero_base_data_fails_positive :
    ¬ RawBaseDegreesPositive zeroBaseDegreeData := by
  intro h
  have hz := h ()
  norm_num [zeroBaseDegreeData] at hz

def zeroRelativeDegreeData : RawPacketDegreeData Unit Unit where
  toBase := id
  relativeDegree := fun _ => 0
  baseDegree := fun _ => 1

theorem zero_relative_data_fails_positive :
    ¬ RawRelativeDegreesPositive zeroRelativeDegreeData := by
  intro h
  have hz := h ()
  norm_num [zeroRelativeDegreeData] at hz

theorem zero_relative_raw_weight_collapses
    (choice : Fin 1 -> Unit) :
    iut3RawChoiceWeight zeroRelativeDegreeData 1 choice = 0 := by
  norm_num [iut3RawChoiceWeight, choiceDegreeProduct, choiceDegreeMass,
    Src.CoreLayer.WeightedAvg.lamProd, zeroRelativeDegreeData]

def conventionCheckData : RawPacketDegreeData Bool Bool where
  toBase := id
  relativeDegree
    | false => 2
    | true => 5
  baseDegree
    | false => 1
    | true => 3

abbrev conventionFalseChoice : Fin 1 -> Bool := fun _ => false

abbrev conventionTrueChoice : Fin 1 -> Bool := fun _ => true

theorem convention_to_base_bijective : LiftToBaseBijective conventionCheckData := by
  exact Function.bijective_id

theorem convention_relative_degrees_positive :
    RawRelativeDegreesPositive conventionCheckData := by
  intro v
  cases v <;> norm_num [conventionCheckData]

theorem convention_base_degrees_positive :
    RawBaseDegreesPositive conventionCheckData := by
  intro v
  cases v <;> norm_num [conventionCheckData]

theorem convention_base_degree_mass :
    choiceDegreeMass 1 conventionCheckData.baseDegree = 4 := by
  rw [choice_degree_mass_eq_sum_pow]
  norm_num [Src.CoreLayer.WeightedAvg.lamE, conventionCheckData]

theorem convention_thm110_false_weight :
    thm110NormalizedChoiceWeight 1 conventionCheckData.baseDegree
      (baseChoiceOfLift conventionCheckData conventionFalseChoice) = 1 / 4 := by
  unfold thm110NormalizedChoiceWeight
  rw [convention_base_degree_mass]
  norm_num [choiceDegreeProduct, Src.CoreLayer.WeightedAvg.lamProd,
    baseChoiceOfLift, conventionCheckData, conventionFalseChoice]

theorem convention_thm110_true_weight :
    thm110NormalizedChoiceWeight 1 conventionCheckData.baseDegree
      (baseChoiceOfLift conventionCheckData conventionTrueChoice) = 3 / 4 := by
  unfold thm110NormalizedChoiceWeight
  rw [convention_base_degree_mass]
  norm_num [choiceDegreeProduct, Src.CoreLayer.WeightedAvg.lamProd,
    baseChoiceOfLift, conventionCheckData, conventionTrueChoice]

theorem convention_iut3_false_raw_weight :
    iut3RawChoiceWeight conventionCheckData 1 conventionFalseChoice = 1 / 8 := by
  unfold iut3RawChoiceWeight
  rw [convention_base_degree_mass]
  norm_num [choiceDegreeProduct, Src.CoreLayer.WeightedAvg.lamProd,
    conventionCheckData, conventionFalseChoice]

theorem convention_iut3_true_raw_weight :
    iut3RawChoiceWeight conventionCheckData 1 conventionTrueChoice = 1 / 20 := by
  unfold iut3RawChoiceWeight
  rw [convention_base_degree_mass]
  norm_num [choiceDegreeProduct, Src.CoreLayer.WeightedAvg.lamProd,
    conventionCheckData, conventionTrueChoice]

theorem raw_and_thm110_conventions_are_distinct :
    iut3RawChoiceWeight conventionCheckData 1 conventionFalseChoice ≠
      thm110NormalizedChoiceWeight 1 conventionCheckData.baseDegree
        (baseChoiceOfLift conventionCheckData conventionFalseChoice) := by
  rw [convention_iut3_false_raw_weight, convention_thm110_false_weight]
  norm_num

theorem thm110_weighted_operator_does_not_bake_a_value :
    (∑ choice : Fin 1 -> Bool,
      thm110NormalizedChoiceWeight 1 conventionCheckData.baseDegree choice * 0) = 0 /\
    (∑ choice : Fin 1 -> Bool,
      thm110NormalizedChoiceWeight 1 conventionCheckData.baseDegree choice * 1) = 1 := by
  constructor
  · simp
  · simpa using thm110_normalized_weights_sum_one 1
      conventionCheckData.baseDegree convention_base_degrees_positive

end CitedLV.Theorem311
