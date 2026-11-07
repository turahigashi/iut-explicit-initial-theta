import Cor312LogVolume.theorem311.CorrectedAdmissiblePacketReadout
import Cor312LogVolume.theorem311.PacketRegionTwoLayerMean

namespace CitedLV.Theorem311

open scoped BigOperators

universe uPlace uLift uDegreeBase uStage

theorem full_choice_normalized_mean_add
    {E : Type uPlace} [Fintype E]
    (n : Nat) (degree : E -> Real)
    (raw correction : (Fin n -> E) -> Real) :
    fullChoiceNormalizedMean n degree
        (fun choice => raw choice + correction choice) =
      fullChoiceNormalizedMean n degree raw +
        fullChoiceNormalizedMean n degree correction := by
  classical
  unfold fullChoiceNormalizedMean
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring

theorem full_choice_normalized_mean_eq_weight_sum
    {E : Type uPlace} [Fintype E]
    (n : Nat) (degree : E -> Real)
    (profile : (Fin n -> E) -> Real) :
    fullChoiceNormalizedMean n degree profile =
      ∑ choice : Fin n -> E,
        thm110NormalizedChoiceWeight n degree choice * profile choice := by
  classical
  unfold fullChoiceNormalizedMean thm110NormalizedChoiceWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro choice _
  ring

theorem full_choice_normalized_mean_const
    {E : Type uPlace} [Fintype E] [Nonempty E]
    (n : Nat) (degree : E -> Real)
    (hdegree : PlaceDegreesPositive degree) (k : Real) :
    fullChoiceNormalizedMean n degree (fun _ => k) = k := by
  classical
  rw [full_choice_normalized_mean_eq_weight_sum]
  rw [← Finset.sum_mul]
  rw [thm110_normalized_weights_sum_one n degree hdegree]
  exact one_mul k

theorem full_choice_normalized_mean_constant_shift
    {E : Type uPlace} [Fintype E] [Nonempty E]
    (n : Nat) (degree : E -> Real)
    (hdegree : PlaceDegreesPositive degree)
    (raw : (Fin n -> E) -> Real) (k : Real) :
    fullChoiceNormalizedMean n degree (fun choice => raw choice + k) =
      fullChoiceNormalizedMean n degree raw + k := by
  rw [full_choice_normalized_mean_add]
  rw [full_choice_normalized_mean_const n degree hdegree k]

theorem ordinary_fin_mean_add
    {n : Nat} (raw correction : Fin n -> Real) :
    ordinaryFinMean (fun j => raw j + correction j) =
      ordinaryFinMean raw + ordinaryFinMean correction := by
  classical
  unfold ordinaryFinMean
  rw [Finset.sum_add_distrib]
  ring

theorem two_layer_normalized_mean_add
    {n : Nat} (E : Fin n -> Type uStage)
    [finiteE : forall j, Fintype (E j)]
    (arity : Fin n -> Nat)
    (degree : (j : Fin n) -> E j -> Real)
    (raw correction :
      (j : Fin n) -> (Fin (arity j) -> E j) -> Real) :
    ordinaryFinMean (fun j =>
        fullChoiceNormalizedMean (arity j) (degree j)
          (fun choice => raw j choice + correction j choice)) =
      ordinaryFinMean (fun j =>
        fullChoiceNormalizedMean (arity j) (degree j) (raw j)) +
      ordinaryFinMean (fun j =>
        fullChoiceNormalizedMean (arity j) (degree j) (correction j)) := by
  calc
    ordinaryFinMean (fun j =>
        fullChoiceNormalizedMean (arity j) (degree j)
          (fun choice => raw j choice + correction j choice)) =
        ordinaryFinMean (fun j =>
          fullChoiceNormalizedMean (arity j) (degree j) (raw j) +
          fullChoiceNormalizedMean (arity j) (degree j) (correction j)) := by
            congr 1
            funext j
            exact full_choice_normalized_mean_add
              (arity j) (degree j) (raw j) (correction j)
    _ = _ := ordinary_fin_mean_add _ _

theorem decomposition_choice_profile_add_const
    {Base : Type uLift} {Above : Base -> Type uPlace}
    {Label : Type uDegreeBase} {arity : Label -> Nat}
    {K : Type uStage} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    (z : SourceSpanTensorPacketQ P j vQ)
    (readout : (choice : SourcePacketChoice Above arity j vQ) ->
      SourceSpanChoiceTensor P j vQ choice -> Real)
    (k : Real) (choice : SourcePacketChoice Above arity j vQ) :
    decompositionChoiceProfile P j vQ z
        (fun choice tensor => readout choice tensor + k) choice =
      decompositionChoiceProfile P j vQ z readout choice + k :=
  rfl

theorem source_span_thm110_value_add_const
    {Base : Type uLift} {Above : Base -> Type uPlace}
    {Label : Type uDegreeBase} {arity : Label -> Nat}
    {K : Type uStage} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [Fintype (Above vQ)] [Nonempty (Above vQ)]
    (z : SourceSpanTensorPacketQ P j vQ)
    (degree : Above vQ -> Real) (hdegree : PlaceDegreesPositive degree)
    (readout : (choice : SourcePacketChoice Above arity j vQ) ->
      SourceSpanChoiceTensor P j vQ choice -> Real)
    (k : Real) :
    sourceSpanThm110DegreeWeightedMean P j vQ z degree
        (fun choice tensor => readout choice tensor + k) =
      sourceSpanThm110DegreeWeightedMean P j vQ z degree readout + k := by
  change fullChoiceNormalizedMean (arity j + 1) degree
      (fun choice => decompositionChoiceProfile P j vQ z
        (fun choice tensor => readout choice tensor + k) choice) = _
  simpa only [decomposition_choice_profile_add_const] using
    full_choice_normalized_mean_constant_shift
      (arity j + 1) degree hdegree
        (decompositionChoiceProfile P j vQ z readout) k

noncomputable def iut3RawFormulaWeightMass
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    [Fintype Lift] [Fintype DegreeBase]
    (D : RawPacketDegreeData Lift DegreeBase) (n : Nat) : Real :=
  ∑ choice : Fin n -> Lift, iut3RawChoiceWeight D n choice

noncomputable def iut3RawFormulaWeightedValue
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    [Fintype Lift] [Fintype DegreeBase]
    (D : RawPacketDegreeData Lift DegreeBase) (n : Nat)
    (profile : (Fin n -> Lift) -> Real) : Real :=
  ∑ choice : Fin n -> Lift,
    iut3RawChoiceWeight D n choice * profile choice

theorem iut3_raw_formula_weighted_value_add
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    [Fintype Lift] [Fintype DegreeBase]
    (D : RawPacketDegreeData Lift DegreeBase) (n : Nat)
    (raw correction : (Fin n -> Lift) -> Real) :
    iut3RawFormulaWeightedValue D n
        (fun choice => raw choice + correction choice) =
      iut3RawFormulaWeightedValue D n raw +
        iut3RawFormulaWeightedValue D n correction := by
  classical
  unfold iut3RawFormulaWeightedValue
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

theorem iut3_raw_formula_constant_value
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    [Fintype Lift] [Fintype DegreeBase]
    (D : RawPacketDegreeData Lift DegreeBase) (n : Nat) (k : Real) :
    iut3RawFormulaWeightedValue D n (fun _ => k) =
      iut3RawFormulaWeightMass D n * k := by
  classical
  unfold iut3RawFormulaWeightedValue iut3RawFormulaWeightMass
  exact (Finset.sum_mul _ _ _).symm

theorem iut3_raw_formula_constant_shift
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    [Fintype Lift] [Fintype DegreeBase]
    (D : RawPacketDegreeData Lift DegreeBase) (n : Nat)
    (raw : (Fin n -> Lift) -> Real) (k : Real) :
    iut3RawFormulaWeightedValue D n (fun choice => raw choice + k) =
      iut3RawFormulaWeightedValue D n raw +
        iut3RawFormulaWeightMass D n * k := by
  rw [iut3_raw_formula_weighted_value_add]
  rw [iut3_raw_formula_constant_value]

theorem source_span_iut3_raw_value_add_const
    {Base : Type uLift} {Above : Base -> Type uPlace}
    {DegreeBase : Type uDegreeBase}
    {Label : Type uDegreeBase} {arity : Label -> Nat}
    {K : Type uStage} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [Fintype (Above vQ)] [Fintype DegreeBase]
    (D : RawPacketDegreeData (Above vQ) DegreeBase)
    (z : SourceSpanTensorPacketQ P j vQ)
    (readout : (choice : SourcePacketChoice Above arity j vQ) ->
      SourceSpanChoiceTensor P j vQ choice -> Real)
    (k : Real) :
    sourceSpanIUT3RawDegreeWeightedValue P j vQ D z
        (fun choice tensor => readout choice tensor + k) =
      sourceSpanIUT3RawDegreeWeightedValue P j vQ D z readout +
        iut3RawFormulaWeightMass D (arity j + 1) * k := by
  unfold sourceSpanIUT3RawDegreeWeightedValue
  simpa only [decomposition_choice_profile_add_const] using
    iut3_raw_formula_constant_shift D (arity j + 1)
      (decompositionChoiceProfile P j vQ z readout) k

def halfMassRawFormulaData : RawPacketDegreeData Unit Unit where
  toBase := id
  relativeDegree := fun _ => 2
  baseDegree := fun _ => 1

theorem half_mass_raw_formula_relative_positive :
    RawRelativeDegreesPositive halfMassRawFormulaData := by
  intro u
  norm_num [halfMassRawFormulaData]

theorem half_mass_raw_formula_base_positive :
    RawBaseDegreesPositive halfMassRawFormulaData := by
  intro u
  norm_num [halfMassRawFormulaData]

theorem half_mass_raw_formula_weight_mass :
    iut3RawFormulaWeightMass halfMassRawFormulaData 1 = 1 / 2 := by
  norm_num [iut3RawFormulaWeightMass, iut3RawChoiceWeight,
    choiceDegreeProduct, choiceDegreeMass,
    Src.CoreLayer.WeightedAvg.lamProd, halfMassRawFormulaData]

theorem positive_bijective_raw_formula_data_need_not_have_unit_mass :
    LiftToBaseBijective halfMassRawFormulaData /\
      RawRelativeDegreesPositive halfMassRawFormulaData /\
      RawBaseDegreesPositive halfMassRawFormulaData /\
      iut3RawFormulaWeightMass halfMassRawFormulaData 1 ≠ 1 := by
  refine ⟨Function.bijective_id,
    half_mass_raw_formula_relative_positive,
    half_mass_raw_formula_base_positive, ?_⟩
  rw [half_mass_raw_formula_weight_mass]
  norm_num

theorem half_mass_raw_formula_constant_four_is_two :
    iut3RawFormulaWeightedValue halfMassRawFormulaData 1 (fun _ => 4) = 2 := by
  rw [iut3_raw_formula_constant_value, half_mass_raw_formula_weight_mass]
  norm_num

theorem normalized_singleton_constant_four_is_four :
    fullChoiceNormalizedMean 1 halfMassRawFormulaData.baseDegree
      (fun _ => 4) = 4 := by
  apply full_choice_normalized_mean_const
  intro u
  norm_num [halfMassRawFormulaData]

theorem raw_formula_and_normalized_constant_corrections_differ :
    iut3RawFormulaWeightedValue halfMassRawFormulaData 1 (fun _ => 4) ≠
      fullChoiceNormalizedMean 1 halfMassRawFormulaData.baseDegree
        (fun _ => 4) := by
  rw [half_mass_raw_formula_constant_four_is_two,
    normalized_singleton_constant_four_is_four]
  norm_num

end CitedLV.Theorem311
