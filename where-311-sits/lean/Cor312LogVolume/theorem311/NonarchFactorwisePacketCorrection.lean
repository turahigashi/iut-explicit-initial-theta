import Cor312LogVolume.theorem311.DegreeWeightedPacketCorrection
import Cor312LogVolume.theorem311.Prop17PacketUpperBound

namespace CitedLV.Theorem311

open scoped BigOperators

universe uPlace

structure NonarchPlaceCorrectionData (Place : Type uPlace) where
  rationalPrime : Nat
  pStarExponent : Nat
  ramificationIndex : Place -> Nat
  residueDegree : Place -> Nat
  torsionPExponent : Place -> Nat

noncomputable def nonarchLocalMonoAnchorValue
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (v : Place) : Real :=
  nonarchMonoIntegralLogVolume D.rationalPrime D.pStarExponent
    (D.ramificationIndex v) (D.residueDegree v) (D.torsionPExponent v)

noncomputable def nonarchLocalAnchorCorrection
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (v : Place) : Real :=
  nonarchMonoIntegralAnchorCorrection D.rationalPrime D.pStarExponent
    (D.ramificationIndex v) (D.residueDegree v) (D.torsionPExponent v)

theorem nonarch_local_anchor_correction_calibrates_zero
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (v : Place) :
    nonarchLocalMonoAnchorValue D v +
      nonarchLocalAnchorCorrection D v = 0 := by
  exact nonarch_single_factor_correction_calibrates_zero
    D.rationalPrime D.pStarExponent (D.ramificationIndex v)
      (D.residueDegree v) (D.torsionPExponent v)

noncomputable def nonarchChoiceMonoAnchorValue
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (n : Nat) (choice : Fin n -> Place) : Real :=
  Src.CoreLayer.WeightedAvg.betaSum n (nonarchLocalMonoAnchorValue D) choice

noncomputable def nonarchPureFactorwiseAnchorCorrection
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (n : Nat) (choice : Fin n -> Place) : Real :=
  Src.CoreLayer.WeightedAvg.betaSum n (nonarchLocalAnchorCorrection D) choice

theorem nonarch_pure_factorwise_correction_calibrates_sum_zero
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (n : Nat) (choice : Fin n -> Place) :
    nonarchChoiceMonoAnchorValue D n choice +
      nonarchPureFactorwiseAnchorCorrection D n choice = 0 := by
  classical
  unfold nonarchChoiceMonoAnchorValue nonarchPureFactorwiseAnchorCorrection
    Src.CoreLayer.WeightedAvg.betaSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero (fun i _ =>
    nonarch_local_anchor_correction_calibrates_zero D (choice i))

def NonarchTensorVolumeDecomposes
    {Place : Type uPlace} (n : Nat)
    (tensorVolume : (Fin n -> Place) -> Real)
    (factorVolume : Place -> Real)
    (tensorOrderVolume : (Fin n -> Place) -> Real) : Prop :=
  ∀ choice, tensorVolume choice =
    Src.CoreLayer.WeightedAvg.betaSum n factorVolume choice +
      tensorOrderVolume choice

def NonarchTensorOrderVolumeNonpositive
    {Place : Type uPlace} {n : Nat}
    (tensorOrderVolume : (Fin n -> Place) -> Real) : Prop :=
  ∀ choice, tensorOrderVolume choice ≤ 0

theorem nonarch_tensor_volume_le_factor_sum
    {Place : Type uPlace} (n : Nat)
    (tensorVolume : (Fin n -> Place) -> Real)
    (factorVolume : Place -> Real)
    (tensorOrderVolume : (Fin n -> Place) -> Real)
    (hdecomp : NonarchTensorVolumeDecomposes n tensorVolume
      factorVolume tensorOrderVolume)
    (horder : NonarchTensorOrderVolumeNonpositive tensorOrderVolume)
    (choice : Fin n -> Place) :
    tensorVolume choice ≤
      Src.CoreLayer.WeightedAvg.betaSum n factorVolume choice := by
  rw [hdecomp choice]
  linarith [horder choice]

theorem nonarch_tensor_pure_factorwise_iff_order_residual_zero
    {Place : Type uPlace} (n : Nat)
    (tensorVolume : (Fin n -> Place) -> Real)
    (factorVolume : Place -> Real)
    (tensorOrderVolume : (Fin n -> Place) -> Real)
    (hdecomp : NonarchTensorVolumeDecomposes n tensorVolume
      factorVolume tensorOrderVolume)
    (choice : Fin n -> Place) :
    tensorVolume choice =
        Src.CoreLayer.WeightedAvg.betaSum n factorVolume choice ↔
      tensorOrderVolume choice = 0 := by
  rw [hdecomp choice]
  constructor <;> intro h
  · linarith
  · rw [h, add_zero]

noncomputable def nonarchTensorAnchorCorrection
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (n : Nat) (tensorOrderVolume : (Fin n -> Place) -> Real)
    (choice : Fin n -> Place) : Real :=
  -(nonarchChoiceMonoAnchorValue D n choice + tensorOrderVolume choice)

theorem nonarch_tensor_anchor_correction_calibrates_decomposition
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (n : Nat) (tensorVolume tensorOrderVolume : (Fin n -> Place) -> Real)
    (hdecomp : NonarchTensorVolumeDecomposes n tensorVolume
      (nonarchLocalMonoAnchorValue D) tensorOrderVolume)
    (choice : Fin n -> Place) :
    tensorVolume choice +
      nonarchTensorAnchorCorrection D n tensorOrderVolume choice = 0 := by
  rw [hdecomp choice]
  unfold nonarchTensorAnchorCorrection nonarchChoiceMonoAnchorValue
  ring

theorem nonarch_local_anchor_correction_eq_neg_mono_value
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (v : Place) :
    nonarchLocalAnchorCorrection D v = -nonarchLocalMonoAnchorValue D v := by
  rfl

theorem nonarch_pure_factorwise_correction_eq_neg_mono_sum
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (n : Nat) (choice : Fin n -> Place) :
    nonarchPureFactorwiseAnchorCorrection D n choice =
      -nonarchChoiceMonoAnchorValue D n choice := by
  classical
  simp [nonarchPureFactorwiseAnchorCorrection,
    nonarchChoiceMonoAnchorValue, Src.CoreLayer.WeightedAvg.betaSum,
    nonarch_local_anchor_correction_eq_neg_mono_value]

theorem nonarch_tensor_anchor_correction_eq_pure_minus_residual
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (n : Nat) (tensorOrderVolume : (Fin n -> Place) -> Real)
    (choice : Fin n -> Place) :
    nonarchTensorAnchorCorrection D n tensorOrderVolume choice =
      nonarchPureFactorwiseAnchorCorrection D n choice -
        tensorOrderVolume choice := by
  rw [nonarch_pure_factorwise_correction_eq_neg_mono_sum]
  unfold nonarchTensorAnchorCorrection
  ring

theorem nonarch_tensor_correction_eq_pure_iff_residual_zero
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (n : Nat) (tensorOrderVolume : (Fin n -> Place) -> Real)
    (choice : Fin n -> Place) :
    nonarchTensorAnchorCorrection D n tensorOrderVolume choice =
        nonarchPureFactorwiseAnchorCorrection D n choice ↔
      tensorOrderVolume choice = 0 := by
  rw [nonarch_tensor_anchor_correction_eq_pure_minus_residual]
  constructor <;> intro h
  · linarith
  · rw [h, sub_zero]

def negativeResidualTensorVolume (_ : Fin 1 -> Unit) : Real := -1

def zeroResidualFactorVolume (_ : Unit) : Real := 0

def negativeTensorOrderVolume (_ : Fin 1 -> Unit) : Real := -1

theorem negative_residual_tensor_decomposes :
    NonarchTensorVolumeDecomposes 1 negativeResidualTensorVolume
      zeroResidualFactorVolume negativeTensorOrderVolume := by
  intro choice
  norm_num [negativeResidualTensorVolume, zeroResidualFactorVolume,
    negativeTensorOrderVolume, Src.CoreLayer.WeightedAvg.betaSum]

theorem negative_tensor_order_is_nonpositive :
    NonarchTensorOrderVolumeNonpositive negativeTensorOrderVolume := by
  intro choice
  norm_num [negativeTensorOrderVolume]

theorem nonpositive_tensor_residual_does_not_force_pure_factorization :
    NonarchTensorVolumeDecomposes 1 negativeResidualTensorVolume
        zeroResidualFactorVolume negativeTensorOrderVolume ∧
      NonarchTensorOrderVolumeNonpositive negativeTensorOrderVolume ∧
      negativeResidualTensorVolume (fun _ => ()) ≠
        Src.CoreLayer.WeightedAvg.betaSum 1 zeroResidualFactorVolume
          (fun _ => ()) := by
  refine ⟨negative_residual_tensor_decomposes,
    negative_tensor_order_is_nonpositive, ?_⟩
  norm_num [negativeResidualTensorVolume, zeroResidualFactorVolume,
    Src.CoreLayer.WeightedAvg.betaSum]

theorem full_choice_normalized_mean_factorwise_sum
    {Place : Type uPlace} [Fintype Place] [DecidableEq Place] [Nonempty Place]
    (n : Nat) (degree localValue : Place -> Real)
    (hdegree : PlaceDegreesPositive degree) :
    fullChoiceNormalizedMean (n + 1) degree
        (fun choice => Src.CoreLayer.WeightedAvg.betaSum
          (n + 1) localValue choice) =
      (n + 1 : Real) *
        (Src.CoreLayer.WeightedAvg.betaE localValue degree /
          Src.CoreLayer.WeightedAvg.lamE degree) := by
  simpa using full_choice_beta_sum_mean_eq (n + 1)
    (Nat.succ_pos n) degree localValue hdegree

theorem nonarch_pure_factorwise_correction_weighted_mean
    {Place : Type uPlace} [Fintype Place] [DecidableEq Place] [Nonempty Place]
    (D : NonarchPlaceCorrectionData Place)
    (n : Nat) (degree : Place -> Real)
    (hdegree : PlaceDegreesPositive degree) :
    fullChoiceNormalizedMean (n + 1) degree
        (nonarchPureFactorwiseAnchorCorrection D (n + 1)) =
      (n + 1 : Real) *
        (Src.CoreLayer.WeightedAvg.betaE
            (nonarchLocalAnchorCorrection D) degree /
          Src.CoreLayer.WeightedAvg.lamE degree) := by
  exact full_choice_normalized_mean_factorwise_sum n degree
    (nonarchLocalAnchorCorrection D) hdegree

theorem full_choice_normalized_mean_sub
    {Place : Type uPlace} [Fintype Place]
    (n : Nat) (degree : Place -> Real)
    (f g : (Fin n -> Place) -> Real) :
    fullChoiceNormalizedMean n degree (fun choice => f choice - g choice) =
      fullChoiceNormalizedMean n degree f -
        fullChoiceNormalizedMean n degree g := by
  classical
  unfold fullChoiceNormalizedMean
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

theorem nonarch_tensor_anchor_correction_weighted_mean
    {Place : Type uPlace} [Fintype Place] [DecidableEq Place] [Nonempty Place]
    (D : NonarchPlaceCorrectionData Place)
    (n : Nat) (degree : Place -> Real)
    (hdegree : PlaceDegreesPositive degree)
    (tensorOrderVolume : (Fin (n + 1) -> Place) -> Real) :
    fullChoiceNormalizedMean (n + 1) degree
        (nonarchTensorAnchorCorrection D (n + 1) tensorOrderVolume) =
      (n + 1 : Real) *
          (Src.CoreLayer.WeightedAvg.betaE
              (nonarchLocalAnchorCorrection D) degree /
            Src.CoreLayer.WeightedAvg.lamE degree) -
        fullChoiceNormalizedMean (n + 1) degree tensorOrderVolume := by
  rw [show nonarchTensorAnchorCorrection D (n + 1) tensorOrderVolume =
      fun choice =>
        nonarchPureFactorwiseAnchorCorrection D (n + 1) choice -
          tensorOrderVolume choice by
    funext choice
    exact nonarch_tensor_anchor_correction_eq_pure_minus_residual
      D (n + 1) tensorOrderVolume choice]
  rw [full_choice_normalized_mean_sub]
  rw [nonarch_pure_factorwise_correction_weighted_mean D n degree hdegree]

theorem nonarch_pure_factorwise_corrected_anchor_weighted_mean_zero
    {Place : Type uPlace} [Fintype Place]
    (D : NonarchPlaceCorrectionData Place)
    (n : Nat) (degree : Place -> Real) :
    fullChoiceNormalizedMean n degree (fun choice =>
        nonarchChoiceMonoAnchorValue D n choice +
          nonarchPureFactorwiseAnchorCorrection D n choice) = 0 := by
  classical
  have hprofile : (fun choice : Fin n -> Place =>
      nonarchChoiceMonoAnchorValue D n choice +
        nonarchPureFactorwiseAnchorCorrection D n choice) = (fun _ => 0) := by
    funext choice
    exact nonarch_pure_factorwise_correction_calibrates_sum_zero D n choice
  rw [hprofile]
  simp [fullChoiceNormalizedMean]

def boolNonarchPlaceCorrectionData : NonarchPlaceCorrectionData Bool where
  rationalPrime := 2
  pStarExponent := 2
  ramificationIndex := fun _ => 1
  residueDegree := fun _ => 1
  torsionPExponent
    | false => 0
    | true => 1

theorem bool_false_local_anchor_correction_eq_neg_log_two :
    nonarchLocalAnchorCorrection boolNonarchPlaceCorrectionData false =
      -Real.log 2 := by
  norm_num [nonarchLocalAnchorCorrection,
    nonarchMonoIntegralAnchorCorrection, nonarchMonoIntegralLogVolume,
    boolNonarchPlaceCorrectionData]

theorem bool_true_local_anchor_correction_zero :
    nonarchLocalAnchorCorrection boolNonarchPlaceCorrectionData true = 0 := by
  norm_num [nonarchLocalAnchorCorrection,
    nonarchMonoIntegralAnchorCorrection, nonarchMonoIntegralLogVolume,
    boolNonarchPlaceCorrectionData]

theorem bool_local_anchor_correction_nonconstant :
    nonarchLocalAnchorCorrection boolNonarchPlaceCorrectionData false ≠
      nonarchLocalAnchorCorrection boolNonarchPlaceCorrectionData true := by
  rw [bool_false_local_anchor_correction_eq_neg_log_two,
    bool_true_local_anchor_correction_zero]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

abbrev boolAllFalseChoice (n : Nat) : Fin n -> Bool := fun _ => false

abbrev boolAllTrueChoice (n : Nat) : Fin n -> Bool := fun _ => true

theorem bool_one_factor_corrections_differ :
    nonarchPureFactorwiseAnchorCorrection boolNonarchPlaceCorrectionData 1
        (boolAllFalseChoice 1) ≠
      nonarchPureFactorwiseAnchorCorrection boolNonarchPlaceCorrectionData 1
        (boolAllTrueChoice 1) := by
  simpa [nonarchPureFactorwiseAnchorCorrection,
    Src.CoreLayer.WeightedAvg.betaSum] using
      bool_local_anchor_correction_nonconstant

theorem bool_factorwise_correction_has_no_single_stage_constant :
    ¬ ∃ k : Real, ∀ choice : Fin 1 -> Bool,
      nonarchPureFactorwiseAnchorCorrection
        boolNonarchPlaceCorrectionData 1 choice = k := by
  rintro ⟨k, hk⟩
  apply bool_one_factor_corrections_differ
  exact (hk (boolAllFalseChoice 1)).trans
    (hk (boolAllTrueChoice 1)).symm

theorem bool_two_false_factors_double_the_local_correction :
    nonarchPureFactorwiseAnchorCorrection boolNonarchPlaceCorrectionData 2
        (boolAllFalseChoice 2) =
      2 * nonarchLocalAnchorCorrection boolNonarchPlaceCorrectionData false := by
  norm_num [nonarchPureFactorwiseAnchorCorrection,
    Src.CoreLayer.WeightedAvg.betaSum, boolAllFalseChoice]

theorem bool_one_and_two_factor_false_corrections_differ :
    nonarchPureFactorwiseAnchorCorrection boolNonarchPlaceCorrectionData 1
        (boolAllFalseChoice 1) ≠
      nonarchPureFactorwiseAnchorCorrection boolNonarchPlaceCorrectionData 2
        (boolAllFalseChoice 2) := by
  rw [bool_two_false_factors_double_the_local_correction]
  simp only [nonarchPureFactorwiseAnchorCorrection,
    Src.CoreLayer.WeightedAvg.betaSum, Fin.sum_univ_one]
  have hnonzero :
      nonarchLocalAnchorCorrection boolNonarchPlaceCorrectionData false ≠ 0 := by
    rw [bool_false_local_anchor_correction_eq_neg_log_two]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  intro h
  apply hnonzero
  linarith

end CitedLV.Theorem311
