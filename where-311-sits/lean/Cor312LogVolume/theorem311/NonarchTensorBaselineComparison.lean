import Cor312LogVolume.theorem311.NonarchFactorwisePacketCorrection

namespace CitedLV.Theorem311

universe uPlace

def NonarchCorrectionCalibrates
    {Place : Type uPlace} {n : Nat}
    (source baseline correction : (Fin n -> Place) -> Real) : Prop :=
  forall choice, source choice + correction choice = baseline choice

def nonarchCorrectionToBaseline
    {Place : Type uPlace} {n : Nat}
    (source baseline : (Fin n -> Place) -> Real)
    (choice : Fin n -> Place) : Real :=
  baseline choice - source choice

theorem nonarch_correction_to_baseline_calibrates
    {Place : Type uPlace} {n : Nat}
    (source baseline : (Fin n -> Place) -> Real) :
    NonarchCorrectionCalibrates source baseline
      (nonarchCorrectionToBaseline source baseline) := by
  intro choice
  unfold nonarchCorrectionToBaseline
  ring

theorem nonarch_calibrating_correction_is_unique
    {Place : Type uPlace} {n : Nat}
    (source baseline correction : (Fin n -> Place) -> Real)
    (hcal : NonarchCorrectionCalibrates source baseline correction)
    (choice : Fin n -> Place) :
    correction choice = nonarchCorrectionToBaseline source baseline choice := by
  unfold NonarchCorrectionCalibrates at hcal
  unfold nonarchCorrectionToBaseline
  linarith [hcal choice]

def nonarchRawTensorOrderBaseline
    {Place : Type uPlace} {n : Nat}
    (tensorOrderVolume : (Fin n -> Place) -> Real) :
    (Fin n -> Place) -> Real :=
  tensorOrderVolume

def nonarchRegularZeroBaseline
    {Place : Type uPlace} {n : Nat} : (Fin n -> Place) -> Real :=
  fun _ => 0

def NonarchMaximalOrderHasZeroVolume
    {Place : Type uPlace} {n : Nat}
    (maximalOrderVolume : (Fin n -> Place) -> Real) : Prop :=
  ∀ choice, maximalOrderVolume choice = 0

def NonarchRawOrderBelowMaximal
    {Place : Type uPlace} {n : Nat}
    (rawOrderVolume maximalOrderVolume : (Fin n -> Place) -> Real) : Prop :=
  ∀ choice, rawOrderVolume choice ≤ maximalOrderVolume choice

def NonarchRegularNormalizationAdapter
    {Place : Type uPlace} {n : Nat}
    (regularVolume maximalOrderVolume : (Fin n -> Place) -> Real) : Prop :=
  ∀ choice, regularVolume choice = maximalOrderVolume choice

def nonarchRawVsMaximalOrderResidual
    {Place : Type uPlace} {n : Nat}
    (rawOrderVolume maximalOrderVolume : (Fin n -> Place) -> Real)
    (choice : Fin n -> Place) : Real :=
  rawOrderVolume choice - maximalOrderVolume choice

def nonarchCorrectionToMaximalOrder
    {Place : Type uPlace} {n : Nat}
    (tensorVolume maximalOrderVolume : (Fin n -> Place) -> Real) :
    (Fin n -> Place) -> Real :=
  nonarchCorrectionToBaseline tensorVolume maximalOrderVolume

theorem nonarch_maximal_zero_profile_eq_regular_zero
    {Place : Type uPlace} {n : Nat}
    (maximalOrderVolume : (Fin n -> Place) -> Real)
    (hmax : NonarchMaximalOrderHasZeroVolume maximalOrderVolume) :
    maximalOrderVolume = nonarchRegularZeroBaseline := by
  funext choice
  exact hmax choice

theorem nonarch_regular_adapter_and_maximal_zero_give_regular_zero
    {Place : Type uPlace} {n : Nat}
    (regularVolume maximalOrderVolume : (Fin n -> Place) -> Real)
    (hadapter : NonarchRegularNormalizationAdapter regularVolume
      maximalOrderVolume)
    (hmax : NonarchMaximalOrderHasZeroVolume maximalOrderVolume)
    (choice : Fin n -> Place) :
    regularVolume choice = 0 := by
  rw [hadapter choice, hmax choice]

theorem nonarch_raw_vs_maximal_residual_nonpositive
    {Place : Type uPlace} {n : Nat}
    (rawOrderVolume maximalOrderVolume : (Fin n -> Place) -> Real)
    (hbelow : NonarchRawOrderBelowMaximal rawOrderVolume maximalOrderVolume)
    (choice : Fin n -> Place) :
    nonarchRawVsMaximalOrderResidual rawOrderVolume maximalOrderVolume choice ≤
      0 := by
  unfold nonarchRawVsMaximalOrderResidual
  linarith [hbelow choice]

def nonarchCorrectionToRawTensorOrder
    {Place : Type uPlace} {n : Nat}
    (tensorVolume tensorOrderVolume : (Fin n -> Place) -> Real) :
    (Fin n -> Place) -> Real :=
  nonarchCorrectionToBaseline tensorVolume
    (nonarchRawTensorOrderBaseline tensorOrderVolume)

def nonarchCorrectionToRegularZero
    {Place : Type uPlace} {n : Nat}
    (tensorVolume : (Fin n -> Place) -> Real) :
    (Fin n -> Place) -> Real :=
  nonarchCorrectionToBaseline tensorVolume nonarchRegularZeroBaseline

theorem nonarch_maximal_order_correction_eq_regular_zero_of_normalization
    {Place : Type uPlace} {n : Nat}
    (tensorVolume maximalOrderVolume : (Fin n -> Place) -> Real)
    (hmax : NonarchMaximalOrderHasZeroVolume maximalOrderVolume) :
    nonarchCorrectionToMaximalOrder tensorVolume maximalOrderVolume =
      nonarchCorrectionToRegularZero tensorVolume := by
  funext choice
  unfold nonarchCorrectionToMaximalOrder nonarchCorrectionToRegularZero
    nonarchCorrectionToBaseline nonarchRegularZeroBaseline
  rw [hmax choice]

theorem nonarch_maximal_minus_raw_correction_eq_neg_raw_vs_maximal
    {Place : Type uPlace} {n : Nat}
    (tensorVolume rawOrderVolume maximalOrderVolume :
      (Fin n -> Place) -> Real)
    (choice : Fin n -> Place) :
    nonarchCorrectionToMaximalOrder tensorVolume maximalOrderVolume choice -
        nonarchCorrectionToRawTensorOrder tensorVolume rawOrderVolume choice =
      -nonarchRawVsMaximalOrderResidual rawOrderVolume maximalOrderVolume
        choice := by
  unfold nonarchCorrectionToMaximalOrder
    nonarchCorrectionToRawTensorOrder nonarchCorrectionToBaseline
    nonarchRawTensorOrderBaseline nonarchRawVsMaximalOrderResidual
  ring

theorem nonarch_raw_tensor_order_correction_calibrates
    {Place : Type uPlace} {n : Nat}
    (tensorVolume tensorOrderVolume : (Fin n -> Place) -> Real) :
    NonarchCorrectionCalibrates tensorVolume
      (nonarchRawTensorOrderBaseline tensorOrderVolume)
      (nonarchCorrectionToRawTensorOrder tensorVolume tensorOrderVolume) := by
  exact nonarch_correction_to_baseline_calibrates _ _

theorem nonarch_regular_zero_correction_calibrates
    {Place : Type uPlace} {n : Nat}
    (tensorVolume : (Fin n -> Place) -> Real) :
    NonarchCorrectionCalibrates tensorVolume nonarchRegularZeroBaseline
      (nonarchCorrectionToRegularZero tensorVolume) := by
  exact nonarch_correction_to_baseline_calibrates _ _

theorem nonarch_raw_tensor_order_correction_of_decomposition
    {Place : Type uPlace} (n : Nat)
    (tensorVolume : (Fin n -> Place) -> Real)
    (factorVolume : Place -> Real)
    (tensorOrderVolume : (Fin n -> Place) -> Real)
    (hdecomp : NonarchTensorVolumeDecomposes n tensorVolume factorVolume
      tensorOrderVolume)
    (choice : Fin n -> Place) :
    nonarchCorrectionToRawTensorOrder tensorVolume tensorOrderVolume choice =
      -Src.CoreLayer.WeightedAvg.betaSum n factorVolume choice := by
  unfold nonarchCorrectionToRawTensorOrder nonarchCorrectionToBaseline
    nonarchRawTensorOrderBaseline
  rw [hdecomp choice]
  ring

theorem nonarch_regular_zero_correction_of_decomposition
    {Place : Type uPlace} (n : Nat)
    (tensorVolume : (Fin n -> Place) -> Real)
    (factorVolume : Place -> Real)
    (tensorOrderVolume : (Fin n -> Place) -> Real)
    (hdecomp : NonarchTensorVolumeDecomposes n tensorVolume factorVolume
      tensorOrderVolume)
    (choice : Fin n -> Place) :
    nonarchCorrectionToRegularZero tensorVolume choice =
      -Src.CoreLayer.WeightedAvg.betaSum n factorVolume choice -
        tensorOrderVolume choice := by
  unfold nonarchCorrectionToRegularZero nonarchCorrectionToBaseline
    nonarchRegularZeroBaseline
  rw [hdecomp choice]
  ring

theorem nonarch_regular_minus_raw_correction_eq_neg_residual
    {Place : Type uPlace} {n : Nat}
    (tensorVolume tensorOrderVolume : (Fin n -> Place) -> Real)
    (choice : Fin n -> Place) :
    nonarchCorrectionToRegularZero tensorVolume choice -
        nonarchCorrectionToRawTensorOrder tensorVolume tensorOrderVolume choice =
      -tensorOrderVolume choice := by
  unfold nonarchCorrectionToRegularZero nonarchCorrectionToRawTensorOrder
    nonarchCorrectionToBaseline nonarchRawTensorOrderBaseline
    nonarchRegularZeroBaseline
  ring

theorem nonarch_regular_and_raw_corrections_agree_iff_residual_zero
    {Place : Type uPlace} {n : Nat}
    (tensorVolume tensorOrderVolume : (Fin n -> Place) -> Real)
    (choice : Fin n -> Place) :
    nonarchCorrectionToRegularZero tensorVolume choice =
        nonarchCorrectionToRawTensorOrder tensorVolume tensorOrderVolume choice ↔
      tensorOrderVolume choice = 0 := by
  unfold nonarchCorrectionToRegularZero nonarchCorrectionToRawTensorOrder
    nonarchCorrectionToBaseline nonarchRawTensorOrderBaseline
    nonarchRegularZeroBaseline
  constructor <;> intro h
  · linarith
  · rw [h]

theorem nonarch_raw_correction_le_regular_of_residual_nonpositive
    {Place : Type uPlace} {n : Nat}
    (tensorVolume tensorOrderVolume : (Fin n -> Place) -> Real)
    (horder : NonarchTensorOrderVolumeNonpositive tensorOrderVolume)
    (choice : Fin n -> Place) :
    nonarchCorrectionToRawTensorOrder tensorVolume tensorOrderVolume choice <=
      nonarchCorrectionToRegularZero tensorVolume choice := by
  have hdiff := nonarch_regular_minus_raw_correction_eq_neg_residual
    tensorVolume tensorOrderVolume choice
  linarith [horder choice]

theorem nonarch_raw_correction_lt_regular_of_residual_negative
    {Place : Type uPlace} {n : Nat}
    (tensorVolume tensorOrderVolume : (Fin n -> Place) -> Real)
    (choice : Fin n -> Place)
    (hnegative : tensorOrderVolume choice < 0) :
    nonarchCorrectionToRawTensorOrder tensorVolume tensorOrderVolume choice <
      nonarchCorrectionToRegularZero tensorVolume choice := by
  have hdiff := nonarch_regular_minus_raw_correction_eq_neg_residual
    tensorVolume tensorOrderVolume choice
  linarith

theorem nonarch_raw_order_correction_eq_pure_factorwise
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (n : Nat) (tensorVolume tensorOrderVolume : (Fin n -> Place) -> Real)
    (hdecomp : NonarchTensorVolumeDecomposes n tensorVolume
      (nonarchLocalMonoAnchorValue D) tensorOrderVolume)
    (choice : Fin n -> Place) :
    nonarchCorrectionToRawTensorOrder tensorVolume tensorOrderVolume choice =
      nonarchPureFactorwiseAnchorCorrection D n choice := by
  calc
    nonarchCorrectionToRawTensorOrder tensorVolume tensorOrderVolume choice =
        -nonarchChoiceMonoAnchorValue D n choice := by
          exact nonarch_raw_tensor_order_correction_of_decomposition n
            tensorVolume (nonarchLocalMonoAnchorValue D) tensorOrderVolume
            hdecomp choice
    _ = nonarchPureFactorwiseAnchorCorrection D n choice :=
      (nonarch_pure_factorwise_correction_eq_neg_mono_sum D n choice).symm

theorem nonarch_regular_zero_correction_eq_whole_tensor
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (n : Nat) (tensorVolume tensorOrderVolume : (Fin n -> Place) -> Real)
    (hdecomp : NonarchTensorVolumeDecomposes n tensorVolume
      (nonarchLocalMonoAnchorValue D) tensorOrderVolume)
    (choice : Fin n -> Place) :
    nonarchCorrectionToRegularZero tensorVolume choice =
      nonarchTensorAnchorCorrection D n tensorOrderVolume choice := by
  unfold nonarchCorrectionToRegularZero nonarchCorrectionToBaseline
    nonarchRegularZeroBaseline nonarchTensorAnchorCorrection
    nonarchChoiceMonoAnchorValue
  rw [hdecomp choice]
  ring

theorem zero_normalized_regular_calibration_forces_whole_tensor_correction
    {Place : Type uPlace} (D : NonarchPlaceCorrectionData Place)
    (n : Nat)
    (tensorVolume regularVolume correction tensorOrderVolume :
      (Fin n -> Place) -> Real)
    (hdecomp : NonarchTensorVolumeDecomposes n tensorVolume
      (nonarchLocalMonoAnchorValue D) tensorOrderVolume)
    (hregular : forall choice, regularVolume choice = 0)
    (hcal : NonarchCorrectionCalibrates tensorVolume regularVolume correction)
    (choice : Fin n -> Place) :
    correction choice =
      nonarchTensorAnchorCorrection D n tensorOrderVolume choice := by
  have hcalChoice := hcal choice
  rw [hregular choice] at hcalChoice
  rw [hdecomp choice] at hcalChoice
  unfold nonarchTensorAnchorCorrection nonarchChoiceMonoAnchorValue
  linarith

theorem one_correction_calibrating_two_baselines_forces_equality
    {Place : Type uPlace} {n : Nat}
    (source baselineOne baselineTwo correction :
      (Fin n -> Place) -> Real)
    (hone : NonarchCorrectionCalibrates source baselineOne correction)
    (htwo : NonarchCorrectionCalibrates source baselineTwo correction)
    (choice : Fin n -> Place) :
    baselineOne choice = baselineTwo choice := by
  linarith [hone choice, htwo choice]

theorem negative_model_raw_tensor_order_correction_zero :
    nonarchCorrectionToRawTensorOrder negativeResidualTensorVolume
        negativeTensorOrderVolume (fun _ => ()) = 0 := by
  norm_num [nonarchCorrectionToRawTensorOrder,
    nonarchCorrectionToBaseline, nonarchRawTensorOrderBaseline,
    negativeResidualTensorVolume, negativeTensorOrderVolume]

theorem negative_model_regular_zero_correction_one :
    nonarchCorrectionToRegularZero negativeResidualTensorVolume
        (fun _ => ()) = 1 := by
  norm_num [nonarchCorrectionToRegularZero, nonarchCorrectionToBaseline,
    nonarchRegularZeroBaseline, negativeResidualTensorVolume]

theorem regular_zero_profile_has_maximal_zero_volume :
    NonarchMaximalOrderHasZeroVolume
      (nonarchRegularZeroBaseline : (Fin 1 -> Unit) -> Real) := by
  intro choice
  rfl

theorem negative_raw_order_is_below_regular_zero :
    NonarchRawOrderBelowMaximal negativeTensorOrderVolume
      (nonarchRegularZeroBaseline : (Fin 1 -> Unit) -> Real) := by
  intro choice
  norm_num [negativeTensorOrderVolume, nonarchRegularZeroBaseline]

theorem negative_raw_vs_regular_zero_residual_is_nonzero :
    nonarchRawVsMaximalOrderResidual negativeTensorOrderVolume
        (nonarchRegularZeroBaseline : (Fin 1 -> Unit) -> Real)
        (fun _ => ()) ≠ 0 := by
  norm_num [nonarchRawVsMaximalOrderResidual, negativeTensorOrderVolume,
    nonarchRegularZeroBaseline]

theorem negative_raw_order_is_not_regular_normalization_adapter :
    ¬ NonarchRegularNormalizationAdapter negativeTensorOrderVolume
      (nonarchRegularZeroBaseline : (Fin 1 -> Unit) -> Real) := by
  intro hadapter
  have h := hadapter (fun _ => ())
  norm_num [negativeTensorOrderVolume, nonarchRegularZeroBaseline] at h

theorem negative_model_baselines_are_distinct :
    nonarchRawTensorOrderBaseline negativeTensorOrderVolume (fun _ => ()) ≠
      (nonarchRegularZeroBaseline : (Fin 1 -> Unit) -> Real) (fun _ => ()) := by
  norm_num [nonarchRawTensorOrderBaseline, nonarchRegularZeroBaseline,
    negativeTensorOrderVolume]

theorem negative_model_corrections_are_distinct :
    nonarchCorrectionToRawTensorOrder negativeResidualTensorVolume
        negativeTensorOrderVolume (fun _ => ()) ≠
      nonarchCorrectionToRegularZero negativeResidualTensorVolume
        (fun _ => ()) := by
  rw [negative_model_raw_tensor_order_correction_zero,
    negative_model_regular_zero_correction_one]
  norm_num

theorem negative_model_has_no_correction_calibrating_both_baselines :
    ¬ ∃ correction : (Fin 1 -> Unit) -> Real,
      NonarchCorrectionCalibrates negativeResidualTensorVolume
          (nonarchRawTensorOrderBaseline negativeTensorOrderVolume) correction ∧
        NonarchCorrectionCalibrates negativeResidualTensorVolume
          nonarchRegularZeroBaseline correction := by
  rintro ⟨correction, hraw, hregular⟩
  exact negative_model_baselines_are_distinct
    (one_correction_calibrating_two_baselines_forces_equality
      negativeResidualTensorVolume
      (nonarchRawTensorOrderBaseline negativeTensorOrderVolume)
      nonarchRegularZeroBaseline correction hraw hregular (fun _ => ()))

end CitedLV.Theorem311
