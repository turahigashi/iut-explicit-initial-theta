import Cor312LogVolume.theorem311.PacketRegionTwoLayerMean

namespace CitedLV.Theorem311

open scoped BigOperators TensorProduct

universe uBase uAbove uLabel uK

namespace Prop17

export Src.CoreLayer.WeightedAvg
  (lamProd betaSum lamE betaE betaE_mul_lamE_pow weighted_average)

end Prop17

theorem prop17_coordinate_factorization
    {E : Type uAbove} [Fintype E] [DecidableEq E] [Nonempty E]
    (n : Nat) (hn : 0 < n) (degree beta : E -> Real) (i : Fin n) :
    Prop17.betaE beta degree * Prop17.lamE degree ^ (n - 1) =
      ∑ choice : Fin n -> E,
        beta (choice i) * Prop17.lamProd n degree choice := by
  cases n with
  | zero => omega
  | succ m =>
      simpa using
        (Prop17.betaE_mul_lamE_pow m degree beta i)

theorem full_choice_beta_sum_mean_eq
    {E : Type uAbove} [Fintype E] [DecidableEq E] [Nonempty E]
    (n : Nat) (hn : 0 < n) (degree beta : E -> Real)
    (hdegree : PlaceDegreesPositive degree) :
    fullChoiceNormalizedMean n degree (Prop17.betaSum n beta) =
      (n : Real) * (Prop17.betaE beta degree / Prop17.lamE degree) := by
  have hprop := Prop17.weighted_average n degree beta hdegree hn
    (prop17_coordinate_factorization n hn degree beta)
  simpa [fullChoiceNormalizedMean, choiceDegreeProduct, choiceDegreeMass,
    mul_comm] using hprop

theorem full_choice_normalized_mean_mono
    {E : Type uAbove} [Fintype E] [Nonempty E]
    (n : Nat) (degree : E -> Real)
    (actual upper : (Fin n -> E) -> Real)
    (hdegree : PlaceDegreesPositive degree)
    (hupper : forall choice, actual choice <= upper choice) :
    fullChoiceNormalizedMean n degree actual <=
      fullChoiceNormalizedMean n degree upper := by
  have hmass : 0 < choiceDegreeMass n degree :=
    choice_degree_mass_pos n degree hdegree
  unfold fullChoiceNormalizedMean
  apply (div_le_div_iff_of_pos_right hmass).2
  apply Finset.sum_le_sum
  intro choice _
  exact mul_le_mul_of_nonneg_left (hupper choice)
    (le_of_lt (choice_degree_product_pos n degree hdegree choice))

theorem full_choice_actual_le_prop17_bound
    {E : Type uAbove} [Fintype E] [DecidableEq E] [Nonempty E]
    (n : Nat) (hn : 0 < n) (degree beta : E -> Real)
    (actual : (Fin n -> E) -> Real)
    (hdegree : PlaceDegreesPositive degree)
    (hactual : forall choice, actual choice <= Prop17.betaSum n beta choice) :
    fullChoiceNormalizedMean n degree actual <=
      (n : Real) * (Prop17.betaE beta degree / Prop17.lamE degree) := by
  calc
    fullChoiceNormalizedMean n degree actual <=
        fullChoiceNormalizedMean n degree (Prop17.betaSum n beta) :=
      full_choice_normalized_mean_mono n degree actual
        (Prop17.betaSum n beta) hdegree hactual
    _ = (n : Real) *
        (Prop17.betaE beta degree / Prop17.lamE degree) :=
      full_choice_beta_sum_mean_eq n hn degree beta hdegree

theorem sourceSpan_region_mean_le_prop17_bound
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base)
    [Fintype (Above vQ)] [DecidableEq (Above vQ)] [Nonempty (Above vQ)]
    (region : Set (SourceSpanTensorPacketQ P j vQ))
    (degree beta : Above vQ -> Real)
    (componentLogVolume :
      (choice : SourcePacketChoice Above arity j vQ) ->
      Set (SourceSpanChoiceTensor P j vQ choice) -> Real)
    (hdegree : PlaceDegreesPositive degree)
    (hcomponent : forall choice,
      componentLogVolume choice
          (decompositionChoiceRegion P j vQ region choice) <=
        Prop17.betaSum (arity j + 1) beta choice) :
    sourceSpanRegionDegreeWeightedMean P j vQ region degree
        componentLogVolume <=
      ((arity j + 1 : Nat) : Real) *
        (Prop17.betaE beta degree / Prop17.lamE degree) := by
  exact full_choice_actual_le_prop17_bound (arity j + 1)
    (Nat.succ_pos (arity j)) degree beta
    (fun choice => componentLogVolume choice
      (decompositionChoiceRegion P j vQ region choice))
    hdegree hcomponent

theorem ordinaryFinMean_mono
    {n : Nat} (actual upper : Fin n -> Real)
    (h : forall j, actual j <= upper j) :
    ordinaryFinMean actual <= ordinaryFinMean upper := by
  unfold ordinaryFinMean
  apply mul_le_mul_of_nonneg_left _
    (by positivity : 0 <= (1 / (n : Real)))
  exact Finset.sum_le_sum (fun j _ => h j)

theorem outer_mean_of_inner_bounds
    {n : Nat} (actual upper : Fin n -> Real)
    (h : forall j, actual j <= upper j) :
    ordinaryFinMean actual <= ordinaryFinMean upper :=
  ordinaryFinMean_mono actual upper h

def sourceLabelOfOuter {lStar : Nat} (k : Fin lStar) : Nat := k.val + 1

def tupleArityOfOuter {lStar : Nat} (k : Fin lStar) : Nat :=
  sourceLabelOfOuter k + 1

theorem tuple_arity_of_outer_eq {lStar : Nat} (k : Fin lStar) :
    tupleArityOfOuter k = k.val + 2 := by
  rfl

noncomputable def fixedJQUpperBound
    (l q : Real) (sourceJ : Nat) : Real :=
  -(CitedLV.Procession.sqScaled q sourceJ / (2 * l))

theorem outer_q_upper_bound_coefficient
    (q : Real) (lStar : Nat) (hlStar : 1 <= lStar) :
    ordinaryFinMean (fun k : Fin lStar =>
      fixedJQUpperBound (2 * (lStar : Real) + 1) q
        (sourceLabelOfOuter k)) =
      -(((2 * (lStar : Real) + 1) + 1) / 24 * q) := by
  have hpositive :
      ordinaryFinMean (fun k : Fin lStar =>
        CitedLV.Procession.sqScaled q (k.val + 1) /
          (2 * (2 * (lStar : Real) + 1))) =
        ((2 * (lStar : Real) + 1) + 1) / 24 * q := by
    have hdiv :
        ordinaryFinMean (fun k : Fin lStar =>
          CitedLV.Procession.sqScaled q (k.val + 1) /
            (2 * (2 * (lStar : Real) + 1))) =
          ordinaryFinMean (fun k : Fin lStar =>
            CitedLV.Procession.sqScaled q (k.val + 1)) /
              (2 * (2 * (lStar : Real) + 1)) := by
      unfold ordinaryFinMean
      rw [← Finset.sum_div]
      ring
    rw [hdiv, ordinaryFinMean_sqScaled_eq_processionAvg]
    exact CitedLV.Procession.procession_normalized_value q lStar hlStar
  calc
    ordinaryFinMean (fun k : Fin lStar =>
        fixedJQUpperBound (2 * (lStar : Real) + 1) q
          (sourceLabelOfOuter k)) =
        -ordinaryFinMean (fun k : Fin lStar =>
          CitedLV.Procession.sqScaled q (k.val + 1) /
            (2 * (2 * (lStar : Real) + 1))) := by
      unfold ordinaryFinMean fixedJQUpperBound sourceLabelOfOuter
      rw [Finset.sum_neg_distrib]
      ring
    _ = -(((2 * (lStar : Real) + 1) + 1) / 24 * q) := by
      rw [hpositive]

def strictUnitDegree (_ : Unit) : Real := 1

def strictActualChoice (_ : Fin 2 -> Unit) : Real := 1

def strictUnitBeta (_ : Unit) : Real := 1

theorem strict_actual_is_componentwise_bounded (choice : Fin 2 -> Unit) :
    strictActualChoice choice <= Prop17.betaSum 2 strictUnitBeta choice := by
  norm_num [strictActualChoice, strictUnitBeta, Prop17.betaSum]

theorem strict_actual_choice_mean_is_one :
    fullChoiceNormalizedMean 2 strictUnitDegree strictActualChoice = 1 := by
  norm_num [fullChoiceNormalizedMean, choiceDegreeProduct, choiceDegreeMass,
    Prop17.lamProd, strictUnitDegree, strictActualChoice]

theorem strict_beta_tuple_mean_is_two :
    fullChoiceNormalizedMean 2 strictUnitDegree
        (Prop17.betaSum 2 strictUnitBeta) = 2 := by
  norm_num [fullChoiceNormalizedMean, choiceDegreeProduct, choiceDegreeMass,
    Prop17.lamProd, Prop17.betaSum, strictUnitDegree, strictUnitBeta]

theorem strict_component_bound_does_not_give_mean_equality :
    fullChoiceNormalizedMean 2 strictUnitDegree strictActualChoice ≠
      fullChoiceNormalizedMean 2 strictUnitDegree
        (Prop17.betaSum 2 strictUnitBeta) := by
  rw [strict_actual_choice_mean_is_one, strict_beta_tuple_mean_is_two]
  norm_num

end CitedLV.Theorem311
