import Cor312LogVolume.theorem311.Prop17PacketUpperBound

namespace CitedLV.Theorem311

open scoped BigOperators

universe uPlace

noncomputable def normalizedPlaceMean
    {E : Type uPlace} [Fintype E]
    (degree value : E -> Real) : Real :=
  Prop17.betaE value degree / Prop17.lamE degree

theorem normalizedPlaceMean_add
    {E : Type uPlace} [Fintype E]
    (degree f g : E -> Real) :
    normalizedPlaceMean degree (fun e => f e + g e) =
      normalizedPlaceMean degree f + normalizedPlaceMean degree g := by
  classical
  unfold normalizedPlaceMean Prop17.betaE
  simp only [add_mul, Finset.sum_add_distrib]
  ring

theorem normalizedPlaceMean_sub
    {E : Type uPlace} [Fintype E]
    (degree f g : E -> Real) :
    normalizedPlaceMean degree (fun e => f e - g e) =
      normalizedPlaceMean degree f - normalizedPlaceMean degree g := by
  classical
  unfold normalizedPlaceMean Prop17.betaE
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

theorem normalizedPlaceMean_scale
    {E : Type uPlace} [Fintype E]
    (degree f : E -> Real) (a : Real) :
    normalizedPlaceMean degree (fun e => a * f e) =
      a * normalizedPlaceMean degree f := by
  classical
  unfold normalizedPlaceMean Prop17.betaE
  rw [show (∑ e, a * f e * degree e) =
      a * (∑ e, f e * degree e) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring]
  ring

theorem normalizedPlaceMean_const
    {E : Type uPlace} [Fintype E] [Nonempty E]
    (degree : E -> Real) (hdegree : PlaceDegreesPositive degree)
    (c : Real) :
    normalizedPlaceMean degree (fun _ => c) = c := by
  have hmass : 0 < ∑ e, degree e := by
    exact Finset.sum_pos (fun e _ => hdegree e) Finset.univ_nonempty
  classical
  unfold normalizedPlaceMean Prop17.betaE Prop17.lamE
  rw [show (∑ e, c * degree e) = c * (∑ e, degree e) by
    rw [Finset.mul_sum]]
  exact mul_div_cancel_right₀ c (ne_of_gt hmass)

noncomputable def specialNonarchLocalQScale
    (l : Real) (sourceJ : Nat) : Real :=
  ((sourceJ : Real) ^ 2) /
    (2 * l * ((sourceJ : Real) + 1))

noncomputable def specialNonarchOneFactorBeta
    {E : Type uPlace}
    (l : Real) (sourceJ : Nat)
    (d q : E -> Real) (primeTerm correction : Real) : E -> Real :=
  fun e =>
    (d e - specialNonarchLocalQScale l sourceJ * q e) +
      (primeTerm / ((sourceJ : Real) + 1) + 4 * correction)

theorem normalized_specialNonarchOneFactorBeta
    {E : Type uPlace} [Fintype E] [Nonempty E]
    (l : Real) (sourceJ : Nat)
    (degree d q : E -> Real) (primeTerm correction : Real)
    (hdegree : PlaceDegreesPositive degree) :
    normalizedPlaceMean degree
        (specialNonarchOneFactorBeta l sourceJ d q primeTerm correction) =
      normalizedPlaceMean degree d -
        specialNonarchLocalQScale l sourceJ *
          normalizedPlaceMean degree q +
        (primeTerm / ((sourceJ : Real) + 1) + 4 * correction) := by
  unfold specialNonarchOneFactorBeta
  rw [normalizedPlaceMean_add, normalizedPlaceMean_sub,
    normalizedPlaceMean_scale, normalizedPlaceMean_const degree hdegree]

noncomputable def specialNonarchFixedJUpperBound
    (l : Real) (sourceJ : Nat)
    (dBar qBar primeTerm correction : Real) : Real :=
  ((sourceJ : Real) + 1) * dBar -
    ((sourceJ : Real) ^ 2) / (2 * l) * qBar +
    primeTerm + 4 * ((sourceJ : Real) + 1) * correction

theorem specialNonarch_beta_tuple_mean_eq_fixedJ_bound
    {E : Type uPlace} [Fintype E] [DecidableEq E] [Nonempty E]
    (l : Real) (hl : l ≠ 0) (sourceJ : Nat)
    (degree d q : E -> Real) (primeTerm correction : Real)
    (hdegree : PlaceDegreesPositive degree) :
    fullChoiceNormalizedMean (sourceJ + 1) degree
        (Prop17.betaSum (sourceJ + 1)
          (specialNonarchOneFactorBeta l sourceJ d q
            primeTerm correction)) =
      specialNonarchFixedJUpperBound l sourceJ
        (normalizedPlaceMean degree d)
        (normalizedPlaceMean degree q) primeTerm correction := by
  rw [full_choice_beta_sum_mean_eq (sourceJ + 1)
    (Nat.succ_pos sourceJ) degree
    (specialNonarchOneFactorBeta l sourceJ d q primeTerm correction)
    hdegree]
  rw [show Prop17.betaE
      (specialNonarchOneFactorBeta l sourceJ d q primeTerm correction)
        degree / Prop17.lamE degree =
      normalizedPlaceMean degree
        (specialNonarchOneFactorBeta l sourceJ d q primeTerm correction) by
    rfl]
  rw [normalized_specialNonarchOneFactorBeta l sourceJ degree d q
    primeTerm correction hdegree]
  unfold specialNonarchFixedJUpperBound specialNonarchLocalQScale
  have hj : ((sourceJ : Real) + 1) ≠ 0 := by positivity
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp [hl, hj]
  ring

theorem specialNonarch_actual_mean_le_fixedJ_bound
    {E : Type uPlace} [Fintype E] [DecidableEq E] [Nonempty E]
    (l : Real) (hl : l ≠ 0) (sourceJ : Nat)
    (degree d q : E -> Real) (primeTerm correction : Real)
    (actual : (Fin (sourceJ + 1) -> E) -> Real)
    (hdegree : PlaceDegreesPositive degree)
    (hactual : forall choice,
      actual choice <= Prop17.betaSum (sourceJ + 1)
        (specialNonarchOneFactorBeta l sourceJ d q
          primeTerm correction) choice) :
    fullChoiceNormalizedMean (sourceJ + 1) degree actual <=
      specialNonarchFixedJUpperBound l sourceJ
        (normalizedPlaceMean degree d)
        (normalizedPlaceMean degree q) primeTerm correction := by
  calc
    fullChoiceNormalizedMean (sourceJ + 1) degree actual <=
        fullChoiceNormalizedMean (sourceJ + 1) degree
          (Prop17.betaSum (sourceJ + 1)
            (specialNonarchOneFactorBeta l sourceJ d q
              primeTerm correction)) :=
      full_choice_normalized_mean_mono (sourceJ + 1) degree actual _
        hdegree hactual
    _ = specialNonarchFixedJUpperBound l sourceJ
        (normalizedPlaceMean degree d)
        (normalizedPlaceMean degree q) primeTerm correction :=
      specialNonarch_beta_tuple_mean_eq_fixedJ_bound l hl sourceJ degree
        d q primeTerm correction hdegree

theorem ordinaryFinMean_add
    {n : Nat} (f g : Fin n -> Real) :
    ordinaryFinMean (fun j => f j + g j) =
      ordinaryFinMean f + ordinaryFinMean g := by
  unfold ordinaryFinMean
  rw [Finset.sum_add_distrib]
  ring

theorem ordinaryFinMean_sub
    {n : Nat} (f g : Fin n -> Real) :
    ordinaryFinMean (fun j => f j - g j) =
      ordinaryFinMean f - ordinaryFinMean g := by
  unfold ordinaryFinMean
  rw [Finset.sum_sub_distrib]
  ring

theorem ordinaryFinMean_scale
    {n : Nat} (a : Real) (f : Fin n -> Real) :
    ordinaryFinMean (fun j => a * f j) =
      a * ordinaryFinMean f := by
  unfold ordinaryFinMean
  rw [show (∑ j, a * f j) = a * ∑ j, f j by
    rw [Finset.mul_sum]]
  ring

theorem ordinaryFinMean_const
    {n : Nat} (hn : 0 < n) (c : Real) :
    ordinaryFinMean (fun _ : Fin n => c) = c := by
  unfold ordinaryFinMean
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hnR : (n : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnR]

theorem ordinaryFinMean_tupleArity
    (lStar : Nat) (hlStar : 1 <= lStar) :
    ordinaryFinMean (fun k : Fin lStar =>
      ((tupleArityOfOuter k : Nat) : Real)) =
      ((2 * (lStar : Real) + 1) + 5) / 4 := by
  have hlabel :
      ordinaryFinMean (fun k : Fin lStar =>
        ((sourceLabelOfOuter k : Nat) : Real)) =
        (1 / 2) * ((lStar : Real) + 1) := by
    unfold ordinaryFinMean sourceLabelOfOuter
    rw [show (∑ k : Fin lStar, ((k.val + 1 : Nat) : Real)) =
        ∑ m ∈ Finset.range (lStar + 1), (m : Real) by
      calc
        (∑ k : Fin lStar, ((k.val + 1 : Nat) : Real)) =
            ∑ m ∈ Finset.range lStar, (((m + 1 : Nat) : Real)) :=
          Fin.sum_univ_eq_sum_range
            (fun m : Nat => (((m + 1 : Nat) : Real))) lStar
        _ = ∑ m ∈ Finset.range (lStar + 1), (m : Real) := by
          symm
          simpa using
            (Finset.sum_range_succ' (fun m : Nat => (m : Real)) lStar)]
    exact Src.CoreLayer.Elementary.E1 lStar hlStar
  rw [show (fun k : Fin lStar => ((tupleArityOfOuter k : Nat) : Real)) =
      (fun k : Fin lStar =>
        ((sourceLabelOfOuter k : Nat) : Real) + 1) by
    funext k
    norm_num [tupleArityOfOuter]]
  rw [ordinaryFinMean_add, hlabel,
    ordinaryFinMean_const (lt_of_lt_of_le Nat.zero_lt_one hlStar) 1]
  ring

theorem outer_specialNonarch_fixedJ_bounds
    (lStar : Nat) (hlStar : 1 <= lStar)
    (dBar qBar primeTerm correction : Real) :
    ordinaryFinMean (fun k : Fin lStar =>
      specialNonarchFixedJUpperBound (2 * (lStar : Real) + 1)
        (sourceLabelOfOuter k) dBar qBar primeTerm correction) =
      (((2 * (lStar : Real) + 1) + 5) / 4) * dBar -
        (((2 * (lStar : Real) + 1) + 1) / 24) * qBar +
        primeTerm +
        ((2 * (lStar : Real) + 1) + 5) * correction := by
  let factor : Fin lStar -> Real := fun k =>
    ((tupleArityOfOuter k : Nat) : Real)
  let qTerm : Fin lStar -> Real := fun k =>
    fixedJQUpperBound (2 * (lStar : Real) + 1) qBar
      (sourceLabelOfOuter k)
  have hfactor : ordinaryFinMean factor =
      ((2 * (lStar : Real) + 1) + 5) / 4 := by
    exact ordinaryFinMean_tupleArity lStar hlStar
  have hq : ordinaryFinMean qTerm =
      -(((2 * (lStar : Real) + 1) + 1) / 24 * qBar) := by
    exact outer_q_upper_bound_coefficient qBar lStar hlStar
  have hfun :
      (fun k : Fin lStar =>
        specialNonarchFixedJUpperBound (2 * (lStar : Real) + 1)
          (sourceLabelOfOuter k) dBar qBar primeTerm correction) =
      (fun k =>
        factor k * dBar + qTerm k + primeTerm +
          4 * factor k * correction) := by
    funext k
    dsimp [qTerm, factor]
    unfold specialNonarchFixedJUpperBound fixedJQUpperBound
      tupleArityOfOuter sourceLabelOfOuter CitedLV.Procession.sqScaled
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  rw [hfun]
  simp_rw [show (fun k : Fin lStar =>
      factor k * dBar + qTerm k + primeTerm +
        4 * factor k * correction) =
      (fun k =>
        (dBar * factor k + qTerm k) +
          ((fun _ : Fin lStar => primeTerm) k +
            (4 * correction) * factor k)) by
    funext k
    ring]
  rw [ordinaryFinMean_add, ordinaryFinMean_add,
    ordinaryFinMean_add, ordinaryFinMean_scale, ordinaryFinMean_scale,
    ordinaryFinMean_const (lt_of_lt_of_le Nat.zero_lt_one hlStar),
    hfactor, hq]
  ring

theorem outer_actual_le_specialNonarch_bound
    (lStar : Nat) (hlStar : 1 <= lStar)
    (dBar qBar primeTerm correction : Real)
    (actual : Fin lStar -> Real)
    (hactual : forall k,
      actual k <= specialNonarchFixedJUpperBound
        (2 * (lStar : Real) + 1) (sourceLabelOfOuter k)
        dBar qBar primeTerm correction) :
    ordinaryFinMean actual <=
      (((2 * (lStar : Real) + 1) + 5) / 4) * dBar -
        (((2 * (lStar : Real) + 1) + 1) / 24) * qBar +
        primeTerm +
        ((2 * (lStar : Real) + 1) + 5) * correction := by
  calc
    ordinaryFinMean actual <= ordinaryFinMean (fun k : Fin lStar =>
        specialNonarchFixedJUpperBound (2 * (lStar : Real) + 1)
          (sourceLabelOfOuter k) dBar qBar primeTerm correction) :=
      ordinaryFinMean_mono actual _ hactual
    _ = (((2 * (lStar : Real) + 1) + 5) / 4) * dBar -
        (((2 * (lStar : Real) + 1) + 1) / 24) * qBar +
        primeTerm +
        ((2 * (lStar : Real) + 1) + 5) * correction :=
      outer_specialNonarch_fixedJ_bounds lStar hlStar
        dBar qBar primeTerm correction

theorem outer_specialNonarch_discriminant_basis :
    ordinaryFinMean (fun k : Fin 2 =>
      specialNonarchFixedJUpperBound 5 (sourceLabelOfOuter k)
        1 0 0 0) = 5 / 2 := by
  norm_num [ordinaryFinMean, specialNonarchFixedJUpperBound,
    sourceLabelOfOuter, Fin.sum_univ_two]

theorem outer_specialNonarch_q_basis :
    ordinaryFinMean (fun k : Fin 2 =>
      specialNonarchFixedJUpperBound 5 (sourceLabelOfOuter k)
        0 1 0 0) = -(1 / 4) := by
  norm_num [ordinaryFinMean, specialNonarchFixedJUpperBound,
    sourceLabelOfOuter, Fin.sum_univ_two]

theorem outer_specialNonarch_prime_basis :
    ordinaryFinMean (fun k : Fin 2 =>
      specialNonarchFixedJUpperBound 5 (sourceLabelOfOuter k)
        0 0 1 0) = 1 := by
  norm_num [ordinaryFinMean, specialNonarchFixedJUpperBound,
    sourceLabelOfOuter, Fin.sum_univ_two]

theorem outer_specialNonarch_correction_basis :
    ordinaryFinMean (fun k : Fin 2 =>
      specialNonarchFixedJUpperBound 5 (sourceLabelOfOuter k)
        0 0 0 1) = 10 := by
  norm_num [ordinaryFinMean, specialNonarchFixedJUpperBound,
    sourceLabelOfOuter, Fin.sum_univ_two]

def strictOuterActual (k : Fin 2) : Real :=
  if k = 0 then 1 else 2

theorem strict_outer_actual_is_bounded (k : Fin 2) :
    strictOuterActual k <=
      specialNonarchFixedJUpperBound 5 (sourceLabelOfOuter k)
        1 0 0 0 := by
  fin_cases k <;>
    norm_num [strictOuterActual, specialNonarchFixedJUpperBound,
      sourceLabelOfOuter]

theorem strict_outer_actual_mean :
    ordinaryFinMean strictOuterActual = 3 / 2 := by
  norm_num [ordinaryFinMean, strictOuterActual, Fin.sum_univ_two]

theorem strict_outer_bound_remains_strict :
    ordinaryFinMean strictOuterActual <
      ordinaryFinMean (fun k : Fin 2 =>
        specialNonarchFixedJUpperBound 5 (sourceLabelOfOuter k)
          1 0 0 0) := by
  rw [strict_outer_actual_mean,
    outer_specialNonarch_discriminant_basis]
  norm_num

end CitedLV.Theorem311
