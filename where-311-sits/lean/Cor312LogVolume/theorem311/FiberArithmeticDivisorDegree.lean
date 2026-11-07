import Cor312LogVolume.theorem311.SpecialNonarchBetaProcession

namespace CitedLV.Theorem311

open scoped BigOperators

universe uBase uLift

structure FiniteLocalTowerRaw
    (BasePlace : Type uBase) (LiftPlace : BasePlace -> Type uLift) where
  baseLocalDegree : BasePlace -> Real
  liftLocalDegree : (v : BasePlace) -> LiftPlace v -> Real
  extensionDegree : Real

def TowerMassCompatible
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [Fintype BasePlace] [forall v, Fintype (LiftPlace v)]
    (T : FiniteLocalTowerRaw BasePlace LiftPlace) : Prop :=
  forall v,
    (∑ w : LiftPlace v, T.liftLocalDegree v w) =
      T.extensionDegree * T.baseLocalDegree v

def BaseLocalDegreesPositive
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    (T : FiniteLocalTowerRaw BasePlace LiftPlace) : Prop :=
  forall v, 0 < T.baseLocalDegree v

def LiftLocalDegreesPositive
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    (T : FiniteLocalTowerRaw BasePlace LiftPlace) : Prop :=
  forall v w, 0 < T.liftLocalDegree v w

structure FiberArithmeticDivisorRaw
    (BasePlace : Type uBase) (LiftPlace : BasePlace -> Type uLift) where
  coefficient : (v : BasePlace) -> LiftPlace v -> Real
  logResidueCard : (v : BasePlace) -> LiftPlace v -> Real

noncomputable def liftDivisorContribution
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    (A : FiberArithmeticDivisorRaw BasePlace LiftPlace)
    (v : BasePlace) (w : LiftPlace v) : Real :=
  A.coefficient v w * A.logResidueCard v w

noncomputable def groupedDivisorNumerator
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [forall v, Fintype (LiftPlace v)]
    (A : FiberArithmeticDivisorRaw BasePlace LiftPlace)
    (v : BasePlace) : Real :=
  ∑ w : LiftPlace v, liftDivisorContribution A v w

noncomputable def groupedLiftMass
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [forall v, Fintype (LiftPlace v)]
    (T : FiniteLocalTowerRaw BasePlace LiftPlace)
    (v : BasePlace) : Real :=
  ∑ w : LiftPlace v, T.liftLocalDegree v w

noncomputable def groupedNormalizedDegree
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [forall v, Fintype (LiftPlace v)]
    (T : FiniteLocalTowerRaw BasePlace LiftPlace)
    (A : FiberArithmeticDivisorRaw BasePlace LiftPlace)
    (v : BasePlace) : Real :=
  groupedDivisorNumerator A v / groupedLiftMass T v

noncomputable def totalFiberNormalizedDegree
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [Fintype BasePlace] [forall v, Fintype (LiftPlace v)]
    (T : FiniteLocalTowerRaw BasePlace LiftPlace)
    (A : FiberArithmeticDivisorRaw BasePlace LiftPlace) : Real :=
  (∑ v, groupedDivisorNumerator A v) /
    (∑ v, groupedLiftMass T v)

theorem total_divisor_numerator_eq_sigma
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [Fintype BasePlace] [forall v, Fintype (LiftPlace v)]
    (A : FiberArithmeticDivisorRaw BasePlace LiftPlace) :
    (∑ v, groupedDivisorNumerator A v) =
      ∑ x : Sigma LiftPlace, liftDivisorContribution A x.1 x.2 := by
  unfold groupedDivisorNumerator
  exact (Fintype.sum_sigma
    (fun x : Sigma LiftPlace => liftDivisorContribution A x.1 x.2)).symm

theorem total_lift_mass_eq_sigma
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [Fintype BasePlace] [forall v, Fintype (LiftPlace v)]
    (T : FiniteLocalTowerRaw BasePlace LiftPlace) :
    (∑ v, groupedLiftMass T v) =
      ∑ x : Sigma LiftPlace, T.liftLocalDegree x.1 x.2 := by
  unfold groupedLiftMass
  exact (Fintype.sum_sigma
    (fun x : Sigma LiftPlace => T.liftLocalDegree x.1 x.2)).symm

theorem tower_compatibility_identifies_grouped_mass
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [Fintype BasePlace] [forall v, Fintype (LiftPlace v)]
    (T : FiniteLocalTowerRaw BasePlace LiftPlace)
    (htower : TowerMassCompatible T) (v : BasePlace) :
    groupedLiftMass T v =
      T.extensionDegree * T.baseLocalDegree v :=
  htower v

theorem tower_compatibility_gives_positive_grouped_mass
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [Fintype BasePlace] [forall v, Fintype (LiftPlace v)]
    (T : FiniteLocalTowerRaw BasePlace LiftPlace)
    (htower : TowerMassCompatible T)
    (hext : 0 < T.extensionDegree)
    (hbase : BaseLocalDegreesPositive T) :
    PlaceDegreesPositive (groupedLiftMass T) := by
  intro v
  rw [tower_compatibility_identifies_grouped_mass T htower v]
  exact mul_pos hext (hbase v)

theorem grouped_mass_weighted_degree_eq_total
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [Fintype BasePlace] [Nonempty BasePlace]
    [forall v, Fintype (LiftPlace v)]
    (T : FiniteLocalTowerRaw BasePlace LiftPlace)
    (A : FiberArithmeticDivisorRaw BasePlace LiftPlace)
    (hmass : PlaceDegreesPositive (groupedLiftMass T)) :
    normalizedPlaceMean (groupedLiftMass T)
        (groupedNormalizedDegree T A) =
      totalFiberNormalizedDegree T A := by
  classical
  unfold normalizedPlaceMean Prop17.betaE Prop17.lamE
    groupedNormalizedDegree totalFiberNormalizedDegree
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  exact div_mul_cancel₀ _ (ne_of_gt (hmass v))

theorem normalizedPlaceMean_scale_degree
    {E : Type uBase} [Fintype E]
    (degree value : E -> Real) (scale : Real)
    (hscale : scale ≠ 0) (hmass : (∑ e, degree e) ≠ 0) :
    normalizedPlaceMean (fun e => scale * degree e) value =
      normalizedPlaceMean degree value := by
  classical
  unfold normalizedPlaceMean Prop17.betaE Prop17.lamE
  rw [show (∑ e, value e * (scale * degree e)) =
      scale * (∑ e, value e * degree e) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring]
  rw [show (∑ e, scale * degree e) = scale * (∑ e, degree e) by
    rw [Finset.mul_sum]]
  field_simp [hscale, hmass]

theorem base_weighted_grouped_degree_eq_total
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [Fintype BasePlace] [Nonempty BasePlace]
    [forall v, Fintype (LiftPlace v)]
    (T : FiniteLocalTowerRaw BasePlace LiftPlace)
    (A : FiberArithmeticDivisorRaw BasePlace LiftPlace)
    (htower : TowerMassCompatible T)
    (hext : 0 < T.extensionDegree)
    (hbase : BaseLocalDegreesPositive T) :
    normalizedPlaceMean T.baseLocalDegree
        (groupedNormalizedDegree T A) =
      totalFiberNormalizedDegree T A := by
  have hmass := tower_compatibility_gives_positive_grouped_mass
    T htower hext hbase
  have hbaseMass : (∑ v, T.baseLocalDegree v) ≠ 0 := by
    exact ne_of_gt (Finset.sum_pos (fun v _ => hbase v)
      Finset.univ_nonempty)
  have hfun : groupedLiftMass T =
      (fun v => T.extensionDegree * T.baseLocalDegree v) := by
    funext v
    exact tower_compatibility_identifies_grouped_mass T htower v
  calc
    normalizedPlaceMean T.baseLocalDegree
        (groupedNormalizedDegree T A) =
        normalizedPlaceMean (groupedLiftMass T)
          (groupedNormalizedDegree T A) := by
      rw [hfun]
      symm
      exact normalizedPlaceMean_scale_degree T.baseLocalDegree
        (groupedNormalizedDegree T A) T.extensionDegree
        (ne_of_gt hext) hbaseMass
    _ = totalFiberNormalizedDegree T A :=
      grouped_mass_weighted_degree_eq_total T A hmass

structure FiberDegreeClaim where
  value : Real

def FiberDegreeClaim.Correct
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [Fintype BasePlace] [forall v, Fintype (LiftPlace v)]
    (claim : FiberDegreeClaim)
    (T : FiniteLocalTowerRaw BasePlace LiftPlace)
    (A : FiberArithmeticDivisorRaw BasePlace LiftPlace) : Prop :=
  claim.value = totalFiberNormalizedDegree T A

theorem base_weighted_grouped_degree_eq_claim
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [Fintype BasePlace] [Nonempty BasePlace]
    [forall v, Fintype (LiftPlace v)]
    (T : FiniteLocalTowerRaw BasePlace LiftPlace)
    (A : FiberArithmeticDivisorRaw BasePlace LiftPlace)
    (claim : FiberDegreeClaim)
    (htower : TowerMassCompatible T)
    (hext : 0 < T.extensionDegree)
    (hbase : BaseLocalDegreesPositive T)
    (hclaim : claim.Correct T A) :
    normalizedPlaceMean T.baseLocalDegree
        (groupedNormalizedDegree T A) = claim.value := by
  rw [base_weighted_grouped_degree_eq_total T A htower hext hbase]
  exact hclaim.symm

theorem specialNonarch_beta_mean_from_fiber_claims
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [Fintype BasePlace] [DecidableEq BasePlace] [Nonempty BasePlace]
    [forall v, Fintype (LiftPlace v)]
    (T : FiniteLocalTowerRaw BasePlace LiftPlace)
    (D Q : FiberArithmeticDivisorRaw BasePlace LiftPlace)
    (dClaim qClaim : FiberDegreeClaim)
    (l : Real) (hl : l ≠ 0) (sourceJ : Nat)
    (primeTerm correction : Real)
    (htower : TowerMassCompatible T)
    (hext : 0 < T.extensionDegree)
    (hbase : BaseLocalDegreesPositive T)
    (hd : dClaim.Correct T D) (hq : qClaim.Correct T Q) :
    fullChoiceNormalizedMean (sourceJ + 1) T.baseLocalDegree
        (Prop17.betaSum (sourceJ + 1)
          (specialNonarchOneFactorBeta l sourceJ
            (groupedNormalizedDegree T D)
            (groupedNormalizedDegree T Q)
            primeTerm correction)) =
      specialNonarchFixedJUpperBound l sourceJ
        dClaim.value qClaim.value primeTerm correction := by
  rw [specialNonarch_beta_tuple_mean_eq_fixedJ_bound l hl sourceJ
    T.baseLocalDegree (groupedNormalizedDegree T D)
    (groupedNormalizedDegree T Q) primeTerm correction hbase]
  rw [base_weighted_grouped_degree_eq_claim T D dClaim htower hext hbase hd,
    base_weighted_grouped_degree_eq_claim T Q qClaim htower hext hbase hq]

theorem outer_specialNonarch_bound_from_fiber_claims
    {BasePlace : Type uBase} {LiftPlace : BasePlace -> Type uLift}
    [Fintype BasePlace] [Nonempty BasePlace]
    [forall v, Fintype (LiftPlace v)]
    (T : FiniteLocalTowerRaw BasePlace LiftPlace)
    (D Q : FiberArithmeticDivisorRaw BasePlace LiftPlace)
    (dClaim qClaim : FiberDegreeClaim)
    (lStar : Nat) (hlStar : 1 <= lStar)
    (primeTerm correction : Real)
    (htower : TowerMassCompatible T)
    (hext : 0 < T.extensionDegree)
    (hbase : BaseLocalDegreesPositive T)
    (hd : dClaim.Correct T D) (hq : qClaim.Correct T Q) :
    ordinaryFinMean (fun k : Fin lStar =>
      specialNonarchFixedJUpperBound (2 * (lStar : Real) + 1)
        (sourceLabelOfOuter k)
        (normalizedPlaceMean T.baseLocalDegree
          (groupedNormalizedDegree T D))
        (normalizedPlaceMean T.baseLocalDegree
          (groupedNormalizedDegree T Q))
        primeTerm correction) =
      (((2 * (lStar : Real) + 1) + 5) / 4) * dClaim.value -
        (((2 * (lStar : Real) + 1) + 1) / 24) * qClaim.value +
        primeTerm +
        ((2 * (lStar : Real) + 1) + 5) * correction := by
  rw [base_weighted_grouped_degree_eq_claim T D dClaim htower hext hbase hd,
    base_weighted_grouped_degree_eq_claim T Q qClaim htower hext hbase hq]
  exact outer_specialNonarch_fixedJ_bounds lStar hlStar
    dClaim.value qClaim.value primeTerm correction

def checkLocalTower : FiniteLocalTowerRaw Bool (fun _ => Unit) where
  baseLocalDegree := fun v => if v then 2 else 1
  liftLocalDegree := fun v _ => if v then 4 else 2
  extensionDegree := 2

def checkDivisor : FiberArithmeticDivisorRaw Bool (fun _ => Unit) where
  coefficient := fun v _ => if v then 3 else 0
  logResidueCard := fun v _ => if v then 2 else 1

def zeroCheckDivisor : FiberArithmeticDivisorRaw Bool (fun _ => Unit) where
  coefficient := fun _ _ => 0
  logResidueCard := fun _ _ => 1

def checkCorrectClaim : FiberDegreeClaim where
  value := 1

def checkWrongClaim : FiberDegreeClaim where
  value := 2

theorem check_tower_mass_compatible :
    TowerMassCompatible checkLocalTower := by
  intro v
  fin_cases v <;> norm_num [checkLocalTower, groupedLiftMass]

theorem check_base_degrees_positive :
    BaseLocalDegreesPositive checkLocalTower := by
  intro v
  fin_cases v <;> norm_num [checkLocalTower]

theorem check_lift_degrees_positive :
    LiftLocalDegreesPositive checkLocalTower := by
  intro v w
  fin_cases v <;> cases w <;> norm_num [checkLocalTower]

theorem check_grouped_local_values :
    groupedNormalizedDegree checkLocalTower checkDivisor false = 0 /\
      groupedNormalizedDegree checkLocalTower checkDivisor true = 3 / 2 := by
  norm_num [groupedNormalizedDegree, groupedDivisorNumerator,
    groupedLiftMass, liftDivisorContribution, checkLocalTower, checkDivisor]

theorem check_total_fiber_degree :
    totalFiberNormalizedDegree checkLocalTower checkDivisor = 1 := by
  norm_num [totalFiberNormalizedDegree, groupedDivisorNumerator,
    groupedLiftMass, liftDivisorContribution, checkLocalTower, checkDivisor,
    Fin.sum_univ_two]

theorem check_correct_claim_passes :
    checkCorrectClaim.Correct checkLocalTower checkDivisor := by
  norm_num [FiberDegreeClaim.Correct, checkCorrectClaim,
    totalFiberNormalizedDegree, groupedDivisorNumerator, groupedLiftMass,
    liftDivisorContribution, checkLocalTower, checkDivisor, Fin.sum_univ_two]

theorem check_wrong_claim_fails :
    ¬ (checkWrongClaim.Correct checkLocalTower checkDivisor) := by
  norm_num [FiberDegreeClaim.Correct, checkWrongClaim,
    totalFiberNormalizedDegree, groupedDivisorNumerator, groupedLiftMass,
    liftDivisorContribution, checkLocalTower, checkDivisor, Fin.sum_univ_two]

theorem check_degree_weighted_coefficients_are_wrong :
    normalizedPlaceMean checkLocalTower.baseLocalDegree
        (fun v => checkDivisor.coefficient v ()) = 2 /\
      totalFiberNormalizedDegree checkLocalTower checkDivisor = 1 := by
  norm_num [normalizedPlaceMean, Prop17.betaE, Prop17.lamE,
    totalFiberNormalizedDegree, groupedDivisorNumerator, groupedLiftMass,
    liftDivisorContribution, checkLocalTower, checkDivisor, Fin.sum_univ_two]

theorem check_input_change_changes_total_degree :
    totalFiberNormalizedDegree checkLocalTower checkDivisor ≠
      totalFiberNormalizedDegree checkLocalTower zeroCheckDivisor := by
  norm_num [totalFiberNormalizedDegree, groupedDivisorNumerator,
    groupedLiftMass, liftDivisorContribution, checkLocalTower, checkDivisor,
    zeroCheckDivisor, Fin.sum_univ_two]

def zeroMassTower : FiniteLocalTowerRaw Unit (fun _ => Unit) where
  baseLocalDegree := fun _ => 0
  liftLocalDegree := fun _ _ => 0
  extensionDegree := 1

theorem zero_mass_tower_fails_base_positivity :
    ¬ (BaseLocalDegreesPositive zeroMassTower) := by
  intro h
  have := h ()
  norm_num [zeroMassTower] at this

def wrongTowerMass : FiniteLocalTowerRaw Bool (fun _ => Unit) where
  baseLocalDegree := fun v => if v then 2 else 1
  liftLocalDegree := fun v _ => if v then 3 else 1
  extensionDegree := 1

theorem wrong_tower_mass_is_rejected :
    ¬ (TowerMassCompatible wrongTowerMass) := by
  intro h
  have := h true
  norm_num [wrongTowerMass] at this

end CitedLV.Theorem311
