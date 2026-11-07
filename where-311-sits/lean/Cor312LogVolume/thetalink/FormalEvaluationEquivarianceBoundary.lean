import Cor312LogVolume.thetalink.FormalEvaluationCarrierBoundary
import Cor312LogVolume.thetalink.CompletePolyIso

namespace CitedLV.ThetaLink

universe uAct uEnv uGau uL uCar uS uU uVal uCopy

structure FormalEvaluationActions
    (G : Type uAct) (Env : Type uEnv) (Gau : Type uGau)
    (L : Type uL) (Carrier : L → Type uCar) [Monoid G] where
  envAction : MulAction G Env
  gauAction : MulAction G Gau
  carrierAction : (j : L) → MulAction G (Carrier j)

def FormalEvaluationActions.envSmul
    {G : Type uAct} {Env : Type uEnv} {Gau : Type uGau}
    {L : Type uL} {Carrier : L → Type uCar} [Monoid G]
    (A : FormalEvaluationActions G Env Gau L Carrier)
    (g : G) (x : Env) : Env := by
  letI : MulAction G Env := A.envAction
  exact g • x

def FormalEvaluationActions.gauSmul
    {G : Type uAct} {Env : Type uEnv} {Gau : Type uGau}
    {L : Type uL} {Carrier : L → Type uCar} [Monoid G]
    (A : FormalEvaluationActions G Env Gau L Carrier)
    (g : G) (x : Gau) : Gau := by
  letI : MulAction G Gau := A.gauAction
  exact g • x

def FormalEvaluationActions.carrierSmul
    {G : Type uAct} {Env : Type uEnv} {Gau : Type uGau}
    {L : Type uL} {Carrier : L → Type uCar} [Monoid G]
    (A : FormalEvaluationActions G Env Gau L Carrier)
    (j : L) (g : G) (x : Carrier j) : Carrier j := by
  letI : MulAction G (Carrier j) := A.carrierAction j
  exact g • x

def EvaluationGEquivariant
    {G : Type uAct} {S : Type uS} {Env : Type uEnv}
    {Gau : Type uGau} {U : Type uU} {L : Type uL}
    {ValueCoord : L → Type uVal} {UnitCopy : L → Type uCopy}
    {SymmRel : L → L → Prop} {Carrier : L → Type uCar}
    [Monoid G] [CommMonoid Env] [CommMonoid Gau]
    [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier)
    (A : FormalEvaluationActions G Env Gau L Carrier) : Prop :=
  ∀ g x,
    D.evaluate (A.envSmul g x) = A.gauSmul g (D.evaluate x)

def ObservationGEquivariant
    {G : Type uAct} {S : Type uS} {Env : Type uEnv}
    {Gau : Type uGau} {U : Type uU} {L : Type uL}
    {ValueCoord : L → Type uVal} {UnitCopy : L → Type uCopy}
    {SymmRel : L → L → Prop} {Carrier : L → Type uCar}
    [Monoid G] [CommMonoid Env] [CommMonoid Gau]
    [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier)
    (A : FormalEvaluationActions G Env Gau L Carrier) : Prop :=
  ∀ g y j,
    D.gauObserve (A.gauSmul g y) j =
      A.carrierSmul j g (D.gauObserve y j)

theorem formalEvaluationMonoidEquiv_is_equivariant
    {G : Type uAct} {S : Type uS} {Env : Type uEnv}
    {Gau : Type uGau} {U : Type uU} {L : Type uL}
    {ValueCoord : L → Type uVal} {UnitCopy : L → Type uCopy}
    {SymmRel : L → L → Prop} {Carrier : L → Type uCar}
    [Monoid G] [CommMonoid Env] [CommMonoid Gau]
    [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier)
    (A : FormalEvaluationActions G Env Gau L Carrier)
    (hone : EvaluationMapOne D) (hmul : EvaluationMapMul D)
    (hbij : EvaluationBijective D) (heq : EvaluationGEquivariant D A)
    (g : G) (x : Env) :
    formalEvaluationMonoidEquiv D hone hmul hbij (A.envSmul g x) =
      A.gauSmul g (formalEvaluationMonoidEquiv D hone hmul hbij x) := by
  exact heq g x

theorem observed_formal_evaluation_is_equivariant
    {G : Type uAct} {S : Type uS} {Env : Type uEnv}
    {Gau : Type uGau} {U : Type uU} {L : Type uL}
    {ValueCoord : L → Type uVal} {UnitCopy : L → Type uCopy}
    {SymmRel : L → L → Prop} {Carrier : L → Type uCar}
    [Monoid G] [CommMonoid Env] [CommMonoid Gau]
    [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier)
    (A : FormalEvaluationActions G Env Gau L Carrier)
    (heval : EvaluationGEquivariant D A)
    (hobserve : ObservationGEquivariant D A)
    (g : G) (x : Env) (j : L) :
    D.gauObserve (D.evaluate (A.envSmul g x)) j =
      A.carrierSmul j g (D.gauObserve (D.evaluate x) j) := by
  rw [heval g x]
  exact hobserve g (D.evaluate x) j

def actionToyValues :
    WeightedDiagonalRayRaw C3Square C3Square C3Square PUnit
      (fun _ ↦ C3Square) where
  sourceRay := id
  realize₀ := fun x _ ↦ c3SquareSwap x
  targetRay := c3SquareSwap

def actionToyUnits :
    LabelledUnitCopiesRaw C3Square PUnit (fun _ ↦ C3Square)
      (fun _ _ ↦ True) where
  embed := fun _ u ↦ c3SquareSwap u
  symmetrize := fun _ ↦ Equiv.refl C3Square
  readout := fun u _ ↦ c3SquareSwap u

def actionToyObserve : C3Square →* (PUnit → C3Square) where
  toFun := fun x _ ↦ x
  map_one' := by
    funext j
    rfl
  map_mul' := by
    intro x y
    funext j
    rfl

def actionToyEvaluation :
    FormalEvaluationCarrierRaw C3Square C3Square C3Square C3Square
      PUnit (fun _ ↦ C3Square) (fun _ ↦ C3Square)
      (fun _ _ ↦ True) (fun _ ↦ C3Square) where
  values := actionToyValues
  units := actionToyUnits
  evaluate := c3SquareSwap
  envUnit := id
  gauUnit := c3SquareSwap
  gauObserve := actionToyObserve
  unitInto := fun _ x ↦ x
  valueInto := fun _ x ↦ x

theorem action_toy_map_one : EvaluationMapOne actionToyEvaluation := by
  rfl

theorem action_toy_map_mul : EvaluationMapMul actionToyEvaluation := by
  intro x y
  exact c3SquareSwap.map_mul x y

theorem action_toy_bijective : EvaluationBijective actionToyEvaluation :=
  c3SquareSwap.bijective

theorem action_toy_unit_square :
    EvaluationUnitSquare actionToyEvaluation := by
  intro u
  rfl

theorem action_toy_ray_square :
    EvaluationRaySquare actionToyEvaluation := by
  intro s
  rfl

theorem action_toy_observed_unit_square :
    ObservedUnitSquare actionToyEvaluation := by
  intro u j
  rfl

theorem action_toy_observed_weighted_square :
    ObservedWeightedSquare actionToyEvaluation := by
  intro s j
  rfl

@[reducible] def regularC3SquareAction : MulAction C3Square C3Square :=
  inferInstance

@[reducible] def swappedC3SquareAction : MulAction C3Square C3Square where
  smul g x := c3SquareSwap g * x
  one_smul x := by
    change c3SquareSwap 1 * x = x
    rw [map_one, one_mul]
  mul_smul g h x := by
    change c3SquareSwap (g * h) * x =
      c3SquareSwap g * (c3SquareSwap h * x)
    rw [map_mul, mul_assoc]

def actionToyGoodActions :
    FormalEvaluationActions C3Square C3Square C3Square PUnit
      (fun _ ↦ C3Square) where
  envAction := regularC3SquareAction
  gauAction := swappedC3SquareAction
  carrierAction := fun _ ↦ swappedC3SquareAction

def actionToyBadEvaluationActions :
    FormalEvaluationActions C3Square C3Square C3Square PUnit
      (fun _ ↦ C3Square) where
  envAction := regularC3SquareAction
  gauAction := regularC3SquareAction
  carrierAction := fun _ ↦ regularC3SquareAction

def actionToyBadObservationActions :
    FormalEvaluationActions C3Square C3Square C3Square PUnit
      (fun _ ↦ C3Square) where
  envAction := regularC3SquareAction
  gauAction := swappedC3SquareAction
  carrierAction := fun _ ↦ regularC3SquareAction

theorem action_toy_good_evaluation_equivariant :
    EvaluationGEquivariant actionToyEvaluation actionToyGoodActions := by
  intro g x
  exact c3SquareSwap.map_mul g x

theorem action_toy_good_observation_equivariant :
    ObservationGEquivariant actionToyEvaluation actionToyGoodActions := by
  intro g y j
  rfl

theorem c3SquareSwap_axis_ne_self :
    c3SquareSwap c3AxisWitness ≠ c3AxisWitness := by
  decide

theorem action_toy_bad_evaluation_not_equivariant :
    ¬ EvaluationGEquivariant actionToyEvaluation
      actionToyBadEvaluationActions := by
  intro h
  have hw := h c3AxisWitness 1
  apply c3SquareSwap_axis_ne_self
  simpa [FormalEvaluationActions.envSmul,
    FormalEvaluationActions.gauSmul, actionToyEvaluation,
    actionToyBadEvaluationActions, regularC3SquareAction] using hw

theorem action_toy_bad_evaluation_observation_still_equivariant :
    ObservationGEquivariant actionToyEvaluation
      actionToyBadEvaluationActions := by
  intro g y j
  rfl

theorem action_toy_bad_observation_evaluation_still_equivariant :
    EvaluationGEquivariant actionToyEvaluation
      actionToyBadObservationActions := by
  intro g x
  exact c3SquareSwap.map_mul g x

theorem action_toy_bad_observation_not_equivariant :
    ¬ ObservationGEquivariant actionToyEvaluation
      actionToyBadObservationActions := by
  intro h
  have hw := h c3AxisWitness 1 PUnit.unit
  apply c3SquareSwap_axis_ne_self
  simpa [FormalEvaluationActions.gauSmul,
    FormalEvaluationActions.carrierSmul, actionToyEvaluation,
    actionToyObserve, actionToyBadObservationActions,
    regularC3SquareAction, swappedC3SquareAction] using hw

theorem e4d_laws_do_not_force_evaluation_equivariance :
    EvaluationMapOne actionToyEvaluation ∧
      EvaluationMapMul actionToyEvaluation ∧
      EvaluationBijective actionToyEvaluation ∧
      EvaluationUnitSquare actionToyEvaluation ∧
      EvaluationRaySquare actionToyEvaluation ∧
      ObservedUnitSquare actionToyEvaluation ∧
      ObservedWeightedSquare actionToyEvaluation ∧
      ¬ EvaluationGEquivariant actionToyEvaluation
        actionToyBadEvaluationActions :=
  ⟨action_toy_map_one, action_toy_map_mul, action_toy_bijective,
    action_toy_unit_square, action_toy_ray_square,
    action_toy_observed_unit_square, action_toy_observed_weighted_square,
    action_toy_bad_evaluation_not_equivariant⟩

theorem evaluation_equivariance_does_not_force_observation_equivariance :
    EvaluationGEquivariant actionToyEvaluation
        actionToyBadObservationActions ∧
      ¬ ObservationGEquivariant actionToyEvaluation
        actionToyBadObservationActions :=
  ⟨action_toy_bad_observation_evaluation_still_equivariant,
    action_toy_bad_observation_not_equivariant⟩

end CitedLV.ThetaLink
