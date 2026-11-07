import Cor312LogVolume.thetalink.WeightedDiagonalRay
import Cor312LogVolume.thetalink.UnitDiagonalSymmetrization
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Ring.Nat

namespace CitedLV.ThetaLink

universe uS uE uG uU uL uV uC uA uB

structure FormalEvaluationCarrierRaw
    (S : Type uS) (Env : Type uE) (Gau : Type uG) (U : Type uU)
    (L : Type uL) (ValueCoord : L → Type uV)
    (UnitCopy : L → Type uC) (SymmRel : L → L → Prop)
    (Carrier : L → Type uA)
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)] where
  values : WeightedDiagonalRayRaw S Env Gau L ValueCoord
  units : LabelledUnitCopiesRaw U L UnitCopy SymmRel
  evaluate : Env → Gau
  envUnit : U → Env
  gauUnit : U → Gau
  gauObserve : Gau →* ((j : L) → Carrier j)
  unitInto : (j : L) → UnitCopy j → Carrier j
  valueInto : (j : L) → ValueCoord j → Carrier j

def EvaluationMapOne
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier) : Prop :=
  D.evaluate 1 = 1

def EvaluationMapMul
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier) : Prop :=
  ∀ x y, D.evaluate (x * y) = D.evaluate x * D.evaluate y

def EvaluationBijective
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier) : Prop :=
  Function.Bijective D.evaluate

def EvaluationUnitSquare
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier) : Prop :=
  ∀ u, D.evaluate (D.envUnit u) = D.gauUnit u

def EvaluationRaySquare
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier) : Prop :=
  ∀ s, D.evaluate (D.values.sourceRay s) = D.values.targetRay s

def ObservedUnitSquare
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier) : Prop :=
  ∀ u j, D.gauObserve (D.gauUnit u) j =
    D.unitInto j (D.units.readout u j)

def ObservedWeightedSquare
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier) : Prop :=
  ∀ s j, D.gauObserve (D.values.targetRay s) j =
    D.valueInto j (realizedSourceProfile D.values s j)

def formalEvaluationMonoidHom
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier)
    (hone : EvaluationMapOne D) (hmul : EvaluationMapMul D) : Env →* Gau where
  toFun := D.evaluate
  map_one' := hone
  map_mul' := hmul

noncomputable def formalEvaluationMonoidEquiv
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier)
    (hone : EvaluationMapOne D) (hmul : EvaluationMapMul D)
    (hbij : EvaluationBijective D) : Env ≃* Gau :=
  MulEquiv.ofBijective (formalEvaluationMonoidHom D hone hmul) hbij

theorem formalEvaluationMonoidEquiv_apply
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier)
    (hone : EvaluationMapOne D) (hmul : EvaluationMapMul D)
    (hbij : EvaluationBijective D) (x : Env) :
    formalEvaluationMonoidEquiv D hone hmul hbij x = D.evaluate x :=
  rfl

def formalEnvWhole
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier) (u : U) (s : S) : Env :=
  D.envUnit u * D.values.sourceRay s

def formalGauWhole
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier) (u : U) (s : S) : Gau :=
  D.gauUnit u * D.values.targetRay s

theorem formal_evaluation_preserves_whole_assembly
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier)
    (hmul : EvaluationMapMul D) (hunit : EvaluationUnitSquare D)
    (hray : EvaluationRaySquare D) (u : U) (s : S) :
    D.evaluate (formalEnvWhole D u s) = formalGauWhole D u s := by
  calc
    D.evaluate (formalEnvWhole D u s) =
        D.evaluate (D.envUnit u) * D.evaluate (D.values.sourceRay s) :=
      hmul _ _
    _ = D.gauUnit u * D.values.targetRay s :=
      congrArg₂ (· * ·) (hunit u) (hray s)
    _ = formalGauWhole D u s := rfl

theorem observed_whole_coordinates
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier)
    (hunit : ObservedUnitSquare D) (hvalue : ObservedWeightedSquare D)
    (u : U) (s : S) (j : L) :
    D.gauObserve (formalGauWhole D u s) j =
      D.unitInto j (D.units.readout u j) *
        D.valueInto j (realizedSourceProfile D.values s j) := by
  calc
    D.gauObserve (formalGauWhole D u s) j =
        D.gauObserve (D.gauUnit u) j *
          D.gauObserve (D.values.targetRay s) j := by
      exact congrFun (D.gauObserve.map_mul (D.gauUnit u)
        (D.values.targetRay s)) j
    _ = D.unitInto j (D.units.readout u j) *
          D.valueInto j (realizedSourceProfile D.values s j) :=
      congrArg₂ (· * ·) (hunit u j) (hvalue s j)

theorem observed_formal_evaluation_coordinates
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier)
    (hmul : EvaluationMapMul D) (hevalUnit : EvaluationUnitSquare D)
    (hevalRay : EvaluationRaySquare D) (hobsUnit : ObservedUnitSquare D)
    (hobsValue : ObservedWeightedSquare D)
    (u : U) (s : S) (j : L) :
    D.gauObserve (D.evaluate (formalEnvWhole D u s)) j =
      D.unitInto j (D.units.readout u j) *
        D.valueInto j (realizedSourceProfile D.values s j) := by
  rw [formal_evaluation_preserves_whole_assembly D hmul hevalUnit hevalRay]
  exact observed_whole_coordinates D hobsUnit hobsValue u s j

theorem observed_formal_evaluation_has_diagonal_weighted_shape
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA} {B : Type uB}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier)
    (hmul : EvaluationMapMul D) (hevalUnit : EvaluationUnitSquare D)
    (hevalRay : EvaluationRaySquare D) (hobsUnit : ObservedUnitSquare D)
    (hobsValue : ObservedWeightedSquare D)
    (hdiagonal : UnitDiagonal D.units)
    (baseRay : S → B) (weight : L → Nat)
    (embed : (j : L) → B → ValueCoord j)
    (scaleCoordinate : (j : L) → Nat → ValueCoord j → ValueCoord j)
    (hweighted : RealizesWeightedDiagonal D.values baseRay weight embed
      scaleCoordinate)
    (u : U) (s : S) (j : L) :
    D.gauObserve (D.evaluate (formalEnvWhole D u s)) j =
      D.unitInto j (D.units.embed j u) *
        D.valueInto j
          (scaleCoordinate j (weight j) (embed j (baseRay s))) := by
  calc
    D.gauObserve (D.evaluate (formalEnvWhole D u s)) j =
        D.unitInto j (D.units.readout u j) *
          D.valueInto j (realizedSourceProfile D.values s j) :=
      observed_formal_evaluation_coordinates D hmul hevalUnit hevalRay
        hobsUnit hobsValue u s j
    _ = D.unitInto j (D.units.embed j u) *
          D.valueInto j
            (scaleCoordinate j (weight j) (embed j (baseRay s))) := by
      rw [hdiagonal u j, hweighted s j]

def EvaluationRayVisible
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier) : Prop :=
  ∃ s t, D.values.sourceRay s ≠ D.values.sourceRay t ∧
    D.evaluate (D.values.sourceRay s) ≠ D.evaluate (D.values.sourceRay t)

def EvaluationUnitVisible
    {S : Type uS} {Env : Type uE} {Gau : Type uG} {U : Type uU}
    {L : Type uL} {ValueCoord : L → Type uV}
    {UnitCopy : L → Type uC} {SymmRel : L → L → Prop}
    {Carrier : L → Type uA}
    [CommMonoid Env] [CommMonoid Gau] [∀ j, CommMonoid (Carrier j)]
    (D : FormalEvaluationCarrierRaw S Env Gau U L ValueCoord UnitCopy
      SymmRel Carrier) : Prop :=
  ∃ u v, u ≠ v ∧ D.evaluate (D.envUnit u) ≠ D.evaluate (D.envUnit v)

def carrierToyRealize (v : Nat) (j : Bool) : Nat :=
  v ^ toyWeight j

def carrierToyValues :
    WeightedDiagonalRayRaw Bool Nat Nat Bool (fun _ ↦ Nat) where
  sourceRay := toySourceRay
  realize₀ := carrierToyRealize
  targetRay := toySourceRay

def carrierToyScale (_j : Bool) (n x : Nat) : Nat := x ^ n

theorem carrier_toy_realizes_weighted_diagonal :
    RealizesWeightedDiagonal carrierToyValues toyBaseRay toyWeight
      toyEmbed carrierToyScale := by
  intro s j
  rfl

def carrierToyEnvUnit : Bool → Nat
  | false => 1
  | true => 2

def carrierToyGauUnit : Bool → Nat := carrierToyEnvUnit

def carrierToyObserve : Nat →* (Bool → Nat) where
  toFun := fun n j ↦ n ^ toyWeight j
  map_one' := by
    funext j
    simp
  map_mul' := by
    intro a b
    funext j
    exact Nat.mul_pow a b (toyWeight j)

def carrierToyUnitInto : (j : Bool) → ToyUnitCopy j → Nat
  | false => fun u ↦ (match u with | false => 1 | true => 2) ^ toyWeight false
  | true => fun u ↦ (u.val + 1) ^ toyWeight true

def carrierToyValueInto (_j : Bool) (x : Nat) : Nat := x

def carrierToyEvaluation :
    FormalEvaluationCarrierRaw Bool Nat Nat Bool Bool (fun _ ↦ Nat)
      ToyUnitCopy ToySymmRel (fun _ ↦ Nat) where
  values := carrierToyValues
  units := toyLabelledUnitCopies
  evaluate := id
  envUnit := carrierToyEnvUnit
  gauUnit := carrierToyGauUnit
  gauObserve := carrierToyObserve
  unitInto := carrierToyUnitInto
  valueInto := carrierToyValueInto

theorem carrier_toy_map_one : EvaluationMapOne carrierToyEvaluation := rfl

theorem carrier_toy_map_mul : EvaluationMapMul carrierToyEvaluation := by
  intro x y
  rfl

theorem carrier_toy_bijective : EvaluationBijective carrierToyEvaluation :=
  Function.bijective_id

theorem carrier_toy_evaluation_unit_square :
    EvaluationUnitSquare carrierToyEvaluation := by
  intro u
  rfl

theorem carrier_toy_evaluation_ray_square :
    EvaluationRaySquare carrierToyEvaluation := by
  intro s
  rfl

theorem carrier_toy_observed_unit_square :
    ObservedUnitSquare carrierToyEvaluation := by
  intro u j
  cases u <;> cases j <;> rfl

theorem carrier_toy_observed_weighted_square :
    ObservedWeightedSquare carrierToyEvaluation := by
  intro s j
  rfl

theorem carrier_toy_ray_visible : EvaluationRayVisible carrierToyEvaluation :=
  ⟨false, true, toy_has_two_distinct_ray_inputs,
    toy_has_two_distinct_ray_inputs⟩

theorem carrier_toy_unit_visible :
    EvaluationUnitVisible carrierToyEvaluation := by
  refine ⟨false, true, Bool.false_ne_true, ?_⟩
  decide

noncomputable def carrierToyMonoidEquiv : Nat ≃* Nat :=
  formalEvaluationMonoidEquiv carrierToyEvaluation carrier_toy_map_one
    carrier_toy_map_mul carrier_toy_bijective

theorem carrier_toy_whole_assembly (u s : Bool) :
    carrierToyEvaluation.evaluate (formalEnvWhole carrierToyEvaluation u s) =
      formalGauWhole carrierToyEvaluation u s :=
  formal_evaluation_preserves_whole_assembly carrierToyEvaluation
    carrier_toy_map_mul carrier_toy_evaluation_unit_square
    carrier_toy_evaluation_ray_square u s

theorem carrier_toy_observed_coordinates (u s j : Bool) :
    carrierToyEvaluation.gauObserve
        (carrierToyEvaluation.evaluate
          (formalEnvWhole carrierToyEvaluation u s)) j =
      carrierToyEvaluation.unitInto j
          (carrierToyEvaluation.units.readout u j) *
        carrierToyEvaluation.valueInto j
          (realizedSourceProfile carrierToyEvaluation.values s j) :=
  observed_formal_evaluation_coordinates carrierToyEvaluation
    carrier_toy_map_mul carrier_toy_evaluation_unit_square
    carrier_toy_evaluation_ray_square carrier_toy_observed_unit_square
    carrier_toy_observed_weighted_square u s j

theorem carrier_toy_observed_diagonal_weighted_shape (u s j : Bool) :
    carrierToyEvaluation.gauObserve
        (carrierToyEvaluation.evaluate
          (formalEnvWhole carrierToyEvaluation u s)) j =
      carrierToyEvaluation.unitInto j
          (carrierToyEvaluation.units.embed j u) *
        carrierToyEvaluation.valueInto j
          (carrierToyScale j (toyWeight j) (toyEmbed j (toyBaseRay s))) :=
  observed_formal_evaluation_has_diagonal_weighted_shape
    carrierToyEvaluation carrier_toy_map_mul
    carrier_toy_evaluation_unit_square carrier_toy_evaluation_ray_square
    carrier_toy_observed_unit_square carrier_toy_observed_weighted_square
    toy_unit_diagonal toyBaseRay toyWeight toyEmbed carrierToyScale
    carrier_toy_realizes_weighted_diagonal u s j

def collapsedCarrierValues :
    WeightedDiagonalRayRaw Bool Nat Nat Bool (fun _ ↦ Nat) where
  sourceRay := toySourceRay
  realize₀ := carrierToyRealize
  targetRay := fun _ ↦ 1

def collapsedCarrierEvaluate (_x : Nat) : Nat := 1

def collapsedCarrierUnit (_u : Bool) : Nat := 1

def collapsedCarrierInto {α : Type} (_j : Bool) (_x : α) : Nat := 1

def collapsedCarrierEvaluation :
    FormalEvaluationCarrierRaw Bool Nat Nat Bool Bool (fun _ ↦ Nat)
      ToyUnitCopy ToySymmRel (fun _ ↦ Nat) where
  values := collapsedCarrierValues
  units := toyLabelledUnitCopies
  evaluate := collapsedCarrierEvaluate
  envUnit := collapsedCarrierUnit
  gauUnit := collapsedCarrierUnit
  gauObserve := carrierToyObserve
  unitInto := fun j x ↦ collapsedCarrierInto j x
  valueInto := fun j x ↦ collapsedCarrierInto j x

theorem collapsed_carrier_map_one :
    EvaluationMapOne collapsedCarrierEvaluation := rfl

theorem collapsed_carrier_map_mul :
    EvaluationMapMul collapsedCarrierEvaluation := by
  intro x y
  rfl

theorem collapsed_carrier_evaluation_unit_square :
    EvaluationUnitSquare collapsedCarrierEvaluation := by
  intro u
  rfl

theorem collapsed_carrier_evaluation_ray_square :
    EvaluationRaySquare collapsedCarrierEvaluation := by
  intro s
  rfl

theorem collapsed_carrier_observed_unit_square :
    ObservedUnitSquare collapsedCarrierEvaluation := by
  intro u j
  cases j <;> rfl

theorem collapsed_carrier_observed_weighted_square :
    ObservedWeightedSquare collapsedCarrierEvaluation := by
  intro s j
  cases j <;> rfl

theorem collapsed_carrier_not_bijective :
    ¬ EvaluationBijective collapsedCarrierEvaluation := by
  intro h
  have hinj := h.1
  have heq : collapsedCarrierEvaluation.evaluate 1 =
      collapsedCarrierEvaluation.evaluate 2 := rfl
  have hbad : (1 : Nat) = 2 := hinj heq
  exact (show (1 : Nat) ≠ 2 by decide) hbad

theorem collapsed_carrier_ray_not_visible :
    ¬ EvaluationRayVisible collapsedCarrierEvaluation := by
  rintro ⟨s, t, _hst, hout⟩
  apply hout
  rfl

theorem collapsed_carrier_unit_not_visible :
    ¬ EvaluationUnitVisible collapsedCarrierEvaluation := by
  rintro ⟨u, v, _huv, hout⟩
  apply hout
  rfl

theorem four_squares_allow_collapsed_constant_model :
    EvaluationUnitSquare collapsedCarrierEvaluation ∧
      EvaluationRaySquare collapsedCarrierEvaluation ∧
      ObservedUnitSquare collapsedCarrierEvaluation ∧
      ObservedWeightedSquare collapsedCarrierEvaluation ∧
      ¬ EvaluationBijective collapsedCarrierEvaluation ∧
      ¬ EvaluationRayVisible collapsedCarrierEvaluation ∧
      ¬ EvaluationUnitVisible collapsedCarrierEvaluation :=
  ⟨collapsed_carrier_evaluation_unit_square,
    collapsed_carrier_evaluation_ray_square,
    collapsed_carrier_observed_unit_square,
    collapsed_carrier_observed_weighted_square,
    collapsed_carrier_not_bijective,
    collapsed_carrier_ray_not_visible,
    collapsed_carrier_unit_not_visible⟩

end CitedLV.ThetaLink
