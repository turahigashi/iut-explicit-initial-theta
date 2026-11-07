import Mathlib.Data.Nat.Basic

namespace CitedLV.ThetaLink

universe uS uV₀ uV₁ uL uC uB

structure WeightedDiagonalRayRaw
    (S : Type uS) (V₀ : Type uV₀) (V₁ : Type uV₁)
    (L : Type uL) (Coord : L → Type uC) where
  sourceRay : S → V₀
  realize₀ : V₀ → ((j : L) → Coord j)
  targetRay : S → V₁

def realizedSourceProfile
    {S : Type uS} {V₀ : Type uV₀} {V₁ : Type uV₁}
    {L : Type uL} {Coord : L → Type uC}
    (D : WeightedDiagonalRayRaw S V₀ V₁ L Coord) :
    S → ((j : L) → Coord j) :=
  D.realize₀ ∘ D.sourceRay

def RepresentativeLaw {L : Type uL} (natRep : L → Nat) : Prop :=
  (∀ j, 0 < natRep j) ∧ Function.Injective natRep

def SquareWeightLaw {L : Type uL} (natRep weight : L → Nat) : Prop :=
  ∀ j, weight j = natRep j * natRep j

def RealizesWeightedDiagonal
    {S : Type uS} {V₀ : Type uV₀} {V₁ : Type uV₁}
    {L : Type uL} {Coord : L → Type uC} {B : Type uB}
    (D : WeightedDiagonalRayRaw S V₀ V₁ L Coord)
    (baseRay : S → B) (weight : L → Nat)
    (embed : (j : L) → B → Coord j)
    (scaleCoordinate : (j : L) → Nat → Coord j → Coord j) : Prop :=
  ∀ s j,
    realizedSourceProfile D s j =
      scaleCoordinate j (weight j) (embed j (baseRay s))

def TransportsWeightedRay
    {S : Type uS} {V₀ : Type uV₀} {V₁ : Type uV₁}
    {L : Type uL} {Coord : L → Type uC}
    (D : WeightedDiagonalRayRaw S V₀ V₁ L Coord)
    (transport : V₀ → V₁) : Prop :=
  ∀ s, transport (D.sourceRay s) = D.targetRay s

def WeightedValueProfileCompatible
    {S : Type uS} {V₀ : Type uV₀} {V₁ : Type uV₁}
    {L : Type uL} {Coord : L → Type uC} {B : Type uB}
    (D : WeightedDiagonalRayRaw S V₀ V₁ L Coord)
    (natRep weight : L → Nat) (baseRay : S → B)
    (embed : (j : L) → B → Coord j)
    (scaleCoordinate : (j : L) → Nat → Coord j → Coord j)
    (transport : V₀ → V₁) : Prop :=
  RepresentativeLaw natRep ∧ SquareWeightLaw natRep weight ∧
    RealizesWeightedDiagonal D baseRay weight embed scaleCoordinate ∧
    TransportsWeightedRay D transport

def RayNonconstant
    {S : Type uS} {V₀ : Type uV₀} {V₁ : Type uV₁}
    {L : Type uL} {Coord : L → Type uC}
    (D : WeightedDiagonalRayRaw S V₀ V₁ L Coord) : Prop :=
  ∃ s t, D.sourceRay s ≠ D.sourceRay t

def ReadoutFaithful
    {S : Type uS} {V₀ : Type uV₀} {V₁ : Type uV₁}
    {L : Type uL} {Coord : L → Type uC}
    (D : WeightedDiagonalRayRaw S V₀ V₁ L Coord) : Prop :=
  Function.Injective D.realize₀

def DistinctWeights {L : Type uL} (weight : L → Nat) : Prop :=
  ∃ i j, weight i ≠ weight j

def toyNatRep : Bool → Nat
  | false => 1
  | true => 2

def toyWeight : Bool → Nat
  | false => 1
  | true => 4

def toyBaseRay : Bool → Nat
  | false => 1
  | true => 2

def toySourceRay : Bool → Nat := toyBaseRay

def toyTargetRay : Bool → Nat
  | false => 11
  | true => 12

def toyRealize₀ (v : Nat) (j : Bool) : Nat := toyWeight j * v

def toyEmbed (_j : Bool) (b : Nat) : Nat := b

def toyScaleCoordinate (_j : Bool) (n x : Nat) : Nat := n * x

def toyData : WeightedDiagonalRayRaw Bool Nat Nat Bool (fun _ ↦ Nat) where
  sourceRay := toySourceRay
  realize₀ := toyRealize₀
  targetRay := toyTargetRay

def toyTransport (v : Nat) : Nat := v + 10

theorem toy_representative_law : RepresentativeLaw toyNatRep := by
  constructor
  · intro j
    cases j <;> decide
  · intro i j h
    cases i <;> cases j <;> simp_all [toyNatRep]

theorem toy_square_weight_law : SquareWeightLaw toyNatRep toyWeight := by
  intro j
  cases j <;> decide

theorem toy_realizes_weighted_diagonal :
    RealizesWeightedDiagonal toyData toyBaseRay toyWeight
      toyEmbed toyScaleCoordinate := by
  intro s j
  cases s <;> cases j <;> rfl

theorem toy_transport_succeeds :
    TransportsWeightedRay toyData toyTransport := by
  intro s
  cases s <;> rfl

theorem toy_weighted_value_profile_compatible :
    WeightedValueProfileCompatible toyData toyNatRep toyWeight toyBaseRay
      toyEmbed toyScaleCoordinate toyTransport :=
  ⟨toy_representative_law, toy_square_weight_law,
    toy_realizes_weighted_diagonal, toy_transport_succeeds⟩

theorem toy_ray_is_nonconstant : RayNonconstant toyData :=
  ⟨false, true, by decide⟩

theorem toy_readout_is_faithful : ReadoutFaithful toyData := by
  intro a b h
  have hf := congrFun h false
  simpa [toyData, toyRealize₀, toyWeight] using hf

theorem toy_has_distinct_weights : DistinctWeights toyWeight :=
  ⟨false, true, by decide⟩

theorem toy_has_two_distinct_ray_inputs :
    toySourceRay false ≠ toySourceRay true := by
  decide

theorem toy_profile_retains_label_information :
    realizedSourceProfile toyData false false ≠
      realizedSourceProfile toyData false true := by
  decide

theorem toy_weight_action_is_nonconstant :
    toyScaleCoordinate false 1 (toyEmbed false 1) ≠
      toyScaleCoordinate false 4 (toyEmbed false 1) := by
  decide

def nonsquareWeight : Bool → Nat := fun _ ↦ 1

theorem nonsquareWeight_fails_square_law :
    ¬ SquareWeightLaw toyNatRep nonsquareWeight := by
  intro h
  have hne : (1 : Nat) ≠ 4 := by decide
  apply hne
  simpa [nonsquareWeight, toyNatRep] using h true

def falseRealizationData :
    WeightedDiagonalRayRaw Bool Nat Nat Bool (fun _ ↦ Nat) where
  sourceRay := toySourceRay
  realize₀ := fun v _j ↦ v
  targetRay := toyTargetRay

theorem falseRealizationData_fails_weighted_realization :
    ¬ RealizesWeightedDiagonal falseRealizationData toyBaseRay toyWeight
      toyEmbed toyScaleCoordinate := by
  intro h
  have hne : (1 : Nat) ≠ 4 := by decide
  apply hne
  simpa [realizedSourceProfile, falseRealizationData, toySourceRay,
    toyBaseRay, toyWeight, toyEmbed, toyScaleCoordinate] using h false true

theorem falseRealizationData_still_transports :
    TransportsWeightedRay falseRealizationData toyTransport := by
  intro s
  cases s <;> rfl

def falseTransport (v : Nat) : Nat := v

theorem falseTransport_fails :
    ¬ TransportsWeightedRay toyData falseTransport := by
  intro h
  have hne : (1 : Nat) ≠ 11 := by decide
  apply hne
  simpa [falseTransport, toyData, toySourceRay, toyBaseRay,
    toyTargetRay] using h false

theorem realization_and_transport_are_independent :
    (¬ RealizesWeightedDiagonal falseRealizationData toyBaseRay toyWeight
        toyEmbed toyScaleCoordinate ∧
      TransportsWeightedRay falseRealizationData toyTransport) ∧
    (RealizesWeightedDiagonal toyData toyBaseRay toyWeight
        toyEmbed toyScaleCoordinate ∧
      ¬ TransportsWeightedRay toyData falseTransport) :=
  ⟨⟨falseRealizationData_fails_weighted_realization,
      falseRealizationData_still_transports⟩,
    ⟨toy_realizes_weighted_diagonal, falseTransport_fails⟩⟩

end CitedLV.ThetaLink
