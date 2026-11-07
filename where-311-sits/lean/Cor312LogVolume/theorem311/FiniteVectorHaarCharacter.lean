import Cor312LogVolume.theorem311.FiniteExtensionHaarCharacter
import Cor312LogVolume.theorem311.NormalizedHaarCore

noncomputable section
set_option autoImplicit false

open Set MeasureTheory TopologicalSpace
open scoped Pointwise ENNReal NNReal

namespace CitedLV.Theorem311.FiniteVectorHaarCharacter

variable (K E : Type*) [NontriviallyNormedField K] [NormedAddCommGroup E]
  [Module K E] [ContinuousSMul K E] [FiniteDimensional K E]
  [LocallyCompactSpace K] [LocallyCompactSpace E]

local instance base_proper : ProperSpace K := ProperSpace.of_locallyCompactSpace K

theorem character_scalar (g : Kˣ) :
    distribHaarChar E g = distribHaarChar K g ^ Module.finrank K E := by
  classical
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let C : PositiveCompacts K := Classical.choice inferInstance
  let μK : Measure K := Measure.addHaarMeasure C
  let ι := Fin (Module.finrank K E)
  let e : E ≃L[K] (ι → K) := (Module.finBasis K E).equivFunL
  letI : SecondCountableTopology E := e.toHomeomorph.secondCountableTopology
  let ν : Measure (ι → K) := Measure.pi fun _ => μK
  let μ : Measure E := ν.map e.symm
  let S : Set (ι → K) := Set.pi Set.univ fun _ => (C : Set K)
  have hμK : μK (C : Set K) = 1 := Measure.addHaarMeasure_self
  have hmeasure (T : Set (ι → K)) : μ (e.symm '' T) = ν T := by
    change ν.map e.symm (e.symm '' T) = ν T
    have he : MeasurableEmbedding (e.symm : (ι → K) → E) :=
      e.symm.toHomeomorph.measurableEmbedding
    rw [he.map_apply, Set.preimage_image_eq T e.symm.injective]
  have hS : μ (e.symm '' S) = 1 := by
    rw [hmeasure]
    change (Measure.pi fun _ : ι => μK) (Set.pi Set.univ fun _ => (C : Set K)) = 1
    rw [Measure.pi_pi]
    simp [hμK]
  have hsmul : g • (e.symm '' S) = e.symm '' (g • S) := by
    rw [← Set.image_smul, ← Set.image_smul, Set.image_image, Set.image_image]
    congr 1
    funext x
    change (g : K) • e.symm x = e.symm ((g : K) • x)
    rw [map_smul]
  apply distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := μ) (s := e.symm '' S) (by rw [hS]; exact one_ne_zero)
    (by rw [hS]; exact ENNReal.one_ne_top)
  rw [hsmul, hmeasure, hS, mul_one]
  change (Measure.pi fun _ : ι => μK) (g • Set.pi Set.univ (fun _ => (C : Set K))) = _
  rw [smul_pi, Measure.pi_pi]
  simp only [Pi.smul_apply, ← distribHaarChar_mul μK g, hμK, mul_one,
    Finset.prod_const, Finset.card_univ, ι, Fintype.card_fin, ENNReal.coe_pow]

theorem log_character_scalar (g : Kˣ) :
    Real.log (distribHaarChar E g : ℝ) =
      (Module.finrank K E : ℝ) * Real.log (distribHaarChar K g : ℝ) := by
  rw [character_scalar, NNReal.coe_pow, Real.log_pow]

def scalarRegion (g : Kˣ) (U : NormalizedHaarRegion E) : NormalizedHaarRegion E :=
  mapNormalizedHaarRegion (LinearEquiv.smulOfUnit g).toContinuousLinearEquiv.toContinuousAddEquiv U

theorem scalarRegion_carrier (g : Kˣ) (U : NormalizedHaarRegion E) :
    (scalarRegion K E g U).val = g • U.val := rfl

theorem logVolume_scalarRegion [MeasurableSpace E] [BorelSpace E]
    (A U : NormalizedHaarRegion E) (g : Kˣ) :
    normalizedHaarLogVolume A (scalarRegion K E g U) =
      (Module.finrank K E : ℝ) * Real.log (distribHaarChar K g : ℝ) +
        normalizedHaarLogVolume A U := by
  have hm : normalizedHaarRealVolume A (scalarRegion K E g U) =
      (distribHaarChar E g : ℝ) * normalizedHaarRealVolume A U := by
    unfold normalizedHaarRealVolume
    rw [scalarRegion_carrier, ← distribHaarChar_mul, ENNReal.toReal_mul]
    rfl
  unfold normalizedHaarLogVolume
  rw [hm, Real.log_mul
    (by exact_mod_cast (distribHaarChar_pos (A := E) (g := g)).ne')
    (normalizedHaarRealVolume_pos A U).ne', log_character_scalar]

end CitedLV.Theorem311.FiniteVectorHaarCharacter
