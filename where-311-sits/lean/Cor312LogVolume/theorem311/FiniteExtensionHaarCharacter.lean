import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.Module.PointwisePi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Pointwise ENNReal NNReal

namespace CitedLV.Theorem311.FiniteExtensionHaarCharacter

variable (K L : Type*) [NontriviallyNormedField K] [NormedField L]
  [Algebra K L] [ContinuousSMul K L] [FiniteDimensional K L]
  [LocallyCompactSpace K] [LocallyCompactSpace L]

local instance base_proper : ProperSpace K := ProperSpace.of_locallyCompactSpace K

theorem character_algebraMap (g : Kˣ) :
    distribHaarChar L (Units.map (algebraMap K L).toMonoidHom g) =
      distribHaarChar K g ^ Module.finrank K L := by
  classical
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  letI : MeasurableSpace L := borel L
  letI : BorelSpace L := ⟨rfl⟩
  let C : PositiveCompacts K := Classical.choice inferInstance
  let μK : Measure K := Measure.addHaarMeasure C
  let ι := Fin (Module.finrank K L)
  let e : L ≃L[K] (ι → K) := (Module.finBasis K L).equivFunL
  letI : SecondCountableTopology L := e.toHomeomorph.secondCountableTopology
  let ν : Measure (ι → K) := Measure.pi fun _ => μK
  let μ : Measure L := ν.map e.symm
  let S : Set (ι → K) := Set.pi Set.univ fun _ => (C : Set K)
  have hμK : μK (C : Set K) = 1 := Measure.addHaarMeasure_self
  have hmeasure (T : Set (ι → K)) : μ (e.symm '' T) = ν T := by
    change ν.map e.symm (e.symm '' T) = ν T
    have he : MeasurableEmbedding (e.symm : (ι → K) → L) :=
      e.symm.toHomeomorph.measurableEmbedding
    rw [he.map_apply,
      Set.preimage_image_eq T e.symm.injective]
  have hS : μ (e.symm '' S) = 1 := by
    rw [hmeasure]
    change (Measure.pi fun _ : ι => μK) (Set.pi Set.univ fun _ => (C : Set K)) = 1
    rw [Measure.pi_pi]
    simp [hμK]
  have hsmul :
      (Units.map (algebraMap K L).toMonoidHom g) • (e.symm '' S) =
        e.symm '' (g • S) := by
    rw [← Set.image_smul, ← Set.image_smul, Set.image_image, Set.image_image]
    congr 1
    funext x
    change algebraMap K L (g : K) * e.symm x = e.symm ((g : K) • x)
    rw [← Algebra.smul_def, map_smul]
  apply distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := μ) (s := e.symm '' S) (by rw [hS]; exact one_ne_zero)
    (by rw [hS]; exact ENNReal.one_ne_top)
  rw [hsmul, hmeasure, hS, mul_one]
  change (Measure.pi fun _ : ι => μK) (g • Set.pi Set.univ (fun _ => (C : Set K))) = _
  rw [smul_pi, Measure.pi_pi]
  simp only [Pi.smul_apply, ← distribHaarChar_mul μK g, hμK, mul_one,
    Finset.prod_const, Finset.card_univ, ι, Fintype.card_fin, ENNReal.coe_pow]

theorem log_character_algebraMap_div_finrank (g : Kˣ) :
    Real.log (distribHaarChar L (Units.map (algebraMap K L).toMonoidHom g) : ℝ) /
        Module.finrank K L = Real.log (distribHaarChar K g : ℝ) := by
  have hd : (Module.finrank K L : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
  rw [character_algebraMap, NNReal.coe_pow, Real.log_pow]
  field_simp

end CitedLV.Theorem311.FiniteExtensionHaarCharacter
