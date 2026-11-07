import Cor312LogVolume.Src.Lib.P211LogVolume
import Cor312LogVolume.theorem311.FiniteExtensionHaarCharacter
import Cor312LogVolume.theorem311.PadicPrimeHaarCharacter
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Analysis.Normed.Algebra.Ultra

noncomputable section
set_option autoImplicit false

namespace CitedLV.ThetaLink.P211FiniteLocalField

open Src.Lib.P211Datum Src.Lib.P211Valuation
open CitedLV.Theorem311 MeasureTheory
open scoped NNReal

theorem qbVal_integral : IsIntegral ℚ_[211] qbVal := by
  apply IsIntegral.of_pow (n := 7) (by norm_num)
  rw [qbVal_spec.1]
  change IsIntegral ℚ_[211] ((algebraMap ℚ_[211] ℂ_[211] (211 : ℚ_[211])) ^ 29)
  exact isIntegral_algebraMap.pow 29

def localField : IntermediateField ℚ_[211] ℂ_[211] :=
  IntermediateField.adjoin ℚ_[211] {qbVal}

abbrev LocalField := ↥localField

instance finiteDimensional : FiniteDimensional ℚ_[211] LocalField :=
  IntermediateField.adjoin.finiteDimensional qbVal_integral

instance completeSpace : CompleteSpace LocalField :=
  FiniteDimensional.complete ℚ_[211] LocalField

instance properSpace : ProperSpace LocalField :=
  FiniteDimensional.proper ℚ_[211] LocalField

instance ultrametric : IsUltrametricDist LocalField :=
  IsUltrametricDist.of_normedAlgebra ℚ_[211]

def qElement : LocalField :=
  ⟨qbVal, IntermediateField.mem_adjoin_simple_self _ _⟩

theorem qElement_ne_zero : qElement ≠ 0 := by
  intro h
  exact qbVal_ne_zero (congrArg Subtype.val h)

def qUnit : LocalFieldˣ := Units.mk0 qElement qElement_ne_zero

theorem qUnit_coe : ((qUnit : LocalField) : ℂ_[211]) = (qb : ℂ_[211]) := rfl

theorem qUnit_small : ‖(qUnit : LocalField)‖ < 1 := qb_norm_lt_one

theorem qUnit_pow : qUnit ^ 7 =
    (Units.map (algebraMap ℚ_[211] LocalField).toMonoidHom (padicPrimeUnit 211)) ^ 29 := by
  apply Units.ext
  apply Subtype.ext
  exact qbVal_spec.1

theorem log_character_eq_degree :
    Real.log (distribHaarChar LocalField qUnit : ℝ) =
      (Module.finrank ℚ_[211] LocalField : ℝ) * (-(29 / 7) * Real.log 211) := by
  have h := congrArg (fun u : LocalFieldˣ => Real.log (distribHaarChar LocalField u : ℝ))
    qUnit_pow
  simp only [map_pow, NNReal.coe_pow, Real.log_pow] at h
  rw [FiniteExtensionHaarCharacter.character_algebraMap,
    NNReal.coe_pow, Real.log_pow, realLog_distribHaarChar_padicPrime] at h
  norm_num only [Nat.cast_ofNat] at h
  nlinarith

theorem normalized_log_character :
    Real.log (distribHaarChar LocalField qUnit : ℝ) /
      Module.finrank ℚ_[211] LocalField = -(29 / 7) * Real.log 211 := by
  rw [log_character_eq_degree]
  have hd : (Module.finrank ℚ_[211] LocalField : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ_[211] LocalField).ne'
  field_simp

end CitedLV.ThetaLink.P211FiniteLocalField
