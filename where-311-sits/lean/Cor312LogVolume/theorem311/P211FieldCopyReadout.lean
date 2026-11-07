import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211FieldCopyReadout

open scoped NumberField
open NumberField IsDedekindDomain Ideal

universe u
variable (F : Type u) [Field F] [NumberField F]

def cLogReadout (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ℝ :=
  Real.log ‖FinitePlace.embedding v (x : F)‖

theorem cLogReadout_eq (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    cLogReadout F v x = Real.log ‖FinitePlace.embedding v (x : F)‖ := rfl

theorem cLogReadout_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    cLogReadout F v (x * y) = cLogReadout F v x + cLogReadout F v y := by
  have hx : ‖FinitePlace.embedding v (x : F)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero _).2 x.ne_zero
  have hy : ‖FinitePlace.embedding v (y : F)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero _).2 y.ne_zero
  show Real.log ‖FinitePlace.embedding v ((x * y : Fˣ) : F)‖ = _
  rw [Units.val_mul, map_mul, norm_mul, Real.log_mul hx hy]
  rfl

@[simp] theorem cLogReadout_one (v : HeightOneSpectrum (𝓞 F)) :
    cLogReadout F v 1 = 0 := by
  simp [cLogReadout, Real.log_one]

theorem cLogReadout_pow (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) (n : ℕ) :
    cLogReadout F v (x ^ n) = (n : ℝ) * cLogReadout F v x := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, cLogReadout_mul, ih]
      push_cast
      ring

theorem weighted_readout_of_pow (v : HeightOneSpectrum (𝓞 F)) (y : Fˣ)
    (hy : cLogReadout F v y = -Real.log 211) :
    (1 / 7 : ℝ) * cLogReadout F v (y ^ 29) = -(29 / 7) * Real.log 211 := by
  rw [cLogReadout_pow, hy]
  push_cast
  ring

theorem weighted_readout_general (v : HeightOneSpectrum (𝓞 F)) (y : Fˣ)
    (hy : cLogReadout F v y = -Real.log 211) (n : ℕ) :
    (1 / 7 : ℝ) * cLogReadout F v (y ^ n) = -((n : ℝ) / 7) * Real.log 211 := by
  rw [cLogReadout_pow, hy]
  ring

theorem weighted_readout_theta (v : HeightOneSpectrum (𝓞 F)) (y : Fˣ)
    (hy : cLogReadout F v y = -Real.log 211) (j : ℕ) :
    (1 / 7 : ℝ) * cLogReadout F v (y ^ (29 * j ^ 2))
      = ((j : ℝ) ^ 2) * (-(29 / 7) * Real.log 211) := by
  rw [cLogReadout_pow, hy]
  push_cast
  ring

theorem cLogReadout_eq_neg_log_of_absNorm
    (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) (hx : x ≠ 0)
    (hN : Ideal.absNorm (v.maxPowDividing (Ideal.span {x})) = 211)
    (y : Fˣ) (hy : (y : F) = algebraMap (𝓞 F) F x) :
    cLogReadout F v y = -Real.log 211 := by
  have h := NumberField.HeightOneSpectrum.embedding_mul_absNorm
    (R := 𝓞 F) (K := F) (v := v) hx
  rw [hN] at h
  have hnorm : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F x)‖ = (211 : ℝ)⁻¹ := by
    push_cast at h
    field_simp
    linarith
  rw [cLogReadout_eq, hy, hnorm, Real.log_inv]

theorem qPilot_value_from_fieldCopy
    (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) (hx : x ≠ 0)
    (hN : Ideal.absNorm (v.maxPowDividing (Ideal.span {x})) = 211)
    (y : Fˣ) (hy : (y : F) = algebraMap (𝓞 F) F x) :
    (1 / 7 : ℝ) * cLogReadout F v (y ^ 29) = -(29 / 7) * Real.log 211 :=
  weighted_readout_of_pow F v y (cLogReadout_eq_neg_log_of_absNorm F v x hx hN y hy)

theorem theta_value_from_fieldCopy
    (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) (hx : x ≠ 0)
    (hN : Ideal.absNorm (v.maxPowDividing (Ideal.span {x})) = 211)
    (y : Fˣ) (hy : (y : F) = algebraMap (𝓞 F) F x) (j : ℕ) :
    (1 / 7 : ℝ) * cLogReadout F v (y ^ (29 * j ^ 2))
      = ((j : ℝ) ^ 2) * (-(29 / 7) * Real.log 211) :=
  weighted_readout_theta F v y (cLogReadout_eq_neg_log_of_absNorm F v x hx hN y hy) j

end CitedLV.Theorem311.P211FieldCopyReadout
end
