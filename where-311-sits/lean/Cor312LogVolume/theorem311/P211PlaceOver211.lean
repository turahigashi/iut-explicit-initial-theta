import Cor312LogVolume.theorem311.P211FieldCopyReadout
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211PlaceOver211

open CitedLV.Theorem311.P211FieldCopyReadout
open scoped NumberField
open NumberField IsDedekindDomain Ideal

def p211 : Nat.Primes := ⟨211, by norm_num⟩

def v211 : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p211

theorem finrank_int_ringOfIntegers_rat : Module.finrank ℤ (𝓞 ℚ) = 1 := by
  rw [NumberField.RingOfIntegers.rank]
  simp

theorem absNorm_span_211 :
    Ideal.absNorm (Ideal.span {((211 : ℕ) : 𝓞 ℚ)}) = 211 := by
  rw [Ideal.absNorm_span_natCast, finrank_int_ringOfIntegers_rat, pow_one]

theorem v211_asIdeal : v211.asIdeal = Ideal.span {((211 : ℕ) : 𝓞 ℚ)} := by
  show ((Ideal.span {((211 : ℕ) : ℤ)}).map
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm.toRingHom) = _
  rw [Ideal.map_span]
  congr 1
  simp

theorem maxPowDividing_self
    {R : Type*} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R) :
    v.maxPowDividing v.asIdeal = v.asIdeal := by
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count v v.ne_bot,
    UniqueFactorizationMonoid.normalizedFactors_irreducible v.irreducible]
  simp

theorem x211_ne_zero : ((211 : ℕ) : 𝓞 ℚ) ≠ 0 := by
  intro h
  have h2 : algebraMap (𝓞 ℚ) ℚ ((211 : ℕ) : 𝓞 ℚ) = 0 := by rw [h, map_zero]
  rw [map_natCast] at h2
  norm_num at h2

theorem absNorm_maxPowDividing_211 :
    Ideal.absNorm (v211.maxPowDividing (Ideal.span {((211 : ℕ) : 𝓞 ℚ)})) = 211 := by
  rw [← v211_asIdeal, maxPowDividing_self, v211_asIdeal, absNorm_span_211]

def y211 : ℚˣ := Units.mk0 (211 : ℚ) (by norm_num)

theorem y211_eq : ((y211 : ℚ)) = algebraMap (𝓞 ℚ) ℚ ((211 : ℕ) : 𝓞 ℚ) := by
  show (211 : ℚ) = _
  rw [map_natCast]
  norm_num

theorem cLogReadout_y211 : cLogReadout ℚ v211 y211 = -Real.log 211 :=
  cLogReadout_eq_neg_log_of_absNorm ℚ v211 ((211 : ℕ) : 𝓞 ℚ)
    x211_ne_zero absNorm_maxPowDividing_211 y211 y211_eq

theorem qPilot_value_at_211 :
    (1 / 7 : ℝ) * cLogReadout ℚ v211 (y211 ^ 29) = -(29 / 7) * Real.log 211 :=
  qPilot_value_from_fieldCopy ℚ v211 ((211 : ℕ) : 𝓞 ℚ)
    x211_ne_zero absNorm_maxPowDividing_211 y211 y211_eq

theorem theta_value_at_211 (j : ℕ) :
    (1 / 7 : ℝ) * cLogReadout ℚ v211 (y211 ^ (29 * j ^ 2))
      = ((j : ℝ) ^ 2) * (-(29 / 7) * Real.log 211) :=
  theta_value_from_fieldCopy ℚ v211 ((211 : ℕ) : 𝓞 ℚ)
    x211_ne_zero absNorm_maxPowDividing_211 y211 y211_eq j

theorem qPilot_is_theta_one :
    (1 / 7 : ℝ) * cLogReadout ℚ v211 (y211 ^ 29)
      = (1 / 7 : ℝ) * cLogReadout ℚ v211 (y211 ^ (29 * 1 ^ 2)) := by
  norm_num

end CitedLV.Theorem311.P211PlaceOver211
end
