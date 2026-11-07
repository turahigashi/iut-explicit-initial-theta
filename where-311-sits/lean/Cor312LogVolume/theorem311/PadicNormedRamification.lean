import Cor312LogVolume.Src.IUT4.Section1Proposition12iLogBounds
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact

noncomputable section
set_option autoImplicit false

namespace CitedLV.Theorem311.PadicNormedRamification

open Src.IUT4.Proposition12i IsDiscreteValuationRing
open scoped NormedField NNReal

abbrev normIntegers (K : Type*) [NormedField K] [IsUltrametricDist K] :=
  (NormedField.valuation (K := K)).integer

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] [IsUltrametricDist K]

include hp

theorem normIntegers_compact : CompactSpace (normIntegers K) := by
  letI : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  apply isCompact_iff_compactSpace.mp
  have hball : (normIntegers K : Set K) = Metric.closedBall 0 1 := by
    ext x
    change ‖x‖₊ ≤ 1 ↔ dist x 0 ≤ 1
    rw [dist_zero_right]
    exact NNReal.coe_le_coe.symm
  rw [hball]
  exact isCompact_closedBall (0 : K) 1

theorem normIntegers_discreteValuationRing : IsDiscreteValuationRing (normIntegers K) := by
  letI : NontriviallyNormedField K :=
    { ‹NormedField K› with
      non_trivial := by
        obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := ℚ_[p])
        exact ⟨algebraMap ℚ_[p] K x, by rwa [norm_algebraMap' K x]⟩ }
  letI : Valued K ℝ≥0 := NormedField.toValued
  letI : (Valued.v : Valuation K ℝ≥0).RankOne :=
    inferInstanceAs (NormedField.valuation (K := K)).RankOne
  letI : CompactSpace (Valued.integer K) := normIntegers_compact p K
  exact Valued.integer.isDiscreteValuationRing_of_compactSpace

def finiteExtensionRamification : RamificationData p K := by
  apply Classical.choice
  letI : NontriviallyNormedField K :=
    { ‹NormedField K› with
      non_trivial := by
        obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := ℚ_[p])
        exact ⟨algebraMap ℚ_[p] K x, by rwa [norm_algebraMap' K x]⟩ }
  letI : Valued K ℝ≥0 := NormedField.toValued
  letI : IsDiscreteValuationRing (Valued.integer K) :=
    normIntegers_discreteValuationRing p K
  have hpNorm : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    calc
      ‖(p : K)‖ = ‖algebraMap ℚ_[p] K (p : ℚ_[p])‖ := by rw [map_natCast]
      _ = ‖(p : ℚ_[p])‖ := norm_algebraMap' K _
      _ = _ := Padic.norm_p
  have hpNormLt : ‖(p : K)‖ < 1 := by
    rw [hpNorm]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpNorm
    exact (inv_pos.mpr hp0).ne' hpNorm.symm
  obtain ⟨π, hπ⟩ := exists_irreducible (Valued.integer K)
  let pInteger : Valued.integer K := ⟨(p : K), by
    change ‖(p : K)‖₊ ≤ 1
    exact_mod_cast hpNormLt.le⟩
  obtain ⟨e, u, he⟩ := eq_unit_mul_pow_irreducible
    (x := pInteger) (by simpa [pInteger, Subtype.ext_iff] using hpK) hπ
  have hpow : ‖(π : K)‖ ^ e = (p : ℝ)⁻¹ := by
    have h := congrArg (fun x : Valued.integer K => ‖(x : K)‖) he
    change ‖(p : K)‖ = ‖((u : Valued.integer K) : K) * (π : K) ^ e‖ at h
    simpa only [hpNorm, norm_mul, norm_pow, Valued.integer.norm_coe_unit, one_mul]
      using h.symm
  have hepos : 0 < e := by
    by_contra h
    have hezero : e = 0 := Nat.eq_zero_of_not_pos h
    rw [hezero, pow_zero, ← hpNorm] at hpow
    exact (ne_of_lt hpNormLt) hpow.symm
  have he0 : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hepos.ne'
  refine ⟨⟨e, hepos, (π : K), ?_, ?_⟩⟩
  · calc
      ‖(π : K)‖ = (‖(π : K)‖ ^ e) ^ (1 / (e : ℝ)) := by
        rw [← Real.rpow_natCast_mul (norm_nonneg _), mul_one_div_cancel he0, Real.rpow_one]
      _ = (p : ℝ) ^ (-(1 : ℝ) / (e : ℝ)) := by
        rw [hpow, ← Real.rpow_neg_one, ← Real.rpow_mul hp0.le]
        congr 1
        ring
  · intro x hx
    obtain ⟨n, u, hu⟩ := exists_units_eq_smul_zpow_of_irreducible (K := K) hπ hx
    refine ⟨n, ?_⟩
    rw [hu]
    change ‖((u : Valued.integer K) : K) * (π : K) ^ n‖ = _
    rw [norm_mul, norm_zpow, Valued.integer.norm_coe_unit, one_mul]

end CitedLV.Theorem311.PadicNormedRamification
