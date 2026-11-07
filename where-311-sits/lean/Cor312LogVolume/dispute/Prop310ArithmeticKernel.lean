import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Cor312LogVolume.Src.IUT3.Section1Remark123LogOfRootsOfUnity

set_option autoImplicit false
noncomputable section
namespace Dispute.Prop310ArithmeticKernel

open scoped NumberField
open NumberField
open NumberField.InfinitePlace

universe u v

variable (F : Type u) [Field F] [NumberField F]

def EverywhereUnit (a : (𝓞 F)ˣ) : Prop :=
  ∀ w : InfinitePlace F, w a = 1

theorem everywhereUnit_iff_torsion (a : (𝓞 F)ˣ) :
    EverywhereUnit F a ↔ a ∈ NumberField.Units.torsion F :=
  (NumberField.Units.mem_torsion (K := F)).symm

def everywhereUnitSet : Set ((𝓞 F)ˣ) :=
  {a | EverywhereUnit F a}

theorem everywhereUnitSet_eq_torsion :
    everywhereUnitSet F =
      (NumberField.Units.torsion F : Set ((𝓞 F)ˣ)) := by
  ext a
  exact everywhereUnit_iff_torsion F a

def EverywhereIntegralBound (x : F) : Prop :=
  x ≠ 0 ∧ IsIntegral ℤ x ∧
    ∀ φ : F →+* ℂ, ‖φ x‖ ≤ 1

theorem everywhereIntegralBound_pow_eq_one
    (x : F) (hx : EverywhereIntegralBound F x) :
    ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  rcases hx with ⟨hx0, hxi, hnorm⟩
  obtain ⟨n, hn, hpow⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_le_one F ℂ hx0 hxi hnorm
  exact ⟨n, hn, hpow⟩

theorem everywhereUnit_of_integralBound
    (a : (𝓞 F)ˣ)
    (h : EverywhereIntegralBound F (((a : 𝓞 F) : F))) :
    EverywhereUnit F a := by
  apply (everywhereUnit_iff_torsion F a).2
  rw [NumberField.Units.torsion, CommGroup.mem_torsion,
    isOfFinOrder_iff_pow_eq_one]
  obtain ⟨n, hn, hpow⟩ :=
    everywhereIntegralBound_pow_eq_one F (a : F) (by
      simpa only [NumberField.Units.coe_coe] using h)
  refine ⟨n, hn, ?_⟩
  ext
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap,
    NumberField.Units.coe_pow, hpow,
    NumberField.RingOfIntegers.coe_eq_algebraMap,
    NumberField.Units.coe_one]

theorem integralBound_fieldElement_lifts_to_torsionUnit
    (x : F) (h : EverywhereIntegralBound F x) :
    ∃ zeta : NumberField.Units.torsion F,
      (((zeta : NumberField.Units.torsion F) : (𝓞 F)ˣ) : F) = x := by
  obtain ⟨n, hn, hpow⟩ := everywhereIntegralBound_pow_eq_one F x h
  let a : 𝓞 F := ⟨x, h.2.1⟩
  let b : 𝓞 F := ⟨x ^ (n - 1), h.2.1.pow (n - 1)⟩
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hab : a * b = 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    change x * x ^ (n - 1) = 1
    rw [← pow_succ', hn1, hpow]
  let u : (𝓞 F)ˣ := Units.mkOfMulEqOne a b hab
  have huField : (u : F) = x := rfl
  have huBound : EverywhereIntegralBound F (u : F) := by
    simpa only [huField] using h
  have huEverywhere : EverywhereUnit F u :=
    everywhereUnit_of_integralBound F u (by
      simpa only [NumberField.Units.coe_coe] using huBound)
  have huTorsion : u ∈ NumberField.Units.torsion F :=
    (everywhereUnit_iff_torsion F u).mp huEverywhere
  exact ⟨⟨u, huTorsion⟩, huField⟩

theorem everywhereUnit_pow_eq_one (a : (𝓞 F)ˣ)
    (ha : EverywhereUnit F a) :
    ∃ n : ℕ, 0 < n ∧ (a : F) ^ n = 1 := by
  have ht : a ∈ NumberField.Units.torsion F :=
    (everywhereUnit_iff_torsion F a).mp ha
  rw [NumberField.Units.torsion, CommGroup.mem_torsion,
    isOfFinOrder_iff_pow_eq_one] at ht
  obtain ⟨n, hn, hpow⟩ := ht
  refine ⟨n, hn, ?_⟩
  have hfield := congrArg (fun z : (𝓞 F)ˣ => (z : F)) hpow
  simpa only [NumberField.Units.coe_pow, NumberField.Units.coe_one] using hfield

theorem mapped_everywhereUnit_pow_eq_one
    {L : Type v} [Field L] (φ : F →+* L)
    (a : (𝓞 F)ˣ) (ha : EverywhereUnit F a) :
    ∃ n : ℕ, 0 < n ∧ (φ (a : F)) ^ n = 1 := by
  obtain ⟨n, hn, hpow⟩ := everywhereUnit_pow_eq_one F a ha
  refine ⟨n, hn, ?_⟩
  simpa only [map_pow, map_one] using congrArg φ hpow

section LocalLog

variable {p : ℕ} [Fact p.Prime]
variable {L : Type v} [NormedField L] [NormedAlgebra ℚ_[p] L]
  [CompleteSpace L] [IsUltrametricDist L]

open Src.IUT3.Proposition35ii
open Src.IUT3.Remark123

theorem mapped_everywhereUnit_log_indeterminacy_vanishes
    (φ : F →+* L) (a : (𝓞 F)ˣ) (ha : EverywhereUnit F a)
    {u y z : L}
    (hza : LogRel p (φ (a : F) * u) z)
    (hu : LogRel p u y) :
    z = y := by
  apply root_of_unity_indeterminacy_vanishes (p := p)
  · exact mapped_everywhereUnit_pow_eq_one F φ a ha
  · exact hza
  · exact hu

theorem mapped_integralBound_log_indeterminacy_vanishes
    (φ : F →+* L) (a : (𝓞 F)ˣ)
    (ha : EverywhereIntegralBound F (((a : 𝓞 F) : F)))
    {u y z : L}
    (hza : LogRel p (φ (a : F) * u) z)
    (hu : LogRel p u y) :
    z = y :=
  mapped_everywhereUnit_log_indeterminacy_vanishes
    F φ a (everywhereUnit_of_integralBound F a ha) hza hu

end LocalLog

end Dispute.Prop310ArithmeticKernel
end
