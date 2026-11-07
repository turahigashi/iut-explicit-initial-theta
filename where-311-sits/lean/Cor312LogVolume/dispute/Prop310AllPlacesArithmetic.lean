import Cor312LogVolume.dispute.Prop310ArithmeticKernel
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.SInteger

set_option autoImplicit false
noncomputable section
namespace Dispute.Prop310AllPlacesArithmetic

open scoped NumberField
open NumberField
open IsDedekindDomain
open Dispute.Prop310ArithmeticKernel

universe u

variable (F : Type u) [Field F] [NumberField F]

def FinitePlaceIntegralBound (x : F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F),
    ‖FinitePlace.embedding v x‖ ≤ 1

def InfinitePlaceIntegralBound (x : F) : Prop :=
  ∀ φ : F →+* ℂ, ‖φ x‖ ≤ 1

def FiniteValuationIntegralBound (x : F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F x ≤ 1

def AllPlacesValuationIntegralBound (x : F) : Prop :=
  x ≠ 0 ∧ FiniteValuationIntegralBound F x ∧
    InfinitePlaceIntegralBound F x

def AllPlacesIntegralBound (x : F) : Prop :=
  x ≠ 0 ∧ FinitePlaceIntegralBound F x ∧
    InfinitePlaceIntegralBound F x

theorem finitePlaceIntegralBound_of_isIntegral
    (x : F) (hx : IsIntegral ℤ x) :
    FinitePlaceIntegralBound F x := by
  obtain ⟨a : 𝓞 F, ha⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).mp hx
  intro v
  rw [← ha]
  exact FinitePlace.norm_le_one F v a

theorem finiteValuationIntegralBound_iff_isIntegral
    (x : F) :
    FiniteValuationIntegralBound F x ↔ IsIntegral ℤ x := by
  constructor
  · intro h
    have hx :
        x ∈ (algebraMap (𝓞 F) F).range :=
      HeightOneSpectrum.mem_integers_of_valuation_le_one F x h
    obtain ⟨a : 𝓞 F, ha⟩ := hx
    rw [← ha]
    exact a.isIntegral_coe
  · intro hx
    obtain ⟨a : 𝓞 F, ha⟩ :=
      (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).mp hx
    intro v
    rw [← ha]
    exact v.valuation_le_one a

theorem finitePlace_norm_le_one_iff_valuation_le_one
    (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    ‖FinitePlace.embedding v x‖ ≤ 1 ↔ v.valuation F x ≤ 1 := by
  rw [FinitePlace.norm_embedding']
  exact WithZeroMulInt.toNNReal_le_one_iff
    (HeightOneSpectrum.one_lt_absNorm_nnreal v)

theorem finitePlaceIntegralBound_iff_isIntegral
    (x : F) :
    FinitePlaceIntegralBound F x ↔ IsIntegral ℤ x := by
  constructor
  · intro h
    apply (finiteValuationIntegralBound_iff_isIntegral F x).mp
    intro v
    exact (finitePlace_norm_le_one_iff_valuation_le_one F v x).mp (h v)
  · intro h
    have hv :
        FiniteValuationIntegralBound F x :=
      (finiteValuationIntegralBound_iff_isIntegral F x).mpr h
    intro v
    exact (finitePlace_norm_le_one_iff_valuation_le_one F v x).mpr (hv v)

theorem allPlacesIntegralBound_iff_allPlacesValuation
    (x : F) :
    AllPlacesIntegralBound F x ↔
      AllPlacesValuationIntegralBound F x := by
  rw [AllPlacesIntegralBound, AllPlacesValuationIntegralBound,
    finitePlaceIntegralBound_iff_isIntegral F x,
    finiteValuationIntegralBound_iff_isIntegral F x]

theorem everywhereIntegralBound_iff_allPlacesValuation
    (x : F) :
    EverywhereIntegralBound F x ↔
      AllPlacesValuationIntegralBound F x := by

  rw [EverywhereIntegralBound, AllPlacesValuationIntegralBound,
    finiteValuationIntegralBound_iff_isIntegral F x,
    InfinitePlaceIntegralBound]

theorem everywhereIntegralBound_iff_allPlacesCompletion
    (x : F) :
    EverywhereIntegralBound F x ↔
      AllPlacesIntegralBound F x := by
  rw [everywhereIntegralBound_iff_allPlacesValuation F x,
    ← allPlacesIntegralBound_iff_allPlacesValuation F x]

theorem everywhereIntegralBound_gives_allPlaces
    (x : F) (h : EverywhereIntegralBound F x) :
    AllPlacesIntegralBound F x := by
  refine ⟨h.1, finitePlaceIntegralBound_of_isIntegral F x h.2.1, ?_⟩
  exact h.2.2

theorem everywhereIntegralBound_allPlaces_pow_eq_one
    (x : F) (h : EverywhereIntegralBound F x) :
    AllPlacesIntegralBound F x ∧
      ∃ n : ℕ, 0 < n ∧ x ^ n = 1 :=
  ⟨everywhereIntegralBound_gives_allPlaces F x h,
    everywhereIntegralBound_pow_eq_one F x h⟩

end Dispute.Prop310AllPlacesArithmetic
end
