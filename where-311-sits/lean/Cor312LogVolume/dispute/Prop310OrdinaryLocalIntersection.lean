import Cor312LogVolume.dispute.Prop310ActualIntersection

set_option autoImplicit false
noncomputable section
namespace Dispute.Prop310OrdinaryLocalIntersection

open scoped NumberField

open NumberField IsDedekindDomain
open Dispute.Prop310AllPlacesArithmetic
open Dispute.Prop310ActualIntersection

universe u

variable (F : Type u) [Field F] [NumberField F]

abbrev OrdinaryPlace :=
  Sum (HeightOneSpectrum (𝓞 F)) (F →+* ℂ)

def localIntegralLocus : OrdinaryPlace F → Set Fˣ
  | Sum.inl v =>
      {x | ‖FinitePlace.embedding v (x : F)‖ ≤ 1}
  | Sum.inr φ =>
      {x | ‖φ (x : F)‖ ≤ 1}

def localIntegralIntersection : Set Fˣ :=
  ⋂ w : OrdinaryPlace F, localIntegralLocus F w

theorem mem_localIntegralIntersection_iff
    (x : Fˣ) :
    x ∈ localIntegralIntersection F ↔
      AllPlacesIntegralBound F (x : F) := by
  constructor
  · intro h
    refine ⟨x.ne_zero, ?_, ?_⟩
    · intro v
      exact Set.mem_iInter.mp h (Sum.inl v)
    · intro φ
      exact Set.mem_iInter.mp h (Sum.inr φ)
  · rintro ⟨_, hfin, hinf⟩
    apply Set.mem_iInter.mpr
    intro w
    cases w with
    | inl v => exact hfin v
    | inr φ => exact hinf φ

theorem localIntegralIntersection_eq_allPlacesCompletion :
    localIntegralIntersection F =
      allPlacesCompletionFieldUnits F := by
  ext x
  exact mem_localIntegralIntersection_iff F x

theorem localIntegralIntersection_eq_rootOfUnityImage :
    localIntegralIntersection F = rootOfUnityImage F := by
  rw [localIntegralIntersection_eq_allPlacesCompletion F,
    allPlacesCompletionFieldUnits_eq_rootOfUnityImage F]

theorem globalGroup_inter_localIntegers_eq_rootsOfUnity :
    (Set.univ : Set Fˣ) ∩ localIntegralIntersection F =
      rootOfUnityImage F := by
  rw [Set.univ_inter, localIntegralIntersection_eq_rootOfUnityImage F]

theorem ratio_mem_localIntersection_iff_torsion_translate
    (a b : Fˣ) :
    b * a⁻¹ ∈ localIntegralIntersection F ↔
      ∃ zeta : NumberField.Units.torsion F,
        globalUnitMap F
            ((zeta : NumberField.Units.torsion F) : (𝓞 F)ˣ) * a = b := by
  rw [localIntegralIntersection_eq_allPlacesCompletion F]
  exact ratio_mem_allPlacesCompletion_iff_torsion_translate F a b

end Dispute.Prop310OrdinaryLocalIntersection
end
