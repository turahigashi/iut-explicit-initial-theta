import Cor312LogVolume.dispute.Prop310ArithmeticKernel
import Cor312LogVolume.dispute.Prop310AllPlacesArithmetic

set_option autoImplicit false
noncomputable section
namespace Dispute.Prop310ActualIntersection

open scoped NumberField
open NumberField
open NumberField.InfinitePlace
open Dispute.Prop310ArithmeticKernel
open Dispute.Prop310AllPlacesArithmetic

universe u

variable (F : Type u) [Field F] [NumberField F]

def globalUnitMap : (𝓞 F)ˣ →* Fˣ :=
  Units.map (algebraMap (𝓞 F) F).toMonoidHom

@[simp] theorem globalUnitMap_val (a : (𝓞 F)ˣ) :
    ((globalUnitMap F a : Fˣ) : F) = (a : F) := rfl

def globalIntegralUnits : Set Fˣ :=
  Set.range (globalUnitMap F)

def archUnitCircle : Set Fˣ :=
  {x | ∀ w : InfinitePlace F, w (x : F) = 1}

def rootOfUnityImage : Set Fˣ :=
  globalUnitMap F '' (NumberField.Units.torsion F : Set ((𝓞 F)ˣ))

def everywhereIntegralFieldUnits : Set Fˣ :=
  {x | EverywhereIntegralBound F (x : F)}

def allPlacesIntegralFieldUnits : Set Fˣ :=
  {x | AllPlacesValuationIntegralBound F (x : F)}

def allPlacesCompletionFieldUnits : Set Fˣ :=
  {x | AllPlacesIntegralBound F (x : F)}

theorem allPlacesCompletionFieldUnits_eq_allPlacesIntegralFieldUnits :
    allPlacesCompletionFieldUnits F = allPlacesIntegralFieldUnits F := by
  ext x
  exact allPlacesIntegralBound_iff_allPlacesValuation F (x : F)

theorem allPlacesIntegralFieldUnits_eq_everywhereIntegralFieldUnits :
    allPlacesIntegralFieldUnits F = everywhereIntegralFieldUnits F := by
  ext x
  exact (everywhereIntegralBound_iff_allPlacesValuation F (x : F)).symm

theorem everywhereIntegralFieldUnits_eq_rootOfUnityImage :
    everywhereIntegralFieldUnits F = rootOfUnityImage F := by
  ext x
  constructor
  · intro hx
    obtain ⟨zeta, hzeta⟩ :=
      integralBound_fieldElement_lifts_to_torsionUnit F (x : F) hx
    refine ⟨((zeta : NumberField.Units.torsion F) : (𝓞 F)ˣ),
      zeta.property, ?_⟩
    apply Units.ext
    simpa only [globalUnitMap_val] using hzeta
  · rintro ⟨a, ha, rfl⟩
    have hevery : EverywhereUnit F a :=
      (everywhereUnit_iff_torsion F a).mpr ha
    refine ⟨?_, ?_, ?_⟩
    · simpa only [globalUnitMap_val] using (globalUnitMap F a).ne_zero
    · simpa only [globalUnitMap_val] using
        (a : 𝓞 F).isIntegral_coe
    · intro φ
      obtain ⟨n, hn, hpow⟩ :=
        mapped_everywhereUnit_pow_eq_one F φ a hevery
      exact (Complex.norm_eq_one_of_pow_eq_one hpow
        (Nat.ne_of_gt hn)).le

theorem allPlacesIntegralFieldUnits_eq_rootOfUnityImage :
    allPlacesIntegralFieldUnits F = rootOfUnityImage F := by
  rw [allPlacesIntegralFieldUnits_eq_everywhereIntegralFieldUnits F,
    everywhereIntegralFieldUnits_eq_rootOfUnityImage F]

theorem allPlacesCompletionFieldUnits_eq_rootOfUnityImage :
    allPlacesCompletionFieldUnits F = rootOfUnityImage F := by
  rw [allPlacesCompletionFieldUnits_eq_allPlacesIntegralFieldUnits F,
    allPlacesIntegralFieldUnits_eq_rootOfUnityImage F]

theorem ratio_mem_allPlaces_iff_torsion_translate
    (a b : Fˣ) :
    b * a⁻¹ ∈ allPlacesIntegralFieldUnits F ↔
      ∃ zeta : NumberField.Units.torsion F,
        globalUnitMap F
            ((zeta : NumberField.Units.torsion F) : (𝓞 F)ˣ) * a = b := by
  constructor
  · intro h
    have hr : b * a⁻¹ ∈ rootOfUnityImage F := by
      rw [← allPlacesIntegralFieldUnits_eq_rootOfUnityImage F]
      exact h
    obtain ⟨u, hu, hratio⟩ := hr
    let zeta : NumberField.Units.torsion F := ⟨u, hu⟩
    refine ⟨zeta, ?_⟩
    have hz :
        globalUnitMap F
            ((zeta : NumberField.Units.torsion F) : (𝓞 F)ˣ) =
          b * a⁻¹ := by

      simpa [zeta] using hratio
    rw [hz]
    simp [mul_assoc]
  · rintro ⟨zeta, hzeta⟩
    have hratio :
        b * a⁻¹ =
          globalUnitMap F
            ((zeta : NumberField.Units.torsion F) : (𝓞 F)ˣ) := by
      calc
        b * a⁻¹ =
            (globalUnitMap F
                ((zeta : NumberField.Units.torsion F) : (𝓞 F)ˣ) * a) * a⁻¹ := by
              rw [hzeta]
        _ = globalUnitMap F
              ((zeta : NumberField.Units.torsion F) : (𝓞 F)ˣ) := by
              simp [mul_assoc]
    rw [allPlacesIntegralFieldUnits_eq_rootOfUnityImage F, hratio]
    exact ⟨((zeta : NumberField.Units.torsion F) : (𝓞 F)ˣ),
      zeta.property, rfl⟩

theorem ratio_mem_allPlacesCompletion_iff_torsion_translate
    (a b : Fˣ) :
    b * a⁻¹ ∈ allPlacesCompletionFieldUnits F ↔
      ∃ zeta : NumberField.Units.torsion F,
        globalUnitMap F
            ((zeta : NumberField.Units.torsion F) : (𝓞 F)ˣ) * a = b := by
  rw [allPlacesCompletionFieldUnits_eq_allPlacesIntegralFieldUnits F]
  exact ratio_mem_allPlaces_iff_torsion_translate F a b

theorem allPlaces_ratio_gives_torsion_correction
    (a b : Fˣ)
    (h : b * a⁻¹ ∈ allPlacesIntegralFieldUnits F) :
    ∃ zeta : NumberField.Units.torsion F,
      globalUnitMap F
          ((zeta : NumberField.Units.torsion F) : (𝓞 F)ˣ) * a = b :=
  (ratio_mem_allPlaces_iff_torsion_translate F a b).mp h

theorem globalIntegral_inter_archCircle_eq_rootOfUnityImage :
    globalIntegralUnits F ∩ archUnitCircle F =
      rootOfUnityImage F := by
  ext x
  constructor
  · rintro ⟨⟨a, rfl⟩, hcircle⟩
    have ha : EverywhereUnit F a := by
      intro w
      simpa only [globalUnitMap_val] using hcircle w
    have ht : a ∈ NumberField.Units.torsion F :=
      (everywhereUnit_iff_torsion F a).mp ha
    exact ⟨a, ht, rfl⟩
  · rintro ⟨a, ht, rfl⟩
    refine ⟨⟨a, rfl⟩, ?_⟩
    intro w
    simpa only [globalUnitMap_val] using
      (NumberField.Units.mem_torsion (K := F)).mp ht w

theorem mem_intersection_iff_root_image (x : Fˣ) :
    x ∈ globalIntegralUnits F ∩ archUnitCircle F ↔
      ∃ zeta : NumberField.Units.torsion F,
        globalUnitMap F
          (zeta : NumberField.Units.torsion F) = x := by
  rw [globalIntegral_inter_archCircle_eq_rootOfUnityImage F]
  constructor
  · rintro ⟨a, ha, hax⟩
    exact ⟨⟨a, ha⟩, hax⟩
  · rintro ⟨zeta, rfl⟩
    exact ⟨(zeta : (𝓞 F)ˣ), zeta.property, rfl⟩

end Dispute.Prop310ActualIntersection
end
