import Cor312LogVolume.theorem311.FiniteSemisimpleRegularNormalization
import Mathlib.Algebra.Algebra.Prod

namespace CitedLV.Theorem311

universe uBase uRaw uRegular uNormalized uAmbient

structure RegularNormalizationCarrierRaw
    (R : Type uBase) (Raw : Type uRaw) (Regular : Type uRegular)
    (Normalized : Type uNormalized) (Ambient : Type uAmbient)
    [CommRing R] [CommRing Raw] [CommRing Regular]
    [CommRing Normalized] [CommRing Ambient]
    [Algebra R Raw] [Algebra R Regular]
    [Algebra R Normalized] [Algebra R Ambient] where
  rawToAmbient : Raw →ₐ[R] Ambient
  regularToAmbient : Regular →ₐ[R] Ambient
  normalizedToAmbient : Normalized →ₐ[R] Ambient
  rawToNormalized : Raw →ₐ[R] Normalized
  regularToNormalized : Regular ≃ₐ[R] Normalized

def RegularNormalizedAmbientCommutes
    {R : Type uBase} {Raw : Type uRaw} {Regular : Type uRegular}
    {Normalized : Type uNormalized} {Ambient : Type uAmbient}
    [CommRing R] [CommRing Raw] [CommRing Regular]
    [CommRing Normalized] [CommRing Ambient]
    [Algebra R Raw] [Algebra R Regular]
    [Algebra R Normalized] [Algebra R Ambient]
    (d : RegularNormalizationCarrierRaw R Raw Regular Normalized Ambient) : Prop :=
  ∀ x, d.regularToAmbient x =
    d.normalizedToAmbient (d.regularToNormalized x)

def RawNormalizedAmbientCommutes
    {R : Type uBase} {Raw : Type uRaw} {Regular : Type uRegular}
    {Normalized : Type uNormalized} {Ambient : Type uAmbient}
    [CommRing R] [CommRing Raw] [CommRing Regular]
    [CommRing Normalized] [CommRing Ambient]
    [Algebra R Raw] [Algebra R Regular]
    [Algebra R Normalized] [Algebra R Ambient]
    (d : RegularNormalizationCarrierRaw R Raw Regular Normalized Ambient) : Prop :=
  ∀ x, d.rawToAmbient x = d.normalizedToAmbient (d.rawToNormalized x)

def NormalizationCarrierMapsInjective
    {R : Type uBase} {Raw : Type uRaw} {Regular : Type uRegular}
    {Normalized : Type uNormalized} {Ambient : Type uAmbient}
    [CommRing R] [CommRing Raw] [CommRing Regular]
    [CommRing Normalized] [CommRing Ambient]
    [Algebra R Raw] [Algebra R Regular]
    [Algebra R Normalized] [Algebra R Ambient]
    (d : RegularNormalizationCarrierRaw R Raw Regular Normalized Ambient) : Prop :=
  Function.Injective d.rawToAmbient ∧
  Function.Injective d.regularToAmbient ∧
  Function.Injective d.normalizedToAmbient ∧
  Function.Injective d.rawToNormalized

def RawOrderIsProper
    {R : Type uBase} {Raw : Type uRaw} {Regular : Type uRegular}
    {Normalized : Type uNormalized} {Ambient : Type uAmbient}
    [CommRing R] [CommRing Raw] [CommRing Regular]
    [CommRing Normalized] [CommRing Ambient]
    [Algebra R Raw] [Algebra R Regular]
    [Algebra R Normalized] [Algebra R Ambient]
    (d : RegularNormalizationCarrierRaw R Raw Regular Normalized Ambient) : Prop :=
  ∃ z : Normalized, z ∉ Set.range d.rawToNormalized

def transportRegularRegion
    {R : Type uBase} {Raw : Type uRaw} {Regular : Type uRegular}
    {Normalized : Type uNormalized} {Ambient : Type uAmbient}
    [CommRing R] [CommRing Raw] [CommRing Regular]
    [CommRing Normalized] [CommRing Ambient]
    [Algebra R Raw] [Algebra R Regular]
    [Algebra R Normalized] [Algebra R Ambient]
    (d : RegularNormalizationCarrierRaw R Raw Regular Normalized Ambient)
    (S : Set Regular) : Set Normalized :=
  d.regularToNormalized '' S

def regularRegionInAmbient
    {R : Type uBase} {Raw : Type uRaw} {Regular : Type uRegular}
    {Normalized : Type uNormalized} {Ambient : Type uAmbient}
    [CommRing R] [CommRing Raw] [CommRing Regular]
    [CommRing Normalized] [CommRing Ambient]
    [Algebra R Raw] [Algebra R Regular]
    [Algebra R Normalized] [Algebra R Ambient]
    (d : RegularNormalizationCarrierRaw R Raw Regular Normalized Ambient)
    (S : Set Regular) : Set Ambient :=
  d.regularToAmbient '' S

def normalizedRegionInAmbient
    {R : Type uBase} {Raw : Type uRaw} {Regular : Type uRegular}
    {Normalized : Type uNormalized} {Ambient : Type uAmbient}
    [CommRing R] [CommRing Raw] [CommRing Regular]
    [CommRing Normalized] [CommRing Ambient]
    [Algebra R Raw] [Algebra R Regular]
    [Algebra R Normalized] [Algebra R Ambient]
    (d : RegularNormalizationCarrierRaw R Raw Regular Normalized Ambient)
    (S : Set Normalized) : Set Ambient :=
  d.normalizedToAmbient '' S

theorem regular_normalized_ambient_images_agree
    {R : Type uBase} {Raw : Type uRaw} {Regular : Type uRegular}
    {Normalized : Type uNormalized} {Ambient : Type uAmbient}
    [CommRing R] [CommRing Raw] [CommRing Regular]
    [CommRing Normalized] [CommRing Ambient]
    [Algebra R Raw] [Algebra R Regular]
    [Algebra R Normalized] [Algebra R Ambient]
    (d : RegularNormalizationCarrierRaw R Raw Regular Normalized Ambient)
    (hcomm : RegularNormalizedAmbientCommutes d) (S : Set Regular) :
    regularRegionInAmbient d S =
      normalizedRegionInAmbient d (transportRegularRegion d S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨d.regularToNormalized x, ⟨x, hx, rfl⟩, ?_⟩
    exact (hcomm x).symm
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, hcomm x⟩

def regularAmbientReadout
    {R : Type uBase} {Raw : Type uRaw} {Regular : Type uRegular}
    {Normalized : Type uNormalized} {Ambient : Type uAmbient}
    [CommRing R] [CommRing Raw] [CommRing Regular]
    [CommRing Normalized] [CommRing Ambient]
    [Algebra R Raw] [Algebra R Regular]
    [Algebra R Normalized] [Algebra R Ambient]
    (d : RegularNormalizationCarrierRaw R Raw Regular Normalized Ambient)
    (volume : Set Ambient -> Real) (S : Set Regular) : Real :=
  volume (regularRegionInAmbient d S)

def normalizedAmbientReadout
    {R : Type uBase} {Raw : Type uRaw} {Regular : Type uRegular}
    {Normalized : Type uNormalized} {Ambient : Type uAmbient}
    [CommRing R] [CommRing Raw] [CommRing Regular]
    [CommRing Normalized] [CommRing Ambient]
    [Algebra R Raw] [Algebra R Regular]
    [Algebra R Normalized] [Algebra R Ambient]
    (d : RegularNormalizationCarrierRaw R Raw Regular Normalized Ambient)
    (volume : Set Ambient -> Real) (S : Set Normalized) : Real :=
  volume (normalizedRegionInAmbient d S)

theorem coherent_carrier_diagram_preserves_all_region_readouts
    {R : Type uBase} {Raw : Type uRaw} {Regular : Type uRegular}
    {Normalized : Type uNormalized} {Ambient : Type uAmbient}
    [CommRing R] [CommRing Raw] [CommRing Regular]
    [CommRing Normalized] [CommRing Ambient]
    [Algebra R Raw] [Algebra R Regular]
    [Algebra R Normalized] [Algebra R Ambient]
    (d : RegularNormalizationCarrierRaw R Raw Regular Normalized Ambient)
    (volume : Set Ambient -> Real)
    (hcomm : RegularNormalizedAmbientCommutes d) (S : Set Regular) :
    regularAmbientReadout d volume S =
      normalizedAmbientReadout d volume (transportRegularRegion d S) := by
  unfold regularAmbientReadout normalizedAmbientReadout
  rw [regular_normalized_ambient_images_agree d hcomm S]

def RegularAmbientReadoutNonconstant
    {R : Type uBase} {Raw : Type uRaw} {Regular : Type uRegular}
    {Normalized : Type uNormalized} {Ambient : Type uAmbient}
    [CommRing R] [CommRing Raw] [CommRing Regular]
    [CommRing Normalized] [CommRing Ambient]
    [Algebra R Raw] [Algebra R Regular]
    [Algebra R Normalized] [Algebra R Ambient]
    (d : RegularNormalizationCarrierRaw R Raw Regular Normalized Ambient)
    (volume : Set Ambient -> Real) : Prop :=
  ∃ S T : Set Regular,
    regularAmbientReadout d volume S ≠ regularAmbientReadout d volume T

structure IndependentCarrierReadouts
    (Regular : Type uRegular) (Normalized : Type uNormalized)
    (Value : Type*) where
  regularReadout : Regular -> Value
  normalizedReadout : Normalized -> Value

def IndependentCarrierReadoutsCompatible
    {R : Type uBase} {Raw : Type uRaw} {Regular : Type uRegular}
    {Normalized : Type uNormalized} {Ambient : Type uAmbient}
    {Value : Type*}
    [CommRing R] [CommRing Raw] [CommRing Regular]
    [CommRing Normalized] [CommRing Ambient]
    [Algebra R Raw] [Algebra R Regular]
    [Algebra R Normalized] [Algebra R Ambient]
    (d : RegularNormalizationCarrierRaw R Raw Regular Normalized Ambient)
    (readouts : IndependentCarrierReadouts Regular Normalized Value) : Prop :=
  ∀ x, readouts.regularReadout x =
    readouts.normalizedReadout (d.regularToNormalized x)

def IndependentCarrierReadoutsNonconstant
    {Regular : Type uRegular} {Normalized : Type uNormalized}
    {Value : Type*}
    (readouts : IndependentCarrierReadouts Regular Normalized Value) : Prop :=
  (∃ x y, readouts.regularReadout x ≠ readouts.regularReadout y) ∧
    (∃ x y, readouts.normalizedReadout x ≠
      readouts.normalizedReadout y)

def ratDiagonalAlgHom : ℚ →ₐ[ℚ] (ℚ × ℚ) :=
  (AlgHom.id ℚ ℚ).prod (AlgHom.id ℚ ℚ)

def ratProdSwapAlgEquiv : (ℚ × ℚ) ≃ₐ[ℚ] (ℚ × ℚ) :=
  { (RingEquiv.prodComm : (ℚ × ℚ) ≃+* (ℚ × ℚ)) with
    commutes' := fun _ => rfl }

def twoFactorCoherentCarrierRaw :
    RegularNormalizationCarrierRaw ℚ ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ) where
  rawToAmbient := ratDiagonalAlgHom
  regularToAmbient := AlgHom.id ℚ (ℚ × ℚ)
  normalizedToAmbient := AlgHom.id ℚ (ℚ × ℚ)
  rawToNormalized := ratDiagonalAlgHom
  regularToNormalized := AlgEquiv.refl

theorem twoFactor_regular_normalized_commutes :
    RegularNormalizedAmbientCommutes twoFactorCoherentCarrierRaw := by
  intro x
  rfl

theorem twoFactor_raw_normalized_commutes :
    RawNormalizedAmbientCommutes twoFactorCoherentCarrierRaw := by
  intro x
  rfl

theorem ratDiagonalAlgHom_injective : Function.Injective ratDiagonalAlgHom := by
  intro x y hxy
  exact congrArg Prod.fst hxy

theorem twoFactor_carrier_maps_injective :
    NormalizationCarrierMapsInjective twoFactorCoherentCarrierRaw := by
  exact ⟨ratDiagonalAlgHom_injective, Function.injective_id,
    Function.injective_id, ratDiagonalAlgHom_injective⟩

theorem twoFactor_raw_order_is_proper :
    RawOrderIsProper twoFactorCoherentCarrierRaw := by
  refine ⟨(0, 1), ?_⟩
  rintro ⟨x, hx⟩
  have hfst : x = 0 := congrArg Prod.fst hx
  have hsnd : x = 1 := congrArg Prod.snd hx
  exact zero_ne_one (hfst.symm.trans hsnd)

noncomputable def twoFactorAmbientReadout (S : Set (ℚ × ℚ)) : Real :=
  by
    classical
    exact if (0, 1) ∈ S then 1 else 0

theorem twoFactor_readout_nonconstant :
    RegularAmbientReadoutNonconstant twoFactorCoherentCarrierRaw
      twoFactorAmbientReadout := by
  refine ⟨∅, Set.univ, ?_⟩
  norm_num [regularAmbientReadout, regularRegionInAmbient,
    twoFactorCoherentCarrierRaw, twoFactorAmbientReadout]

def twoFactorFirstCoordinateReadouts :
    IndependentCarrierReadouts (ℚ × ℚ) (ℚ × ℚ) ℚ where
  regularReadout := Prod.fst
  normalizedReadout := Prod.fst

def twoFactorReindexedCoordinateReadouts :
    IndependentCarrierReadouts (ℚ × ℚ) (ℚ × ℚ) ℚ where
  regularReadout := Prod.fst
  normalizedReadout := Prod.snd

def twoFactorConstantZeroReadouts :
    IndependentCarrierReadouts (ℚ × ℚ) (ℚ × ℚ) ℚ where
  regularReadout := fun _ => 0
  normalizedReadout := fun _ => 0

theorem identity_first_coordinate_readouts_compatible :
    IndependentCarrierReadoutsCompatible twoFactorCoherentCarrierRaw
      twoFactorFirstCoordinateReadouts := by
  intro x
  rfl

theorem first_coordinate_readouts_nonconstant :
    IndependentCarrierReadoutsNonconstant
      twoFactorFirstCoordinateReadouts := by
  constructor
  · exact ⟨(0, 0), (1, 0), zero_ne_one⟩
  · exact ⟨(0, 0), (1, 0), zero_ne_one⟩

def twoFactorOneSidedSwapCarrierRaw :
    RegularNormalizationCarrierRaw ℚ ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ) where
  rawToAmbient := ratDiagonalAlgHom
  regularToAmbient := AlgHom.id ℚ (ℚ × ℚ)
  normalizedToAmbient := AlgHom.id ℚ (ℚ × ℚ)
  rawToNormalized := ratDiagonalAlgHom
  regularToNormalized := ratProdSwapAlgEquiv

theorem one_sided_factor_swap_fails_ambient_commutativity :
    ¬ RegularNormalizedAmbientCommutes twoFactorOneSidedSwapCarrierRaw := by
  intro hcomm
  have h := hcomm (0, 1)
  norm_num [twoFactorOneSidedSwapCarrierRaw, ratProdSwapAlgEquiv] at h

theorem one_sided_factor_swap_fails_fixed_readouts :
    ¬ IndependentCarrierReadoutsCompatible
      twoFactorOneSidedSwapCarrierRaw twoFactorFirstCoordinateReadouts := by
  intro hcompatible
  have h := hcompatible (0, 1)
  norm_num [twoFactorOneSidedSwapCarrierRaw, ratProdSwapAlgEquiv,
    twoFactorFirstCoordinateReadouts] at h

def twoFactorReindexedSwapCarrierRaw :
    RegularNormalizationCarrierRaw ℚ ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ) where
  rawToAmbient := ratDiagonalAlgHom
  regularToAmbient := AlgHom.id ℚ (ℚ × ℚ)
  normalizedToAmbient := ratProdSwapAlgEquiv.toAlgHom
  rawToNormalized := ratDiagonalAlgHom
  regularToNormalized := ratProdSwapAlgEquiv

theorem reindexed_factor_swap_restores_ambient_commutativity :
    RegularNormalizedAmbientCommutes twoFactorReindexedSwapCarrierRaw := by
  intro x
  rcases x with ⟨x, y⟩
  rfl

theorem reindexed_factor_swap_preserves_raw_commutativity :
    RawNormalizedAmbientCommutes twoFactorReindexedSwapCarrierRaw := by
  intro x
  rfl

theorem reindexed_factor_swap_maps_are_injective :
    NormalizationCarrierMapsInjective twoFactorReindexedSwapCarrierRaw := by
  exact ⟨ratDiagonalAlgHom_injective, Function.injective_id,
    ratProdSwapAlgEquiv.injective, ratDiagonalAlgHom_injective⟩

theorem reindexed_factor_swap_restores_readout_compatibility :
    IndependentCarrierReadoutsCompatible twoFactorReindexedSwapCarrierRaw
      twoFactorReindexedCoordinateReadouts := by
  rintro ⟨x, y⟩
  rfl

theorem reindexed_coordinate_readouts_nonconstant :
    IndependentCarrierReadoutsNonconstant
      twoFactorReindexedCoordinateReadouts := by
  constructor
  · exact ⟨(0, 0), (1, 0), zero_ne_one⟩
  · exact ⟨(0, 0), (0, 1), zero_ne_one⟩

theorem constant_zero_readout_fails_nondegeneracy :
    ¬ RegularAmbientReadoutNonconstant twoFactorCoherentCarrierRaw
      (fun _ => 0) := by
  rintro ⟨S, T, hne⟩
  exact hne rfl

theorem constant_zero_carrier_readouts_are_compatible :
    IndependentCarrierReadoutsCompatible twoFactorCoherentCarrierRaw
      twoFactorConstantZeroReadouts := by
  intro x
  rfl

theorem constant_zero_carrier_readouts_fail_nondegeneracy :
    ¬ IndependentCarrierReadoutsNonconstant
      twoFactorConstantZeroReadouts := by
  rintro ⟨⟨x, y, hne⟩, _⟩
  exact hne rfl

end CitedLV.Theorem311
