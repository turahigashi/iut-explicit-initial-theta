import Cor312LogVolume.theorem311.CanonicalFiniteSplitNormalizationDiagram
import Cor312LogVolume.theorem311.NormalizedHaarCore
import Mathlib.Topology.Homeomorph.Lemmas

namespace CitedLV.Theorem311

universe uBase uIndex uComponent uPacket uValue

def subalgebraHomeomorphOfEq
    {R : Type uBase} {K : Type uPacket}
    [CommRing R] [CommRing K] [Algebra R K] [TopologicalSpace K]
    (S T : Subalgebra R K) (h : S = T) : S ≃ₜ T :=
  Homeomorph.setCongr
    (congrArg (fun U : Subalgebra R K => (U : Set K)) h)

theorem subalgebraHomeomorphOfEq_coe
    {R : Type uBase} {K : Type uPacket}
    [CommRing R] [CommRing K] [Algebra R K] [TopologicalSpace K]
    (S T : Subalgebra R K) (h : S = T) (x : S) :
    ((subalgebraHomeomorphOfEq S T h x : T) : K) = (x : K) :=
  rfl

noncomputable def finiteSplitRegularNormalizationHomeomorph
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K] [TopologicalSpace K]
    (split : K ≃ₐ[R] (∀ i, A i)) :
    regularIntegerOrderOfFiniteSplit split ≃ₜ integralClosure R K :=
  subalgebraHomeomorphOfEq _ _
    (regularIntegerOrderOfFiniteSplit_eq_integralClosure split)

theorem finiteSplit_homeomorph_coe
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K] [TopologicalSpace K]
    (split : K ≃ₐ[R] (∀ i, A i))
    (x : regularIntegerOrderOfFiniteSplit split) :
    ((finiteSplitRegularNormalizationHomeomorph split x :
      integralClosure R K) : K) = (x : K) :=
  rfl

theorem finiteSplit_algEquiv_homeomorph_coherent
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K] [TopologicalSpace K]
    (split : K ≃ₐ[R] (∀ i, A i))
    (x : regularIntegerOrderOfFiniteSplit split) :
    finiteSplitRegularNormalizationHomeomorph split x =
      finiteSplitRegularNormalizationEquiv split x := by
  apply Subtype.ext
  rfl

theorem finiteSplit_transport_isCompact_iff
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K] [TopologicalSpace K]
    (split : K ≃ₐ[R] (∀ i, A i))
    (S : Set (regularIntegerOrderOfFiniteSplit split)) :
    IsCompact (finiteSplitRegularNormalizationHomeomorph split '' S) ↔
      IsCompact S :=
  (finiteSplitRegularNormalizationHomeomorph split).isCompact_image

theorem finiteSplit_transport_isOpen_iff
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K] [TopologicalSpace K]
    (split : K ≃ₐ[R] (∀ i, A i))
    (S : Set (regularIntegerOrderOfFiniteSplit split)) :
    IsOpen (finiteSplitRegularNormalizationHomeomorph split '' S) ↔
      IsOpen S :=
  (finiteSplitRegularNormalizationHomeomorph split).isOpen_image

theorem finiteSplit_transport_isCompactOpen_iff
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K] [TopologicalSpace K]
    (split : K ≃ₐ[R] (∀ i, A i))
    (S : Set (regularIntegerOrderOfFiniteSplit split)) :
    IsCompactOpenRegion
        (finiteSplitRegularNormalizationHomeomorph split '' S) ↔
      IsCompactOpenRegion S := by
  exact and_congr (finiteSplit_transport_isCompact_iff split S)
    (finiteSplit_transport_isOpen_iff split S)

theorem finiteSplit_transport_nonempty_iff
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K] [TopologicalSpace K]
    (split : K ≃ₐ[R] (∀ i, A i))
    (S : Set (regularIntegerOrderOfFiniteSplit split)) :
    (finiteSplitRegularNormalizationHomeomorph split '' S).Nonempty ↔
      S.Nonempty := by
  constructor
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨x, hx⟩
  · exact fun hS => hS.image _

theorem finiteSplit_transport_isNonemptyCompactOpen_iff
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K] [TopologicalSpace K]
    (split : K ≃ₐ[R] (∀ i, A i))
    (S : Set (regularIntegerOrderOfFiniteSplit split)) :
    IsNonemptyCompactOpenRegion
        (finiteSplitRegularNormalizationHomeomorph split '' S) ↔
      IsNonemptyCompactOpenRegion S := by
  exact and_congr (finiteSplit_transport_isCompactOpen_iff split S)
    (finiteSplit_transport_nonempty_iff split S)

theorem finiteSplit_transport_ambient_image
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K] [TopologicalSpace K]
    (split : K ≃ₐ[R] (∀ i, A i))
    (S : Set (regularIntegerOrderOfFiniteSplit split)) :
    (fun y : integralClosure R K => (y : K)) ''
        (finiteSplitRegularNormalizationHomeomorph split '' S) =
      (fun x : regularIntegerOrderOfFiniteSplit split => (x : K)) '' S := by
  ext k
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨finiteSplitRegularNormalizationHomeomorph split x,
      ⟨x, hx, rfl⟩, rfl⟩

structure IndependentRegionReadouts
    (X Y : Type*) (Value : Type uValue) where
  sourceReadout : Set X -> Value
  targetReadout : Set Y -> Value

def RegionReadoutsCompatible
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {Value : Type uValue}
    (e : X ≃ₜ Y) (readouts : IndependentRegionReadouts X Y Value) : Prop :=
  ∀ S : Set X, readouts.sourceReadout S =
    readouts.targetReadout (e '' S)

def RegionReadoutsNonconstant
    {X Y : Type*} {Value : Type uValue}
    (readouts : IndependentRegionReadouts X Y Value) : Prop :=
  (∃ S T : Set X,
      readouts.sourceReadout S ≠ readouts.sourceReadout T) ∧
    (∃ S T : Set Y,
      readouts.targetReadout S ≠ readouts.targetReadout T)

structure AdmissibleRegionReadouts
    (X Y : Type*) (Value : Type uValue)
    (sourceAdmissible : Set X -> Prop)
    (targetAdmissible : Set Y -> Prop) where
  sourceReadout : {S : Set X // sourceAdmissible S} -> Value
  targetReadout : {S : Set Y // targetAdmissible S} -> Value

def AdmissibleRegionReadoutsCompatible
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {Value : Type uValue}
    {sourceAdmissible : Set X -> Prop}
    {targetAdmissible : Set Y -> Prop}
    (e : X ≃ₜ Y)
    (htransport : ∀ S : Set X,
      sourceAdmissible S ↔ targetAdmissible (e '' S))
    (readouts : AdmissibleRegionReadouts X Y Value
      sourceAdmissible targetAdmissible) : Prop :=
  ∀ S : {S : Set X // sourceAdmissible S},
    readouts.sourceReadout S =
      readouts.targetReadout
        ⟨e '' S.1, (htransport S.1).mp S.2⟩

def AdmissibleRegionReadoutsNonconstant
    {X Y : Type*} {Value : Type uValue}
    {sourceAdmissible : Set X -> Prop}
    {targetAdmissible : Set Y -> Prop}
    (readouts : AdmissibleRegionReadouts X Y Value
      sourceAdmissible targetAdmissible) : Prop :=
  (∃ S T : {S : Set X // sourceAdmissible S},
      readouts.sourceReadout S ≠ readouts.sourceReadout T) ∧
    (∃ S T : {S : Set Y // targetAdmissible S},
      readouts.targetReadout S ≠ readouts.targetReadout T)

def zeroOneRegionReadouts (X Y : Type*) :
    IndependentRegionReadouts X Y Real where
  sourceReadout := fun _ => 0
  targetReadout := fun _ => 1

def constantZeroRegionReadouts (X Y : Type*) :
    IndependentRegionReadouts X Y Real where
  sourceReadout := fun _ => 0
  targetReadout := fun _ => 0

theorem homeomorph_does_not_force_region_readout_compatibility
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) :
    ¬ RegionReadoutsCompatible e (zeroOneRegionReadouts X Y) := by
  intro hcompatible
  have h := hcompatible ∅
  norm_num [zeroOneRegionReadouts] at h

theorem constant_region_readouts_compatible_but_degenerate
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) :
    RegionReadoutsCompatible e (constantZeroRegionReadouts X Y) ∧
      ¬ RegionReadoutsNonconstant (constantZeroRegionReadouts X Y) := by
  constructor
  · intro S
    rfl
  · rintro ⟨⟨S, T, hne⟩, _⟩
    exact hne rfl

noncomputable def boolSeparatedRegionReadouts :
    IndependentRegionReadouts Bool Bool Real := by
  classical
  exact
    { sourceReadout := fun S => if true ∈ S then 1 else 0
      targetReadout := fun S => if false ∈ S then 1 else 0 }

theorem boolSeparated_region_readouts_nonconstant :
    RegionReadoutsNonconstant boolSeparatedRegionReadouts := by
  constructor
  · refine ⟨{true}, {false}, ?_⟩
    norm_num [boolSeparatedRegionReadouts]
  · refine ⟨{false}, {true}, ?_⟩
    norm_num [boolSeparatedRegionReadouts]

theorem bool_singletons_are_nonempty_compact_open :
    IsNonemptyCompactOpenRegion ({true} : Set Bool) ∧
      IsNonemptyCompactOpenRegion ({false} : Set Bool) := by
  constructor <;>
    exact ⟨⟨isCompact_singleton, isOpen_discrete _⟩, Set.singleton_nonempty _⟩

theorem nondegenerate_compact_open_readouts_still_need_compatibility :
    RegionReadoutsNonconstant boolSeparatedRegionReadouts ∧
      IsNonemptyCompactOpenRegion ({true} : Set Bool) ∧
      ¬ RegionReadoutsCompatible (Homeomorph.refl Bool)
        boolSeparatedRegionReadouts := by
  refine ⟨boolSeparated_region_readouts_nonconstant,
    bool_singletons_are_nonempty_compact_open.1, ?_⟩
  intro hcompatible
  have h := hcompatible ({true} : Set Bool)
  norm_num [boolSeparatedRegionReadouts] at h

end CitedLV.Theorem311
