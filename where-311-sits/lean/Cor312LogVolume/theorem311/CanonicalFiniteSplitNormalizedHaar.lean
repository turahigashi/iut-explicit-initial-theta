import Cor312LogVolume.theorem311.CanonicalFiniteSplitNormalizationTopology
import Cor312LogVolume.theorem311.NormalizedHaarCore
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Topology

namespace CitedLV.Theorem311

universe uBase uIndex uComponent uPacket uX uY

variable {X : Type uX} [AddGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]

section Transport

variable {Y : Type uY} [AddGroup Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]

def NormalizationAnchorsMatch
    (e : X ≃ₜ+ Y)
    (sourceAnchor : NormalizedHaarRegion X)
    (targetAnchor : NormalizedHaarRegion Y) : Prop :=
  e '' sourceAnchor.1 = targetAnchor.1

theorem mappedRegion_eq_of_normalizationAnchorsMatch
    (e : X ≃ₜ+ Y)
    (sourceAnchor : NormalizedHaarRegion X)
    (targetAnchor : NormalizedHaarRegion Y)
    (hAnchor : NormalizationAnchorsMatch e sourceAnchor targetAnchor) :
    mapNormalizedHaarRegion e sourceAnchor = targetAnchor := by
  apply Subtype.ext
  exact hAnchor

theorem distinct_mapped_anchor_rejects_normalizationAnchorsMatch
    (e : X ≃ₜ+ Y)
    (sourceAnchor : NormalizedHaarRegion X)
    (targetAnchor : NormalizedHaarRegion Y)
    (hne : mapNormalizedHaarRegion e sourceAnchor ≠ targetAnchor) :
    ¬ NormalizationAnchorsMatch e sourceAnchor targetAnchor := by
  intro hAnchor
  exact hne
    (mappedRegion_eq_of_normalizationAnchorsMatch
      e sourceAnchor targetAnchor hAnchor)

theorem normalizedAddHaar_map
    (e : X ≃ₜ+ Y) (K : NormalizedHaarRegion X) :
    Measure.map e (normalizedAddHaar K) =
      normalizedAddHaar (mapNormalizedHaarRegion e K) := by
  letI : SigmaFinite (normalizedAddHaar K) := inferInstance
  letI : SigmaFinite (Measure.map e (normalizedAddHaar K)) :=
    e.toHomeomorph.measurableEmbedding.sigmaFinite_map
  letI : (Measure.map e (normalizedAddHaar K)).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map (normalizedAddHaar K)
  symm
  apply (Measure.addHaarMeasure_eq_iff
    (normalizedHaarRegionToPositiveCompacts
      (mapNormalizedHaarRegion e K))
    (Measure.map e (normalizedAddHaar K))).2
  calc
    Measure.map e (normalizedAddHaar K)
        (mapNormalizedHaarRegion e K).1 =
      normalizedAddHaar K (e ⁻¹' (mapNormalizedHaarRegion e K).1) :=
        Measure.map_apply e.toHomeomorph.measurable
          (mapNormalizedHaarRegion e K).2.1.2.measurableSet
    _ = normalizedAddHaar K K.1 := by
      congr 1
      exact Equiv.preimage_image e.toEquiv K.1
    _ = 1 := normalizedAddHaar_anchor K

theorem normalizedAddHaar_map_to_independent_anchor
    (e : X ≃ₜ+ Y)
    (sourceAnchor : NormalizedHaarRegion X)
    (targetAnchor : NormalizedHaarRegion Y)
    (hAnchor : NormalizationAnchorsMatch e sourceAnchor targetAnchor) :
    Measure.map e (normalizedAddHaar sourceAnchor) =
      normalizedAddHaar targetAnchor := by
  rw [normalizedAddHaar_map e sourceAnchor]
  exact congrArg normalizedAddHaar
    (mappedRegion_eq_of_normalizationAnchorsMatch
      e sourceAnchor targetAnchor hAnchor)

theorem normalizedAddHaar_image
    (e : X ≃ₜ+ Y) (K U : NormalizedHaarRegion X) :
    normalizedAddHaar (mapNormalizedHaarRegion e K)
        (mapNormalizedHaarRegion e U).1 =
      normalizedAddHaar K U.1 := by
  rw [← normalizedAddHaar_map e K]
  calc
    Measure.map e (normalizedAddHaar K)
        (mapNormalizedHaarRegion e U).1 =
      normalizedAddHaar K (e ⁻¹' (mapNormalizedHaarRegion e U).1) :=
        Measure.map_apply e.toHomeomorph.measurable
          (mapNormalizedHaarRegion e U).2.1.2.measurableSet
    _ = normalizedAddHaar K U.1 := by
      congr 1
      exact Equiv.preimage_image e.toEquiv U.1

theorem normalizedAddHaar_image_to_independent_anchor
    (e : X ≃ₜ+ Y)
    (sourceAnchor : NormalizedHaarRegion X)
    (targetAnchor : NormalizedHaarRegion Y)
    (hAnchor : NormalizationAnchorsMatch e sourceAnchor targetAnchor)
    (U : NormalizedHaarRegion X) :
    normalizedAddHaar targetAnchor (mapNormalizedHaarRegion e U).1 =
      normalizedAddHaar sourceAnchor U.1 := by
  rw [← normalizedAddHaar_map_to_independent_anchor
    e sourceAnchor targetAnchor hAnchor]
  calc
    Measure.map e (normalizedAddHaar sourceAnchor)
        (mapNormalizedHaarRegion e U).1 =
      normalizedAddHaar sourceAnchor
        (e ⁻¹' (mapNormalizedHaarRegion e U).1) :=
          Measure.map_apply e.toHomeomorph.measurable
            (mapNormalizedHaarRegion e U).2.1.2.measurableSet
    _ = normalizedAddHaar sourceAnchor U.1 := by
      congr 1
      exact Equiv.preimage_image e.toEquiv U.1

theorem normalizedHaarRealVolume_map
    (e : X ≃ₜ+ Y) (K U : NormalizedHaarRegion X) :
    normalizedHaarRealVolume (mapNormalizedHaarRegion e K)
        (mapNormalizedHaarRegion e U) =
      normalizedHaarRealVolume K U := by
  simp [normalizedHaarRealVolume, normalizedAddHaar_image]

theorem normalizedHaarRealVolume_map_to_independent_anchor
    (e : X ≃ₜ+ Y)
    (sourceAnchor : NormalizedHaarRegion X)
    (targetAnchor : NormalizedHaarRegion Y)
    (hAnchor : NormalizationAnchorsMatch e sourceAnchor targetAnchor)
    (U : NormalizedHaarRegion X) :
    normalizedHaarRealVolume targetAnchor (mapNormalizedHaarRegion e U) =
      normalizedHaarRealVolume sourceAnchor U := by
  unfold normalizedHaarRealVolume
  exact congrArg ENNReal.toReal
    (normalizedAddHaar_image_to_independent_anchor
      e sourceAnchor targetAnchor hAnchor U)

theorem normalizedHaarLogVolume_map
    (e : X ≃ₜ+ Y) (K U : NormalizedHaarRegion X) :
    normalizedHaarLogVolume (mapNormalizedHaarRegion e K)
        (mapNormalizedHaarRegion e U) =
      normalizedHaarLogVolume K U := by
  simp [normalizedHaarLogVolume, normalizedHaarRealVolume_map]

theorem normalizedHaarLogVolume_map_to_independent_anchor
    (e : X ≃ₜ+ Y)
    (sourceAnchor : NormalizedHaarRegion X)
    (targetAnchor : NormalizedHaarRegion Y)
    (hAnchor : NormalizationAnchorsMatch e sourceAnchor targetAnchor)
    (U : NormalizedHaarRegion X) :
    normalizedHaarLogVolume targetAnchor (mapNormalizedHaarRegion e U) =
      normalizedHaarLogVolume sourceAnchor U := by
  unfold normalizedHaarLogVolume
  exact congrArg Real.log
    (normalizedHaarRealVolume_map_to_independent_anchor
      e sourceAnchor targetAnchor hAnchor U)

end Transport

noncomputable def finiteSplitRegularNormalizationContinuousAddEquiv
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K] [TopologicalSpace K]
    (split : K ≃ₐ[R] (∀ i, A i)) :
    regularIntegerOrderOfFiniteSplit split ≃ₜ+
      integralClosure R K :=
  ContinuousAddEquiv.mk'
    (finiteSplitRegularNormalizationHomeomorph split) (by
      intro x y
      apply Subtype.ext
      rfl)

theorem finiteSplit_orderSubtype_normalizedHaarLogVolume_transport
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K]
    [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    (split : K ≃ₐ[R] (∀ i, A i))
    [IsTopologicalAddGroup (regularIntegerOrderOfFiniteSplit split)]
    [IsTopologicalAddGroup (integralClosure R K)]
    [SecondCountableTopology (regularIntegerOrderOfFiniteSplit split)]
    [SecondCountableTopology (integralClosure R K)]
    (anchor region :
      NormalizedHaarRegion (regularIntegerOrderOfFiniteSplit split)) :
    normalizedHaarLogVolume
        (mapNormalizedHaarRegion
          (finiteSplitRegularNormalizationContinuousAddEquiv split) anchor)
        (mapNormalizedHaarRegion
          (finiteSplitRegularNormalizationContinuousAddEquiv split) region) =
      normalizedHaarLogVolume anchor region := by
  exact normalizedHaarLogVolume_map
    (finiteSplitRegularNormalizationContinuousAddEquiv split) anchor region

theorem finiteSplit_orderSubtype_normalizedHaarLogVolume_transport_of_named_anchors
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K]
    [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    (split : K ≃ₐ[R] (∀ i, A i))
    [IsTopologicalAddGroup (regularIntegerOrderOfFiniteSplit split)]
    [IsTopologicalAddGroup (integralClosure R K)]
    [SecondCountableTopology (regularIntegerOrderOfFiniteSplit split)]
    [SecondCountableTopology (integralClosure R K)]
    (sourceAnchor :
      NormalizedHaarRegion (regularIntegerOrderOfFiniteSplit split))
    (targetAnchor : NormalizedHaarRegion (integralClosure R K))
    (hAnchor : NormalizationAnchorsMatch
      (finiteSplitRegularNormalizationContinuousAddEquiv split)
      sourceAnchor targetAnchor)
    (region : NormalizedHaarRegion
      (regularIntegerOrderOfFiniteSplit split)) :
    normalizedHaarLogVolume targetAnchor
        (mapNormalizedHaarRegion
          (finiteSplitRegularNormalizationContinuousAddEquiv split) region) =
      normalizedHaarLogVolume sourceAnchor region := by
  exact normalizedHaarLogVolume_map_to_independent_anchor
    (finiteSplitRegularNormalizationContinuousAddEquiv split)
    sourceAnchor targetAnchor hAnchor region

end CitedLV.Theorem311
