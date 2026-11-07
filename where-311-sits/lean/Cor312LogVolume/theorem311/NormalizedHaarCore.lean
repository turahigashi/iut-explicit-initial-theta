import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.NormNum

open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Topology

namespace CitedLV.Theorem311

universe uX uY

def IsCompactOpenRegion
    {X : Type*} [TopologicalSpace X] (S : Set X) : Prop :=
  IsCompact S ∧ IsOpen S

def IsNonemptyCompactOpenRegion
    {X : Type*} [TopologicalSpace X] (S : Set X) : Prop :=
  IsCompactOpenRegion S ∧ S.Nonempty

abbrev NormalizedHaarRegion
    (X : Type uX) [TopologicalSpace X] :=
  {S : Set X // IsNonemptyCompactOpenRegion S}

def normalizedHaarRegionToPositiveCompacts
    {X : Type uX} [TopologicalSpace X]
    (K : NormalizedHaarRegion X) : PositiveCompacts X where
  carrier := K.1
  isCompact' := K.2.1.1
  interior_nonempty' := by
    rw [K.2.1.2.interior_eq]
    exact K.2.2

variable {X : Type uX} [AddGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]

noncomputable abbrev normalizedAddHaar
    (K : NormalizedHaarRegion X) : Measure X :=
  Measure.addHaarMeasure (normalizedHaarRegionToPositiveCompacts K)

theorem normalizedAddHaar_anchor
    (K : NormalizedHaarRegion X) :
    normalizedAddHaar K K.1 = 1 := by
  exact Measure.addHaarMeasure_self

theorem normalizedAddHaar_region_pos
    (K U : NormalizedHaarRegion X) :
    0 < normalizedAddHaar K U.1 := by
  exact U.2.1.2.measure_pos (normalizedAddHaar K) U.2.2

theorem normalizedAddHaar_region_lt_top
    (K U : NormalizedHaarRegion X) :
    normalizedAddHaar K U.1 < ⊤ := by
  exact U.2.1.1.measure_lt_top

noncomputable def normalizedHaarRealVolume
    (K U : NormalizedHaarRegion X) : Real :=
  (normalizedAddHaar K U.1).toReal

theorem normalizedHaarRealVolume_pos
    (K U : NormalizedHaarRegion X) :
    0 < normalizedHaarRealVolume K U := by
  exact ENNReal.toReal_pos (normalizedAddHaar_region_pos K U).ne'
    (normalizedAddHaar_region_lt_top K U).ne

theorem normalizedHaarRealVolume_anchor
    (K : NormalizedHaarRegion X) :
    normalizedHaarRealVolume K K = 1 := by
  simp [normalizedHaarRealVolume, normalizedAddHaar_anchor]

noncomputable def normalizedHaarLogVolume
    (K U : NormalizedHaarRegion X) : Real :=
  Real.log (normalizedHaarRealVolume K U)

theorem normalizedHaarLogVolume_anchor
    (K : NormalizedHaarRegion X) :
    normalizedHaarLogVolume K K = 0 := by
  simp [normalizedHaarLogVolume, normalizedHaarRealVolume_anchor]

theorem positive_scale_preserves_addHaar
    (mu : Measure X) [mu.IsAddHaarMeasure]
    (c : NNReal) (hc : c ≠ 0) :
    (c • mu).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.nnreal_smul mu hc

theorem two_scaled_addHaar_changes_anchor
    (K : NormalizedHaarRegion X) :
    ((2 : NNReal) • normalizedAddHaar K) K.1 = 2 := by
  rw [Measure.smul_apply]
  simp [normalizedAddHaar_anchor]

theorem two_scaled_addHaar_is_not_normalized
    (K : NormalizedHaarRegion X) :
    ((2 : NNReal) • normalizedAddHaar K) K.1 ≠ 1 := by
  rw [two_scaled_addHaar_changes_anchor]
  norm_num

theorem zero_measure_is_not_addHaar
    (K : NormalizedHaarRegion X) :
    ¬ Measure.IsAddHaarMeasure (0 : Measure X) := by
  intro hzero
  letI : Measure.IsAddHaarMeasure (0 : Measure X) := hzero
  have hpos := K.2.1.2.measure_pos (μ := (0 : Measure X)) K.2.2
  simpa using hpos

theorem normalizedAddHaar_empty_log_aliases_anchor
    (K : NormalizedHaarRegion X) :
    Real.log ((normalizedAddHaar K) (∅ : Set X)).toReal =
      normalizedHaarLogVolume K K := by
  rw [normalizedHaarLogVolume_anchor]
  simp

variable {Y : Type uY} [AddGroup Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [MeasurableSpace Y] [BorelSpace Y]

def mapNormalizedHaarRegion
    (e : X ≃ₜ+ Y) (K : NormalizedHaarRegion X) :
    NormalizedHaarRegion Y where
  val := e '' K.1
  property :=
    ⟨⟨K.2.1.1.image e.continuous,
      e.toHomeomorph.isOpenMap K.1 K.2.1.2⟩,
      K.2.2.image e⟩

end CitedLV.Theorem311
