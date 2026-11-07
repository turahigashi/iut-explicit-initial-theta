import Cor312LogVolume.theorem311.NormalizedHaarCore
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Pointwise Topology

namespace CitedLV.Theorem311

universe uK
variable {K : Type uK} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [MeasurableSpace K] [BorelSpace K]
  [LocallyCompactSpace K]

def localScalarAddEquiv (g : Kˣ) : K ≃ₜ+ K :=
  ContinuousAddEquiv.mulLeft g

def localScalarHaarRegion (g : Kˣ) (U : NormalizedHaarRegion K) :
    NormalizedHaarRegion K :=
  mapNormalizedHaarRegion (localScalarAddEquiv g) U

omit [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] in
theorem localScalarHaarRegion_carrier (g : Kˣ)
    (U : NormalizedHaarRegion K) :
    (localScalarHaarRegion g U).1 = g • U.1 := by
  rfl

theorem normalizedAddHaar_localScalarRegion
    (anchor U : NormalizedHaarRegion K) (g : Kˣ) :
    normalizedAddHaar anchor (localScalarHaarRegion g U).1 =
      (MeasureTheory.distribHaarChar K g : ENNReal) *
        normalizedAddHaar anchor U.1 := by
  rw [localScalarHaarRegion_carrier]
  exact (MeasureTheory.distribHaarChar_mul
    (normalizedAddHaar anchor) g U.1).symm

theorem normalizedHaarRealVolume_localScalarRegion
    (anchor U : NormalizedHaarRegion K) (g : Kˣ) :
    normalizedHaarRealVolume anchor (localScalarHaarRegion g U) =
      (MeasureTheory.distribHaarChar K g : Real) *
        normalizedHaarRealVolume anchor U := by
  unfold normalizedHaarRealVolume
  rw [normalizedAddHaar_localScalarRegion]
  rw [ENNReal.toReal_mul]
  rfl

theorem normalizedHaarLogVolume_localScalarRegion
    (anchor U : NormalizedHaarRegion K) (g : Kˣ) :
    normalizedHaarLogVolume anchor (localScalarHaarRegion g U) =
      Real.log (MeasureTheory.distribHaarChar K g : Real) +
        normalizedHaarLogVolume anchor U := by
  unfold normalizedHaarLogVolume
  rw [normalizedHaarRealVolume_localScalarRegion]
  rw [Real.log_mul
    (by exact_mod_cast
      (MeasureTheory.distribHaarChar_pos (A := K) (g := g)).ne')
    (normalizedHaarRealVolume_pos anchor U).ne']

end CitedLV.Theorem311
