import Cor312LogVolume.theorem311.PacketPossibleRegionAdapter
import Cor312LogVolume.theorem311.PacketProcessionNormalizationAdapter
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.PacketHullPipelineAdapter

open Src.IUT3.Theorem311
open Src.CoreLayer.RelativeXiFFamily
open CitedLV.Theorem311.PacketOutputTraceFrontier
open CitedLV.Theorem311.PacketPossibleRegionAdapter
open CitedLV.Theorem311.PacketProcessionNormalizationAdapter
open CitedLV.Theorem311.PacketHullEndpoint

variable {S : PacketSystem} {Input : Type}

def packetRegularHull
    (T : PacketOutputTrace S Input) (qReadout : Input -> ℝ)
    (H : HullFamily S) :
    RegularHull (packetFamilyPresentation T qReadout) where
  Derivation := fun {_} A r =>
    PLift (
      UnionAdmissible S H (nativeRegionSet S A) ∧
      r = regionToOutputFamily S
        (hullProfile S H (nativeRegionSet S A)))

def packetHulledFamily
    (T : PacketOutputTrace S Input) (qReadout : Input -> ℝ)
    (H : HullFamily S) (i : Input)
    (z : ProducedFamily (packetFamilyPresentation T qReadout) (b := ()) i)
    (hdom : UnionAdmissible S H (tracedRegions T i)) :
    HulledFamily
      (packetFamilyPresentation T qReadout)
      (packetRegularHull T qReadout H) (b := ()) i where
  seed := z
  region :=
    regionToOutputFamily S (hullProfile S H (tracedRegions T i))
  derivation := by
    refine PLift.up ⟨?_, ?_⟩
    · rw [native_possibleRegionFamilies_eq_tracedRegions S T qReadout i]
      exact hdom
    · rw [native_possibleRegionFamilies_eq_tracedRegions S T qReadout i]

def packetFiniteReadout
    (T : PacketOutputTrace S Input) (qReadout : Input -> ℝ)
    (H : HullFamily S) (i : Input)
    (z : ProducedFamily (packetFamilyPresentation T qReadout) (b := ()) i)
    (hdom : UnionAdmissible S H (tracedRegions T i)) :
    FiniteFamilyReadout
      (packetFamilyPresentation T qReadout)
      (packetRegularHull T qReadout H)
      (packetProcessionNormalization S T qReadout)
      (b := ()) i where
  hulled := packetHulledFamily T qReadout H i z hdom
  value := endpoint S H (tracedRegions T i)
  value_spec := by
    simpa [endpoint] using
      (extendedReadout_region_eq_procVol
        S T qReadout (hullProfile S H (tracedRegions T i))).symm

theorem packetFiniteReadout_value_eq_endpoint
    (T : PacketOutputTrace S Input) (qReadout : Input -> ℝ)
    (H : HullFamily S) (i : Input)
    (w : FiniteFamilyReadout
      (packetFamilyPresentation T qReadout)
      (packetRegularHull T qReadout H)
      (packetProcessionNormalization S T qReadout)
      (b := ()) i) :
    w.value = endpoint S H (tracedRegions T i) := by
  have hderiv := w.hulled.derivation.down
  have hregion :
      w.hulled.region =
        regionToOutputFamily S (hullProfile S H (tracedRegions T i)) := by
    have h := hderiv.2
    rw [native_possibleRegionFamilies_eq_tracedRegions S T qReadout i] at h
    exact h
  have hw :
      (w.value : WithTop ℝ) =
        (endpoint S H (tracedRegions T i) : WithTop ℝ) := by
    calc
      (w.value : WithTop ℝ) =
          extendedFamilyReadout
            (packetFamilyPresentation T qReadout)
            (packetProcessionNormalization S T qReadout)
            w.hulled.region := w.value_spec
      _ =
          extendedFamilyReadout
            (packetFamilyPresentation T qReadout)
            (packetProcessionNormalization S T qReadout)
            (regionToOutputFamily S
              (hullProfile S H (tracedRegions T i))) := by
            rw [hregion]
      _ =
          (S.procVol (hullProfile S H (tracedRegions T i)) :
            WithTop ℝ) :=
        extendedReadout_region_eq_procVol
          S T qReadout (hullProfile S H (tracedRegions T i))
      _ = (endpoint S H (tracedRegions T i) : WithTop ℝ) := rfl
  exact WithTop.coe_eq_coe.mp hw

theorem packetPipelineScalars_subset_singleton
    (T : PacketOutputTrace S Input) (qReadout : Input -> ℝ)
    (H : HullFamily S) (i : Input) :
    pipelineScalars
        (packetFamilyPresentation T qReadout)
        (packetRegularHull T qReadout H)
        (packetProcessionNormalization S T qReadout)
        (b := ()) i
      ⊆ {endpoint S H (tracedRegions T i)} := by
  rintro y ⟨w, rfl⟩
  exact Set.mem_singleton_iff.mpr
    (packetFiniteReadout_value_eq_endpoint T qReadout H i w)

theorem deterministic_packet_hull_has_no_outputShape
    (T : PacketOutputTrace S Input) (qReadout : Input -> ℝ)
    (H : HullFamily S) (i : Input) :
    ¬ Nonempty
      (OutputShape
        (packetFamilyPresentation T qReadout)
        (packetRegularHull T qReadout H)
        (packetProcessionNormalization S T qReadout)
        (b := ()) i) := by
  rintro ⟨shape⟩
  have hsub :=
    packetPipelineScalars_subset_singleton T qReadout H i
  have htop :
      shape.thetaBound ∈
        pipelineScalars
          (packetFamilyPresentation T qReadout)
          (packetRegularHull T qReadout H)
          (packetProcessionNormalization S T qReadout)
          (b := ()) i := by
    rw [shape.shape]
    exact Set.mem_Iic.mpr le_rfl
  have hlower :
      shape.thetaBound - 1 ∈
        pipelineScalars
          (packetFamilyPresentation T qReadout)
          (packetRegularHull T qReadout H)
          (packetProcessionNormalization S T qReadout)
          (b := ()) i := by
    rw [shape.shape]
    exact Set.mem_Iic.mpr (by linarith)
  have heqTop :
      shape.thetaBound = endpoint S H (tracedRegions T i) :=
    Set.mem_singleton_iff.mp (hsub htop)
  have heqLower :
      shape.thetaBound - 1 = endpoint S H (tracedRegions T i) :=
    Set.mem_singleton_iff.mp (hsub hlower)
  linarith

theorem packetEndpoint_mem_pipelineScalars
    (T : PacketOutputTrace S Input) (qReadout : Input -> ℝ)
    (H : HullFamily S) (i : Input)
    (z : ProducedFamily (packetFamilyPresentation T qReadout) (b := ()) i)
    (hdom : UnionAdmissible S H (tracedRegions T i)) :
    endpoint S H (tracedRegions T i) ∈
      pipelineScalars
        (packetFamilyPresentation T qReadout)
        (packetRegularHull T qReadout H)
        (packetProcessionNormalization S T qReadout)
        (b := ()) i := by
  exact ⟨packetFiniteReadout T qReadout H i z hdom, rfl⟩

end CitedLV.Theorem311.PacketHullPipelineAdapter
end
