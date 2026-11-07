import Cor312LogVolume.theorem311.PacketOutputTraceFrontier

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.PacketPossibleRegionAdapter

open Src.IUT3.Theorem311
open Src.CoreLayer.RelativeXiFFamily
open CitedLV.Theorem311.PacketOutputTraceFrontier

variable {Input : Type}

def nativeRegionSet (S : PacketSystem)
    (A : Set ((j : Fin (S.lstar + 1)) ->
      (vQ : S.PlaceQ) -> Set (S.Packet vQ j))) :
    Set S.Regions :=
  {R | regionToOutputFamily S R ∈ A}

theorem native_possibleRegionFamilies_eq_tracedRegions
    (S : PacketSystem) (T : PacketOutputTrace S Input)
    (qReadout : Input -> ℝ) (i : Input) :
    nativeRegionSet S
        (possibleRegionFamilies
          (packetFamilyPresentation T qReadout) (b := ()) i)
      = tracedRegions T i := by
  ext R
  constructor
  · intro hR
    change
      regionToOutputFamily S R ∈
        possibleRegionFamilies
          (packetFamilyPresentation T qReadout) (b := ()) i at hR
    rcases hR with ⟨z, hz⟩
    have hout : z.output = regionToOutputFamily S R := by
      change z.output = regionToOutputFamily S R at hz
      exact hz
    have htrace : T.Trace i (outputFamilyToRegion S z.output) := z.trace
    have hnative : outputFamilyToRegion S z.output = R := by
      rw [hout, outputFamilyToRegion_regionToOutputFamily]
    rw [hnative] at htrace
    exact ⟨htrace⟩
  · rintro ⟨htrace⟩
    let z :
        ProducedFamily (packetFamilyPresentation T qReadout) (b := ()) i :=
      { output := regionToOutputFamily S R
        trace := by
          change T.Trace i
            (outputFamilyToRegion S (regionToOutputFamily S R))
          rw [outputFamilyToRegion_regionToOutputFamily]
          exact htrace }
    change
      regionToOutputFamily S R ∈
        possibleRegionFamilies
          (packetFamilyPresentation T qReadout) (b := ()) i
    refine ⟨z, ?_⟩
    rfl

theorem native_mem_possibleRegionFamilies_iff_trace
    (S : PacketSystem) (T : PacketOutputTrace S Input)
    (qReadout : Input -> ℝ) (i : Input) (R : S.Regions) :
    R ∈ nativeRegionSet S
        (possibleRegionFamilies
          (packetFamilyPresentation T qReadout) (b := ()) i)
      ↔ Nonempty (T.Trace i R) := by
  rw [native_possibleRegionFamilies_eq_tracedRegions]
  rfl

end CitedLV.Theorem311.PacketPossibleRegionAdapter
end
