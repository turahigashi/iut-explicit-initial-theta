import Cor312LogVolume.theorem311.PacketReadoutObject
import Cor312LogVolume.theorem311.assembly.StepXiInference
import Cor312LogVolume.relative.SimultaneousFamilyFrontier

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.PacketOutputTraceFrontier

open Src.IUT3.Theorem311
open CitedLV.Theorem311.StepXi
open Src.CoreLayer.RelativeXiFFamily

structure PacketOutputTrace (S : PacketSystem) (Input : Type) where
  Trace : Input -> S.Regions -> Type

variable {S : PacketSystem} {Input : Type}

def tracedRegions (T : PacketOutputTrace S Input) (i : Input) : Set S.Regions :=
  {R | Nonempty (T.Trace i R)}

def tracedTwoReadings
    (T : PacketOutputTrace S Input) (i : Input) (qRegion : S.Regions) :
    TwoReadings S.Regions Real where
  thetaPossible := tracedRegions T i
  vol := S.procVol
  qObject := qRegion

theorem sameConstruction_iff_trace
    (T : PacketOutputTrace S Input) (i : Input) (qRegion : S.Regions) :
    SameConstruction (tracedTwoReadings T i qRegion) ↔
      Nonempty (T.Trace i qRegion) := by
  rfl

def regionToOutputFamily (S : PacketSystem) (R : S.Regions) :
    (j : Fin (S.lstar + 1)) -> (vQ : S.PlaceQ) -> Set (S.Packet vQ j) :=
  fun j vQ => R vQ j

def outputFamilyToRegion (S : PacketSystem)
    (o : (j : Fin (S.lstar + 1)) ->
      (vQ : S.PlaceQ) -> Set (S.Packet vQ j)) :
    S.Regions :=
  fun vQ j => o j vQ

@[simp] theorem outputFamilyToRegion_regionToOutputFamily
    (S : PacketSystem) (R : S.Regions) :
    outputFamilyToRegion S (regionToOutputFamily S R) = R := by
  funext vQ j
  rfl

@[simp] theorem regionToOutputFamily_outputFamilyToRegion
    (S : PacketSystem)
    (o : (j : Fin (S.lstar + 1)) ->
      (vQ : S.PlaceQ) -> Set (S.Packet vQ j)) :
    regionToOutputFamily S (outputFamilyToRegion S o) = o := by
  funext j vQ
  rfl

def packetFamilyPresentation
    (T : PacketOutputTrace S Input) (qReadout : Input -> Real) :
    FamilyPresentation Unit
      (fun _ => Fin (S.lstar + 1)) (fun _ => S.PlaceQ) where
  QInput := fun _ => Input
  OutputFiber := fun _ j vQ => Set (S.Packet vQ j)
  RegionFiber := fun _ j vQ => Set (S.Packet vQ j)
  Trace := fun i o => T.Trace i (outputFamilyToRegion S o)
  outputRegion := id
  rawLogVol := fun {_} {j} {vQ} R =>
    (S.packetLogVolume vQ j R : WithBot Real)
  qLogVolume := fun i => qReadout i

def ProducesRegion
    (T : PacketOutputTrace S Input) (qReadout : Input -> Real)
    (i : Input) (R : S.Regions) : Prop :=
  ∃ z :
      ProducedFamily (packetFamilyPresentation T qReadout) (b := ()) i,
    outputFamilyToRegion S z.output = R

theorem producesRegion_iff_trace
    (T : PacketOutputTrace S Input) (qReadout : Input -> Real)
    (i : Input) (R : S.Regions) :
    ProducesRegion T qReadout i R ↔ Nonempty (T.Trace i R) := by
  constructor
  · rintro ⟨z, hz⟩
    have htrace : T.Trace i (outputFamilyToRegion S z.output) := z.trace
    rw [hz] at htrace
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
    exact ⟨z, outputFamilyToRegion_regionToOutputFamily S R⟩

theorem sameConstruction_iff_producesRegion
    (T : PacketOutputTrace S Input) (qReadout : Input -> Real)
    (i : Input) (qRegion : S.Regions) :
    SameConstruction (tracedTwoReadings T i qRegion) ↔
      ProducesRegion T qReadout i qRegion := by
  rw [sameConstruction_iff_trace, producesRegion_iff_trace]

theorem trace_gives_volumeMembership
    (T : PacketOutputTrace S Input) (i : Input) (qRegion : S.Regions)
    (htrace : Nonempty (T.Trace i qRegion)) :
    qVolume (tracedTwoReadings T i qRegion) ∈
      thetaVolumes (tracedTwoReadings T i qRegion) :=
  xi_f_inference_is_valid _ ((sameConstruction_iff_trace T i qRegion).2 htrace)

def tracedScalarValues
    (T : PacketOutputTrace S Input) (i : Input) : Set ℝ :=
  S.procVol '' tracedRegions T i

def TracedScalarProduction
    (T : PacketOutputTrace S Input) (i : Input) (qValue : ℝ) : Prop :=
  qValue ∈ tracedScalarValues T i

theorem tracedScalarProduction_iff_exists_trace_equal_value
    (T : PacketOutputTrace S Input) (i : Input) (qValue : ℝ) :
    TracedScalarProduction T i qValue ↔
      ∃ R : S.Regions, Nonempty (T.Trace i R) ∧ S.procVol R = qValue := by
  constructor
  · rintro ⟨R, htrace, hvalue⟩
    exact ⟨R, htrace, hvalue⟩
  · rintro ⟨R, htrace, hvalue⟩
    exact ⟨R, htrace, hvalue⟩

theorem tracedScalarProduction_iff_exists_producedRegion
    (T : PacketOutputTrace S Input) (qReadout : Input -> Real)
    (i : Input) (qValue : ℝ) :
    TracedScalarProduction T i qValue ↔
      ∃ R : S.Regions,
        ProducesRegion T qReadout i R ∧ S.procVol R = qValue := by
  rw [tracedScalarProduction_iff_exists_trace_equal_value]
  constructor
  · rintro ⟨R, htrace, hvalue⟩
    exact ⟨R, (producesRegion_iff_trace T qReadout i R).2 htrace, hvalue⟩
  · rintro ⟨R, hproduced, hvalue⟩
    exact ⟨R, (producesRegion_iff_trace T qReadout i R).1 hproduced, hvalue⟩

theorem trace_implies_tracedScalarProduction
    (T : PacketOutputTrace S Input) (i : Input) (R : S.Regions)
    (htrace : Nonempty (T.Trace i R)) :
    TracedScalarProduction T i (S.procVol R) := by
  exact
    (tracedScalarProduction_iff_exists_trace_equal_value T i (S.procVol R)).2
      ⟨R, htrace, rfl⟩

theorem scalarProduction_does_not_force_namedRegionTrace :
    ∃ (T : PacketOutputTrace modelSystem Unit)
      (qRegion : modelSystem.Regions),
      TracedScalarProduction T () (modelSystem.procVol qRegion) ∧
        ¬ Nonempty (T.Trace () qRegion) := by
  obtain ⟨x, y, hind2, hxy⟩ := model_ind2_nontrivial
  let T : PacketOutputTrace modelSystem Unit :=
    { Trace := fun _ R => PLift (R = x) }
  refine ⟨T, y, ?_, ?_⟩
  · exact
      (tracedScalarProduction_iff_exists_trace_equal_value
        T () (modelSystem.procVol y)).2
        ⟨x, ⟨PLift.up rfl⟩, modelSystem.procVol_ind2 hind2⟩
  · rintro ⟨htrace⟩
    exact hxy htrace.down.symm

end CitedLV.Theorem311.PacketOutputTraceFrontier
end
