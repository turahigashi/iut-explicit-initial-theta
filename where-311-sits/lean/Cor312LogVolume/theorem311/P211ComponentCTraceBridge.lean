import Cor312LogVolume.theorem311.P211RLGPRawComponents
import Cor312LogVolume.theorem311.P211PlaceOver211
import Cor312LogVolume.theorem311.PacketOutputTraceFrontier

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211ComponentCTraceBridge

open Metric
open scoped NumberField
open CitedLV.Theorem311
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211RLGPRaw
open CitedLV.Theorem311.P211FieldCopyReadout
open CitedLV.Theorem311.P211PlaceOver211
open CitedLV.Theorem311.PacketOutputTraceFrontier
open CitedLV.Theorem311.StepXi
open Src.IUT3.Theorem311

def selectedLabel : P211RLGPRaw.Label := 0

def componentCGlobal211 :
    P211RLGPRaw.Global.GlobalCopy selectedLabel :=
  y211

theorem components_fieldCopy_eq_actual :
    P211RLGPRaw.components.fieldCopy = P211RLGPRaw.Global.fieldCopy := rfl

def integralContainer : p211PacketSystem.Regions :=
  fun vQ j => p211PacketSystem.integral vQ j

def sourceFacingComponents :
    RLGPRawComponents
      p211PacketSystem.Regions P211RLGPRaw.SplittingDatum
        P211RLGPRaw.FieldCopyDatum where
  packet := integralContainer
  splitting := P211RLGPRaw.splitting
  fieldCopy := P211RLGPRaw.Global.fieldCopy

@[simp] theorem sourceFacingComponents_packet :
    sourceFacingComponents.packet = integralContainer := rfl

@[simp] theorem sourceFacingComponents_splitting :
    sourceFacingComponents.splitting = P211RLGPRaw.splitting := rfl

@[simp] theorem sourceFacingComponents_fieldCopy :
    sourceFacingComponents.fieldCopy = P211RLGPRaw.Global.fieldCopy := rfl

abbrev V211LocalField :=
  Dispute.Prop310OrdinaryGlobalLocalization.LocalField ℚ (Sum.inl v211)

def v211CompletionToPadic : V211LocalField ≃A[ℚ] ℚ_[211] :=
  (Padic.adicCompletionEquiv (𝓞 ℚ) p211).symm

def fieldCopyFiniteValue
    (x : P211RLGPRaw.Global.GlobalCopy selectedLabel) : V211LocalField :=
  ((sourceFacingComponents.fieldCopy.embed selectedLabel x (Sum.inl v211)
      : V211LocalFieldˣ) : V211LocalField)

theorem fieldCopyFiniteValue_eq_embedding
    (x : P211RLGPRaw.Global.GlobalCopy selectedLabel) :
    fieldCopyFiniteValue x =
      NumberField.FinitePlace.embedding v211 (x : ℚ) := by
  unfold fieldCopyFiniteValue
  rw [sourceFacingComponents_fieldCopy]
  rfl

def fieldCopyPadicScalar
    (x : P211RLGPRaw.Global.GlobalCopy selectedLabel) : ℚ_[211] :=
  v211CompletionToPadic (fieldCopyFiniteValue x)

theorem fieldCopyPadicScalar_eq_algebraMap
    (x : P211RLGPRaw.Global.GlobalCopy selectedLabel) :
    fieldCopyPadicScalar x = algebraMap ℚ ℚ_[211] (x : ℚ) := by
  unfold fieldCopyPadicScalar
  rw [fieldCopyFiniteValue_eq_embedding]
  simpa only [NumberField.FinitePlace.embedding_apply] using
    (v211CompletionToPadic.commutes (x : ℚ))

theorem componentCGlobal211_padic :
    fieldCopyPadicScalar componentCGlobal211 = pElt := by
  rw [fieldCopyPadicScalar_eq_algebraMap]
  norm_num [componentCGlobal211, y211, pElt]

def fieldCopyActOnContainer
    (x : P211RLGPRaw.Global.GlobalCopy selectedLabel) (n : ℕ) :
    p211PacketSystem.Regions :=
  fun vQ j =>
    (fun z : ℚ_[211] => (fieldCopyPadicScalar x ^ n) * z) ''
      sourceFacingComponents.packet vQ j

theorem fieldCopyActOnContainer_y211_eq_qRegion :
    fieldCopyActOnContainer componentCGlobal211 29 = p211QRegion := by
  funext vQ j
  change
    (fun z : ℚ_[211] =>
      (fieldCopyPadicScalar componentCGlobal211 ^ 29) * z) ''
        sourceFacingComponents.packet vQ j
      = qBall 29
  rw [sourceFacingComponents_packet]
  change
    (fun z : ℚ_[211] =>
      (fieldCopyPadicScalar componentCGlobal211 ^ 29) * z) ''
        closedBall (0 : ℚ_[211]) 1
      = qBall 29
  rw [componentCGlobal211_padic]
  rfl

theorem fieldCopyReadout_eq_packetProcVol :
    (1 / 7 : ℝ) * cLogReadout ℚ v211 (y211 ^ 29)
      =
    p211PacketSystem.procVol
      (fieldCopyActOnContainer componentCGlobal211 29) := by
  calc
    (1 / 7 : ℝ) * cLogReadout ℚ v211 (y211 ^ 29)
        = -(29 / 7) * Real.log 211 := qPilot_value_at_211
    _ = p211PacketSystem.procVol
          (fieldCopyActOnContainer componentCGlobal211 29) := by
      rw [fieldCopyActOnContainer_y211_eq_qRegion, p211_procVol]

structure ComponentCInput where
  globalElement : P211RLGPRaw.Global.GlobalCopy selectedLabel
  exponent : ℕ

def p211Input : ComponentCInput where
  globalElement := componentCGlobal211
  exponent := 29

def inputRegion (i : ComponentCInput) : p211PacketSystem.Regions :=
  fieldCopyActOnContainer i.globalElement i.exponent

def componentCInputReadout (i : ComponentCInput) : ℝ :=
  (1 / 7 : ℝ) * cLogReadout ℚ v211 (i.globalElement ^ i.exponent)

theorem p211Input_region_eq_qRegion :
    inputRegion p211Input = p211QRegion := by
  simpa [inputRegion, p211Input] using fieldCopyActOnContainer_y211_eq_qRegion

theorem p211Input_readout_eq_obligationE :
    componentCInputReadout p211Input = -(29 / 7) * Real.log 211 := by
  simpa [componentCInputReadout, p211Input, componentCGlobal211] using
    qPilot_value_at_211

theorem p211Input_readout_eq_packetProcVol :
    componentCInputReadout p211Input =
      p211PacketSystem.procVol (inputRegion p211Input) := by
  simpa [componentCInputReadout, inputRegion, p211Input, componentCGlobal211] using
    fieldCopyReadout_eq_packetProcVol

def componentCTrace :
    PacketOutputTrace p211PacketSystem ComponentCInput where
  Trace := fun i R =>
    PLift
      (Quot.mk p211PacketSystem.IndRel R =
        Quot.mk p211PacketSystem.IndRel (inputRegion i))

theorem componentCTrace_inputRegion (i : ComponentCInput) :
    Nonempty (componentCTrace.Trace i (inputRegion i)) :=
  ⟨PLift.up rfl⟩

theorem componentCTrace_qRegion :
    Nonempty (componentCTrace.Trace p211Input p211QRegion) := by
  rw [← p211Input_region_eq_qRegion]
  exact componentCTrace_inputRegion p211Input

theorem componentC_tracedScalarProduction :
    TracedScalarProduction componentCTrace p211Input
      (componentCInputReadout p211Input) := by
  exact
    (tracedScalarProduction_iff_exists_trace_equal_value
      componentCTrace p211Input (componentCInputReadout p211Input)).2
      ⟨inputRegion p211Input,
        componentCTrace_inputRegion p211Input,
        p211Input_readout_eq_packetProcVol.symm⟩

theorem componentC_tracedScalarProduction_obligationE :
    TracedScalarProduction componentCTrace p211Input
      (-(29 / 7) * Real.log 211) := by
  rw [← p211Input_readout_eq_obligationE]
  exact componentC_tracedScalarProduction

theorem componentC_sameConstruction_qRegion :
    SameConstruction
      (tracedTwoReadings componentCTrace p211Input p211QRegion) :=
  (sameConstruction_iff_trace componentCTrace p211Input p211QRegion).2
    componentCTrace_qRegion

theorem componentC_produces_qRegion :
    ProducesRegion componentCTrace componentCInputReadout
      p211Input p211QRegion :=
  (producesRegion_iff_trace
    componentCTrace componentCInputReadout p211Input p211QRegion).2
    componentCTrace_qRegion

end CitedLV.Theorem311.P211ComponentCTraceBridge
end
