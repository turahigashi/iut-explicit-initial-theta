import Cor312LogVolume.theorem311.P211ActualLogShellHullBinding
import Cor312LogVolume.theorem311.P211TensorPacketCollapse

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211Completion

open Src.IUT3.Theorem311
open Src.IUT3.Remark122
open Src.CoreLayer.RelativeXiFFamily
open CitedLV.Theorem311
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211ComponentCTraceBridge
open CitedLV.Theorem311.P211ComponentCRadialXiF
open CitedLV.Theorem311.P211SourceFacingSimultaneousXiF
open CitedLV.Theorem311.P211LambdaHullSourceBinding
open CitedLV.Theorem311.P211ActualLogShellHullBinding
open CitedLV.Theorem311.P211LogShellPacketBridge
open CitedLV.Theorem311.P211TensorPacketCollapse
open CitedLV.Theorem311.PadicTensorPacketTopology
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Theorem311.PacketHullPipelineAdapter
open CitedLV.Theorem311.PacketProcessionNormalizationAdapter

theorem p211NormHulls_actualLogShellHullLaw :
    SourceLambdaActualLogShellHullLaw p211NormHulls :=
  (sourceLambdaIntegralHullLaw_iff_actualLogShell p211NormHulls).1
    p211NormHulls_sourceLambdaIntegralHullLaw

theorem qRegion_is_nonzero_lambda_actualLogShell
    (vQ : p211PacketSystem.PlaceQ)
    (j : Fin (p211PacketSystem.lstar + 1)) :
    ∃ c : ℚ_[211], c ≠ 0 ∧
      p211QRegion vQ j =
        (fun z : ℚ_[211] => c * z) ''
          logShell (K := ℚ_[211]) 211 := by
  refine ⟨pElt ^ 29, pow_ne_zero _ pElt_ne_zero, ?_⟩
  rw [← integral_eq_actual_logShell vQ j]
  rfl

def completedXiFGenerated :
    XiFGenerated
      simultaneousPresentation
      (packetRegularHull
        simultaneousTrace componentCInputReadout p211NormHulls)
      (packetProcessionNormalization
        p211PacketSystem simultaneousTrace componentCInputReadout)
      (b := ()) p211Input :=
  xifGenerated_of_actualLogShellHullLaw
    p211NormHulls p211NormHulls_actualLogShellHullLaw

theorem completedXiFGenerated_value :
    completedXiFGenerated.readout.value =
      -(29 / 7) * Real.log 211 := by
  calc
    completedXiFGenerated.readout.value =
        componentCInputReadout p211Input :=
      completedXiFGenerated.generates_q
    _ = -(29 / 7) * Real.log 211 :=
      p211Input_readout_eq_obligationE

theorem p211_obligationE_completed :
    ∃ x :
      XiFGenerated
        simultaneousPresentation
        (packetRegularHull
          simultaneousTrace componentCInputReadout p211NormHulls)
        (packetProcessionNormalization
          p211PacketSystem simultaneousTrace componentCInputReadout)
        (b := ()) p211Input,
      x.readout.value = -(29 / 7) * Real.log 211 :=
  ⟨completedXiFGenerated, completedXiFGenerated_value⟩

structure Certificate : Prop where
  simultaneous_checked :
    CheckedProcessionFunctorialAlgorithm sourceAlgorithm
  packet_is_container :
    (sourceAlgorithm.build ()).packet = integralContainer
  fieldCopy_is_actual :
    (sourceAlgorithm.build ()).fieldCopy =
      P211RLGPRaw.Global.fieldCopy
  tensor_carrier_equivalent :
    ∀ j : Fin (p211PacketSystem.lstar + 1),
      Nonempty
        (TensorPacket (j.val + 1) ≃ₗ[ℚ_[211]]
          p211PacketSystem.Packet () j)
  realized_qRegion :
    realizedRegion p211Input = p211QRegion
  integral_is_actual_logShell :
    ∀ vQ j,
      p211PacketSystem.integral vQ j =
        logShell (K := ℚ_[211]) 211
  qRegion_is_lambda_actualLogShell :
    ∀ vQ j, ∃ c : ℚ_[211], c ≠ 0 ∧
      p211QRegion vQ j =
        (fun z : ℚ_[211] => c * z) ''
          logShell (K := ℚ_[211]) 211
  trace_contains_qRegion :
    Nonempty (simultaneousTrace.Trace p211Input p211QRegion)
  xif_generated :
    Nonempty
      (XiFGenerated
        simultaneousPresentation
        (packetRegularHull
          simultaneousTrace componentCInputReadout p211NormHulls)
        (packetProcessionNormalization
          p211PacketSystem simultaneousTrace componentCInputReadout)
        (b := ()) p211Input)
  target_value :
    completedXiFGenerated.readout.value =
      -(29 / 7) * Real.log 211

theorem certificate : Certificate := by
  refine
    { simultaneous_checked := sourceAlgorithm_checked
      packet_is_container := sourceAlgorithm_packet
      fieldCopy_is_actual := sourceAlgorithm_fieldCopy
      tensor_carrier_equivalent := ?_
      realized_qRegion := realizedRegion_p211
      integral_is_actual_logShell := ?_
      qRegion_is_lambda_actualLogShell := ?_
      trace_contains_qRegion := simultaneousTrace_p211_qRegion
      xif_generated := ⟨completedXiFGenerated⟩
      target_value := completedXiFGenerated_value }
  · intro j
    exact stage_tensor_carrier_equivalent j
  · intro vQ j
    exact integral_eq_actual_logShell vQ j
  · intro vQ j
    exact qRegion_is_nonzero_lambda_actualLogShell vQ j

end CitedLV.Theorem311.P211Completion
end
