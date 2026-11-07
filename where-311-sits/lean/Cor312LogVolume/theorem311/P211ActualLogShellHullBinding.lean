import Cor312LogVolume.theorem311.P211LambdaHullSourceBinding
import Cor312LogVolume.theorem311.P211LogShellPacketBridge

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211ActualLogShellHullBinding

open Src.IUT3.Theorem311
open Src.IUT3.Remark122
open Src.CoreLayer.RelativeXiFFamily
open CitedLV.Theorem311
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211LogShellPacketBridge
open CitedLV.Theorem311.P211ComponentCTraceBridge
open CitedLV.Theorem311.P211SourceFacingSimultaneousXiF
open CitedLV.Theorem311.P211LambdaHullSourceBinding
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Theorem311.PacketHullPipelineAdapter
open CitedLV.Theorem311.PacketProcessionNormalizationAdapter

def SourceLambdaActualLogShellHullLaw
    (H : HullFamily p211PacketSystem) : Prop :=
  ∀ vQ j (c : ℚ_[211]), c ≠ 0 →
    (H vQ j).isHull
      ((fun z : ℚ_[211] => c * z) ''
        logShell (K := ℚ_[211]) 211)

theorem sourceLambdaIntegralHullLaw_iff_actualLogShell
    (H : HullFamily p211PacketSystem) :
    SourceLambdaIntegralHullLaw H ↔
      SourceLambdaActualLogShellHullLaw H := by
  constructor
  · intro h vQ j c hc
    rw [← integral_eq_actual_logShell vQ j]
    exact h vQ j c hc
  · intro h vQ j c hc
    rw [integral_eq_actual_logShell vQ j]
    exact h vQ j c hc

def xifGenerated_of_actualLogShellHullLaw
    (H : HullFamily p211PacketSystem)
    (hH : SourceLambdaActualLogShellHullLaw H) :
    XiFGenerated
      simultaneousPresentation
      (packetRegularHull simultaneousTrace componentCInputReadout H)
      (packetProcessionNormalization
        p211PacketSystem simultaneousTrace componentCInputReadout)
      (b := ()) p211Input :=
  xifGenerated_of_sourceLambdaIntegralHullLaw H
    ((sourceLambdaIntegralHullLaw_iff_actualLogShell H).2 hH)

theorem xifGenerated_nonempty_of_actualLogShellHullLaw
    (H : HullFamily p211PacketSystem)
    (hH : SourceLambdaActualLogShellHullLaw H) :
    Nonempty
      (XiFGenerated
        simultaneousPresentation
        (packetRegularHull simultaneousTrace componentCInputReadout H)
        (packetProcessionNormalization
          p211PacketSystem simultaneousTrace componentCInputReadout)
        (b := ()) p211Input) :=
  ⟨xifGenerated_of_actualLogShellHullLaw H hH⟩

end CitedLV.Theorem311.P211ActualLogShellHullBinding
end
