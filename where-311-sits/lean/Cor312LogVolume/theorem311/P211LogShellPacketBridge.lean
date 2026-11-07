import Cor312LogVolume.theorem311.P211PacketSystem
import Cor312LogVolume.Src.IUT3.Section1Remark122LogShellInclusions

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211LogShellPacketBridge

open CitedLV.Theorem311.P211Packet
open Src.IUT3.Theorem311
open Src.IUT3.Remark122
open Src.IUT4.Proposition14ii

theorem integral_eq_actual_logShell
    (vQ : p211PacketSystem.PlaceQ)
    (j : Fin (p211PacketSystem.lstar + 1)) :
    p211PacketSystem.integral vQ j =
      logShell (K := ℚ_[211]) 211 := by
  change Metric.closedBall (0 : ℚ_[211]) 1 =
    logShell (K := ℚ_[211]) 211
  exact (logShell_Qp_eq (p := 211)).symm

theorem actual_logShell_logVolume_zero :
    logVolume (haarQp 211) (Metric.closedBall (0 : ℚ_[211]) 1)
      (logShell (K := ℚ_[211]) 211) = 0 := by
  exact (remark397i_Qp (p := 211)).2

theorem packetLogVolume_eq_actual_logShell
    (vQ : p211PacketSystem.PlaceQ)
    (j : Fin (p211PacketSystem.lstar + 1))
    (A : Set ℚ_[211]) :
    p211PacketSystem.packetLogVolume vQ j A =
      (1 / 7 : ℝ) *
        logVolume (haarQp 211) (logShell (K := ℚ_[211]) 211) A := by
  change (1 / 7 : ℝ) *
      logVolume (haarQp 211) (Metric.closedBall (0 : ℚ_[211]) 1) A + 0 = _
  rw [logShell_Qp_eq]
  ring

theorem p211_q_packetLogVolume_actual_logShell
    (vQ : p211PacketSystem.PlaceQ)
    (j : Fin (p211PacketSystem.lstar + 1)) :
    (1 / 7 : ℝ) *
        logVolume (haarQp 211) (logShell (K := ℚ_[211]) 211)
          (p211QRegion vQ j)
      = -(29 / 7) * Real.log 211 := by
  rw [← packetLogVolume_eq_actual_logShell vQ j]
  exact p211_packetLogVolume vQ j

end CitedLV.Theorem311.P211LogShellPacketBridge
end
