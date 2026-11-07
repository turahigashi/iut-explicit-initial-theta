import Cor312LogVolume.theorem311.P211PacketSystemN

noncomputable section
namespace CitedLV.Theorem311.P211PacketN

open Metric Set MeasureTheory
open Src.IUT3.Theorem311 Src.IUT4.Proposition14ii
open CitedLV.Theorem311.P211Packet

theorem qBallN_zero_eq_ball (n : ℕ) :
    qBallN n 0 = closedBall (0 : Fin n → ℚ_[211]) 1 := by
  rw [qBallN, closedBall_pi _ (by norm_num : (0:ℝ) ≤ 1)]
  congr 1
  funext _
  rw [qBall_eq]
  simp

def qRegionN : p211PacketSystemN.Regions :=
  fun _ j => qBallN (j.val + 1) 29

theorem packetLogVolume_qRegionN (vQ : p211PacketSystemN.PlaceQ)
    (j : Fin (p211PacketSystemN.lstar + 1)) :
    p211PacketSystemN.packetLogVolume vQ j (qRegionN vQ j)
      = -(29 / 7) * Real.log 211 := by
  show (1 / (7 * ((j.val : ℝ) + 1)))
      * logVolume (muPi (j.val + 1)) (closedBall (0 : Fin (j.val + 1) → ℚ_[211]) 1)
          (qBallN (j.val + 1) 29) + 0 = _
  rw [← qBallN_zero_eq_ball, logVolume_qBallN]
  have hj : ((j.val : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem p211N_procVol :
    p211PacketSystemN.procVol qRegionN = -(29 / 7) * Real.log 211 := by
  rw [PacketSystem.procVol]
  simp only [packetLogVolume_qRegionN, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : Fintype.card p211PacketSystemN.PlaceQ = 1 := rfl
  have hl : (p211PacketSystemN.lstar : ℝ) = 3 := by norm_num [p211PacketSystemN]
  have hf : Fintype.card (Fin p211PacketSystemN.lstar) = 3 := by
    simp [p211PacketSystemN]
  rw [hc, hl, hf]
  push_cast
  ring

end CitedLV.Theorem311.P211PacketN
end
