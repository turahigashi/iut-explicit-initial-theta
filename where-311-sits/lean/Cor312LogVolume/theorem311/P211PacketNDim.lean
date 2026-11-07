import Cor312LogVolume.theorem311.P211PacketSystem
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
namespace CitedLV.Theorem311.P211PacketN

open Metric Set MeasureTheory
open Src.IUT3.Theorem311 Src.IUT4.Proposition14ii
open CitedLV.Theorem311.P211Packet

abbrev muPi (n : ℕ) : Measure (Fin n → ℚ_[211]) :=
  Measure.pi (fun _ => haarQp 211)

instance muPi_isAddHaar (n : ℕ) : (muPi n).IsAddHaarMeasure := inferInstance

theorem haarQp_unit : haarQp 211 (closedBall (0 : ℚ_[211]) 1) = 1 := by
  unfold haarQp
  exact Measure.addHaarMeasure_self

theorem haarQp_qBall (k : ℕ) :
    haarQp 211 (qBall k) = ((211 : ENNReal))⁻¹ ^ k := by
  induction k with
  | zero =>
      have h0 : qBall 0 = closedBall (0 : ℚ_[211]) 1 := by rw [qBall_eq]; norm_num
      rw [h0, haarQp_unit]
      simp
  | succ k ih =>
      rw [qBall_succ, haarQp_mul_p (qBall k) (qBall_measurable k), ih]
      ring

def qBallN (n k : ℕ) : Set (Fin n → ℚ_[211]) :=
  Set.univ.pi (fun _ => qBall k)

theorem qBallN_measure (n k : ℕ) :
    muPi n (qBallN n k) = (((211 : ENNReal))⁻¹ ^ k) ^ n := by
  rw [qBallN, Measure.pi_pi]
  simp [haarQp_qBall]

theorem qBallN_zero_measure (n : ℕ) : muPi n (qBallN n 0) = 1 := by
  rw [qBallN_measure]
  simp

theorem logVolume_qBallN (n k : ℕ) :
    logVolume (muPi n) (qBallN n 0) (qBallN n k)
      = -((n : ℝ) * (k : ℝ)) * Real.log 211 := by
  unfold logVolume
  rw [qBallN_measure, qBallN_zero_measure]
  have h1 : ((((211 : ENNReal))⁻¹ ^ k) ^ n).toReal = ((211 : ℝ)⁻¹ ^ k) ^ n := by
    simp [ENNReal.toReal_pow, ENNReal.toReal_inv]
  rw [h1, ENNReal.toReal_one, Real.log_one, sub_zero]

  rw [Real.log_pow, Real.log_pow, Real.log_inv]
  ring

end CitedLV.Theorem311.P211PacketN
end
