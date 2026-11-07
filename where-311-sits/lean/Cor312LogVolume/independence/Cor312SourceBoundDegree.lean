import Cor312LogVolume.independence.Cor312SourceBoundTheory
import Cor312LogVolume.theorem311.NumberFieldRealDivisor

set_option autoImplicit false
noncomputable section

namespace CitedLV.Independence.Cor312SourceBoundDegree

open NumberField
open Src.EtTh.PadicThetaValues
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211FieldCopyReadout
open CitedLV.Theorem311.P211PlaceOver211
open CitedLV.Theorem311.NumberFieldRealDivisor
open CitedLV.Independence.Cor312SourceBound

def w211 : FinitePlace ℚ := FinitePlace.mk v211

def qDivisor : Divisor ℚ :=
  (Finsupp.single w211 (finitePrincipal (y211 ^ 29) w211), 0)

def thetaDivisor (t : ℂ_[211]ˣ) : Divisor ℚ :=
  (Finsupp.single w211 (-Real.log ‖((t : ℂ_[211]ˣ) : ℂ_[211])‖), 0)

theorem degree_single (x : ℝ) : degree ℚ (Finsupp.single w211 x, 0) = x := by
  rw [degree_apply]
  simp [Finsupp.sum_single_index]

theorem finitePrincipal_y211_pow :
    finitePrincipal (y211 ^ 29) w211 = -cLogReadout ℚ v211 (y211 ^ 29) := by
  rfl

theorem cLogReadout_y211_pow : cLogReadout ℚ v211 (y211 ^ 29) = -29 * Real.log 211 := by
  have h := qPilot_value_at_211
  linarith

theorem qDivisor_degree : degree ℚ qDivisor = 29 * Real.log 211 := by
  rw [qDivisor, degree_single, finitePrincipal_y211_pow, cLogReadout_y211_pow]
  ring

theorem thetaDivisor_degree (j : ℕ) (t : ℂ_[211]ˣ) (ht : t ∈ rootValues 211 tateUnit 7 j) :
    degree ℚ (thetaDivisor t) = ((29 * (j * j) : ℕ) : ℝ) * Real.log 211 := by
  rw [thetaDivisor, degree_single, theta_root_norm j t ht, Real.log_pow, Real.log_inv]
  ring

theorem procVol_q_eq_degree :
    p211PacketSystem.procVol sourceQPilot = -(1 / 7) * degree ℚ qDivisor := by
  rw [procVol_sourceQPilot, qDivisor_degree]
  ring

theorem procVol_theta_eq_degree (t : Fin 3 → ℂ_[211]ˣ)
    (ht : ∀ k : Fin 3, t k ∈ rootValues 211 tateUnit 7 (k.val + 1)) :
    p211PacketSystem.procVol sourceThetaPilot
      = -(1 / 7) * ((∑ k : Fin 3, degree ℚ (thetaDivisor (t k))) / 3) := by
  have h : ∀ k : Fin 3, degree ℚ (thetaDivisor (t k))
      = ((29 * ((k.val + 1) * (k.val + 1)) : ℕ) : ℝ) * Real.log 211 :=
    fun k => thetaDivisor_degree (k.val + 1) (t k) (ht k)
  rw [procVol_sourceThetaPilot, Fin.sum_univ_three, h 0, h 1, h 2]
  norm_num
  ring

theorem exists_roots : ∃ t : Fin 3 → ℂ_[211]ˣ, ∀ k : Fin 3, t k ∈ rootValues 211 tateUnit 7 (k.val + 1) := by
  refine ⟨fun k => (rootValues_nonempty 211 tateUnit tateUnit_small 7 (k.val + 1) (by norm_num)).some,
    fun k => (rootValues_nonempty 211 tateUnit tateUnit_small 7 (k.val + 1) (by norm_num)).some_mem⟩

theorem degree_ratio (t : Fin 3 → ℂ_[211]ˣ)
    (ht : ∀ k : Fin 3, t k ∈ rootValues 211 tateUnit 7 (k.val + 1)) :
    (∑ k : Fin 3, degree ℚ (thetaDivisor (t k))) / 3 = (14 / 3) * degree ℚ qDivisor := by
  have h : ∀ k : Fin 3, degree ℚ (thetaDivisor (t k))
      = ((29 * ((k.val + 1) * (k.val + 1)) : ℕ) : ℝ) * Real.log 211 :=
    fun k => thetaDivisor_degree (k.val + 1) (t k) (ht k)
  rw [Fin.sum_univ_three, h 0, h 1, h 2, qDivisor_degree]
  norm_num
  ring

end CitedLV.Independence.Cor312SourceBoundDegree

section Check
open CitedLV.Independence.Cor312SourceBoundDegree
end Check
