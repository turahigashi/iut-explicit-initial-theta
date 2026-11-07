import Cor312LogVolume.theorem311.P211NondegenerateXiF
import Cor312LogVolume.theorem311.Theta311AcceptancePackage

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211RealCarrierPackage

open Metric
open scoped Pointwise
open Src.IUT3.Theorem311
open CitedLV.Theorem311
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211PacketN
open CitedLV.Theorem311.P211IndeterminacyOrbit
open CitedLV.Theorem311.P211NondegenerateXiF

abbrev V := p211PacketSystemN.Regions

def unitVolP : ℝ := -(29 / 7) * Real.log 211

theorem unitVolP_neg : unitVolP < 0 := by
  unfold unitVolP
  have h : 0 < Real.log 211 := Real.log_pos (by norm_num)
  linarith

def thetaRegion (m : ℕ) : V := fun _ k => qBallN (k.val + 1) (29 * m)

theorem packetLogVolume_thetaRegion (m : ℕ) (vQ : p211PacketSystemN.PlaceQ)
    (k : Fin (p211PacketSystemN.lstar + 1)) :
    p211PacketSystemN.packetLogVolume vQ k (thetaRegion m vQ k)
      = -(29 * (m : ℝ) / 7) * Real.log 211 := by
  show (1 / (7 * ((k.val : ℝ) + 1)))
      * logVolume (muPi (k.val + 1)) (closedBall (0 : Fin (k.val + 1) → ℚ_[211]) 1)
          (qBallN (k.val + 1) (29 * m)) + 0 = _
  rw [← qBallN_zero_eq_ball, logVolume_qBallN]
  have hk : ((k.val : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem procVol_thetaRegion (m : ℕ) :
    p211PacketSystemN.procVol (thetaRegion m) = (m : ℝ) * unitVolP := by
  rw [PacketSystem.procVol]
  simp only [packetLogVolume_thetaRegion, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : Fintype.card p211PacketSystemN.PlaceQ = 1 := rfl
  have hl : (p211PacketSystemN.lstar : ℝ) = 3 := by norm_num [p211PacketSystemN]
  have hf : Fintype.card (Fin p211PacketSystemN.lstar) = 3 := by
    simp [p211PacketSystemN]
  rw [hc, hl, hf]
  unfold unitVolP
  push_cast
  ring

theorem thetaRegion_one : thetaRegion 1 = qRegionN := by
  funext vQ k
  simp [thetaRegion, qRegionN]

theorem ind2Act_thetaRegion (g : p211PacketSystemN.Ind2Element) (m : ℕ) :
    p211PacketSystemN.ind2Act g (thetaRegion m) = thetaRegion m := by
  funext vQ k
  exact unitAutQp_image_qBallN (k.val + 1) (29 * m) (g vQ k)

theorem smul_qBallN (n k a : ℕ) :
    (pElt ^ a) • qBallN n k = qBallN n (k + a) := by
  rw [qBallN_eq_closedBall, qBallN_eq_closedBall,
    smul_closedBall' (pow_ne_zero _ pElt_ne_zero), norm_pow, norm_p211, smul_zero, pow_add]
  ring_nf

def g0 : p211PacketSystemN.Ind2Element := fun _ _ _ _ => (-1 : ℤ_[211]ˣ)

def thetaSetP : Set V := {R | ∃ j : ℕ, j < 3 ∧ R = thetaRegion ((j + 1) ^ 2)}

def baseP : Assembly.Assembly V ℝ where
  thetaSet := thetaSetP
  qValue := qRegionN
  unitAction := p211PacketSystemN.ind2Act g0
  readout := p211PacketSystemN.procVol
  readout_invariant := fun v => (p211PacketSystemN.procVol_ind2 ⟨g0, rfl⟩).symm
  thetaSet_stable := by
    rintro v ⟨j, hj, rfl⟩
    exact ⟨j, hj, ind2Act_thetaRegion g0 _⟩
  bound := unitVolP
  thetaSet_bounded := by
    rintro v ⟨j, _, rfl⟩
    rw [procVol_thetaRegion]
    have hu := unitVolP_neg
    have hm : (1 : ℝ) ≤ (((j + 1) ^ 2 : ℕ) : ℝ) := by
      have : 1 ≤ (j + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos j)
      exact_mod_cast this
    nlinarith

def realCarrierPackage : Theta311ConstructionPackage V where
  base := baseP
  l := 7
  hl5 := by norm_num
  thetaVal := fun j => thetaRegion ((j.val + 1) ^ 2)
  thetaVal_mem := fun j => ⟨j.val, by have := j.isLt; omega, rfl⟩
  unitVol := unitVolP
  unitVol_neg := unitVolP_neg
  readout_spec := fun j => by
    show p211PacketSystemN.procVol (thetaRegion ((j.val + 1) ^ 2)) = _
    rw [procVol_thetaRegion]
    push_cast
    ring
  algorithm := fun R j vQ k =>
    (fun z : Fin (k.val + 1) → ℚ_[211] =>
      fun α => (pElt ^ (29 * ((j.val + 1) ^ 2 - 1))) * z α) '' R vQ k
  algorithm_spec := by
    funext j vQ k
    change (pElt ^ (29 * ((j.val + 1) ^ 2 - 1))) • qBallN (k.val + 1) 29
      = qBallN (k.val + 1) (29 * (j.val + 1) ^ 2)
    rw [smul_qBallN]
    congr 1
    have hm : 1 ≤ (j.val + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    generalize (j.val + 1) ^ 2 = m at hm ⊢
    omega
  qVol := unitVolP
  qVol_spec := by
    show p211PacketSystemN.procVol qRegionN = unitVolP
    rw [p211N_procVol]
    rfl
  Primes := Unit
  primes_nonempty := ⟨()⟩
  holAt := fun _ => Bool
  hol_plural := fun _ => ⟨true, false, by decide⟩
  LogLinks := ℕ
  logLinks_plural := ⟨0, 1, by decide⟩
  ThetaLinks := Bool
  thetaLinks_plural := ⟨true, false, by decide⟩
  Deformations := Bool
  deformations_plural := ⟨true, false, by decide⟩

theorem qValue_eq_label_one :
    realCarrierPackage.base.qValue = realCarrierPackage.thetaVal realCarrierPackage.jZero := by
  show qRegionN = thetaRegion ((0 + 1) ^ 2)
  simp [thetaRegion_one]

theorem qValue_mem_thetaSet :
    realCarrierPackage.base.qValue ∈ realCarrierPackage.base.thetaSet := by
  rw [qValue_eq_label_one]
  exact realCarrierPackage.thetaVal_mem _

theorem qVol_le_bound :
    realCarrierPackage.qVol ≤ realCarrierPackage.base.bound := le_refl _

theorem realCarrier_values_nonconstant :
    realCarrierPackage.base.readout (realCarrierPackage.thetaVal realCarrierPackage.jZero) ≠
      realCarrierPackage.base.readout (realCarrierPackage.thetaVal realCarrierPackage.jOne) :=
  realCarrierPackage.values_nonconstant

theorem g0_moves_a_point :
    ∃ x : p211PacketSystemN.Packet () 0,
      p211PacketSystemN.ismAct () 0 (g0 () 0) x ≠ x := by
  refine ⟨fun _ => 1, ?_⟩
  intro h
  have h0 := congrFun h 0
  change (((( -1 : ℤ_[211]ˣ) : ℤ_[211]) : ℚ_[211])) * 1 = 1 at h0
  norm_num at h0

def thetaPilotRegion : V := fun _ k => qBallN (k.val + 1) (29 * k.val ^ 2)

theorem procVol_thetaPilotRegion :
    p211PacketSystemN.procVol thetaPilotRegion = (14 / 3) * unitVolP := by
  have hstage : ∀ (vQ : p211PacketSystemN.PlaceQ) (k : Fin p211PacketSystemN.lstar),
      p211PacketSystemN.packetLogVolume vQ k.succ (thetaPilotRegion vQ k.succ)
        = (((k.val + 1) ^ 2 : ℕ) : ℝ) * (-(29 / 7) * Real.log 211) := by
    intro vQ k
    have e : thetaPilotRegion vQ k.succ = thetaRegion ((k.val + 1) ^ 2) vQ k.succ := by
      simp only [thetaPilotRegion, thetaRegion, Fin.val_succ]
    rw [e, packetLogVolume_thetaRegion]
    push_cast
    ring
  have hl : (p211PacketSystemN.lstar : ℝ) = 3 := by norm_num [p211PacketSystemN]
  rw [PacketSystem.procVol]
  simp only [hstage]
  rw [hl]
  show (∑ _x : Unit, (∑ k : Fin 3,
      (((k.val + 1) ^ 2 : ℕ) : ℝ) * (-(29 / 7) * Real.log 211)) / (3 : ℝ)) = _
  simp only [Fin.sum_univ_three, Finset.univ_unique, Finset.sum_singleton]
  unfold unitVolP
  norm_num
  ring

theorem thetaPilot_below_q :
    p211PacketSystemN.procVol thetaPilotRegion < p211PacketSystemN.procVol qRegionN := by
  rw [procVol_thetaPilotRegion, p211N_procVol]
  have hu := unitVolP_neg
  unfold unitVolP at hu ⊢
  linarith

theorem thetaPilot_gap :
    p211PacketSystemN.procVol qRegionN - p211PacketSystemN.procVol thetaPilotRegion
      = (11 / 3) * |unitVolP| := by
  rw [procVol_thetaPilotRegion, p211N_procVol, abs_of_neg unitVolP_neg]
  unfold unitVolP
  ring

end CitedLV.Theorem311.P211RealCarrierPackage

section Check
open CitedLV.Theorem311.P211RealCarrierPackage
end Check
