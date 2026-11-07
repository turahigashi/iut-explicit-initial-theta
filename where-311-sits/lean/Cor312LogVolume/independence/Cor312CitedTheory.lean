import Cor312LogVolume.theorem311.P211RealCarrierTheta311Package
import Cor312LogVolume.theorem311.P211IndeterminacyOrbit
import Cor312LogVolume.theorem311.PacketUnionHullEndpoint
import Cor312LogVolume.Src.IUT3.Section3Corollary312StepXInd3

set_option autoImplicit false
noncomputable section

namespace CitedLV.Independence.Cor312Cited

open Metric
open Src.IUT3.Theorem311
open CitedLV.Theorem311
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211PacketN
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Theorem311.P211RealCarrierPackage
open CitedLV.Theorem311.P211IndeterminacyOrbit

structure CitedTheory : Type 1 where

  S : PacketSystem

  thetaPilot : S.Regions

  qPilot : S.Regions

  container : S.Regions

  Possible : Set S.Regions

  IsLambdaO : ∀ vQ (j : Fin (S.lstar + 1)), Set (S.Packet vQ j) → Prop

  hull : S.Regions

  theta_possible : thetaPilot ∈ Possible

  ind1_closed : ∀ x ∈ Possible, ∀ y, S.Ind1 x y → y ∈ Possible

  ind2_closed : ∀ x ∈ Possible, ∀ y, S.Ind2 x y → y ∈ Possible

  ind3_bound : ∀ x ∈ Possible, RegionLE S x container

  ind3_saturated : ∀ x ∈ Possible, ∀ y, RegionLE S x y → RegionLE S y container → y ∈ Possible

  container_le_integral : RegionLE S container S.integralRegions

  hull_isLambdaO : ∀ vQ j, IsLambdaO vQ j (hull vQ j)

  hull_contains : ∀ x ∈ Possible, RegionLE S x hull

  hull_minimal : ∀ T : S.Regions, (∀ vQ j, IsLambdaO vQ j (T vQ j)) →
    (∀ x ∈ Possible, RegionLE S x T) → RegionLE S hull T

  hull_le_integral : RegionLE S hull S.integralRegions

  q_hasVolume : S.HasVolume qPilot
  q_le_integral : RegionLE S qPilot S.integralRegions

  q_neg : S.procVol qPilot < 0

  linkScale : ℝ
  linkScale_pos : 0 < linkScale

  link_degree : S.procVol qPilot = linkScale * S.procVol thetaPilot

  ipl : ∀ x ∈ Possible, ∃ c : ℝ, 0 < c ∧ S.procVol qPilot = c * S.procVol x

namespace CitedTheory

variable (T : CitedTheory)

def negLogTheta : ℝ := T.S.procVol T.hull

def negLogQ : ℝ := T.S.procVol T.qPilot

def Conclusion : Prop := T.negLogQ ≤ T.negLogTheta

def WeakSHE : Prop :=
  ∃ alg : T.S.Regions → Set T.S.Regions,
    T.Possible = alg T.container ∧ ∀ c x, x ∈ alg c → RegionLE T.S x c

def StrongSHECarrier : Prop := T.qPilot ∈ T.Possible

def StrongSHEValue : Prop := T.negLogQ ∈ Set.Iic T.negLogTheta

theorem strongValue_iff_conclusion : T.StrongSHEValue ↔ T.Conclusion := Set.mem_Iic

theorem strongCarrier_implies_strongValue (h : T.StrongSHECarrier) : T.StrongSHEValue := by
  have hle := T.hull_contains _ h
  exact Set.mem_Iic.mpr
    (T.S.procVol_ind3 (fun vQ j => ⟨hle vQ j, T.hull_le_integral vQ j⟩) T.q_hasVolume)

theorem strongCarrier_implies_conclusion (h : T.StrongSHECarrier) : T.Conclusion :=
  (T.strongValue_iff_conclusion).mp (T.strongCarrier_implies_strongValue h)

end CitedTheory

theorem qBallN_subset_unit (n k : ℕ) : qBallN n k ⊆ closedBall (0 : Fin n → ℚ_[211]) 1 := by
  rw [← qBallN_zero_eq_ball]
  intro z hz
  simp only [qBallN, Set.mem_pi, Set.mem_univ, forall_true_left] at hz ⊢
  intro α
  have h := hz α
  rw [qBall_eq, mem_closedBall_zero_iff] at h ⊢
  calc ‖z α‖ ≤ ((211 : ℝ)⁻¹) ^ k := h
    _ ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
    _ = ((211 : ℝ)⁻¹) ^ 0 := by simp

theorem ind1Act_thetaPilotRegion (h : p211PacketSystemN.ProcessionAut) :
    h.act thetaPilotRegion = thetaPilotRegion := by
  funext vQ j
  show (h.packetAut vQ j) '' qBallN (j.val + 1) (29 * j.val ^ 2) = qBallN (j.val + 1) (29 * j.val ^ 2)
  have hpa : (h.packetAut vQ j : (Fin (j.val + 1) → ℚ_[211]) → _)
      = permAutQp (j.val + 1) (h.labelPerm j) := rfl
  rw [hpa]
  exact permAutQp_image_qBallN _ _ _

theorem ind2Act_thetaPilotRegion (g : p211PacketSystemN.Ind2Element) :
    p211PacketSystemN.ind2Act g thetaPilotRegion = thetaPilotRegion := by
  funext vQ j
  exact unitAutQp_image_qBallN (j.val + 1) (29 * j.val ^ 2) (g vQ j)

theorem qRegionN_hasVolume : p211PacketSystemN.HasVolume qRegionN := by
  intro vQ j
  show muPi (j.val + 1) (qBallN (j.val + 1) 29) ≠ 0
  rw [qBallN_measure]
  exact pow_ne_zero _ (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp)))

def modelTheory : CitedTheory where
  S := p211PacketSystemN
  thetaPilot := thetaPilotRegion
  qPilot := qRegionN
  container := thetaPilotRegion
  Possible := {thetaPilotRegion}
  IsLambdaO := fun _ j A => ∃ k : ℕ, A = qBallN (j.val + 1) k
  hull := thetaPilotRegion
  theta_possible := rfl
  ind1_closed := by
    rintro x rfl y ⟨h, rfl⟩
    exact ind1Act_thetaPilotRegion h
  ind2_closed := by
    rintro x rfl y ⟨g, rfl⟩
    exact ind2Act_thetaPilotRegion g
  ind3_bound := by
    rintro x rfl
    exact fun _ _ => subset_rfl
  ind3_saturated := by
    rintro x rfl y hxy hyc
    exact funext fun vQ => funext fun j => Set.Subset.antisymm (hyc vQ j) (hxy vQ j)
  container_le_integral := fun _ j => qBallN_subset_unit (j.val + 1) (29 * j.val ^ 2)
  hull_isLambdaO := fun _ j => ⟨29 * j.val ^ 2, rfl⟩
  hull_contains := by
    rintro x rfl
    exact fun _ _ => subset_rfl
  hull_minimal := fun _ _ hT => hT _ rfl
  hull_le_integral := fun _ j => qBallN_subset_unit (j.val + 1) (29 * j.val ^ 2)
  q_hasVolume := qRegionN_hasVolume
  q_le_integral := fun _ j => qBallN_subset_unit (j.val + 1) 29
  q_neg := by
    rw [p211N_procVol]
    have h := unitVolP_neg
    unfold unitVolP at h
    linarith
  linkScale := 3 / 14
  linkScale_pos := by norm_num
  link_degree := by
    rw [p211N_procVol, procVol_thetaPilotRegion]
    unfold unitVolP
    ring
  ipl := by
    rintro x rfl
    refine ⟨3 / 14, by norm_num, ?_⟩
    rw [p211N_procVol, procVol_thetaPilotRegion]
    unfold unitVolP
    ring

theorem model_weakSHE : modelTheory.WeakSHE :=
  ⟨fun c => {c}, rfl, by
    rintro c x rfl
    exact fun _ _ => subset_rfl⟩

theorem model_not_conclusion : ¬ modelTheory.Conclusion := by
  intro h
  have h' : p211PacketSystemN.procVol qRegionN ≤ p211PacketSystemN.procVol thetaPilotRegion := h
  have := thetaPilot_below_q
  linarith

theorem model_q_not_possible : ¬ modelTheory.StrongSHECarrier := fun h =>
  model_not_conclusion (modelTheory.strongCarrier_implies_conclusion h)

theorem model_linkScale : modelTheory.linkScale = 3 / 14 := rfl

theorem weakSHE_does_not_yield_conclusion :
    ¬ ∀ T : CitedTheory, T.WeakSHE → T.Conclusion := fun h =>
  model_not_conclusion (h modelTheory model_weakSHE)

theorem strongCarrier_not_derivable :
    ¬ ∀ T : CitedTheory, T.WeakSHE → T.StrongSHECarrier := fun h =>
  model_q_not_possible (h modelTheory model_weakSHE)

theorem strongValue_not_derivable :
    ¬ ∀ T : CitedTheory, T.WeakSHE → T.StrongSHEValue := fun h =>
  model_not_conclusion ((modelTheory.strongValue_iff_conclusion).mp (h modelTheory model_weakSHE))

end CitedLV.Independence.Cor312Cited

section Check
open CitedLV.Independence.Cor312Cited
end Check
