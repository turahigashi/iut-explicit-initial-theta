import Cor312LogVolume.independence.Cor312CitedPrimeStripLayer
import Cor312LogVolume.theorem311.P211Completion
import Cor312LogVolume.Src.EtTh.Section1PadicThetaValues

set_option autoImplicit false
noncomputable section

namespace CitedLV.Independence.Cor312SourceBound

open Metric CategoryTheory
open Src.IUT3.Theorem311
open Src.IUT3.Remark122
open Src.IUT4.Proposition14ii
open Src.EtTh.PadicThetaValues
open Src.IUT3.Remark395ix
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211LogShellPacketBridge
open CitedLV.Theorem311.P211ComponentCTraceBridge
open CitedLV.Theorem311.P211SourceFacingSimultaneousXiF
open CitedLV.Theorem311.P211TensorPacketCollapse
open CitedLV.Theorem311.PadicTensorPacketTopology
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Independence.Cor312Cited

def qPilotScalar : ℚ_[211] := pElt ^ 29

def tateParameter : ℚ_[211] := qPilotScalar ^ 14

theorem norm_qPilotScalar : ‖qPilotScalar‖ = ((211 : ℝ)⁻¹) ^ 29 := by
  rw [qPilotScalar, norm_pow, norm_p211]

theorem tateParameter_ne_zero : tateParameter ≠ 0 :=
  pow_ne_zero _ (pow_ne_zero _ pElt_ne_zero)

def tateUnit : ℂ_[211]ˣ :=
  Units.mk0 ((tateParameter : ℚ_[211]) : ℂ_[211]) (by
    intro h
    have h' := congrArg (fun z : ℂ_[211] => ‖z‖) h
    simp only [PadicComplex.norm_extends', norm_zero] at h'
    exact tateParameter_ne_zero (norm_eq_zero.mp h'))

theorem norm_tateUnit : ‖((tateUnit : ℂ_[211]ˣ) : ℂ_[211])‖ = (((211 : ℝ)⁻¹) ^ 29) ^ 14 := by
  show ‖((tateParameter : ℚ_[211]) : ℂ_[211])‖ = _
  rw [PadicComplex.norm_extends', tateParameter, norm_pow, norm_qPilotScalar]

theorem tateUnit_small : ‖((tateUnit : ℂ_[211]ˣ) : ℂ_[211])‖ < 1 := by
  rw [norm_tateUnit]
  have h0 : (0 : ℝ) ≤ ((211 : ℝ)⁻¹) ^ 29 := by positivity
  have h1 : ((211 : ℝ)⁻¹) ^ 29 < 1 := pow_lt_one₀ (by positivity) (by norm_num) (by norm_num)
  exact pow_lt_one₀ h0 h1 (by norm_num)

theorem theta_root_norm (j : ℕ) (t : ℂ_[211]ˣ) (ht : t ∈ rootValues 211 tateUnit 7 j) :
    ‖((t : ℂ_[211]ˣ) : ℂ_[211])‖ = ((211 : ℝ)⁻¹) ^ (29 * (j * j)) := by
  have hpow := (mem_rootValues_iff_power 211 tateUnit tateUnit_small 7 j t).mp ht
  have hn := congrArg (fun z : ℂ_[211]ˣ => ‖((z : ℂ_[211]ˣ) : ℂ_[211])‖) hpow
  simp only [Units.val_pow_eq_pow_val, norm_pow] at hn
  rw [norm_tateUnit] at hn
  have hrhs : ((((211 : ℝ)⁻¹) ^ 29) ^ 14) ^ (j * j) = (((211 : ℝ)⁻¹) ^ (29 * (j * j))) ^ (2 * 7) := by
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hrhs] at hn
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hn

def thetaValueRegion (j : ℕ) : Set ℚ_[211] :=
  {x | ∃ t ∈ rootValues 211 tateUnit 7 j, ‖x‖ ≤ ‖((t : ℂ_[211]ˣ) : ℂ_[211])‖}

theorem thetaValueRegion_eq (j : ℕ) : thetaValueRegion j = qBall (29 * (j * j)) := by
  rw [qBall_eq]
  ext x
  simp only [thetaValueRegion, Set.mem_setOf_eq, mem_closedBall_zero_iff]
  constructor
  · rintro ⟨t, ht, hx⟩
    rw [theta_root_norm j t ht] at hx
    exact hx
  · intro hx
    obtain ⟨t, ht⟩ := rootValues_nonempty 211 tateUnit tateUnit_small 7 j (by norm_num)
    exact ⟨t, ht, by rw [theta_root_norm j t ht]; exact hx⟩

def sourceThetaPilot : p211PacketSystem.Regions := fun _ j => thetaValueRegion j.val

def sourceQPilot : p211PacketSystem.Regions := realizedRegion p211Input

theorem sourceThetaPilot_eq (vQ : p211PacketSystem.PlaceQ) (j : Fin (p211PacketSystem.lstar + 1)) :
    sourceThetaPilot vQ j = qBall (29 * (j.val * j.val)) :=
  thetaValueRegion_eq j.val

theorem sourceQPilot_eq : sourceQPilot = p211QRegion := realizedRegion_p211

theorem qBall_subset_integral (n : ℕ) : qBall n ⊆ closedBall (0 : ℚ_[211]) 1 := by
  rw [qBall_eq]
  exact closedBall_subset_closedBall (pow_le_one₀ (by positivity) (by norm_num))

theorem qBall_eq_lambda_logShell (n : ℕ) :
    qBall n = (fun z : ℚ_[211] => (pElt ^ n) * z) '' logShell (K := ℚ_[211]) 211 := by
  rw [logShell_Qp_eq]
  rfl

theorem packetLogVolume_qBall (vQ : p211PacketSystem.PlaceQ) (j : Fin (p211PacketSystem.lstar + 1)) (n : ℕ) :
    p211PacketSystem.packetLogVolume vQ j (qBall n) = (1 / 7) * (-(n : ℝ) * Real.log 211) := by
  show (1 / 7 : ℝ) * logVolume (haarQp 211) (closedBall (0 : ℚ_[211]) 1) (qBall n) + 0 = _
  rw [logVolume_qBall]
  ring

theorem procVol_sourceThetaPilot :
    p211PacketSystem.procVol sourceThetaPilot = (14 / 3) * (-(29 / 7) * Real.log 211) := by
  have hstage : ∀ (vQ : p211PacketSystem.PlaceQ) (k : Fin p211PacketSystem.lstar),
      p211PacketSystem.packetLogVolume vQ k.succ (sourceThetaPilot vQ k.succ)
        = (((k.val + 1) * (k.val + 1) : ℕ) : ℝ) * (-(29 / 7) * Real.log 211) := by
    intro vQ k
    rw [sourceThetaPilot_eq, packetLogVolume_qBall, Fin.val_succ]
    push_cast
    ring
  have hl : (p211PacketSystem.lstar : ℝ) = 3 := by norm_num [p211PacketSystem]
  rw [PacketSystem.procVol]
  simp only [hstage]
  rw [hl]
  show (∑ _x : Unit, (∑ k : Fin 3,
      (((k.val + 1) * (k.val + 1) : ℕ) : ℝ) * (-(29 / 7) * Real.log 211)) / (3 : ℝ)) = _
  simp only [Fin.sum_univ_three, Finset.univ_unique, Finset.sum_singleton]
  norm_num
  ring

theorem procVol_sourceQPilot :
    p211PacketSystem.procVol sourceQPilot = -(29 / 7) * Real.log 211 := by
  rw [sourceQPilot_eq]
  exact p211_procVol

theorem act_id (h : p211PacketSystem.ProcessionAut) (x : p211PacketSystem.Regions) : h.act x = x := by
  funext vQ j
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem ind2Act_id (g : p211PacketSystem.Ind2Element) (x : p211PacketSystem.Regions) :
    p211PacketSystem.ind2Act g x = x := by
  funext vQ j
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem qBall_hasVolume (n : ℕ) : haarQp 211 (qBall n) ≠ 0 :=
  (measure_pos_ne_top (haarQp 211) (qBall_isCompact n) (qBall_interior n)).1

def sourceBoundTheory : CitedTheory where
  S := p211PacketSystem
  thetaPilot := sourceThetaPilot
  qPilot := sourceQPilot
  container := sourceThetaPilot
  Possible := {sourceThetaPilot}
  IsLambdaO := fun _ _ A => ∃ c : ℚ_[211], c ≠ 0 ∧
    A = (fun z : ℚ_[211] => c * z) '' logShell (K := ℚ_[211]) 211
  hull := sourceThetaPilot
  theta_possible := rfl
  ind1_closed := by
    rintro x rfl y ⟨h, rfl⟩
    exact act_id h _
  ind2_closed := by
    rintro x rfl y ⟨g, rfl⟩
    exact ind2Act_id g _
  ind3_bound := by
    rintro x rfl
    exact fun _ _ => subset_rfl
  ind3_saturated := by
    rintro x rfl y hxy hyc
    exact funext fun vQ => funext fun j => Set.Subset.antisymm (hyc vQ j) (hxy vQ j)
  container_le_integral := fun vQ j => by
    rw [sourceThetaPilot_eq]
    exact qBall_subset_integral _
  hull_isLambdaO := fun vQ j =>
    ⟨pElt ^ (29 * (j.val * j.val)), pow_ne_zero _ pElt_ne_zero, by
      rw [sourceThetaPilot_eq, qBall_eq_lambda_logShell]⟩
  hull_contains := by
    rintro x rfl
    exact fun _ _ => subset_rfl
  hull_minimal := fun _ _ hT => hT _ rfl
  hull_le_integral := fun vQ j => by
    rw [sourceThetaPilot_eq]
    exact qBall_subset_integral _
  q_hasVolume := by
    intro vQ j
    rw [sourceQPilot_eq]
    exact qBall_hasVolume 29
  q_le_integral := by
    intro vQ j
    rw [sourceQPilot_eq]
    exact qBall_subset_integral 29
  q_neg := by
    rw [procVol_sourceQPilot]
    have h : 0 < Real.log 211 := Real.log_pos (by norm_num)
    linarith
  linkScale := 3 / 14
  linkScale_pos := by norm_num
  link_degree := by
    rw [procVol_sourceQPilot, procVol_sourceThetaPilot]
    ring
  ipl := by
    rintro x rfl
    refine ⟨3 / 14, by norm_num, ?_⟩
    rw [procVol_sourceQPilot, procVol_sourceThetaPilot]
    ring

theorem sourceBound_weakSHE : sourceBoundTheory.WeakSHE :=
  ⟨fun c => {c}, rfl, by
    rintro c x rfl
    exact fun _ _ => subset_rfl⟩

theorem sourceBound_not_conclusion : ¬ sourceBoundTheory.Conclusion := by
  intro h
  have h' : p211PacketSystem.procVol sourceQPilot ≤ p211PacketSystem.procVol sourceThetaPilot := h
  rw [procVol_sourceQPilot, procVol_sourceThetaPilot] at h'
  have hl : 0 < Real.log 211 := Real.log_pos (by norm_num)
  nlinarith

theorem unit_mul_qBall (u : ℚ_[211]) (hu : ‖u‖ = 1) (n : ℕ) :
    (fun z : ℚ_[211] => u * z) '' qBall n = qBall n := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  rw [qBall_eq, image_mul_closedBall u hu0 (by positivity), hu, one_mul]

theorem sourceBound_provenance :
    sourceBoundTheory.S = p211PacketSystem ∧
      (∀ j : Fin (p211PacketSystem.lstar + 1),
        Nonempty (TensorPacket (j.val + 1) ≃ₗ[ℚ_[211]] p211PacketSystem.Packet () j)) ∧
      (∀ vQ j, p211PacketSystem.integral vQ j = logShell (K := ℚ_[211]) 211) ∧
      sourceBoundTheory.qPilot = realizedRegion p211Input ∧
      sourceBoundTheory.thetaPilot = sourceThetaPilot ∧
      (∀ vQ (j : Fin (p211PacketSystem.lstar + 1)), sourceThetaPilot vQ j = thetaValueRegion j.val) ∧
      (∀ j : ℕ, thetaValueRegion j =
        {x : ℚ_[211] | ∃ t ∈ rootValues 211 tateUnit 7 j, ‖x‖ ≤ ‖((t : ℂ_[211]ˣ) : ℂ_[211])‖}) ∧
      tateParameter = qPilotScalar ^ 14 ∧
      (∀ (j : ℕ) (t : ℂ_[211]ˣ), t ∈ rootValues 211 tateUnit 7 j →
        ‖((t : ℂ_[211]ˣ) : ℂ_[211])‖ = ‖qPilotScalar‖ ^ (j * j)) :=
  ⟨rfl, fun j => stage_tensor_carrier_equivalent j, integral_eq_actual_logShell, rfl, rfl,
    fun _ _ => rfl, fun _ => rfl, rfl,
    fun j t ht => by rw [theta_root_norm j t ht, norm_qPilotScalar, ← pow_mul]⟩

theorem sourceBound_layer :
    sourceBoundTheory.WeakSHE ∧
      sourceBoundTheory.primeStripLayer.possible = sourceBoundTheory.Possible ∧
      (∀ x ∈ sourceBoundTheory.primeStripLayer.possible, sourceBoundTheory.primeStripLayer.Linked x) ∧
      sourceBoundTheory.layerLoop.ClosedUpToFormalQuotient completedBeforeSQ5 ∧
      sourceBoundTheory.layerLoop.loopArrow (𝟙 _) (𝟙 _) = 𝟙 _ ∧
      ¬ sourceBoundTheory.primeStripLayer.ScalarProduction sourceBoundTheory.S.procVol
          sourceBoundTheory.negLogQ ∧
      ¬ sourceBoundTheory.Conclusion := by
  have heq : sourceBoundTheory.primeStripLayer.possible = sourceBoundTheory.Possible :=
    sourceBoundTheory.layer_possible_eq (by
      rintro y rfl
      exact fun _ _ => subset_rfl)
  refine ⟨sourceBound_weakSHE, heq, sourceBoundTheory.layer_ipl, sourceBoundTheory.layer_closed_before_sq5,
    sourceBoundTheory.layer_holonomy_trivial, ?_, sourceBound_not_conclusion⟩
  rintro ⟨x, hx, he⟩
  have hx' : x = sourceThetaPilot := sourceBoundTheory.layer_possible_subset hx
  subst hx'
  have h1 : p211PacketSystem.procVol sourceThetaPilot = p211PacketSystem.procVol sourceQPilot := he
  rw [procVol_sourceQPilot, procVol_sourceThetaPilot] at h1
  have hl : 0 < Real.log 211 := Real.log_pos (by norm_num)
  nlinarith

end CitedLV.Independence.Cor312SourceBound

section Check
open CitedLV.Independence.Cor312SourceBound
end Check
