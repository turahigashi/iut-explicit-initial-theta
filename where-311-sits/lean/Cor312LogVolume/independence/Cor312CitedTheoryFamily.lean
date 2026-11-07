import Cor312LogVolume.independence.Cor312CitedTheory
import Cor312LogVolume.theorem311.PrimePacketSystem

set_option autoImplicit false
noncomputable section

namespace CitedLV.Independence.Cor312CitedFamily

open Metric MeasureTheory
open Src.IUT3.Theorem311
open CitedLV.Theorem311
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211PacketN
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Theorem311.P211RealCarrierPackage
open CitedLV.Theorem311.P211IndeterminacyOrbit
open CitedLV.Independence.Cor312Cited

structure CitedTheoryFam : Type 1 where
  ι : Type
  [ιFintype : Fintype ι]
  S : ι → PacketSystem

  lstar_common : ∀ i k, (S i).lstar = (S k).lstar
  thetaPilot : ∀ i, (S i).Regions
  qPilot : ∀ i, (S i).Regions
  container : ∀ i, (S i).Regions
  Possible : Set (∀ i, (S i).Regions)
  IsLambdaO : ∀ i vQ (j : Fin ((S i).lstar + 1)), Set ((S i).Packet vQ j) → Prop
  hull : ∀ i, (S i).Regions
  theta_possible : thetaPilot ∈ Possible
  ind1_closed : ∀ x ∈ Possible, ∀ y : (∀ i, (S i).Regions),
    (∀ i, (S i).Ind1 (x i) (y i)) → y ∈ Possible
  ind2_closed : ∀ x ∈ Possible, ∀ y : (∀ i, (S i).Regions),
    (∀ i, (S i).Ind2 (x i) (y i)) → y ∈ Possible
  ind3_bound : ∀ x ∈ Possible, ∀ i, RegionLE (S i) (x i) (container i)
  ind3_saturated : ∀ x ∈ Possible, ∀ y : (∀ i, (S i).Regions),
    (∀ i, RegionLE (S i) (x i) (y i)) → (∀ i, RegionLE (S i) (y i) (container i)) → y ∈ Possible
  container_le_integral : ∀ i, RegionLE (S i) (container i) (S i).integralRegions
  hull_isLambdaO : ∀ i vQ j, IsLambdaO i vQ j (hull i vQ j)
  hull_contains : ∀ x ∈ Possible, ∀ i, RegionLE (S i) (x i) (hull i)
  hull_minimal : ∀ T : (∀ i, (S i).Regions), (∀ i vQ j, IsLambdaO i vQ j (T i vQ j)) →
    (∀ x ∈ Possible, ∀ i, RegionLE (S i) (x i) (T i)) → ∀ i, RegionLE (S i) (hull i) (T i)
  hull_le_integral : ∀ i, RegionLE (S i) (hull i) (S i).integralRegions
  q_hasVolume : ∀ i, (S i).HasVolume (qPilot i)
  q_le_integral : ∀ i, RegionLE (S i) (qPilot i) (S i).integralRegions
  q_neg : ∑ i, (S i).procVol (qPilot i) < 0
  linkScale : ℝ
  linkScale_pos : 0 < linkScale
  link_degree : ∑ i, (S i).procVol (qPilot i) = linkScale * ∑ i, (S i).procVol (thetaPilot i)
  ipl : ∀ x ∈ Possible, ∃ c : ℝ, 0 < c ∧
    ∑ i, (S i).procVol (qPilot i) = c * ∑ i, (S i).procVol (x i)

attribute [instance] CitedTheoryFam.ιFintype

namespace CitedTheoryFam

variable (T : CitedTheoryFam)

def negLogTheta : ℝ := ∑ i, (T.S i).procVol (T.hull i)
def negLogQ : ℝ := ∑ i, (T.S i).procVol (T.qPilot i)
def Conclusion : Prop := T.negLogQ ≤ T.negLogTheta

def WeakSHE : Prop :=
  ∃ alg : (∀ i, (T.S i).Regions) → Set (∀ i, (T.S i).Regions),
    T.Possible = alg T.container ∧ ∀ c x, x ∈ alg c → ∀ i, RegionLE (T.S i) (x i) (c i)

def StrongSHECarrier : Prop := T.qPilot ∈ T.Possible
def StrongSHEValue : Prop := T.negLogQ ∈ Set.Iic T.negLogTheta

theorem strongValue_iff_conclusion : T.StrongSHEValue ↔ T.Conclusion := Set.mem_Iic

theorem strongCarrier_implies_strongValue (h : T.StrongSHECarrier) : T.StrongSHEValue := by
  refine Set.mem_Iic.mpr (Finset.sum_le_sum fun i _ => ?_)
  have hle := T.hull_contains _ h i
  exact (T.S i).procVol_ind3 (fun vQ j => ⟨hle vQ j, T.hull_le_integral i vQ j⟩) (T.q_hasVolume i)

theorem strongCarrier_implies_conclusion (h : T.StrongSHECarrier) : T.Conclusion :=
  (T.strongValue_iff_conclusion).mp (T.strongCarrier_implies_strongValue h)

end CitedTheoryFam

theorem act_integralRegions (S : PacketSystem) (h : S.ProcessionAut) :
    h.act S.integralRegions = S.integralRegions := by
  funext vQ j
  show h.packetAut vQ j '' S.integral vQ j = S.integral vQ j
  conv_lhs => rw [← h.packetAut_integral vQ j]
  exact Set.image_preimage_eq _ (h.packetAut vQ j).surjective

theorem ind2Act_integralRegions (S : PacketSystem) (g : S.Ind2Element) :
    S.ind2Act g S.integralRegions = S.integralRegions := by
  funext vQ j
  show S.ismAct vQ j (g vQ j) '' S.integral vQ j = S.integral vQ j
  conv_lhs => rw [← S.ismAct_integral vQ j (g vQ j)]
  exact Set.image_preimage_eq _ (S.ismAct vQ j (g vQ j)).surjective

def ballRegion (f : ℕ → ℕ) : p211PacketSystemN.Regions := fun _ k => qBallN (k.val + 1) (f k.val)

theorem ind1Act_ballRegion (f : ℕ → ℕ) (h : p211PacketSystemN.ProcessionAut) :
    h.act (ballRegion f) = ballRegion f := by
  funext vQ j
  show (h.packetAut vQ j) '' qBallN (j.val + 1) (f j.val) = qBallN (j.val + 1) (f j.val)
  have hpa : (h.packetAut vQ j : (Fin (j.val + 1) → ℚ_[211]) → _)
      = permAutQp (j.val + 1) (h.labelPerm j) := rfl
  rw [hpa]
  exact permAutQp_image_qBallN _ _ _

theorem ind2Act_ballRegion (f : ℕ → ℕ) (g : p211PacketSystemN.Ind2Element) :
    p211PacketSystemN.ind2Act g (ballRegion f) = ballRegion f := by
  funext vQ j
  exact unitAutQp_image_qBallN (j.val + 1) (f j.val) (g vQ j)

theorem ballRegion_hasVolume (f : ℕ → ℕ) : p211PacketSystemN.HasVolume (ballRegion f) := by
  intro vQ j
  show muPi (j.val + 1) (qBallN (j.val + 1) (f j.val)) ≠ 0
  rw [qBallN_measure]
  exact pow_ne_zero _ (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp)))

theorem ballRegion_le_integral (f : ℕ → ℕ) :
    RegionLE p211PacketSystemN (ballRegion f) p211PacketSystemN.integralRegions :=
  fun _ j => qBallN_subset_unit (j.val + 1) (f j.val)

abbrev thetaN (N : ℕ) : p211PacketSystemN.Regions := ballRegion fun k => 29 * (N * k ^ 2)

abbrev qN (N : ℕ) : p211PacketSystemN.Regions := ballRegion fun _ => 29 * N

theorem procVol_thetaN (N : ℕ) :
    p211PacketSystemN.procVol (thetaN N) = (N : ℝ) * (14 / 3) * unitVolP := by
  have hstage : ∀ (vQ : p211PacketSystemN.PlaceQ) (k : Fin p211PacketSystemN.lstar),
      p211PacketSystemN.packetLogVolume vQ k.succ (thetaN N vQ k.succ)
        = ((N * (k.val + 1) ^ 2 : ℕ) : ℝ) * (-(29 / 7) * Real.log 211) := by
    intro vQ k
    have e : thetaN N vQ k.succ = thetaRegion (N * (k.val + 1) ^ 2) vQ k.succ := by
      simp only [thetaN, ballRegion, thetaRegion, Fin.val_succ]
    rw [e, packetLogVolume_thetaRegion]
    push_cast
    ring
  have hl : (p211PacketSystemN.lstar : ℝ) = 3 := by norm_num [p211PacketSystemN]
  rw [PacketSystem.procVol]
  simp only [hstage]
  rw [hl]
  show (∑ _x : Unit, (∑ k : Fin 3,
      ((N * (k.val + 1) ^ 2 : ℕ) : ℝ) * (-(29 / 7) * Real.log 211)) / (3 : ℝ)) = _
  simp only [Fin.sum_univ_three, Finset.univ_unique, Finset.sum_singleton]
  unfold unitVolP
  norm_num
  ring

theorem procVol_qN (N : ℕ) : p211PacketSystemN.procVol (qN N) = (N : ℝ) * unitVolP :=
  procVol_thetaRegion N

structure ExtraPlace : Type 1 where
  S : PacketSystem
  lstar_eq : S.lstar = 3
  q : S.Regions
  q_hasVolume : S.HasVolume q
  q_le_integral : RegionLE S q S.integralRegions

variable {κ : Type} [Fintype κ] (E : κ → ExtraPlace)

def famS : Option κ → PacketSystem
  | none => p211PacketSystemN
  | some k => (E k).S

omit [Fintype κ] in
theorem famS_lstar : ∀ i, (famS E i).lstar = 3
  | none => rfl
  | some k => (E k).lstar_eq

def famTheta (N : ℕ) : ∀ i, (famS E i).Regions
  | none => thetaN N
  | some k => (E k).S.integralRegions

def famQ (N : ℕ) : ∀ i, (famS E i).Regions
  | none => qN N
  | some k => (E k).q

def famLam : ∀ i, ∀ vQ (j : Fin ((famS E i).lstar + 1)), Set ((famS E i).Packet vQ j) → Prop
  | none => fun _ j A => ∃ k : ℕ, A = qBallN (j.val + 1) k
  | some k => fun vQ j A => A = (E k).S.integral vQ j

def extraTheta : ℝ := ∑ k, (E k).S.procVol (E k).S.integralRegions

def extraQ : ℝ := ∑ k, (E k).S.procVol (E k).q

theorem extraQ_le_extraTheta : extraQ E ≤ extraTheta E :=
  Finset.sum_le_sum fun k _ =>
    (E k).S.procVol_le_integral (fun vQ j => (E k).q_le_integral vQ j) (E k).q_hasVolume

theorem tot_famTheta (N : ℕ) :
    ∑ i, (famS E i).procVol (famTheta E N i) = (N : ℝ) * (14 / 3) * unitVolP + extraTheta E := by
  rw [Fintype.sum_option]
  exact congrArg₂ (· + ·) (procVol_thetaN N) rfl

theorem tot_famQ (N : ℕ) :
    ∑ i, (famS E i).procVol (famQ E N i) = (N : ℝ) * unitVolP + extraQ E := by
  rw [Fintype.sum_option]
  exact congrArg₂ (· + ·) (procVol_qN N) rfl

set_option maxHeartbeats 1000000 in

def famModel (N : ℕ) (hq : (N : ℝ) * unitVolP + extraQ E < 0)
    (hθ : (N : ℝ) * (14 / 3) * unitVolP + extraTheta E < 0) : CitedTheoryFam where
  ι := Option κ
  S := famS E
  lstar_common := fun i k => (famS_lstar E i).trans (famS_lstar E k).symm
  thetaPilot := famTheta E N
  qPilot := famQ E N
  container := famTheta E N
  Possible := {famTheta E N}
  IsLambdaO := famLam E
  hull := famTheta E N
  theta_possible := rfl
  ind1_closed := by
    rintro x rfl y hy
    refine Set.mem_singleton_iff.mpr (funext fun i => ?_)
    cases i with
    | none =>
      obtain ⟨h, hh⟩ := hy none
      exact hh.trans (ind1Act_ballRegion (fun k => 29 * (N * k ^ 2)) h)
    | some k =>
      obtain ⟨h, hh⟩ := hy (some k)
      exact hh.trans (act_integralRegions (E k).S h)
  ind2_closed := by
    rintro x rfl y hy
    refine Set.mem_singleton_iff.mpr (funext fun i => ?_)
    cases i with
    | none =>
      obtain ⟨g, hg⟩ := hy none
      exact hg.trans (ind2Act_ballRegion (fun k => 29 * (N * k ^ 2)) g)
    | some k =>
      obtain ⟨g, hg⟩ := hy (some k)
      exact hg.trans (ind2Act_integralRegions (E k).S g)
  ind3_bound := by
    rintro x rfl i
    exact fun _ _ => subset_rfl
  ind3_saturated := by
    rintro x rfl y hxy hyc
    exact Set.mem_singleton_iff.mpr (funext fun i => funext fun vQ => funext fun j =>
      Set.Subset.antisymm (hyc i vQ j) (hxy i vQ j))
  container_le_integral := by
    intro i
    cases i with
    | none =>
      show RegionLE p211PacketSystemN (thetaN N) p211PacketSystemN.integralRegions
      exact ballRegion_le_integral _
    | some k =>
      show RegionLE (E k).S (E k).S.integralRegions (E k).S.integralRegions
      exact fun _ _ => subset_rfl
  hull_isLambdaO := by
    intro i
    cases i with
    | none =>
      show ∀ (vQ : p211PacketSystemN.PlaceQ) (j : Fin (p211PacketSystemN.lstar + 1)),
        ∃ m : ℕ, thetaN N vQ j = qBallN (j.val + 1) m
      exact fun _ j => ⟨29 * (N * j.val ^ 2), rfl⟩
    | some k =>
      show ∀ (vQ : (E k).S.PlaceQ) (j : Fin ((E k).S.lstar + 1)),
        (E k).S.integralRegions vQ j = (E k).S.integral vQ j
      exact fun _ _ => rfl
  hull_contains := by
    rintro x rfl i
    exact fun _ _ => subset_rfl
  hull_minimal := fun _ _ hT => hT _ rfl
  hull_le_integral := by
    intro i
    cases i with
    | none =>
      show RegionLE p211PacketSystemN (thetaN N) p211PacketSystemN.integralRegions
      exact ballRegion_le_integral _
    | some k =>
      show RegionLE (E k).S (E k).S.integralRegions (E k).S.integralRegions
      exact fun _ _ => subset_rfl
  q_hasVolume := by
    intro i
    cases i with
    | none =>
      show p211PacketSystemN.HasVolume (qN N)
      exact ballRegion_hasVolume _
    | some k =>
      show (E k).S.HasVolume (E k).q
      exact (E k).q_hasVolume
  q_le_integral := by
    intro i
    cases i with
    | none =>
      show RegionLE p211PacketSystemN (qN N) p211PacketSystemN.integralRegions
      exact ballRegion_le_integral _
    | some k =>
      show RegionLE (E k).S (E k).q (E k).S.integralRegions
      exact (E k).q_le_integral
  q_neg := by
    rw [tot_famQ]
    exact hq
  linkScale := ((N : ℝ) * unitVolP + extraQ E) / ((N : ℝ) * (14 / 3) * unitVolP + extraTheta E)
  linkScale_pos := div_pos_of_neg_of_neg hq hθ
  link_degree := by
    rw [tot_famQ, tot_famTheta]
    exact (div_mul_cancel₀ _ hθ.ne).symm
  ipl := by
    rintro x rfl
    refine ⟨((N : ℝ) * unitVolP + extraQ E) / ((N : ℝ) * (14 / 3) * unitVolP + extraTheta E),
      div_pos_of_neg_of_neg hq hθ, ?_⟩
    rw [tot_famQ, tot_famTheta]
    exact (div_mul_cancel₀ _ hθ.ne).symm

theorem famModel_weakSHE (N : ℕ) (hq) (hθ) : (famModel E N hq hθ).WeakSHE :=
  ⟨fun c => {c}, rfl, by
    rintro c x rfl i
    exact fun _ _ => subset_rfl⟩

theorem famModel_not_conclusion (N : ℕ) (hq) (hθ)
    (hgap : (N : ℝ) * (14 / 3) * unitVolP + extraTheta E < (N : ℝ) * unitVolP + extraQ E) :
    ¬ (famModel E N hq hθ).Conclusion := by
  intro h
  have h' : ∑ i, (famS E i).procVol (famQ E N i) ≤ ∑ i, (famS E i).procVol (famTheta E N i) := h
  rw [tot_famQ, tot_famTheta] at h'
  linarith

theorem robust : ∃ (N : ℕ) (hq : (N : ℝ) * unitVolP + extraQ E < 0)
    (hθ : (N : ℝ) * (14 / 3) * unitVolP + extraTheta E < 0),
    (famModel E N hq hθ).WeakSHE ∧ ¬ (famModel E N hq hθ).Conclusion := by
  have hu : 0 < -unitVolP := by linarith [unitVolP_neg]
  set A := extraTheta E
  set B := extraQ E
  obtain ⟨N, hN⟩ := exists_nat_gt ((|A| + |B| + 1) / -unitVolP)
  have ht : |A| + |B| + 1 < (N : ℝ) * -unitVolP := (div_lt_iff₀ hu).mp hN
  have hA1 := le_abs_self A
  have hA2 := neg_abs_le A
  have hB1 := le_abs_self B
  have hB2 := neg_abs_le B
  have e1 : (N : ℝ) * (14 / 3) * unitVolP = (14 / 3) * ((N : ℝ) * unitVolP) := by ring
  have e2 : (N : ℝ) * -unitVolP = -((N : ℝ) * unitVolP) := by ring
  rw [e2] at ht
  have hq : (N : ℝ) * unitVolP + B < 0 := by linarith
  have hθ : (N : ℝ) * (14 / 3) * unitVolP + A < 0 := by rw [e1]; linarith
  have hgap : (N : ℝ) * (14 / 3) * unitVolP + A < (N : ℝ) * unitVolP + B := by rw [e1]; linarith
  exact ⟨N, hq, hθ, famModel_weakSHE E N hq hθ, famModel_not_conclusion E N hq hθ hgap⟩

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

def goodPlace5 : ExtraPlace where
  S := CitedLV.Theorem311.PrimePacket.primePacketSystem 5
  lstar_eq := rfl
  q := fun _ _ => CitedLV.Theorem311.PrimePacket.qBall 5 1
  q_hasVolume := fun _ _ => by
    show Src.IUT4.Proposition14ii.haarQp 5 (CitedLV.Theorem311.PrimePacket.qBall 5 1) ≠ 0
    exact (Measure.measure_pos_of_nonempty_interior _
      (CitedLV.Theorem311.PrimePacket.qBall_interior 5 1)).ne'
  q_le_integral := fun _ _ => by
    show CitedLV.Theorem311.PrimePacket.qBall 5 1 ⊆ closedBall 0 1
    rw [CitedLV.Theorem311.PrimePacket.qBall_eq]
    exact closedBall_subset_closedBall (by norm_num)

def archSystem3 : PacketSystem where
  lstar := 3
  lstar_pos := by norm_num
  PlaceQ := Unit
  IsArch := fun _ => True
  Above := fun _ => Unit
  Packet := fun _ j => Fin (j.val + 1) → ℝ
  haar := fun _ _ => volume
  integral := fun _ _ => closedBall 0 1
  integral_isCompact := fun _ _ => isCompact_closedBall 0 1
  integral_interior_nonempty := fun _ _ =>
    ⟨0, ball_subset_interior_closedBall (mem_ball_self one_pos)⟩
  weight := fun _ j => 1 / ((j.val : ℝ) + 1)
  weight_pos := fun _ _ => by positivity
  adjustment := fun _ _ => 0
  StripAut := fun _ _ => Unit
  Ism := fun _ _ => ℤˣ
  ism_arch_order_two := fun _ _ _ g => Int.units_mul_self g
  labelAct := fun _ j σ => permPacketAut (j.val + 1) σ
  stripAct := fun _ _ _ => ContinuousAddEquiv.refl _
  ismAct := fun _ j g => signPacketAut (j.val + 1) g
  labelAct_one := fun _ _ => rfl
  labelAct_mul := fun _ _ _ _ => rfl
  stripAct_one := fun _ _ => rfl
  stripAct_mul := fun _ _ _ _ => rfl
  ismAct_one := fun _ _ => by ext z α; simp [signPacketAut]
  ismAct_mul := fun _ _ g h => by ext z α; simp [signPacketAut, mul_assoc]
  labelAct_integral := fun _ j σ => permPacketAut_integral (j.val + 1) σ
  stripAct_integral := fun _ _ _ => rfl
  ismAct_integral := fun _ j g => signPacketAut_integral (j.val + 1) g

def archPlace : ExtraPlace where
  S := archSystem3
  lstar_eq := rfl
  q := fun _ j => (closedBall (0 : Fin (j.val + 1) → ℝ) (1 / 2) : Set (Fin (j.val + 1) → ℝ))
  q_hasVolume := fun _ j => by
    show (volume : Measure (Fin (j.val + 1) → ℝ)) (closedBall 0 (1 / 2)) ≠ 0
    exact (measure_closedBall_pos volume 0 (by norm_num)).ne'
  q_le_integral := fun _ j => by
    show closedBall (0 : Fin (j.val + 1) → ℝ) (1 / 2) ⊆ closedBall 0 1
    exact closedBall_subset_closedBall (by norm_num)

theorem concrete : ∃ (N : ℕ) (hq : (N : ℝ) * unitVolP + extraQ ![goodPlace5, archPlace] < 0)
    (hθ : (N : ℝ) * (14 / 3) * unitVolP + extraTheta ![goodPlace5, archPlace] < 0),
    (famModel ![goodPlace5, archPlace] N hq hθ).WeakSHE ∧
      ¬ (famModel ![goodPlace5, archPlace] N hq hθ).Conclusion :=
  robust _

theorem weakSHE_does_not_yield_conclusion_fam :
    ¬ ∀ T : CitedTheoryFam, T.WeakSHE → T.Conclusion := by
  intro h
  obtain ⟨N, hq, hθ, hw, hnot⟩ := concrete
  exact hnot (h _ hw)

theorem strongCarrier_not_derivable_fam :
    ¬ ∀ T : CitedTheoryFam, T.WeakSHE → T.StrongSHECarrier := by
  intro h
  obtain ⟨N, hq, hθ, hw, hnot⟩ := concrete
  exact hnot (CitedTheoryFam.strongCarrier_implies_conclusion _ (h _ hw))

theorem strongValue_not_derivable_fam :
    ¬ ∀ T : CitedTheoryFam, T.WeakSHE → T.StrongSHEValue := by
  intro h
  obtain ⟨N, hq, hθ, hw, hnot⟩ := concrete
  exact hnot ((CitedTheoryFam.strongValue_iff_conclusion _).mp (h _ hw))

end CitedLV.Independence.Cor312CitedFamily

section Check
open CitedLV.Independence.Cor312CitedFamily
end Check
