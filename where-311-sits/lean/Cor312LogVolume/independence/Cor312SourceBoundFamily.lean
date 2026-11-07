import Cor312LogVolume.independence.Cor312SourceBoundTheory

set_option autoImplicit false
noncomputable section

namespace CitedLV.Independence.Cor312SourceBoundFamily

open Metric MeasureTheory CategoryTheory
open Src.IUT3.Theorem311
open Src.IUT3.Remark122
open Src.IUT4.Proposition14ii
open Src.EtTh.PadicThetaValues
open Src.IUT3.Remark395ix
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211RealCarrierPackage
open CitedLV.Theorem311.P211LogShellPacketBridge
open CitedLV.Theorem311.P211ComponentCTraceBridge
open CitedLV.Theorem311.P211SourceFacingSimultaneousXiF
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Independence.Cor312Cited
open CitedLV.Independence.Cor312CitedFamily
open CitedLV.Independence.Cor312SourceBound

def inputN (N : ℕ) : ComponentCInput where
  globalElement := componentCGlobal211
  exponent := 29 * N

theorem fieldCopyAct_eq_qBall (n : ℕ) :
    fieldCopyActOnContainer componentCGlobal211 n = fun _ _ => qBall n := by
  funext vQ j
  change (fun z : ℚ_[211] => (fieldCopyPadicScalar componentCGlobal211 ^ n) * z) ''
      sourceFacingComponents.packet vQ j = qBall n
  rw [sourceFacingComponents_packet]
  change (fun z : ℚ_[211] => (fieldCopyPadicScalar componentCGlobal211 ^ n) * z) ''
      closedBall (0 : ℚ_[211]) 1 = qBall n
  rw [componentCGlobal211_padic]
  rfl

theorem realizedRegion_inputN (N : ℕ) : realizedRegion (inputN N) = fun _ _ => qBall (29 * N) := by
  rw [realizedRegion_eq_inputRegion]
  exact fieldCopyAct_eq_qBall (29 * N)

def tateN (N : ℕ) : ℚ_[211] := (pElt ^ (29 * N)) ^ 14

theorem tateN_ne_zero (N : ℕ) : tateN N ≠ 0 :=
  pow_ne_zero _ (pow_ne_zero _ pElt_ne_zero)

def tateUnitN (N : ℕ) : ℂ_[211]ˣ :=
  Units.mk0 ((tateN N : ℚ_[211]) : ℂ_[211]) (by
    intro h
    have h' := congrArg (fun z : ℂ_[211] => ‖z‖) h
    simp only [PadicComplex.norm_extends', norm_zero] at h'
    exact tateN_ne_zero N (norm_eq_zero.mp h'))

theorem norm_tateUnitN (N : ℕ) :
    ‖((tateUnitN N : ℂ_[211]ˣ) : ℂ_[211])‖ = (((211 : ℝ)⁻¹) ^ (29 * N)) ^ 14 := by
  show ‖((tateN N : ℚ_[211]) : ℂ_[211])‖ = _
  rw [PadicComplex.norm_extends', tateN, norm_pow, norm_pow, norm_p211]

theorem tateUnitN_small (N : ℕ) (hN : 0 < N) : ‖((tateUnitN N : ℂ_[211]ˣ) : ℂ_[211])‖ < 1 := by
  rw [norm_tateUnitN]
  have h0 : (0 : ℝ) ≤ ((211 : ℝ)⁻¹) ^ (29 * N) := by positivity
  have h1 : ((211 : ℝ)⁻¹) ^ (29 * N) < 1 := pow_lt_one₀ (by positivity) (by norm_num) (by omega)
  exact pow_lt_one₀ h0 h1 (by norm_num)

theorem theta_root_normN (N : ℕ) (hN : 0 < N) (j : ℕ) (t : ℂ_[211]ˣ)
    (ht : t ∈ rootValues 211 (tateUnitN N) 7 j) :
    ‖((t : ℂ_[211]ˣ) : ℂ_[211])‖ = ((211 : ℝ)⁻¹) ^ (29 * N * (j * j)) := by
  have hpow := (mem_rootValues_iff_power 211 (tateUnitN N) (tateUnitN_small N hN) 7 j t).mp ht
  have hn := congrArg (fun z : ℂ_[211]ˣ => ‖((z : ℂ_[211]ˣ) : ℂ_[211])‖) hpow
  simp only [Units.val_pow_eq_pow_val, norm_pow] at hn
  rw [norm_tateUnitN] at hn
  have hrhs : ((((211 : ℝ)⁻¹) ^ (29 * N)) ^ 14) ^ (j * j)
      = (((211 : ℝ)⁻¹) ^ (29 * N * (j * j))) ^ (2 * 7) := by
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hrhs] at hn
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hn

def thetaValueRegionN (N j : ℕ) : Set ℚ_[211] :=
  {x | ∃ t ∈ rootValues 211 (tateUnitN N) 7 j, ‖x‖ ≤ ‖((t : ℂ_[211]ˣ) : ℂ_[211])‖}

theorem thetaValueRegionN_eq (N : ℕ) (hN : 0 < N) (j : ℕ) :
    thetaValueRegionN N j = qBall (29 * N * (j * j)) := by
  rw [qBall_eq]
  ext x
  simp only [thetaValueRegionN, Set.mem_setOf_eq, mem_closedBall_zero_iff]
  constructor
  · rintro ⟨t, ht, hx⟩
    rw [theta_root_normN N hN j t ht] at hx
    exact hx
  · intro hx
    obtain ⟨t, ht⟩ := rootValues_nonempty 211 (tateUnitN N) (tateUnitN_small N hN) 7 j (by norm_num)
    exact ⟨t, ht, by rw [theta_root_normN N hN j t ht]; exact hx⟩

theorem qBall_anti {m m' : ℕ} (h : m' ≤ m) : qBall m ⊆ qBall m' := by
  rw [qBall_eq, qBall_eq]
  exact closedBall_subset_closedBall (pow_le_pow_of_le_one (by positivity) (by norm_num) h)

theorem procVol_qBall_const (n : ℕ) :
    p211PacketSystem.procVol (fun _ _ => qBall n) = (1 / 7) * (-(n : ℝ) * Real.log 211) := by
  rw [PacketSystem.procVol]
  simp only [packetLogVolume_qBall, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : Fintype.card p211PacketSystem.PlaceQ = 1 := rfl
  have hl : (p211PacketSystem.lstar : ℝ) = 3 := by norm_num [p211PacketSystem]
  have hf : Fintype.card (Fin p211PacketSystem.lstar) = 3 := by simp [p211PacketSystem]
  rw [hc, hl, hf]
  push_cast
  ring

theorem procVol_ball_stage (f : ℕ → ℕ) :
    p211PacketSystem.procVol (fun _ j => qBall (f j.val))
      = ((f 1 + f 2 + f 3 : ℕ) : ℝ) / 3 * ((1 / 7) * (-Real.log 211)) := by
  have hstage : ∀ (vQ : p211PacketSystem.PlaceQ) (k : Fin p211PacketSystem.lstar),
      p211PacketSystem.packetLogVolume vQ k.succ (qBall (f k.succ.val))
        = (f (k.val + 1) : ℝ) * ((1 / 7) * (-Real.log 211)) := by
    intro vQ k
    rw [packetLogVolume_qBall, Fin.val_succ]
    ring
  have hl : (p211PacketSystem.lstar : ℝ) = 3 := by norm_num [p211PacketSystem]
  rw [PacketSystem.procVol]
  simp only [hstage]
  rw [hl]
  show (∑ _x : Unit, (∑ k : Fin 3, (f (k.val + 1) : ℝ) * ((1 / 7) * (-Real.log 211))) / (3 : ℝ)) = _
  simp only [Fin.sum_univ_three, Finset.univ_unique, Finset.sum_singleton, Fin.val_zero, Fin.val_one,
    Fin.val_two, zero_add, Nat.reduceAdd]
  push_cast
  ring

variable {κ : Type} [Fintype κ] (E : κ → ExtraPlace)

def famS' : Option κ → PacketSystem
  | none => p211PacketSystem
  | some k => (E k).S

omit [Fintype κ] in
theorem famS'_lstar : ∀ i, (famS' E i).lstar = 3
  | none => rfl
  | some k => (E k).lstar_eq

def famTheta' (N : ℕ) : ∀ i, (famS' E i).Regions
  | none => fun _ j => thetaValueRegionN N j.val
  | some k => (E k).S.integralRegions

def famQ' (N : ℕ) : ∀ i, (famS' E i).Regions
  | none => realizedRegion (inputN N)
  | some k => (E k).q

def famCont' (N c : ℕ) : ∀ i, (famS' E i).Regions
  | none => fun _ j => qBall (29 * N * (j.val * j.val) - c)
  | some k => (E k).S.integralRegions

def famPoss' (N c : ℕ) : Set (∀ i, (famS' E i).Regions) :=
  {x | ∀ i, RegionLE (famS' E i) (famTheta' E N i) (x i) ∧ RegionLE (famS' E i) (x i) (famCont' E N c i)}

def famLam' : ∀ i, ∀ vQ (j : Fin ((famS' E i).lstar + 1)), Set ((famS' E i).Packet vQ j) → Prop
  | none => fun _ _ A => ∃ c : ℚ_[211], c ≠ 0 ∧
      A = (fun z : ℚ_[211] => c * z) '' logShell (K := ℚ_[211]) 211
  | some k => fun vQ j A => A = (E k).S.integral vQ j

omit [Fintype κ] in
theorem famTheta'_le_famCont' (N c : ℕ) (hN : 0 < N) :
    ∀ i, RegionLE (famS' E i) (famTheta' E N i) (famCont' E N c i)
  | none => fun _ j => by
      show thetaValueRegionN N j.val ⊆ qBall (29 * N * (j.val * j.val) - c)
      rw [thetaValueRegionN_eq N hN]
      exact qBall_anti (Nat.sub_le _ _)
  | some _ => fun _ _ => subset_rfl

omit [Fintype κ] in
theorem famCont'_le_integral (N c : ℕ) :
    ∀ i, RegionLE (famS' E i) (famCont' E N c i) (famS' E i).integralRegions
  | none => fun _ _ => qBall_subset_integral _
  | some _ => fun _ _ => subset_rfl

omit [Fintype κ] in
theorem famTheta'_act (N : ℕ) :
    ∀ i (h : (famS' E i).ProcessionAut), h.act (famTheta' E N i) = famTheta' E N i
  | none, h => act_id h _
  | some k, h => act_integralRegions (E k).S h

omit [Fintype κ] in
theorem famCont'_act (N c : ℕ) :
    ∀ i (h : (famS' E i).ProcessionAut), h.act (famCont' E N c i) = famCont' E N c i
  | none, h => act_id h _
  | some k, h => act_integralRegions (E k).S h

omit [Fintype κ] in
theorem famTheta'_ind2 (N : ℕ) :
    ∀ i (g : (famS' E i).Ind2Element), (famS' E i).ind2Act g (famTheta' E N i) = famTheta' E N i
  | none, g => ind2Act_id g _
  | some k, g => ind2Act_integralRegions (E k).S g

omit [Fintype κ] in
theorem famCont'_ind2 (N c : ℕ) :
    ∀ i (g : (famS' E i).Ind2Element), (famS' E i).ind2Act g (famCont' E N c i) = famCont' E N c i
  | none, g => ind2Act_id g _
  | some k, g => ind2Act_integralRegions (E k).S g

omit [Fintype κ] in
theorem famTheta'_hasVolume (N : ℕ) (hN : 0 < N) : ∀ i, (famS' E i).HasVolume (famTheta' E N i)
  | none => by
      intro vQ j
      show haarQp 211 (thetaValueRegionN N j.val) ≠ 0
      rw [thetaValueRegionN_eq N hN]
      exact qBall_hasVolume _
  | some k => by
      show (E k).S.HasVolume (E k).S.integralRegions
      intro vQ j
      exact (Measure.measure_pos_of_nonempty_interior _ ((E k).S.integral_interior_nonempty vQ j)).ne'

omit [Fintype κ] in
theorem famPoss'_hasVolume (N c : ℕ) (hN : 0 < N) {x : ∀ i, (famS' E i).Regions}
    (hx : x ∈ famPoss' E N c) : ∀ i, (famS' E i).HasVolume (x i) := fun i vQ j h0 =>
  famTheta'_hasVolume E N hN i vQ j (measure_mono_null ((hx i).1 vQ j) h0)

theorem tot_famTheta' (N : ℕ) (hN : 0 < N) :
    ∑ i, (famS' E i).procVol (famTheta' E N i) = (N : ℝ) * (14 / 3) * unitVolP + extraTheta E := by
  rw [Fintype.sum_option]
  refine congrArg₂ (· + ·) ?_ rfl
  have e : (fun (_ : p211PacketSystem.PlaceQ) (j : Fin (p211PacketSystem.lstar + 1)) =>
      thetaValueRegionN N j.val) = fun _ j => qBall ((fun m => 29 * N * (m * m)) j.val) := by
    funext vQ j
    exact thetaValueRegionN_eq N hN j.val
  show p211PacketSystem.procVol (fun _ j => thetaValueRegionN N j.val) = _
  rw [e, procVol_ball_stage (fun m => 29 * N * (m * m))]
  unfold unitVolP
  push_cast
  ring

theorem tot_famQ' (N : ℕ) :
    ∑ i, (famS' E i).procVol (famQ' E N i) = (N : ℝ) * unitVolP + extraQ E := by
  rw [Fintype.sum_option]
  refine congrArg₂ (· + ·) ?_ rfl
  show p211PacketSystem.procVol (realizedRegion (inputN N)) = _
  rw [realizedRegion_inputN, procVol_qBall_const]
  unfold unitVolP
  push_cast
  ring

theorem tot_famCont' (N c : ℕ) (hc : c ≤ 29 * N) :
    ∑ i, (famS' E i).procVol (famCont' E N c i)
      = (N : ℝ) * (14 / 3) * unitVolP + (c : ℝ) / 7 * Real.log 211 + extraTheta E := by
  rw [Fintype.sum_option]
  refine congrArg₂ (· + ·) ?_ rfl
  show p211PacketSystem.procVol (fun _ j => qBall ((fun m => 29 * N * (m * m) - c) j.val)) = _
  rw [procVol_ball_stage (fun m => 29 * N * (m * m) - c)]
  have h1 : c ≤ 29 * N * (1 * 1) := by simpa using hc
  have h2 : c ≤ 29 * N * (2 * 2) := by nlinarith
  have h3 : c ≤ 29 * N * (3 * 3) := by nlinarith
  have hsum : ((29 * N * (1 * 1) - c + (29 * N * (2 * 2) - c) + (29 * N * (3 * 3) - c) : ℕ) : ℝ)
      = 29 * N * 14 - 3 * c := by
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
    ring
  rw [hsum]
  unfold unitVolP
  ring

theorem famPoss'_vol_le (N c : ℕ) (hN : 0 < N) {x : ∀ i, (famS' E i).Regions}
    (hx : x ∈ famPoss' E N c) :
    ∑ i, (famS' E i).procVol (x i) ≤ ∑ i, (famS' E i).procVol (famCont' E N c i) :=
  Finset.sum_le_sum fun i _ =>
    (famS' E i).procVol_ind3 (fun vQ j => ⟨(hx i).2 vQ j, famCont'_le_integral E N c i vQ j⟩)
      (famPoss'_hasVolume E N c hN hx i)

set_option maxHeartbeats 1000000 in

def famModelSB (N c : ℕ) (hN : 0 < N) (hc : c ≤ 29 * N)
    (hq : (N : ℝ) * unitVolP + extraQ E < 0)
    (hθ : (N : ℝ) * (14 / 3) * unitVolP + extraTheta E < 0)
    (hC : (N : ℝ) * (14 / 3) * unitVolP + (c : ℝ) / 7 * Real.log 211 + extraTheta E < 0) :
    CitedTheoryFam where
  ι := Option κ
  S := famS' E
  lstar_common := fun i k => (famS'_lstar E i).trans (famS'_lstar E k).symm
  thetaPilot := famTheta' E N
  qPilot := famQ' E N
  container := famCont' E N c
  Possible := famPoss' E N c
  IsLambdaO := famLam' E
  hull := famCont' E N c
  theta_possible := fun i => ⟨fun _ _ => subset_rfl, famTheta'_le_famCont' E N c hN i⟩
  ind1_closed := by
    intro x hx y hy i
    obtain ⟨h, hh⟩ := hy i
    rw [hh]
    refine ⟨?_, ?_⟩
    · rw [← famTheta'_act E N i h]
      exact act_regionLE h (hx i).1
    · rw [← famCont'_act E N c i h]
      exact act_regionLE h (hx i).2
  ind2_closed := by
    intro x hx y hy i
    obtain ⟨g, hg⟩ := hy i
    rw [hg]
    refine ⟨?_, ?_⟩
    · rw [← famTheta'_ind2 E N i g]
      exact ind2Act_regionLE g (hx i).1
    · rw [← famCont'_ind2 E N c i g]
      exact ind2Act_regionLE g (hx i).2
  ind3_bound := fun _ hx i => (hx i).2
  ind3_saturated := fun _ hx _ hxy hyc i =>
    ⟨fun vQ j => ((hx i).1 vQ j).trans (hxy i vQ j), hyc i⟩
  container_le_integral := famCont'_le_integral E N c
  hull_isLambdaO := by
    intro i
    cases i with
    | none =>
      intro vQ j
      exact ⟨pElt ^ (29 * N * (j.val * j.val) - c), pow_ne_zero _ pElt_ne_zero,
        qBall_eq_lambda_logShell _⟩
    | some k =>
      show ∀ (vQ : (E k).S.PlaceQ) (j : Fin ((E k).S.lstar + 1)),
        (E k).S.integralRegions vQ j = (E k).S.integral vQ j
      exact fun _ _ => rfl
  hull_contains := fun _ hx i => (hx i).2
  hull_minimal := fun _ _ hT =>
    hT _ (fun i => ⟨famTheta'_le_famCont' E N c hN i, fun _ _ => subset_rfl⟩)
  hull_le_integral := famCont'_le_integral E N c
  q_hasVolume := by
    intro i
    cases i with
    | none =>
      intro vQ j
      show haarQp 211 (realizedRegion (inputN N) vQ j) ≠ 0
      rw [realizedRegion_inputN]
      exact qBall_hasVolume _
    | some k =>
      show (E k).S.HasVolume (E k).q
      exact (E k).q_hasVolume
  q_le_integral := by
    intro i
    cases i with
    | none =>
      intro vQ j
      show realizedRegion (inputN N) vQ j ⊆ p211PacketSystem.integral vQ j
      rw [realizedRegion_inputN]
      exact qBall_subset_integral _
    | some k =>
      show RegionLE (E k).S (E k).q (E k).S.integralRegions
      exact (E k).q_le_integral
  q_neg := by
    rw [tot_famQ']
    exact hq
  linkScale := ((N : ℝ) * unitVolP + extraQ E) / ((N : ℝ) * (14 / 3) * unitVolP + extraTheta E)
  linkScale_pos := div_pos_of_neg_of_neg hq hθ
  link_degree := by
    rw [tot_famQ', tot_famTheta' E N hN]
    exact (div_mul_cancel₀ _ hθ.ne).symm
  ipl := by
    intro x hx
    have hxneg : ∑ i, (famS' E i).procVol (x i) < 0 := by
      have := famPoss'_vol_le E N c hN hx
      rw [tot_famCont' E N c hc] at this
      linarith
    refine ⟨(∑ i, (famS' E i).procVol (famQ' E N i)) / ∑ i, (famS' E i).procVol (x i),
      div_pos_of_neg_of_neg (by rw [tot_famQ']; exact hq) hxneg, ?_⟩
    exact (div_mul_cancel₀ _ hxneg.ne).symm

theorem famModelSB_weakSHE (N c : ℕ) (hN) (hc) (hq) (hθ) (hC) :
    (famModelSB E N c hN hc hq hθ hC).WeakSHE :=
  ⟨fun c' => {x | ∀ i, RegionLE (famS' E i) (famTheta' E N i) (x i) ∧ RegionLE (famS' E i) (x i) (c' i)},
    rfl, fun _ _ hx i => (hx i).2⟩

theorem famModelSB_not_conclusion (N c : ℕ) (hN) (hc) (hq) (hθ) (hC)
    (hgap : (N : ℝ) * (14 / 3) * unitVolP + (c : ℝ) / 7 * Real.log 211 + extraTheta E
      < (N : ℝ) * unitVolP + extraQ E) :
    ¬ (famModelSB E N c hN hc hq hθ hC).Conclusion := by
  intro h
  have h' : ∑ i, (famS' E i).procVol (famQ' E N i) ≤ ∑ i, (famS' E i).procVol (famCont' E N c i) := h
  rw [tot_famQ', tot_famCont' E N c hc] at h'
  linarith

theorem robust_sourceBound (c : ℕ) :
    ∃ (N : ℕ) (hN : 0 < N) (hc : c ≤ 29 * N) (hq : (N : ℝ) * unitVolP + extraQ E < 0)
      (hθ : (N : ℝ) * (14 / 3) * unitVolP + extraTheta E < 0)
      (hC : (N : ℝ) * (14 / 3) * unitVolP + (c : ℝ) / 7 * Real.log 211 + extraTheta E < 0),
      (famModelSB E N c hN hc hq hθ hC).WeakSHE ∧ ¬ (famModelSB E N c hN hc hq hθ hC).Conclusion := by
  obtain ⟨N, hc, hq, hθ, hC, _, hnot⟩ := robust_enlarged E c
  have hnot' : ¬ (∑ i, (famS E i).procVol (famQ E N i)
      ≤ ∑ i, (famS E i).procVol (famCont E N c i)) := hnot
  rw [tot_famQ, tot_famCont E N c hc] at hnot'
  have hgap := lt_of_not_ge hnot'
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      have hle := extraQ_le_extraTheta E
      have hL : 0 ≤ Real.log 211 := Real.log_nonneg (by norm_num)
      have hcnn : (0 : ℝ) ≤ (c : ℝ) / 7 * Real.log 211 := by positivity
      simp only [Nat.cast_zero, zero_mul] at hgap
      linarith
    · exact h0
  exact ⟨N, hN, hc, hq, hθ, hC, famModelSB_weakSHE E N c hN hc hq hθ hC,
    famModelSB_not_conclusion E N c hN hc hq hθ hC hgap⟩

theorem sourceBoundFamily_layer (c : ℕ) :
    ∃ (N : ℕ) (hN : 0 < N) (hc : c ≤ 29 * N) (hq : (N : ℝ) * unitVolP + extraQ E < 0)
      (hθ : (N : ℝ) * (14 / 3) * unitVolP + extraTheta E < 0)
      (hC : (N : ℝ) * (14 / 3) * unitVolP + (c : ℝ) / 7 * Real.log 211 + extraTheta E < 0),
      let T := famModelSB E N c hN hc hq hθ hC
      T.WeakSHE ∧
        T.primeStripLayer.possible = T.Possible ∧
        (∀ x ∈ T.primeStripLayer.possible, T.primeStripLayer.Linked x) ∧
        T.layerLoop.ClosedUpToFormalQuotient completedBeforeSQ5 ∧
        T.layerLoop.loopArrow (𝟙 _) (𝟙 _) = 𝟙 _ ∧
        ¬ T.primeStripLayer.ScalarProduction (fun x => ∑ i, (T.S i).procVol (x i)) T.negLogQ ∧
        ¬ T.Conclusion := by
  obtain ⟨N, hN, hc, hq, hθ, hC, hw, hnot⟩ := robust_sourceBound E c
  refine ⟨N, hN, hc, hq, hθ, hC, ?_⟩
  intro T
  have heq : T.primeStripLayer.possible = T.Possible :=
    T.layer_possible_eq (fun y hy i => (hy i).1)
  refine ⟨hw, heq, T.layer_ipl, T.layer_closed_before_sq5, T.layer_holonomy_trivial, ?_, hnot⟩
  rintro ⟨x, hx, he⟩
  have hxP : x ∈ famPoss' E N c := T.layer_possible_subset hx
  exact hnot (T.layer_volume_production_implies_conclusion
    ⟨x, hx, famPoss'_hasVolume E N c hN hxP, he⟩)

theorem concrete_sourceBound :
    ∃ (N : ℕ) (hN : 0 < N) (hc : 1 ≤ 29 * N)
      (hq : (N : ℝ) * unitVolP + extraQ ![goodPlace5, archPlace] < 0)
      (hθ : (N : ℝ) * (14 / 3) * unitVolP + extraTheta ![goodPlace5, archPlace] < 0)
      (hC : (N : ℝ) * (14 / 3) * unitVolP + ((1 : ℕ) : ℝ) / 7 * Real.log 211
          + extraTheta ![goodPlace5, archPlace] < 0),
      (famModelSB ![goodPlace5, archPlace] N 1 hN hc hq hθ hC).WeakSHE ∧
        ¬ (famModelSB ![goodPlace5, archPlace] N 1 hN hc hq hθ hC).Conclusion :=
  robust_sourceBound _ 1

end CitedLV.Independence.Cor312SourceBoundFamily

section Check
open CitedLV.Independence.Cor312SourceBoundFamily
end Check
