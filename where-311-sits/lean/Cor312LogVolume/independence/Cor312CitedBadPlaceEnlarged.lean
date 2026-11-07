import Cor312LogVolume.independence.Cor312CitedTheoryFamily

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
open CitedLV.Independence.Cor312Cited

theorem act_regionLE {S : PacketSystem} (h : S.ProcessionAut) {a b : S.Regions}
    (hab : RegionLE S a b) : RegionLE S (h.act a) (h.act b) :=
  fun vQ j => Set.image_mono (hab vQ j)

theorem ind2Act_regionLE {S : PacketSystem} (g : S.Ind2Element) {a b : S.Regions}
    (hab : RegionLE S a b) : RegionLE S (S.ind2Act g a) (S.ind2Act g b) :=
  fun vQ j => Set.image_mono (hab vQ j)

theorem ballN_anti (n : ℕ) {k k' : ℕ} (hk : k' ≤ k) : qBallN n k ⊆ qBallN n k' := by
  rw [qBallN, qBallN]
  refine Set.pi_mono fun _ _ => ?_
  rw [qBall_eq, qBall_eq]
  exact closedBall_subset_closedBall (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk)

theorem packetLogVolume_qBallN_stage (m : ℕ) (vQ : p211PacketSystemN.PlaceQ)
    (k : Fin (p211PacketSystemN.lstar + 1)) :
    p211PacketSystemN.packetLogVolume vQ k (qBallN (k.val + 1) m)
      = -((m : ℝ) / 7) * Real.log 211 := by
  show (1 / (7 * ((k.val : ℝ) + 1)))
      * logVolume (muPi (k.val + 1)) (closedBall (0 : Fin (k.val + 1) → ℚ_[211]) 1)
          (qBallN (k.val + 1) m) + 0 = _
  rw [← qBallN_zero_eq_ball, logVolume_qBallN]
  have hk : ((k.val : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem procVol_ballRegion (f : ℕ → ℕ) :
    p211PacketSystemN.procVol (ballRegion f)
      = -(Real.log 211 / 21) * ((f 1 : ℝ) + f 2 + f 3) := by
  have hstage : ∀ (vQ : p211PacketSystemN.PlaceQ) (k : Fin p211PacketSystemN.lstar),
      p211PacketSystemN.packetLogVolume vQ k.succ (ballRegion f vQ k.succ)
        = -(((f (k.val + 1) : ℕ) : ℝ) / 7) * Real.log 211 := by
    intro vQ k
    exact packetLogVolume_qBallN_stage (f (k.val + 1)) vQ k.succ
  have hl : (p211PacketSystemN.lstar : ℝ) = 3 := by norm_num [p211PacketSystemN]
  rw [PacketSystem.procVol]
  simp only [hstage]
  rw [hl]
  show (∑ _x : Unit, (∑ k : Fin 3,
      -(((f (k.val + 1) : ℕ) : ℝ) / 7) * Real.log 211) / (3 : ℝ)) = _
  simp only [Fin.sum_univ_three, Finset.univ_unique, Finset.sum_singleton]
  norm_num
  ring

abbrev thetaNc (N c : ℕ) : p211PacketSystemN.Regions := ballRegion fun k => 29 * (N * k ^ 2) - c

theorem thetaN_le_thetaNc (N c : ℕ) : RegionLE p211PacketSystemN (thetaN N) (thetaNc N c) :=
  fun _ j => by
    show qBallN (j.val + 1) (29 * (N * j.val ^ 2)) ⊆ qBallN (j.val + 1) (29 * (N * j.val ^ 2) - c)
    exact ballN_anti _ (Nat.sub_le _ _)

theorem procVol_thetaNc (N c : ℕ) (hc : c ≤ 29 * N) :
    p211PacketSystemN.procVol (thetaNc N c)
      = (N : ℝ) * (14 / 3) * unitVolP + (c : ℝ) / 7 * Real.log 211 := by
  rw [procVol_ballRegion]
  have h1 : c ≤ 29 * (N * 1 ^ 2) := by simpa using hc
  have h2 : c ≤ 29 * (N * 2 ^ 2) := by norm_num; omega
  have h3 : c ≤ 29 * (N * 3 ^ 2) := by norm_num; omega
  simp only [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
  unfold unitVolP
  push_cast
  ring

variable {κ : Type} [Fintype κ] (E : κ → ExtraPlace)

def famCont (N c : ℕ) : ∀ i, (famS E i).Regions
  | none => thetaNc N c
  | some k => (E k).S.integralRegions

def famPoss (N c : ℕ) : Set (∀ i, (famS E i).Regions) :=
  {x | ∀ i, RegionLE (famS E i) (famTheta E N i) (x i) ∧ RegionLE (famS E i) (x i) (famCont E N c i)}

omit [Fintype κ] in
theorem famTheta_le_famCont (N c : ℕ) :
    ∀ i, RegionLE (famS E i) (famTheta E N i) (famCont E N c i)
  | none => thetaN_le_thetaNc N c
  | some _ => fun _ _ => subset_rfl

omit [Fintype κ] in
theorem famCont_le_integral (N c : ℕ) :
    ∀ i, RegionLE (famS E i) (famCont E N c i) (famS E i).integralRegions
  | none => by
      show RegionLE p211PacketSystemN (thetaNc N c) p211PacketSystemN.integralRegions
      exact ballRegion_le_integral _
  | some _ => fun _ _ => subset_rfl

omit [Fintype κ] in
theorem famTheta_act (N : ℕ) :
    ∀ i (h : (famS E i).ProcessionAut), h.act (famTheta E N i) = famTheta E N i
  | none, h => ind1Act_ballRegion (fun k => 29 * (N * k ^ 2)) h
  | some k, h => act_integralRegions (E k).S h

omit [Fintype κ] in
theorem famCont_act (N c : ℕ) :
    ∀ i (h : (famS E i).ProcessionAut), h.act (famCont E N c i) = famCont E N c i
  | none, h => ind1Act_ballRegion (fun k => 29 * (N * k ^ 2) - c) h
  | some k, h => act_integralRegions (E k).S h

omit [Fintype κ] in
theorem famTheta_ind2 (N : ℕ) :
    ∀ i (g : (famS E i).Ind2Element), (famS E i).ind2Act g (famTheta E N i) = famTheta E N i
  | none, g => ind2Act_ballRegion (fun k => 29 * (N * k ^ 2)) g
  | some k, g => ind2Act_integralRegions (E k).S g

omit [Fintype κ] in
theorem famCont_ind2 (N c : ℕ) :
    ∀ i (g : (famS E i).Ind2Element), (famS E i).ind2Act g (famCont E N c i) = famCont E N c i
  | none, g => ind2Act_ballRegion (fun k => 29 * (N * k ^ 2) - c) g
  | some k, g => ind2Act_integralRegions (E k).S g

omit [Fintype κ] in
theorem famTheta_hasVolume (N : ℕ) : ∀ i, (famS E i).HasVolume (famTheta E N i)
  | none => by
      show p211PacketSystemN.HasVolume (thetaN N)
      exact ballRegion_hasVolume _
  | some k => by
      show (E k).S.HasVolume (E k).S.integralRegions
      intro vQ j
      exact (Measure.measure_pos_of_nonempty_interior _ ((E k).S.integral_interior_nonempty vQ j)).ne'

omit [Fintype κ] in
theorem famPoss_hasVolume (N c : ℕ) {x : ∀ i, (famS E i).Regions} (hx : x ∈ famPoss E N c) :
    ∀ i, (famS E i).HasVolume (x i) := fun i vQ j h0 =>
  famTheta_hasVolume E N i vQ j (measure_mono_null ((hx i).1 vQ j) h0)

theorem tot_famCont (N c : ℕ) (hc : c ≤ 29 * N) :
    ∑ i, (famS E i).procVol (famCont E N c i)
      = (N : ℝ) * (14 / 3) * unitVolP + (c : ℝ) / 7 * Real.log 211 + extraTheta E := by
  rw [Fintype.sum_option]
  exact congrArg₂ (· + ·) (procVol_thetaNc N c hc) rfl

theorem famPoss_vol_le (N c : ℕ) {x : ∀ i, (famS E i).Regions} (hx : x ∈ famPoss E N c) :
    ∑ i, (famS E i).procVol (x i) ≤ ∑ i, (famS E i).procVol (famCont E N c i) :=
  Finset.sum_le_sum fun i _ =>
    (famS E i).procVol_ind3 (fun vQ j => ⟨(hx i).2 vQ j, famCont_le_integral E N c i vQ j⟩)
      (famPoss_hasVolume E N c hx i)

set_option maxHeartbeats 1000000 in

def famModelC (N c : ℕ) (hc : c ≤ 29 * N)
    (hq : (N : ℝ) * unitVolP + extraQ E < 0)
    (hθ : (N : ℝ) * (14 / 3) * unitVolP + extraTheta E < 0)
    (hC : (N : ℝ) * (14 / 3) * unitVolP + (c : ℝ) / 7 * Real.log 211 + extraTheta E < 0) :
    CitedTheoryFam where
  ι := Option κ
  S := famS E
  lstar_common := fun i k => (famS_lstar E i).trans (famS_lstar E k).symm
  thetaPilot := famTheta E N
  qPilot := famQ E N
  container := famCont E N c
  Possible := famPoss E N c
  IsLambdaO := famLam E
  hull := famCont E N c
  theta_possible := fun i => ⟨fun _ _ => subset_rfl, famTheta_le_famCont E N c i⟩
  ind1_closed := by
    intro x hx y hy i
    obtain ⟨h, hh⟩ := hy i
    rw [hh]
    refine ⟨?_, ?_⟩
    · rw [← famTheta_act E N i h]
      exact act_regionLE h (hx i).1
    · rw [← famCont_act E N c i h]
      exact act_regionLE h (hx i).2
  ind2_closed := by
    intro x hx y hy i
    obtain ⟨g, hg⟩ := hy i
    rw [hg]
    refine ⟨?_, ?_⟩
    · rw [← famTheta_ind2 E N i g]
      exact ind2Act_regionLE g (hx i).1
    · rw [← famCont_ind2 E N c i g]
      exact ind2Act_regionLE g (hx i).2
  ind3_bound := fun _ hx i => (hx i).2
  ind3_saturated := fun _ hx _ hxy hyc i =>
    ⟨fun vQ j => ((hx i).1 vQ j).trans (hxy i vQ j), hyc i⟩
  container_le_integral := famCont_le_integral E N c
  hull_isLambdaO := by
    intro i
    cases i with
    | none =>
      show ∀ (vQ : p211PacketSystemN.PlaceQ) (j : Fin (p211PacketSystemN.lstar + 1)),
        ∃ m : ℕ, thetaNc N c vQ j = qBallN (j.val + 1) m
      exact fun _ j => ⟨29 * (N * j.val ^ 2) - c, rfl⟩
    | some k =>
      show ∀ (vQ : (E k).S.PlaceQ) (j : Fin ((E k).S.lstar + 1)),
        (E k).S.integralRegions vQ j = (E k).S.integral vQ j
      exact fun _ _ => rfl
  hull_contains := fun _ hx i => (hx i).2
  hull_minimal := fun _ _ hT =>
    hT _ (fun i => ⟨famTheta_le_famCont E N c i, fun _ _ => subset_rfl⟩)
  hull_le_integral := famCont_le_integral E N c
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
    intro x hx
    have hxneg : ∑ i, (famS E i).procVol (x i) < 0 := by
      have := famPoss_vol_le E N c hx
      rw [tot_famCont E N c hc] at this
      linarith
    refine ⟨(∑ i, (famS E i).procVol (famQ E N i)) / ∑ i, (famS E i).procVol (x i),
      div_pos_of_neg_of_neg (by rw [tot_famQ]; exact hq) hxneg, ?_⟩
    exact (div_mul_cancel₀ _ hxneg.ne).symm

theorem famModelC_weakSHE (N c : ℕ) (hc) (hq) (hθ) (hC) :
    (famModelC E N c hc hq hθ hC).WeakSHE :=
  ⟨fun c' => {x | ∀ i, RegionLE (famS E i) (famTheta E N i) (x i) ∧ RegionLE (famS E i) (x i) (c' i)},
    rfl, fun _ _ hx i => (hx i).2⟩

theorem famModelC_not_conclusion (N c : ℕ) (hc) (hq) (hθ) (hC)
    (hgap : (N : ℝ) * (14 / 3) * unitVolP + (c : ℝ) / 7 * Real.log 211 + extraTheta E
      < (N : ℝ) * unitVolP + extraQ E) :
    ¬ (famModelC E N c hc hq hθ hC).Conclusion := by
  intro h
  have h' : ∑ i, (famS E i).procVol (famQ E N i) ≤ ∑ i, (famS E i).procVol (famCont E N c i) := h
  rw [tot_famQ, tot_famCont E N c hc] at h'
  linarith

theorem robust_enlarged (c : ℕ) :
    ∃ (N : ℕ) (hc : c ≤ 29 * N) (hq : (N : ℝ) * unitVolP + extraQ E < 0)
      (hθ : (N : ℝ) * (14 / 3) * unitVolP + extraTheta E < 0)
      (hC : (N : ℝ) * (14 / 3) * unitVolP + (c : ℝ) / 7 * Real.log 211 + extraTheta E < 0),
      (famModelC E N c hc hq hθ hC).WeakSHE ∧ ¬ (famModelC E N c hc hq hθ hC).Conclusion := by
  have hu : 0 < -unitVolP := by linarith [unitVolP_neg]
  have hL : 0 ≤ Real.log 211 := Real.log_nonneg (by norm_num)
  set A := extraTheta E
  set B := extraQ E
  set δ : ℝ := (c : ℝ) / 7 * Real.log 211 with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt ((|A| + |B| + δ + 1) / -unitVolP + c)
  have hpos : 0 ≤ (|A| + |B| + δ + 1) / -unitVolP := by positivity
  have hNc : (c : ℝ) < N := by linarith
  have hc : c ≤ 29 * N := by
    have : c < N := by exact_mod_cast hNc
    omega
  have hN' : (|A| + |B| + δ + 1) / -unitVolP < N := by linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
  have ht : |A| + |B| + δ + 1 < (N : ℝ) * -unitVolP := (div_lt_iff₀ hu).mp hN'
  have hA1 := le_abs_self A
  have hA2 := neg_abs_le A
  have hB1 := le_abs_self B
  have hB2 := neg_abs_le B
  have e1 : (N : ℝ) * (14 / 3) * unitVolP = (14 / 3) * ((N : ℝ) * unitVolP) := by ring
  have e2 : (N : ℝ) * -unitVolP = -((N : ℝ) * unitVolP) := by ring
  rw [e2] at ht
  have hq : (N : ℝ) * unitVolP + B < 0 := by linarith
  have hθ : (N : ℝ) * (14 / 3) * unitVolP + A < 0 := by rw [e1]; linarith
  have hC : (N : ℝ) * (14 / 3) * unitVolP + δ + A < 0 := by rw [e1]; linarith
  have hgap : (N : ℝ) * (14 / 3) * unitVolP + δ + A < (N : ℝ) * unitVolP + B := by
    rw [e1]; linarith
  exact ⟨N, hc, hq, hθ, hC, famModelC_weakSHE E N c hc hq hθ hC,
    famModelC_not_conclusion E N c hc hq hθ hC hgap⟩

theorem weakSHE_does_not_yield_conclusion_enlarged (c : ℕ) :
    ¬ ∀ T : CitedTheoryFam, T.WeakSHE → T.Conclusion := by
  intro h
  obtain ⟨N, hc, hq, hθ, hC, hw, hnot⟩ := robust_enlarged ![goodPlace5, archPlace] c
  exact hnot (h _ hw)

theorem concrete_enlarged :
    ∃ (N : ℕ) (hc : 1 ≤ 29 * N)
      (hq : (N : ℝ) * unitVolP + extraQ ![goodPlace5, archPlace] < 0)
      (hθ : (N : ℝ) * (14 / 3) * unitVolP + extraTheta ![goodPlace5, archPlace] < 0)
      (hC : (N : ℝ) * (14 / 3) * unitVolP + ((1 : ℕ) : ℝ) / 7 * Real.log 211
          + extraTheta ![goodPlace5, archPlace] < 0),
      (famModelC ![goodPlace5, archPlace] N 1 hc hq hθ hC).WeakSHE ∧
        ¬ (famModelC ![goodPlace5, archPlace] N 1 hc hq hθ hC).Conclusion :=
  robust_enlarged _ 1

theorem thetaN_ne_thetaNc (N c : ℕ) (hc : c ≤ 29 * N) (hc0 : 0 < c) : thetaN N ≠ thetaNc N c := by
  intro h
  have e := procVol_thetaNc N c hc
  rw [← h, procVol_thetaN] at e
  have hL : 0 < Real.log 211 := Real.log_pos (by norm_num)
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc0
  have : (0 : ℝ) < (c : ℝ) / 7 * Real.log 211 := by positivity
  linarith

theorem strongCarrier_not_derivable_enlarged (c : ℕ) :
    ¬ ∀ T : CitedTheoryFam, T.WeakSHE → T.StrongSHECarrier := by
  intro h
  obtain ⟨N, hc, hq, hθ, hC, hw, hnot⟩ := robust_enlarged ![goodPlace5, archPlace] c
  exact hnot ((CitedTheoryFam.strongCarrier_implies_conclusion _) (h _ hw))

theorem strongValue_not_derivable_enlarged (c : ℕ) :
    ¬ ∀ T : CitedTheoryFam, T.WeakSHE → T.StrongSHEValue := by
  intro h
  obtain ⟨N, hc, hq, hθ, hC, hw, hnot⟩ := robust_enlarged ![goodPlace5, archPlace] c
  exact hnot ((CitedTheoryFam.strongValue_iff_conclusion _).mp (h _ hw))

end CitedLV.Independence.Cor312CitedFamily

section Check
open CitedLV.Independence.Cor312CitedFamily
end Check
