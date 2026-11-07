import Mathlib
import Cor312LogVolume.Src.IUT3.Section3Theorem311Indeterminacies
import Cor312LogVolume.Src.IUT4.Section1Proposition14iiLogUnitsVolumeQp

namespace Src.IUT3.Theorem311

open MeasureTheory Metric Set
open scoped Pointwise

namespace PacketSystem

variable (S : PacketSystem)

def Ind3 (x y : S.Regions) : Prop :=
  ∀ vQ j, x vQ j ⊆ y vQ j ∧ y vQ j ⊆ S.integral vQ j

def HasVolume (x : S.Regions) : Prop :=
  ∀ vQ j, S.haar vQ j (x vQ j) ≠ 0

def integralRegions : S.Regions :=
  fun vQ j => S.integral vQ j

variable {S}

theorem packetLogVolume_mono {vQ : S.PlaceQ} {j : Fin (S.lstar + 1)} {A B : Set (S.Packet vQ j)}
    (hAB : A ⊆ B) (hB : B ⊆ S.integral vQ j) (hA : S.haar vQ j A ≠ 0) :
    S.packetLogVolume vQ j A ≤ S.packetLogVolume vQ j B := by
  have hOtop := (measure_pos_ne_top (S.haar vQ j) (S.integral_isCompact vQ j)
    (S.integral_interior_nonempty vQ j)).2
  have hBtop : S.haar vQ j B ≠ ⊤ := ne_top_of_le_ne_top hOtop (measure_mono hB)
  have hAtop : S.haar vQ j A ≠ ⊤ := ne_top_of_le_ne_top hBtop (measure_mono hAB)
  have hApos : 0 < (S.haar vQ j A).toReal := ENNReal.toReal_pos hA hAtop
  have hle : (S.haar vQ j A).toReal ≤ (S.haar vQ j B).toReal :=
    ENNReal.toReal_mono hBtop (measure_mono hAB)
  have hlog := Real.log_le_log hApos hle
  have hmul := mul_le_mul_of_nonneg_left
    (sub_le_sub_right hlog (Real.log (S.haar vQ j (S.integral vQ j)).toReal)) (S.weight_pos vQ j).le
  unfold packetLogVolume logVolume
  linarith

theorem procVol_ind3 {x y : S.Regions} (hxy : S.Ind3 x y) (hx : S.HasVolume x) :
    S.procVol x ≤ S.procVol y := by
  have hl : (0 : ℝ) < S.lstar := by exact_mod_cast S.lstar_pos
  unfold procVol
  refine Finset.sum_le_sum fun vQ _ => ?_
  refine (div_le_div_iff_of_pos_right hl).2 ?_
  exact Finset.sum_le_sum fun j _ => packetLogVolume_mono (hxy vQ j.succ).1 (hxy vQ j.succ).2 (hx vQ j.succ)

theorem procVol_le_integral {x : S.Regions} (hx : ∀ vQ j, x vQ j ⊆ S.integral vQ j) (hv : S.HasVolume x) :
    S.procVol x ≤ S.procVol S.integralRegions :=
  procVol_ind3 (fun vQ j => ⟨hx vQ j, subset_rfl⟩) hv

end PacketSystem

section Model

theorem logVolume_smul_closedBall (k : ℕ) {c : ℝ} (hc : 0 < c) :
    logVolume (volume : Measure (Fin k → ℝ)) (closedBall 0 1) (c • closedBall 0 1) = k * Real.log c := by
  obtain ⟨hpos, htop⟩ := measure_pos_ne_top (volume : Measure (Fin k → ℝ))
    (isCompact_closedBall (0 : Fin k → ℝ) 1) ⟨0, ball_subset_interior_closedBall (mem_ball_self one_pos)⟩
  have hreal : (volume (closedBall (0 : Fin k → ℝ) 1)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨hpos, htop⟩
  unfold logVolume
  rw [Measure.addHaar_smul, Module.finrank_fin_fun, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (by positivity),
    Real.log_mul (by positivity) hreal, Real.log_pow]
  ring

theorem smul_closedBall_subset (k : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    c • closedBall (0 : Fin k → ℝ) 1 ⊆ closedBall 0 1 := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_closedBall_zero_iff] at hz ⊢
  rw [norm_smul, Real.norm_of_nonneg hc0]
  nlinarith [norm_nonneg z]

noncomputable def halfRegions' : modelSystem.Regions :=
  fun _ j => (1 / 2 : ℝ) • closedBall (0 : Fin (j.val + 1) → ℝ) 1

noncomputable def quarterRegions : modelSystem.Regions :=
  fun _ j => (1 / 4 : ℝ) • closedBall (0 : Fin (j.val + 1) → ℝ) 1

def emptyRegions : modelSystem.Regions :=
  fun _ _ => ∅

theorem model_ind3_half : modelSystem.Ind3 halfRegions' modelSystem.integralRegions :=
  fun _ j => ⟨smul_closedBall_subset (j.val + 1) (c := 1 / 2) (by norm_num) (by norm_num), subset_rfl⟩

theorem model_hasVolume_half : modelSystem.HasVolume halfRegions' := by
  intro _ j
  change (volume : Measure (Fin (j.val + 1) → ℝ)) ((1 / 2 : ℝ) • closedBall 0 1) ≠ 0
  rw [Measure.addHaar_smul]
  refine mul_ne_zero (by norm_num) ?_
  exact (measure_pos_ne_top (volume : Measure (Fin (j.val + 1) → ℝ)) (isCompact_closedBall 0 1)
    ⟨0, ball_subset_interior_closedBall (mem_ball_self one_pos)⟩).1

theorem model_procVol_lt {x y : modelSystem.Regions}
    (h : ∀ vQ (j : Fin modelSystem.lstar),
      modelSystem.packetLogVolume vQ j.succ (x vQ j.succ) < modelSystem.packetLogVolume vQ j.succ (y vQ j.succ)) :
    modelSystem.procVol x < modelSystem.procVol y := by
  have hl : (0 : ℝ) < modelSystem.lstar := by exact_mod_cast modelSystem.lstar_pos
  unfold PacketSystem.procVol
  exact Finset.sum_lt_sum_of_nonempty ⟨(), Finset.mem_univ _⟩ fun vQ _ =>
    (div_lt_div_iff_of_pos_right hl).2
      (Finset.sum_lt_sum_of_nonempty ⟨⟨0, modelSystem.lstar_pos⟩, Finset.mem_univ _⟩ fun j _ => h vQ j)

theorem model_ind3_strict :
    modelSystem.Ind3 halfRegions' modelSystem.integralRegions ∧ modelSystem.HasVolume halfRegions' ∧
      modelSystem.procVol halfRegions' < modelSystem.procVol modelSystem.integralRegions := by
  refine ⟨model_ind3_half, model_hasVolume_half, model_procVol_lt fun vQ j => ?_⟩
  change 1 / ((j.succ.val : ℝ) + 1) * logVolume (volume : Measure (Fin (j.succ.val + 1) → ℝ))
      (closedBall 0 1) ((1 / 2 : ℝ) • closedBall 0 1) + 0 <
    1 / ((j.succ.val : ℝ) + 1) * logVolume (volume : Measure (Fin (j.succ.val + 1) → ℝ))
      (closedBall 0 1) (closedBall 0 1) + 0
  rw [logVolume_smul_closedBall _ (by norm_num), logVolume_self, mul_zero, add_zero, add_zero]
  have hneg : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  exact mul_neg_of_pos_of_neg (by positivity) (mul_neg_of_pos_of_neg (by positivity) hneg)

theorem hasVolume_needed :
    modelSystem.Ind3 emptyRegions quarterRegions ∧
      modelSystem.procVol quarterRegions < modelSystem.procVol emptyRegions := by
  refine ⟨fun _ j => ⟨empty_subset _, smul_closedBall_subset (j.val + 1) (c := 1 / 4) (by norm_num) (by norm_num)⟩,
    model_procVol_lt fun vQ j => ?_⟩
  change 1 / ((j.succ.val : ℝ) + 1) * logVolume (volume : Measure (Fin (j.succ.val + 1) → ℝ))
      (closedBall 0 1) ((1 / 4 : ℝ) • closedBall 0 1) + 0 <
    1 / ((j.succ.val : ℝ) + 1) * logVolume (volume : Measure (Fin (j.succ.val + 1) → ℝ))
      (closedBall 0 1) ∅ + 0
  have he : logVolume (volume : Measure (Fin (j.succ.val + 1) → ℝ)) (closedBall 0 1) ∅ =
      -(((j.succ.val + 1 : ℕ) : ℝ) * Real.log 2) := by
    unfold logVolume
    rw [measure_empty, ENNReal.toReal_zero, Real.log_zero, Real.volume_pi_closedBall _ zero_le_one, mul_one,
      ENNReal.toReal_ofReal (by positivity), Fintype.card_fin, Real.log_pow]
    ring
  rw [logVolume_smul_closedBall _ (by norm_num), he]
  have h4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h4]
  have hl2 := Real.log_pos (one_lt_two : (1 : ℝ) < 2)
  have hk : (0 : ℝ) < ((j.succ.val + 1 : ℕ) : ℝ) := by positivity
  have hk' : (0 : ℝ) < 1 / ((j.succ.val : ℝ) + 1) := by positivity
  have := mul_pos (mul_pos hk' hk) hl2
  nlinarith

end Model

section PadicInstance

open Src.IUT4.Proposition14ii

theorem qp_prop35_instance (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    logUnits p ⊆ Src.IUT3.Remark122.logShell (K := ℚ_[p]) p ∧
      logVolume (haarQp p) (closedBall (0 : ℚ_[p]) 1) (logUnits p) = -Real.log p ∧
      logVolume (haarQp p) (closedBall (0 : ℚ_[p]) 1) (Src.IUT3.Remark122.logShell (K := ℚ_[p]) p) = 0 ∧
      -Real.log p < 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine ⟨?_, logVolume_logUnits_odd hp2, ?_, ?_⟩
  · rw [logUnits_eq_odd hp2, logShell_Qp_eq (p := p)]
    exact closedBall_subset_closedBall (inv_le_one_of_one_le₀ hp1.le)
  · rw [logShell_Qp_eq (p := p)]
    exact logVolume_self _ _
  · exact neg_neg_of_pos (Real.log_pos hp1)

end PadicInstance

end Src.IUT3.Theorem311

section Check
open Src.IUT3.Theorem311
end Check
