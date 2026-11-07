import Cor312LogVolume.Src.IUT3.Section3Theorem311Indeterminacies
import Cor312LogVolume.Src.IUT4.Section1Proposition14iiLogUnitsVolumeQp

noncomputable section
namespace CitedLV.Theorem311.P211Packet

open Metric Set MeasureTheory
open Src.IUT3.Theorem311 Src.IUT4.Proposition14ii

instance fact211 : Fact (Nat.Prime 211) := ⟨by norm_num⟩

def p211PacketSystem : PacketSystem where
  lstar := 3
  lstar_pos := by norm_num
  PlaceQ := Unit
  IsArch := fun _ => False
  Above := fun _ => Unit
  Packet := fun _ _ => ℚ_[211]
  haar := fun _ _ => haarQp 211
  integral := fun _ _ => closedBall 0 1
  integral_isCompact := fun _ _ => isCompact_closedBall 0 1
  integral_interior_nonempty := fun _ _ =>
    ⟨0, ball_subset_interior_closedBall (mem_ball_self one_pos)⟩
  weight := fun _ _ => 1 / 7
  weight_pos := fun _ _ => by norm_num
  adjustment := fun _ _ => 0
  StripAut := fun _ _ => Unit
  Ism := fun _ _ => Unit
  ism_arch_order_two := fun _ h => absurd h id
  labelAct := fun _ _ _ => ContinuousAddEquiv.refl _
  stripAct := fun _ _ _ => ContinuousAddEquiv.refl _
  ismAct := fun _ _ _ => ContinuousAddEquiv.refl _
  labelAct_one := fun _ _ => rfl
  labelAct_mul := fun _ _ _ _ => rfl
  stripAct_one := fun _ _ => rfl
  stripAct_mul := fun _ _ _ _ => rfl
  ismAct_one := fun _ _ => rfl
  ismAct_mul := fun _ _ _ _ => rfl
  labelAct_integral := fun _ _ _ => rfl
  stripAct_integral := fun _ _ _ => rfl
  ismAct_integral := fun _ _ _ => rfl

theorem image_mul_closedBall (c : ℚ_[211]) (hc : c ≠ 0) {r : ℝ} (_hr : 0 ≤ r) :
    (fun x => c * x) '' closedBall (0 : ℚ_[211]) r = closedBall 0 (‖c‖ * r) := by
  ext y
  simp only [Set.mem_image, mem_closedBall_zero_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg c)
  · intro hy
    refine ⟨c⁻¹ * y, ?_, by field_simp⟩
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr hc)]
    exact hy

abbrev pElt : ℚ_[211] := ((211 : ℕ) : ℚ_[211])

def qBall (n : ℕ) : Set ℚ_[211] :=
  (fun x => (pElt ^ n) * x) '' closedBall 0 1

theorem norm_p211 : ‖pElt‖ = (211 : ℝ)⁻¹ := by
  simpa using (Padic.norm_p (p := 211))

theorem pElt_ne_zero : pElt ≠ 0 := by
  intro h
  have := norm_p211
  rw [h, norm_zero] at this
  norm_num at this

theorem qBall_eq (n : ℕ) : qBall n = closedBall (0 : ℚ_[211]) (((211 : ℝ)⁻¹) ^ n) := by
  have hc : (pElt ^ n) ≠ 0 := pow_ne_zero _ pElt_ne_zero
  rw [qBall, image_mul_closedBall _ hc (by norm_num), norm_pow, norm_p211, mul_one]

theorem qBall_isCompact (n : ℕ) : IsCompact (qBall n) := by
  rw [qBall_eq]; exact isCompact_closedBall 0 _

theorem qBall_interior (n : ℕ) : (interior (qBall n)).Nonempty := by
  rw [qBall_eq]
  refine ⟨0, ball_subset_interior_closedBall (mem_ball_self ?_)⟩
  positivity

theorem qBall_measurable (n : ℕ) : MeasurableSet (qBall n) := by
  rw [qBall_eq]; exact measurableSet_closedBall

theorem qBall_succ (n : ℕ) :
    qBall (n + 1) = (fun x => pElt * x) '' qBall n := by
  rw [qBall, qBall, ← Set.image_comp]
  congr 1
  funext x
  simp only [Function.comp_apply, pow_succ]
  ring

theorem logVolume_qBall (n : ℕ) :
    logVolume (haarQp 211) (closedBall (0 : ℚ_[211]) 1) (qBall n)
      = -(n : ℝ) * Real.log 211 := by
  induction n with
  | zero =>
      have h0 : qBall 0 = closedBall (0 : ℚ_[211]) 1 := by
        rw [qBall_eq]; norm_num
      rw [h0, logVolume_self]; norm_num
  | succ n ih =>
      obtain ⟨hne, htop⟩ :=
        measure_pos_ne_top (haarQp 211) (qBall_isCompact n) (qBall_interior n)
      rw [qBall_succ,
        logVolume_mul_p (qBall n) (qBall_measurable n)
          (pos_iff_ne_zero.mpr hne) (lt_top_iff_ne_top.mpr htop), ih]
      push_cast
      ring

def p211QRegion : p211PacketSystem.Regions := fun _ _ => qBall 29

theorem p211_packetLogVolume (vQ : p211PacketSystem.PlaceQ)
    (j : Fin (p211PacketSystem.lstar + 1)) :
    p211PacketSystem.packetLogVolume vQ j (p211QRegion vQ j)
      = -(29 / 7) * Real.log 211 := by
  show (1 / 7 : ℝ) * logVolume (haarQp 211) (closedBall (0 : ℚ_[211]) 1) (qBall 29) + 0 = _
  rw [logVolume_qBall]
  push_cast
  ring

theorem p211_procVol :
    p211PacketSystem.procVol p211QRegion = -(29 / 7) * Real.log 211 := by
  rw [PacketSystem.procVol]
  simp only [p211_packetLogVolume, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : Fintype.card p211PacketSystem.PlaceQ = 1 := rfl
  have hl : (p211PacketSystem.lstar : ℝ) = 3 := by norm_num [p211PacketSystem]
  have hf : Fintype.card (Fin p211PacketSystem.lstar) = 3 := by
    simp [p211PacketSystem]
  rw [hc, hl, hf]
  push_cast
  ring

end CitedLV.Theorem311.P211Packet
end
