import Cor312LogVolume.Src.IUT3.Section3Theorem311Indeterminacies
import Cor312LogVolume.Src.IUT4.Section1Proposition14iiLogUnitsVolumeQp

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.PrimePacket

open Metric Set MeasureTheory
open Src.IUT3.Theorem311
open Src.IUT4.Proposition14ii

variable (p : ℕ) [Fact p.Prime]

def primePacketSystem : PacketSystem where
  lstar := 3
  lstar_pos := by norm_num
  PlaceQ := Unit
  IsArch := fun _ => False
  Above := fun _ => Unit
  Packet := fun _ _ => ℚ_[p]
  haar := fun _ _ => haarQp p
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

theorem image_mul_closedBall
    (c : ℚ_[p]) (hc : c ≠ 0) {r : ℝ} (_hr : 0 ≤ r) :
    (fun x => c * x) '' closedBall (0 : ℚ_[p]) r =
      closedBall 0 (‖c‖ * r) := by
  ext y
  simp only [Set.mem_image, mem_closedBall_zero_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg c)
  · intro hy
    refine ⟨c⁻¹ * y, ?_, by field_simp⟩
    rw [norm_mul, norm_inv,
      inv_mul_le_iff₀ (norm_pos_iff.mpr hc)]
    exact hy

abbrev pElt : ℚ_[p] := ((p : ℕ) : ℚ_[p])

def qBall (n : ℕ) : Set ℚ_[p] :=
  (fun x => (pElt p ^ n) * x) '' closedBall 0 1

theorem norm_pElt :
    ‖pElt p‖ = (p : ℝ)⁻¹ := by
  simpa using (Padic.norm_p (p := p))

theorem pElt_ne_zero :
    pElt p ≠ 0 := by
  intro h
  have hn := norm_pElt p
  rw [h, norm_zero] at hn
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hinv : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpR
  linarith

theorem qBall_eq (n : ℕ) :
    qBall p n =
      closedBall (0 : ℚ_[p]) (((p : ℝ)⁻¹) ^ n) := by
  have hc : (pElt p ^ n) ≠ 0 :=
    pow_ne_zero _ (pElt_ne_zero p)
  rw [qBall, image_mul_closedBall p _ hc (by norm_num),
    norm_pow, norm_pElt, mul_one]

theorem qBall_isCompact (n : ℕ) :
    IsCompact (qBall p n) := by
  rw [qBall_eq]
  exact isCompact_closedBall 0 _

theorem qBall_interior (n : ℕ) :
    (interior (qBall p n)).Nonempty := by
  rw [qBall_eq]
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hr : 0 < ((p : ℝ)⁻¹) ^ n :=
    pow_pos (inv_pos.mpr hpR) n
  exact
    ⟨0, ball_subset_interior_closedBall
      (mem_ball_self hr)⟩

theorem qBall_measurable (n : ℕ) :
    MeasurableSet (qBall p n) := by
  rw [qBall_eq]
  exact measurableSet_closedBall

theorem qBall_succ (n : ℕ) :
    qBall p (n + 1) =
      (fun x => pElt p * x) '' qBall p n := by
  rw [qBall, qBall, ← Set.image_comp]
  congr 1
  funext x
  simp only [Function.comp_apply, pow_succ]
  ring

theorem logVolume_qBall (n : ℕ) :
    logVolume (haarQp p) (closedBall (0 : ℚ_[p]) 1) (qBall p n)
      = -(n : ℝ) * Real.log p := by
  induction n with
  | zero =>
      have h0 :
          qBall p 0 = closedBall (0 : ℚ_[p]) 1 := by
        rw [qBall_eq]
        norm_num
      rw [h0, logVolume_self]
      norm_num
  | succ n ih =>
      obtain ⟨hne, htop⟩ :=
        measure_pos_ne_top (haarQp p)
          (qBall_isCompact p n) (qBall_interior p n)
      rw [qBall_succ,
        logVolume_mul_p (p := p) (qBall p n)
          (qBall_measurable p n)
          (pos_iff_ne_zero.mpr hne)
          (lt_top_iff_ne_top.mpr htop),
        ih]
      push_cast
      ring

def primeQRegion : (primePacketSystem p).Regions :=
  fun _ _ => qBall p 29

theorem prime_packetLogVolume
    (vQ : (primePacketSystem p).PlaceQ)
    (j : Fin ((primePacketSystem p).lstar + 1)) :
    (primePacketSystem p).packetLogVolume vQ j
        (primeQRegion p vQ j)
      =
    -(29 / 7) * Real.log p := by
  show
    (1 / 7 : ℝ) *
        logVolume (haarQp p)
          (closedBall (0 : ℚ_[p]) 1) (qBall p 29) + 0
      = _
  rw [logVolume_qBall]
  push_cast
  ring

theorem prime_procVol :
    (primePacketSystem p).procVol (primeQRegion p)
      =
    -(29 / 7) * Real.log p := by
  rw [PacketSystem.procVol]
  simp only [prime_packetLogVolume,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc :
      Fintype.card (primePacketSystem p).PlaceQ = 1 := rfl
  have hl :
      ((primePacketSystem p).lstar : ℝ) = 3 := by
    norm_num [primePacketSystem]
  have hf :
      Fintype.card (Fin (primePacketSystem p).lstar) = 3 := by
    simp [primePacketSystem]
  rw [hc, hl, hf]
  push_cast
  ring

end CitedLV.Theorem311.PrimePacket
end
