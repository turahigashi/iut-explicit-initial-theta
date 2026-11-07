import Cor312LogVolume.theorem311.P211ProcVolN
import Cor312LogVolume.theorem311.P211PacketSystemN

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211IndeterminacyOrbit

open Metric
open CitedLV.Theorem311
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211PacketN

theorem unitAutQp_qBallN (n k : ℕ) (g : Fin n → Unit → ℤ_[211]ˣ) :
    unitAutQp n g ⁻¹' qBallN n k = qBallN n k := by
  ext z
  simp only [Set.mem_preimage, qBallN, Set.mem_pi, Set.mem_univ, forall_true_left]
  refine forall_congr' fun α => ?_
  show (((g α () : ℤ_[211]) : ℚ_[211]) * z α) ∈ qBall k ↔ z α ∈ qBall k
  rw [qBall_eq, mem_closedBall_zero_iff, mem_closedBall_zero_iff,
    norm_mul, norm_padicInt_unit, one_mul]

theorem unitAutQp_image_qBallN (n k : ℕ) (g : Fin n → Unit → ℤ_[211]ˣ) :
    unitAutQp n g '' qBallN n k = qBallN n k := by
  conv_lhs => rw [← unitAutQp_qBallN n k g]
  exact Set.image_preimage_eq _ (unitAutQp n g).surjective

theorem ind2Act_qRegionN (g : p211PacketSystemN.Ind2Element) :
    p211PacketSystemN.ind2Act g qRegionN = qRegionN := by
  funext vQ j
  exact unitAutQp_image_qBallN (j.val + 1) 29 (g vQ j)

theorem ind2_orbit_qRegionN_singleton (y : p211PacketSystemN.Regions)
    (h : p211PacketSystemN.Ind2 qRegionN y) : y = qRegionN := by
  obtain ⟨g, rfl⟩ := h
  exact ind2Act_qRegionN g

theorem permAutQp_qBallN (n k : ℕ) (σ : Equiv.Perm (Fin n)) :
    permAutQp n σ ⁻¹' qBallN n k = qBallN n k := by
  ext z
  simp only [Set.mem_preimage, qBallN, Set.mem_pi, Set.mem_univ, forall_true_left]
  exact ⟨fun h α => by simpa [permAutQp] using h (σ α),
         fun h α => by simpa [permAutQp] using h (σ.symm α)⟩

theorem permAutQp_image_qBallN (n k : ℕ) (σ : Equiv.Perm (Fin n)) :
    permAutQp n σ '' qBallN n k = qBallN n k := by
  conv_lhs => rw [← permAutQp_qBallN n k σ]
  exact Set.image_preimage_eq _ (permAutQp n σ).surjective

theorem ind1Act_qRegionN (h : p211PacketSystemN.ProcessionAut) :
    h.act qRegionN = qRegionN := by
  funext vQ j
  show (h.packetAut vQ j) '' qBallN (j.val + 1) 29 = qBallN (j.val + 1) 29
  have hpa : (h.packetAut vQ j : (Fin (j.val + 1) → ℚ_[211]) → _)
      = permAutQp (j.val + 1) (h.labelPerm j) := rfl
  rw [hpa]
  exact permAutQp_image_qBallN _ _ _

theorem ind1_orbit_qRegionN_singleton (y : p211PacketSystemN.Regions)
    (hy : p211PacketSystemN.Ind1 qRegionN y) : y = qRegionN := by
  obtain ⟨h, rfl⟩ := hy
  exact ind1Act_qRegionN h

theorem indeterminacies_fix_qRegionN :
    (∀ y, p211PacketSystemN.Ind1 qRegionN y → y = qRegionN)
    ∧ (∀ y, p211PacketSystemN.Ind2 qRegionN y → y = qRegionN) :=
  ⟨ind1_orbit_qRegionN_singleton, ind2_orbit_qRegionN_singleton⟩

end CitedLV.Theorem311.P211IndeterminacyOrbit
end
