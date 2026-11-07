import Cor312LogVolume.theorem311.P211PacketNDim

noncomputable section
namespace CitedLV.Theorem311.P211PacketN

open Metric Set MeasureTheory
open Src.IUT3.Theorem311 Src.IUT4.Proposition14ii

def permAutQp (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (Fin k → ℚ_[211]) ≃ₜ+ (Fin k → ℚ_[211]) where
  toFun z := z ∘ σ.symm
  invFun z := z ∘ σ
  left_inv z := by ext α; simp
  right_inv z := by ext α; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

theorem permAutQp_integral (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    permAutQp k σ ⁻¹' closedBall (0 : Fin k → ℚ_[211]) 1
      = closedBall 0 1 := by
  ext z
  simp only [Set.mem_preimage, mem_closedBall_zero_iff,
    pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
  exact ⟨fun h α => by simpa [permAutQp] using h (σ α), fun h α => h _⟩

theorem norm_padicInt_unit (u : ℤ_[211]ˣ) : ‖((u : ℤ_[211]) : ℚ_[211])‖ = 1 := by
  have h : IsUnit (u : ℤ_[211]) := u.isUnit
  rw [PadicInt.isUnit_iff] at h
  simpa using h

def unitAutQp (k : ℕ) (g : Fin k → Unit → ℤ_[211]ˣ) :
    (Fin k → ℚ_[211]) ≃ₜ+ (Fin k → ℚ_[211]) where
  toFun z α := ((g α () : ℤ_[211]) : ℚ_[211]) * z α
  invFun z α := (((g α ())⁻¹ : ℤ_[211]ˣ) : ℚ_[211]) * z α
  left_inv z := by
    ext α
    simp only
    rw [← mul_assoc]
    norm_cast
    simp
  right_inv z := by
    ext α
    simp only
    rw [← mul_assoc]
    norm_cast
    simp
  map_add' z w := by ext α; simp [mul_add]
  continuous_toFun := continuous_pi fun α => continuous_const.mul (continuous_apply α)
  continuous_invFun := continuous_pi fun α => continuous_const.mul (continuous_apply α)

theorem unitAutQp_integral (k : ℕ) (g : Fin k → Unit → ℤ_[211]ˣ) :
    unitAutQp k g ⁻¹' closedBall (0 : Fin k → ℚ_[211]) 1
      = closedBall 0 1 := by
  ext z
  simp only [Set.mem_preimage, mem_closedBall_zero_iff,
    pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
  refine forall_congr' fun α => ?_
  show ‖((g α () : ℤ_[211]) : ℚ_[211]) * z α‖ ≤ 1 ↔ ‖z α‖ ≤ 1
  rw [norm_mul, norm_padicInt_unit, one_mul]

end CitedLV.Theorem311.P211PacketN
end
