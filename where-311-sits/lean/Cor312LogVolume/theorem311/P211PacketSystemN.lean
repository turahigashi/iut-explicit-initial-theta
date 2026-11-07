import Cor312LogVolume.theorem311.P211PacketNActions

noncomputable section
namespace CitedLV.Theorem311.P211PacketN

open Metric Set MeasureTheory
open Src.IUT3.Theorem311 Src.IUT4.Proposition14ii

def p211PacketSystemN : PacketSystem where
  lstar := 3
  lstar_pos := by norm_num
  PlaceQ := Unit
  IsArch := fun _ => False
  Above := fun _ => Unit
  Packet := fun _ j => Fin (j.val + 1) → ℚ_[211]
  haar := fun _ j => muPi (j.val + 1)
  integral := fun _ _ => closedBall 0 1
  integral_isCompact := fun _ _ => isCompact_closedBall 0 1
  integral_interior_nonempty := fun _ _ =>
    ⟨0, ball_subset_interior_closedBall (mem_ball_self one_pos)⟩
  weight := fun _ j => 1 / (7 * ((j.val : ℝ) + 1))
  weight_pos := fun _ j => by positivity
  adjustment := fun _ _ => 0
  StripAut := fun _ _ => Unit
  Ism := fun _ _ => ℤ_[211]ˣ
  ism_arch_order_two := fun _ h => absurd h id
  labelAct := fun _ j σ => permAutQp (j.val + 1) σ
  stripAct := fun _ _ _ => ContinuousAddEquiv.refl _
  ismAct := fun _ j g => unitAutQp (j.val + 1) g
  labelAct_one := fun _ j => by
    apply ContinuousAddEquiv.ext
    intro z
    funext α
    rfl
  labelAct_mul := fun _ j σ τ => by
    apply ContinuousAddEquiv.ext
    intro z
    funext α
    rfl
  stripAct_one := fun _ _ => rfl
  stripAct_mul := fun _ _ _ _ => rfl
  ismAct_one := fun _ j => by
    apply ContinuousAddEquiv.ext
    intro z
    funext α
    show ((((1 : Fin (j.val + 1) → Unit → ℤ_[211]ˣ) α () : ℤ_[211]) : ℚ_[211])) * z α = z α
    simp
  ismAct_mul := fun _ j g h => by
    apply ContinuousAddEquiv.ext
    intro z
    funext α
    show (((((g * h) α () : ℤ_[211]ˣ) : ℤ_[211]) : ℚ_[211])) * z α
        = (((g α () : ℤ_[211]) : ℚ_[211])) * ((((h α () : ℤ_[211]) : ℚ_[211])) * z α)
    simp only [Pi.mul_apply, Units.val_mul, PadicInt.coe_mul]
    ring
  labelAct_integral := fun _ j σ => permAutQp_integral (j.val + 1) σ
  stripAct_integral := fun _ _ _ => rfl
  ismAct_integral := fun _ j g => unitAutQp_integral (j.val + 1) g

end CitedLV.Theorem311.P211PacketN
end
