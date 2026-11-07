import Cor312LogVolume.independence.Cor312SourceBoundTheory

set_option autoImplicit false
noncomputable section

namespace CitedLV.Independence.Cor312SourceBoundIsm

open Metric
open Src.IUT3.Theorem311
open Src.IUT4.Proposition14ii
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211ComponentCTraceBridge
open CitedLV.Theorem311.P211SourceFacingSimultaneousXiF
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Independence.Cor312Cited
open CitedLV.Independence.Cor312SourceBound

def mulEquiv (c : ℚ_[211]) (hc : c ≠ 0) : ℚ_[211] ≃ₜ+ ℚ_[211] where
  toFun x := c * x
  invFun x := c⁻¹ * x
  left_inv x := by
    show c⁻¹ * (c * x) = x
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  right_inv x := by
    show c * (c⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  map_add' x y := mul_add c x y
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem mulEquiv_apply (c : ℚ_[211]) (hc : c ≠ 0) (x : ℚ_[211]) : mulEquiv c hc x = c * x := rfl

theorem unit_coe_ne_zero (u : ℤ_[211]ˣ) : ((u : ℤ_[211]) : ℚ_[211]) ≠ 0 := by
  intro h
  have h1 : ‖((u : ℤ_[211]) : ℚ_[211])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.isUnit_iff.mp u.isUnit
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem norm_unit_coe (u : ℤ_[211]ˣ) : ‖((u : ℤ_[211]) : ℚ_[211])‖ = 1 := by
  rw [PadicInt.padic_norm_e_of_padicInt]
  exact PadicInt.isUnit_iff.mp u.isUnit

def unitProd {n : ℕ} (g : Fin n → Unit → ℤ_[211]ˣ) : ℤ_[211]ˣ := ∏ α, g α ()

def p211PacketSystemIsm : PacketSystem where
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
  Ism := fun _ _ => ℤ_[211]ˣ
  ism_arch_order_two := fun _ h => absurd h id
  labelAct := fun _ _ _ => ContinuousAddEquiv.refl _
  stripAct := fun _ _ _ => ContinuousAddEquiv.refl _
  ismAct := fun _ _ g => mulEquiv ((unitProd g : ℤ_[211]) : ℚ_[211]) (unit_coe_ne_zero _)
  labelAct_one := fun _ _ => rfl
  labelAct_mul := fun _ _ _ _ => rfl
  stripAct_one := fun _ _ => rfl
  stripAct_mul := fun _ _ _ _ => rfl
  ismAct_one := fun _ _ => by
    ext x
    show ((unitProd (1 : Fin _ → Unit → ℤ_[211]ˣ) : ℤ_[211]) : ℚ_[211]) * x = x
    simp [unitProd]
  ismAct_mul := fun _ _ g h => by
    ext x
    show ((unitProd (g * h) : ℤ_[211]) : ℚ_[211]) * x
      = ((unitProd g : ℤ_[211]) : ℚ_[211]) * (((unitProd h : ℤ_[211]) : ℚ_[211]) * x)
    simp only [unitProd, Pi.mul_apply, Finset.prod_mul_distrib, Units.val_mul, PadicInt.coe_mul]
    ring
  labelAct_integral := fun _ _ _ => rfl
  stripAct_integral := fun _ _ _ => rfl
  ismAct_integral := fun _ _ g => by
    ext x
    show ((unitProd g : ℤ_[211]) : ℚ_[211]) * x ∈ closedBall (0 : ℚ_[211]) 1 ↔ x ∈ closedBall 0 1
    simp only [mem_closedBall_zero_iff, norm_mul, norm_unit_coe, one_mul]

theorem ind2_nontrivial :
    ∃ (g : p211PacketSystemIsm.Ind2Element) (x : p211PacketSystemIsm.Regions),
      p211PacketSystemIsm.ind2Act g x ≠ x := by
  let g : p211PacketSystemIsm.Ind2Element := fun _ _ _ _ => (-1 : ℤ_[211]ˣ)
  let x : p211PacketSystemIsm.Regions := fun _ _ => ({1} : Set ℚ_[211])
  refine ⟨g, x, ?_⟩
  intro h
  have h0 := congrFun (congrFun h ()) 0
  have hmem : (1 : ℚ_[211]) ∈ p211PacketSystemIsm.ind2Act g x () 0 := by
    rw [h0]
    show (1 : ℚ_[211]) ∈ ({1} : Set ℚ_[211])
    rfl
  obtain ⟨y, hy, hyx⟩ := hmem
  have hy1 : y = (1 : ℚ_[211]) := hy
  subst hy1
  have : ((unitProd (fun (_ : Fin 1) (_ : Unit) => (-1 : ℤ_[211]ˣ)) : ℤ_[211]) : ℚ_[211]) * 1 = 1 := hyx
  simp [unitProd] at this
  norm_num at this

theorem ind2Act_ball (g : p211PacketSystemIsm.Ind2Element) (f : ℕ → ℕ) :
    p211PacketSystemIsm.ind2Act g (fun _ j => qBall (f j.val)) = fun _ j => qBall (f j.val) := by
  funext vQ j
  exact unit_mul_qBall _ (norm_unit_coe _) _

theorem act_id' (h : p211PacketSystemIsm.ProcessionAut) (x : p211PacketSystemIsm.Regions) : h.act x = x := by
  funext vQ j
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem procVol_eq (x : p211PacketSystemIsm.Regions) :
    p211PacketSystemIsm.procVol x = p211PacketSystem.procVol x := rfl

theorem sourceThetaPilot_ball :
    (sourceThetaPilot : p211PacketSystemIsm.Regions) = fun _ j => qBall (29 * (j.val * j.val)) := by
  funext vQ j
  exact sourceThetaPilot_eq vQ j

def sourceBoundIsmTheory : CitedTheory where
  S := p211PacketSystemIsm
  thetaPilot := sourceThetaPilot
  qPilot := sourceQPilot
  container := sourceThetaPilot
  Possible := {sourceThetaPilot}
  IsLambdaO := sourceBoundTheory.IsLambdaO
  hull := sourceThetaPilot
  theta_possible := rfl
  ind1_closed := by
    rintro x rfl y ⟨h, rfl⟩
    exact act_id' h _
  ind2_closed := by
    rintro x rfl y ⟨g, rfl⟩
    show p211PacketSystemIsm.ind2Act g sourceThetaPilot = sourceThetaPilot
    rw [sourceThetaPilot_ball]
    exact ind2Act_ball g (fun m => 29 * (m * m))
  ind3_bound := sourceBoundTheory.ind3_bound
  ind3_saturated := sourceBoundTheory.ind3_saturated
  container_le_integral := sourceBoundTheory.container_le_integral
  hull_isLambdaO := sourceBoundTheory.hull_isLambdaO
  hull_contains := sourceBoundTheory.hull_contains
  hull_minimal := sourceBoundTheory.hull_minimal
  hull_le_integral := sourceBoundTheory.hull_le_integral
  q_hasVolume := sourceBoundTheory.q_hasVolume
  q_le_integral := sourceBoundTheory.q_le_integral
  q_neg := sourceBoundTheory.q_neg
  linkScale := 3 / 14
  linkScale_pos := by norm_num
  link_degree := sourceBoundTheory.link_degree
  ipl := sourceBoundTheory.ipl

theorem sourceBoundIsm_weakSHE : sourceBoundIsmTheory.WeakSHE :=
  ⟨fun c => {c}, rfl, by
    rintro c x rfl
    exact fun _ _ => subset_rfl⟩

theorem sourceBoundIsm_not_conclusion : ¬ sourceBoundIsmTheory.Conclusion :=
  sourceBound_not_conclusion

end CitedLV.Independence.Cor312SourceBoundIsm

section Check
open CitedLV.Independence.Cor312SourceBoundIsm
end Check
