import Cor312LogVolume.thetalink.GaussianThetaLogReadout
import Cor312LogVolume.theorem311.TensorFactorHaarCharacter
import Cor312LogVolume.Src.IUT3.Section3Proposition35iiUpperSemiCompat

noncomputable section
set_option autoImplicit false

namespace CitedLV.ThetaLink.GaussianThetaTensorReadout

open CitedLV.Theorem311
open CitedLV.Theorem311.TensorIntegralLattice
open CitedLV.Theorem311.TensorFactorHaarCharacter
open CitedLV.ThetaLink.GaussianMonoidFromThetaValues
open CitedLV.ThetaLink.GaussianThetaLogReadout
open Src.EtTh.ThetaValueArithmetic
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
variable {V : Type*} (K : V → Type*)
  [∀ v, NormedField (K v)] [∀ v, NormedAlgebra ℚ_[p] (K v)]

def choiceProjection (stage : ℕ) (choice : Fin (stage + 1) → V) :
    Src.IUT3.Proposition35ii.Packet p K stage →ₗ[ℚ_[p]]
      TensorIntegralLattice.Packet p (fun a => K (choice a)) :=
  PiTensorProduct.map fun a => LinearMap.proj (choice a)

theorem choiceProjection_tprod (stage : ℕ) (choice : Fin (stage + 1) → V)
    (x : Fin (stage + 1) → ((v : V) → K v)) :
    choiceProjection p K stage choice (PiTensorProduct.tprod ℚ_[p] x) =
      PiTensorProduct.tprod ℚ_[p] (fun a => x a (choice a)) :=
  PiTensorProduct.map_tprod _ _

def fullFactorUnit (stage : ℕ) (slot : Fin (stage + 1))
    (u : (v : V) → (K v)ˣ) :
    (Src.IUT3.Proposition35ii.Packet p K stage)ˣ :=
  Units.map (PiTensorProduct.singleAlgHom
    (R := ℚ_[p]) (A := fun _ : Fin (stage + 1) => (v : V) → K v) slot).toMonoidHom
    (MulEquiv.piUnits.symm u)

private theorem choiceProjection_fullFactorUnit_tprod
    (stage : ℕ) (choice : Fin (stage + 1) → V) (slot : Fin (stage + 1))
    (u : (v : V) → (K v)ˣ) (x : Fin (stage + 1) → ((v : V) → K v)) :
    choiceProjection p K stage choice
        ((fullFactorUnit p K stage slot u :
          Src.IUT3.Proposition35ii.Packet p K stage) * PiTensorProduct.tprod ℚ_[p] x) =
      (factorUnit p (fun a => K (choice a)) slot (u (choice slot)) :
        TensorIntegralLattice.Packet p (fun a => K (choice a))) *
          choiceProjection p K stage choice (PiTensorProduct.tprod ℚ_[p] x) := by
  change PiTensorProduct.map (fun a => LinearMap.proj (choice a))
      ((PiTensorProduct.tprod ℚ_[p] (Pi.mulSingle slot (fun v => (u v : K v)))) *
        PiTensorProduct.tprod ℚ_[p] x) =
    (PiTensorProduct.tprod ℚ_[p] (Pi.mulSingle slot (u (choice slot) : K (choice slot)))) *
      PiTensorProduct.map (fun a => LinearMap.proj (choice a)) (PiTensorProduct.tprod ℚ_[p] x)
  rw [PiTensorProduct.tprod_mul_tprod, PiTensorProduct.map_tprod,
    PiTensorProduct.map_tprod, PiTensorProduct.tprod_mul_tprod]
  congr 1
  funext a
  by_cases ha : a = slot
  · subst a
    simp
  · simp [Pi.mulSingle_eq_of_ne ha]

theorem choiceProjection_fullFactorUnit_mul
    (stage : ℕ) (choice : Fin (stage + 1) → V) (slot : Fin (stage + 1))
    (u : (v : V) → (K v)ˣ)
    (x : Src.IUT3.Proposition35ii.Packet p K stage) :
    choiceProjection p K stage choice
        ((fullFactorUnit p K stage slot u :
          Src.IUT3.Proposition35ii.Packet p K stage) * x) =
      (factorUnit p (fun a => K (choice a)) slot (u (choice slot)) :
        TensorIntegralLattice.Packet p (fun a => K (choice a))) *
          choiceProjection p K stage choice x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    have hr : r • PiTensorProduct.tprod ℚ_[p] x =
        PiTensorProduct.tprod ℚ_[p] (Function.update x slot (r • x slot)) := by
      symm
      rw [MultilinearMap.map_update_smul, Function.update_eq_self]
    rw [hr]
    exact choiceProjection_fullFactorUnit_tprod p K stage choice slot u _
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]

section Haar

variable [∀ v, IsUltrametricDist (K v)] [∀ v, FiniteDimensional ℚ_[p] (K v)]
  [∀ v, ProperSpace (K v)]
  [∀ v, Algebra ℤ_[p] (K v)] [∀ v, IsScalarTower ℤ_[p] ℚ_[p] (K v)]

theorem gaussian_choice_factor_normalized_shift
    (stage : ℕ) (choice : Fin (stage + 1) → V) (slot : Fin (stage + 1))
    (s i : (K (choice slot))ˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell : ℕ) (hell : 0 < ell)
    (ξ : Labels ell → (K (choice slot))ˣ) (hξ : ξ ∈ actualProfiles s i ell)
    (label : Labels ell) (u : normOneUnits (K (choice slot))) (n : ℕ)
    (A U : NormalizedHaarRegion (TensorIntegralLattice.Packet p (fun a => K (choice a)))) :
    (normalizedHaarLogVolume A
        (factorRegion p (fun a => K (choice a)) slot
          ((u : (K (choice slot))ˣ) * ξ label ^ n) U) -
      normalizedHaarLogVolume A U) /
        (Module.finrank ℚ_[p] (TensorIntegralLattice.Packet p (fun a => K (choice a))) : ℝ) =
      (n : ℝ) * (((label.val : ℝ) + 1) ^ 2 / (2 * (ell : ℝ))) *
        Real.log ‖((s ^ 2 : (K (choice slot))ˣ) : K (choice slot))‖ := by
  have hd : (Module.finrank ℚ_[p]
      (TensorIntegralLattice.Packet p (fun a => K (choice a))) : ℝ) ≠ 0 := by
    exact_mod_cast (packet_finrank_pos p (fun a => K (choice a))).ne'
  rw [logVolume_factorRegion, add_sub_cancel_right, mul_div_cancel_left₀ _ hd]
  exact gaussian_log_norm s i hi h ell hell ξ hξ u n label

theorem gaussian_source_stage_factor_normalized_shift
    (ell : ℕ) (hell : 0 < ell) (label : Labels ell)
    (choice : Fin (label.val + 1 + 1) → V) (slot : Fin (label.val + 1 + 1))
    (s i : (K (choice slot))ˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i)
    (ξ : Labels ell → (K (choice slot))ˣ) (hξ : ξ ∈ actualProfiles s i ell)
    (u : normOneUnits (K (choice slot))) (n : ℕ)
    (A U : NormalizedHaarRegion (TensorIntegralLattice.Packet p (fun a => K (choice a)))) :
    (normalizedHaarLogVolume A
        (factorRegion p (fun a => K (choice a)) slot
          ((u : (K (choice slot))ˣ) * ξ label ^ n) U) -
      normalizedHaarLogVolume A U) /
        (Module.finrank ℚ_[p] (TensorIntegralLattice.Packet p (fun a => K (choice a))) : ℝ) =
      (n : ℝ) * (((label.val : ℝ) + 1) ^ 2 / (2 * (ell : ℝ))) *
        Real.log ‖((s ^ 2 : (K (choice slot))ˣ) : K (choice slot))‖ :=
  gaussian_choice_factor_normalized_shift p K (label.val + 1) choice slot
    s i hi h ell hell ξ hξ label u n A U

end Haar

end CitedLV.ThetaLink.GaussianThetaTensorReadout
