import Cor312LogVolume.theorem311.TensorIntegralLattice
import Cor312LogVolume.theorem311.FiniteVectorHaarCharacter
import Cor312LogVolume.theorem311.FinitePadicHaarNorm

noncomputable section
set_option autoImplicit false

namespace CitedLV.Theorem311.TensorFactorHaarCharacter

open TensorIntegralLattice
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Type*)
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, ProperSpace (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

def factorHom (i : ι) : L i →ₐ[ℚ_[p]] Packet p L :=
  PiTensorProduct.singleAlgHom (R := ℚ_[p]) (A := L) i

def factorUnit (i : ι) (u : (L i)ˣ) : (Packet p L)ˣ :=
  Units.map (factorHom p L i).toMonoidHom u

def factorRegion (i : ι) (u : (L i)ˣ) (U : NormalizedHaarRegion (Packet p L)) :
    NormalizedHaarRegion (Packet p L) :=
  mapNormalizedHaarRegion
    ((factorUnit p L i u).mulLeftLinearEquiv ℚ_[p] (Packet p L)).toContinuousLinearEquiv.toContinuousAddEquiv U

theorem logVolume_factorRegion (A U : NormalizedHaarRegion (Packet p L))
    (i : ι) (u : (L i)ˣ) :
    normalizedHaarLogVolume A (factorRegion p L i u U) =
      (Module.finrank ℚ_[p] (Packet p L) : ℝ) * Real.log ‖(u : L i)‖ +
        normalizedHaarLogVolume A U := by
  letI : NontriviallyNormedField (L i) :=
    { (inferInstance : NormedField (L i)) with
      non_trivial := by
        obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := ℚ_[p])
        exact ⟨algebraMap ℚ_[p] (L i) x, by simpa only [norm_algebraMap'] using hx⟩ }
  letI : IsModuleTopology ℚ_[p] (Packet p L) := isModuleTopologyOfFiniteDimensional
  letI : Algebra (L i) (Packet p L) := (factorHom p L i).toAlgebra
  letI : IsScalarTower ℚ_[p] (L i) (Packet p L) :=
    IsScalarTower.of_algebraMap_eq' (factorHom p L i).comp_algebraMap.symm
  letI : FiniteDimensional (L i) (Packet p L) :=
    Module.Finite.of_restrictScalars_finite ℚ_[p] (L i) (Packet p L)
  letI : IsTopologicalRing (Packet p L) :=
    IsModuleTopology.isTopologicalRing ℚ_[p] (Packet p L)
  letI : ContinuousSMul (L i) (Packet p L) := ⟨by
    simpa only [Algebra.smul_def] using
      ((factorHom p L i).toLinearMap.continuous_of_finiteDimensional.comp continuous_fst).mul
        continuous_snd⟩
  have heq : factorRegion p L i u U =
      FiniteVectorHaarCharacter.scalarRegion (L i) (Packet p L) u U := by
    apply Subtype.ext
    rfl
  rw [heq, FiniteVectorHaarCharacter.logVolume_scalarRegion,
    FinitePadicHaarNorm.log_character_eq_degree_mul_log_norm p (L i)]
  have hd : (Module.finrank (L i) (Packet p L) : ℝ) * (Module.finrank ℚ_[p] (L i) : ℝ) =
      (Module.finrank ℚ_[p] (Packet p L) : ℝ) := by
    rw [mul_comm]
    exact_mod_cast Module.finrank_mul_finrank ℚ_[p] (L i) (Packet p L)
  rw [← mul_assoc, hd]

def unitRegion (u : (Packet p L)ˣ) (U : NormalizedHaarRegion (Packet p L)) :
    NormalizedHaarRegion (Packet p L) :=
  mapNormalizedHaarRegion
    (u.mulLeftLinearEquiv ℚ_[p] (Packet p L)).toContinuousLinearEquiv.toContinuousAddEquiv U

theorem unitRegion_mul (u v : (Packet p L)ˣ) (U : NormalizedHaarRegion (Packet p L)) :
    unitRegion p L (u * v) U = unitRegion p L u (unitRegion p L v U) := by
  apply Subtype.ext
  change (fun x => ((u * v : (Packet p L)ˣ) : Packet p L) * x) '' U.val =
    (fun x => (u : Packet p L) * x) '' ((fun x => (v : Packet p L) * x) '' U.val)
  rw [Set.image_image]
  congr 1
  funext x
  exact mul_assoc _ _ _

theorem unitRegion_one (U : NormalizedHaarRegion (Packet p L)) :
    unitRegion p L 1 U = U := by
  apply Subtype.ext
  change (fun x : Packet p L => 1 * x) '' U.val = U.val
  simp

theorem logVolume_productRegion (A U : NormalizedHaarRegion (Packet p L))
    (s : Finset ι) (u : ∀ i, (L i)ˣ) :
    normalizedHaarLogVolume A (unitRegion p L (∏ i ∈ s, factorUnit p L i (u i)) U) =
      (Module.finrank ℚ_[p] (Packet p L) : ℝ) * (∑ i ∈ s, Real.log ‖(u i : L i)‖) +
        normalizedHaarLogVolume A U := by
  induction s using Finset.induction_on with
  | empty => simp [unitRegion_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, unitRegion_mul]
    change normalizedHaarLogVolume A
      (factorRegion p L i (u i) (unitRegion p L (∏ j ∈ s, factorUnit p L j (u j)) U)) = _
    rw [logVolume_factorRegion, ih, Finset.sum_insert hi]
    ring

theorem product_factorUnit_val (u : ∀ i, (L i)ˣ) :
    ((∏ i, factorUnit p L i (u i) : (Packet p L)ˣ) : Packet p L) =
      PiTensorProduct.tprod ℚ_[p] (fun i => (u i : L i)) := by
  rw [Units.coe_prod]
  change (∏ i, (PiTensorProduct.singleAlgHom (R := ℚ_[p]) (A := L) i) (u i)) = _
  simp only [PiTensorProduct.singleAlgHom_apply, MonoidHom.mulSingle_apply]
  rw [← PiTensorProduct.tprod_prod, Finset.univ_prod_mulSingle]

theorem packet_finrank_pos : 0 < Module.finrank ℚ_[p] (Packet p L) := by
  let b : Module.Basis (∀ i, Fin (Module.finrank ℚ_[p] (L i))) ℚ_[p] (Packet p L) :=
    Basis.piTensorProduct (fun i => Module.finBasis ℚ_[p] (L i))
  let j : ∀ i, Fin (Module.finrank ℚ_[p] (L i)) := fun i => ⟨0, Module.finrank_pos⟩
  letI : Nontrivial (Packet p L) := ⟨⟨b j, 0, b.ne_zero j⟩⟩
  exact Module.finrank_pos

end CitedLV.Theorem311.TensorFactorHaarCharacter
