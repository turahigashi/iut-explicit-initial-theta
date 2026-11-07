import Cor312LogVolume.theorem311.TensorIntegralLattice
import Cor312LogVolume.theorem311.FiniteSemisimpleRegularNormalization
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.PrincipalIdealDomain

noncomputable section
set_option autoImplicit false
namespace CitedLV.Theorem311.TensorNormalizationPrincipal

open Src.IUT4.Proposition11
open CitedLV.Theorem311.TensorIntegralLattice
open CitedLV.Theorem311.PadicNormIntegerRing
open CitedLV.Theorem311.PadicNormedRamification
open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (p : ℕ) [Fact p.Prime]

theorem packet_isReduced {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Type*)
    [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
    [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
    [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)] :
    IsReduced (Packet p L) := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
    fun i => normIntegers_discreteValuationRing p (L i)
  constructor
  intro z hz
  let b := packetDualBasis ℤ_[p] ℚ_[p] L (fun i => Integers (L i))
  have hc : ∀ n, b.repr z n = 0 := by
    intro n
    rw [packetDual_repr_eq_trace]
    exact (Algebra.isNilpotent_trace_of_isNilpotent
      ((Commute.all z _).isNilpotent_mul_right hz)).eq_zero
  calc
    z = ∑ n, b.repr z n • b n := (b.sum_repr z).symm
    _ = 0 := by simp only [hc, zero_smul, Finset.sum_const_zero]

private theorem finite_reduced_normalization_principal
    (A : Type*) [CommRing A] [Algebra ℚ_[p] A] [FiniteDimensional ℚ_[p] A]
    [IsReduced A] [Algebra ℤ_[p] A] [IsScalarTower ℤ_[p] ℚ_[p] A] :
    IsPrincipalIdealRing (integralClosure ℤ_[p] A) := by
  classical
  letI : IsArtinianRing A := IsArtinianRing.of_finite ℚ_[p] A
  let J := MaximalSpectrum A
  let E : J → Type _ := fun j => A ⧸ j.asIdeal
  letI : Fintype J := Fintype.ofFinite J
  letI : ∀ j, Field (E j) := fun j => Ideal.Quotient.field j.asIdeal
  let e : A ≃ₐ[ℚ_[p]] (∀ j, E j) := (IsArtinianRing.equivPi A).restrictScalars ℚ_[p]
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j =>
    Module.Finite.of_surjective ((Pi.evalAlgHom ℚ_[p] E j).comp e.toAlgHom).toLinearMap
      ((Function.surjective_eval j).comp e.surjective)
  letI : ∀ j, NontriviallyNormedField (E j) := fun j =>
    spectralNorm.nontriviallyNormedField ℚ_[p] (E j)
  letI : ∀ j, NormedAlgebra ℚ_[p] (E j) := fun j =>
    spectralNorm.normedAlgebra ℚ_[p] (E j)
  letI : ∀ j, IsUltrametricDist (E j) := fun _ => IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : ∀ j, IsDiscreteValuationRing (Integers (E j)) :=
    fun j => normIntegers_discreteValuationRing p (E j)
  let f₁ := (e.restrictScalars ℤ_[p]).mapIntegralClosure
  let f₂ : integralClosure ℤ_[p] (∀ j, E j) ≃ₐ[ℤ_[p]]
      componentwiseIntegralOrder ℤ_[p] E :=
    Subalgebra.equivOfEq _ _ (componentwiseIntegralOrder_eq_integralClosure
      (R := ℤ_[p]) (A := E)).symm
  let f₃ := componentwiseIntegralOrderEquivPi (R := ℤ_[p]) (A := E)
  let f₄ : (∀ j, integralClosure ℤ_[p] (E j)) ≃ₐ[ℤ_[p]] (∀ j, Integers (E j)) :=
    AlgEquiv.piCongrRight fun j =>
      IsIntegralClosure.equiv ℤ_[p] (integralClosure ℤ_[p] (E j)) (E j) (Integers (E j))
  let f := f₁.trans (f₂.trans (f₃.trans f₄))
  exact IsPrincipalIdealRing.of_surjective f.symm.toRingHom f.symm.surjective

theorem packet_normalization_isPrincipalIdealRing
    {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Type*)
    [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
    [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
    [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)] :
    IsPrincipalIdealRing (integralClosure ℤ_[p] (Packet p L)) := by
  letI := packet_isReduced p L
  exact finite_reduced_normalization_principal p (Packet p L)

end CitedLV.Theorem311.TensorNormalizationPrincipal
