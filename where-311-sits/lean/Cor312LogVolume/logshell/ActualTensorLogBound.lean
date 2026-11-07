import Cor312LogVolume.logshell.LogShellTensorAction
import Cor312LogVolume.theorem311.PadicNormDifferent

noncomputable section
set_option autoImplicit false

namespace CitedLV.ActualTensorLogBound

open Src.IUT4.Proposition12i Src.IUT4.Proposition12ii
open CitedLV.Theorem311.PadicNormIntegerRing
open CitedLV.Theorem311.PadicNormedRamification
open CitedLV.Theorem311.PadicNormDifferent
open CitedLV.LogShellAmbientExtension CitedLV.LogShellTensorAction
open scoped TensorProduct nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (p : ℕ) [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Type*)
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, CompleteSpace (L i)] [∀ i, ProperSpace (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

theorem actual_tensor_bound
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)
    (i₀ : ι) (k : ℤ) (z : ⨂[ℚ_[p]] i, L i) (hz : IsIntegral ℤ_[p] z) :
    letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
      fun i => normIntegers_discreteValuationRing p (L i)
    let R := fun i => finiteExtensionRamification p (L i)
    let Δ := (actualDifferentData p L).val
    (∃ w ∈ logUnits p L, tensorEquiv p e (piAt p R i₀ k * z) =
      ((p : ℚ_[p]) ^ ⌊(k : ℝ) / (R i₀).e - dI p Δ - aI p R⌋) • w) ∧
    ∃ v, IsIntegral ℤ_[p] v ∧ tensorEquiv p e (piAt p R i₀ k * z) =
      ((p : ℚ_[p]) ^ ⌊(k : ℝ) / (R i₀).e - dI p Δ - aI p R⌋) • (piNegB p R * v) := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
    fun i => normIntegers_discreteValuationRing p (L i)
  exact shell_tensor_prop12ii p e (fun i => finiteExtensionRamification p (L i))
    (actualDifferentData p L).val i₀ k z hz

end CitedLV.ActualTensorLogBound
