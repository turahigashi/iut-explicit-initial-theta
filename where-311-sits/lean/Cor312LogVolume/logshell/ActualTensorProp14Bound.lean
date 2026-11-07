import Cor312LogVolume.logshell.ActualTensorHaarNumericalBound
import Cor312LogVolume.Src.IUT4.Section1Proposition14iNormalizedLogVolume

noncomputable section
set_option autoImplicit false

namespace CitedLV.ActualTensorProp14Bound

open Src.IUT4.Proposition12i Src.IUT4.Proposition12ii
open Src.IUT4.Proposition14i
open CitedLV.Theorem311 CitedLV.Theorem311.TensorIntegralLattice
open CitedLV.Theorem311.PadicNormIntegerRing
open CitedLV.Theorem311.PadicNormedRamification
open CitedLV.Theorem311.PadicNormDifferent
open CitedLV.LogShellAmbientExtension CitedLV.ActualTensorHaarBound
open CitedLV.ActualTensorHaarNumericalBound

variable (p : ℕ) [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Type*)
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, CompleteSpace (L i)] [∀ i, ProperSpace (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

theorem actual_tensor_prop14iii_second
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)
    (i₀ : ι) (k : ℤ) (Istar : Finset ι)
    (hIstar : ∀ i ∉ Istar, (finiteExtensionRamification p (L i)).e + 2 ≤ p) :
    letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
      fun i => normIntegers_discreteValuationRing p (L i)
    let R := fun i => finiteExtensionRamification p (L i)
    let Δ := (actualDifferentData p L).val
    normalizedHaarLogVolume (integralAnchor p L) (sourceRegion p L e i₀ k) /
        (Module.finrank ℚ_[p] (Packet p L) : ℝ) ≤
      (-((k : ℝ) / (R i₀).e) + dI p Δ + 1) * Real.log (p : ℝ) +
        ∑ i ∈ Istar, (3 + Real.log (R i).e) := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
    fun i => normIntegers_discreteValuationRing p (L i)
  let R := fun i => finiteExtensionRamification p (L i)
  let Δ := (actualDifferentData p L).val
  apply (actual_tensor_normalizedLogVolume_le p L e i₀ k).trans
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have h := Src.CoreLayer.LogVol.second_inequality Istar (p : ℝ) hp2
    (fun i => ((R i).e : ℝ)) (fun i => aExp p (R i).e) (fun i => bExp p (R i).e)
    (fun i => (Δ.D i : ℝ) / (R i).e) ((k : ℝ) / (R i₀).e)
    (fun i => show (0 : ℝ) < (R i).e by exact_mod_cast (R i).e_pos)
    (fun i _ => aExp_sub_le p (R i).e (R i).e_pos)
    (fun i _ => bExp_add_mul_log_le p (R i).e (R i).e_pos)
    (fun i hi => aExp_add_bExp_of_small p (R i).e (R i).e_pos (hIstar i hi))
  simpa only [boundExponent, dI, aI, bI, neg_sub] using h

end CitedLV.ActualTensorProp14Bound
