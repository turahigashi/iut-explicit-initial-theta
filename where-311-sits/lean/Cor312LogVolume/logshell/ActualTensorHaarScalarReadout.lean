import Cor312LogVolume.logshell.ActualTensorHaarBound
import Cor312LogVolume.theorem311.FiniteVectorHaarCharacter
import Cor312LogVolume.theorem311.PadicPrimeHaarCharacter

noncomputable section
set_option autoImplicit false

namespace CitedLV.ActualTensorHaarScalarReadout

open Src.IUT4.Proposition12i Src.IUT4.Proposition12ii
open CitedLV.Theorem311 CitedLV.Theorem311.TensorIntegralLattice
open CitedLV.Theorem311.PadicNormIntegerRing
open CitedLV.Theorem311.PadicNormedRamification
open CitedLV.LogShellAmbientExtension CitedLV.ActualTensorHaarBound
open CitedLV.Theorem311.FiniteVectorHaarCharacter
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Type*)
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, CompleteSpace (L i)] [∀ i, ProperSpace (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

private abbrev R := fun i => finiteExtensionRamification p (L i)

private theorem correction_isUnit : IsUnit (piNegB p (R p L) : Packet p L) := by
  apply IsUnit.map (PiTensorProduct.tprodMonoidHom (A := L) ℚ_[p])
  apply Pi.isUnit_iff.mpr
  exact fun i => isUnit_iff_ne_zero.mpr (zpow_ne_zero _ (pi_ne_zero p (R p L i)))

def correctionEquiv : Packet p L ≃ₗ[ℚ_[p]] Packet p L :=
  (correction_isUnit p L).unit.mulLeftLinearEquiv ℚ_[p] (Packet p L)

theorem correctionEquiv_apply (x : Packet p L) :
    correctionEquiv p L x = Mul.mul (α := Packet p L) (piNegB p (R p L)) x := by
  simp [correctionEquiv, IsUnit.unit_spec]
  rfl

def correctionRegion : NormalizedHaarRegion (Packet p L) :=
  mapNormalizedHaarRegion (correctionEquiv p L).toContinuousLinearEquiv.toContinuousAddEquiv
    (integralAnchor p L)

theorem boundRegion_eq_scalar_correction (i₀ : ι) (k : ℤ) :
    boundRegion p L i₀ k = scalarRegion ℚ_[p] (Packet p L)
      (padicPrimeUnit p ^ boundExponent p L i₀ k) (correctionRegion p L) := by
  apply Subtype.ext
  change (boundEquiv p L i₀ k) '' (integralAnchor p L).val =
    (fun x : Packet p L => ((padicPrimeUnit p ^ boundExponent p L i₀ k : ℚ_[p]ˣ) : ℚ_[p]) • x) ''
      ((correctionEquiv p L) '' (integralAnchor p L).val)
  rw [Set.image_image]
  congr 1
  funext x
  rw [boundEquiv_apply, correctionEquiv_apply]
  simp [padicPrimeUnit]

theorem bound_logVolume_eq (i₀ : ι) (k : ℤ) :
    normalizedHaarLogVolume (integralAnchor p L) (boundRegion p L i₀ k) =
      normalizedHaarLogVolume (integralAnchor p L) (correctionRegion p L) -
        (boundExponent p L i₀ k : ℝ) * (Module.finrank ℚ_[p] (Packet p L) : ℝ) *
          Real.log (p : ℝ) := by
  rw [boundRegion_eq_scalar_correction, logVolume_scalarRegion,
    map_zpow, NNReal.coe_zpow, Real.log_zpow,
    realLog_distribHaarChar_padicPrime]
  ring

theorem actual_tensor_logVolume_le_explicit_p
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)
    (i₀ : ι) (k : ℤ) :
    normalizedHaarLogVolume (integralAnchor p L) (sourceRegion p L e i₀ k) ≤
      normalizedHaarLogVolume (integralAnchor p L) (correctionRegion p L) -
        (boundExponent p L i₀ k : ℝ) * (Module.finrank ℚ_[p] (Packet p L) : ℝ) *
          Real.log (p : ℝ) := by
  rw [← bound_logVolume_eq]
  exact actual_tensor_logVolume_le p L e i₀ k

end CitedLV.ActualTensorHaarScalarReadout
