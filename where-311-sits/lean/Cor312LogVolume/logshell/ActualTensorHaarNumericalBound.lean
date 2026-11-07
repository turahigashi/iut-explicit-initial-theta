import Cor312LogVolume.logshell.ActualTensorHaarScalarReadout
import Cor312LogVolume.theorem311.TensorFactorHaarCharacter

noncomputable section
set_option autoImplicit false

namespace CitedLV.ActualTensorHaarNumericalBound

open Src.IUT4.Proposition12i Src.IUT4.Proposition12ii
open CitedLV.Theorem311 CitedLV.Theorem311.TensorIntegralLattice
open CitedLV.Theorem311.PadicNormedRamification
open CitedLV.Theorem311.TensorFactorHaarCharacter
open CitedLV.LogShellAmbientExtension CitedLV.ActualTensorHaarBound
open CitedLV.ActualTensorHaarScalarReadout
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Type*)
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, CompleteSpace (L i)] [∀ i, ProperSpace (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

private abbrev R := fun i => finiteExtensionRamification p (L i)

def correctionUnits (i : ι) : (L i)ˣ :=
  Units.mk0 ((R p L i).pi ^ (-bNum p (R p L i).e))
    (zpow_ne_zero _ (pi_ne_zero p (R p L i)))

theorem correctionRegion_eq_product :
    correctionRegion p L = unitRegion p L
      (∏ i, factorUnit p L i (correctionUnits p L i)) (integralAnchor p L) := by
  apply Subtype.ext
  change (correctionEquiv p L) '' (integralAnchor p L).val =
    (fun x => ((∏ i, factorUnit p L i (correctionUnits p L i) : (Packet p L)ˣ) : Packet p L) * x) ''
      (integralAnchor p L).val
  congr 1
  funext x
  rw [correctionEquiv_apply, product_factorUnit_val]
  rfl

theorem log_norm_correctionUnits (i : ι) :
    Real.log ‖(correctionUnits p L i : L i)‖ = bExp p (R p L i).e * Real.log (p : ℝ) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have he0 : ((R p L i).e : ℝ) ≠ 0 := by exact_mod_cast (R p L i).e_pos.ne'
  change Real.log ‖(R p L i).pi ^ (-bNum p (R p L i).e)‖ = _
  rw [norm_zpow, Real.log_zpow, (R p L i).norm_pi, Real.log_rpow hp0]
  simp only [Int.cast_neg]
  rw [bNum_eq p (R p L i).e (R p L i).e_pos]
  field_simp

theorem correction_logVolume_eq :
    normalizedHaarLogVolume (integralAnchor p L) (correctionRegion p L) =
      (Module.finrank ℚ_[p] (Packet p L) : ℝ) * bI p (R p L) * Real.log (p : ℝ) := by
  rw [correctionRegion_eq_product, logVolume_productRegion, normalizedHaarLogVolume_anchor]
  simp_rw [log_norm_correctionUnits]
  rw [← Finset.sum_mul]
  simp only [add_zero, bI]
  ring

theorem bound_logVolume_numerical (i₀ : ι) (k : ℤ) :
    normalizedHaarLogVolume (integralAnchor p L) (boundRegion p L i₀ k) =
      (Module.finrank ℚ_[p] (Packet p L) : ℝ) *
        (bI p (R p L) - (boundExponent p L i₀ k : ℝ)) * Real.log (p : ℝ) := by
  rw [bound_logVolume_eq, correction_logVolume_eq]
  ring

theorem actual_tensor_logVolume_le_numerical
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)
    (i₀ : ι) (k : ℤ) :
    normalizedHaarLogVolume (integralAnchor p L) (sourceRegion p L e i₀ k) ≤
      (Module.finrank ℚ_[p] (Packet p L) : ℝ) *
        (bI p (R p L) - (boundExponent p L i₀ k : ℝ)) * Real.log (p : ℝ) := by
  rw [← bound_logVolume_numerical]
  exact actual_tensor_logVolume_le p L e i₀ k

theorem actual_tensor_normalizedLogVolume_le
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)
    (i₀ : ι) (k : ℤ) :
    normalizedHaarLogVolume (integralAnchor p L) (sourceRegion p L e i₀ k) /
        (Module.finrank ℚ_[p] (Packet p L) : ℝ) ≤
      (bI p (R p L) - (boundExponent p L i₀ k : ℝ)) * Real.log (p : ℝ) := by
  have hd : (0 : ℝ) < Module.finrank ℚ_[p] (Packet p L) := by
    exact_mod_cast packet_finrank_pos p L
  apply (div_le_iff₀ hd).mpr
  convert actual_tensor_logVolume_le_numerical p L e i₀ k using 1 <;> ring

end CitedLV.ActualTensorHaarNumericalBound
