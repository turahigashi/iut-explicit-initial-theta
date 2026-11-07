import Cor312LogVolume.logshell.ActualTensorLogBound
import Cor312LogVolume.theorem311.TensorIntegralLattice

noncomputable section
set_option autoImplicit false

namespace CitedLV.ActualTensorHaarBound

open Src.IUT4.Proposition12i Src.IUT4.Proposition12ii
open CitedLV.Theorem311 CitedLV.Theorem311.TensorIntegralLattice
open CitedLV.Theorem311.PadicNormIntegerRing
open CitedLV.Theorem311.PadicNormedRamification
open CitedLV.Theorem311.PadicNormDifferent
open CitedLV.LogShellAmbientExtension CitedLV.LogShellTensorAction
open CitedLV.ActualTensorLogBound
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Type*)
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, CompleteSpace (L i)] [∀ i, ProperSpace (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

private abbrev R := fun i => finiteExtensionRamification p (L i)

private theorem piAt_isUnit (i₀ : ι) (k : ℤ) :
    IsUnit (piAt p (R p L) i₀ k : Packet p L) := by
  apply IsUnit.map (PiTensorProduct.tprodMonoidHom (A := L) ℚ_[p])
  apply Pi.isUnit_iff.mpr
  intro j
  by_cases h : j = i₀
  · subst j
    simpa only [Pi.mulSingle_eq_same] using
      (isUnit_iff_ne_zero.mpr (zpow_ne_zero k (pi_ne_zero p (R p L i₀))))
  · simp [Pi.mulSingle, h]

private theorem piNegB_isUnit : IsUnit (piNegB p (R p L) : Packet p L) := by
  apply IsUnit.map (PiTensorProduct.tprodMonoidHom (A := L) ℚ_[p])
  apply Pi.isUnit_iff.mpr
  exact fun i => isUnit_iff_ne_zero.mpr (zpow_ne_zero _ (pi_ne_zero p (R p L i)))

def boundExponent (i₀ : ι) (k : ℤ) : ℤ := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
    fun i => normIntegers_discreteValuationRing p (L i)
  exact ⌊(k : ℝ) / (R p L i₀).e - dI p (actualDifferentData p L).val - aI p (R p L)⌋

variable (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)

def sourceEquiv (i₀ : ι) (k : ℤ) : Packet p L ≃ₗ[ℚ_[p]] Packet p L :=
  ((piAt_isUnit p L i₀ k).unit.mulLeftLinearEquiv ℚ_[p] (Packet p L)).trans
    (tensorEquiv p e)

theorem sourceEquiv_apply (i₀ : ι) (k : ℤ) (x : Packet p L) :
    sourceEquiv p L e i₀ k x =
      tensorEquiv p e (Mul.mul (α := Packet p L) (piAt p (R p L) i₀ k) x) := by
  simp [sourceEquiv, IsUnit.unit_spec]
  rfl

def boundEquiv (i₀ : ι) (k : ℤ) : Packet p L ≃ₗ[ℚ_[p]] Packet p L :=
  ((piNegB_isUnit p L).unit.mulLeftLinearEquiv ℚ_[p] (Packet p L)).trans
    (LinearEquiv.smulOfUnit (Units.mk0 ((p : ℚ_[p]) ^ boundExponent p L i₀ k)
      (zpow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))))

theorem boundEquiv_apply (i₀ : ι) (k : ℤ) (x : Packet p L) :
    boundEquiv p L i₀ k x =
      ((p : ℚ_[p]) ^ boundExponent p L i₀ k) •
        Mul.mul (α := Packet p L) (piNegB p (R p L)) x := by
  simp [boundEquiv, IsUnit.unit_spec]
  rfl

def sourceRegion (i₀ : ι) (k : ℤ) : NormalizedHaarRegion (Packet p L) :=
  mapNormalizedHaarRegion (sourceEquiv p L e i₀ k).toContinuousLinearEquiv.toContinuousAddEquiv
    (integralAnchor p L)

def boundRegion (i₀ : ι) (k : ℤ) : NormalizedHaarRegion (Packet p L) :=
  mapNormalizedHaarRegion (boundEquiv p L i₀ k).toContinuousLinearEquiv.toContinuousAddEquiv
    (integralAnchor p L)

theorem sourceRegion_subset_boundRegion (i₀ : ι) (k : ℤ) :
    (sourceRegion p L e i₀ k).val ⊆ (boundRegion p L i₀ k).val := by
  rintro y ⟨z, hz, rfl⟩
  change IsIntegral ℤ_[p] z at hz
  obtain ⟨w, hw, heq⟩ := (actual_tensor_bound p L e i₀ k z hz).2
  refine ⟨w, hw, ?_⟩
  change boundEquiv p L i₀ k w = sourceEquiv p L e i₀ k z
  rw [boundEquiv_apply, sourceEquiv_apply]
  exact heq.symm

theorem normalizedHaarLogVolume_mono
    {X : Type*} [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [MeasurableSpace X] [BorelSpace X]
    (A U V : NormalizedHaarRegion X) (hUV : U.val ⊆ V.val) :
    normalizedHaarLogVolume A U ≤ normalizedHaarLogVolume A V := by
  apply Real.log_le_log (normalizedHaarRealVolume_pos A U)
  exact ENNReal.toReal_mono (normalizedAddHaar_region_lt_top A V).ne
    (MeasureTheory.measure_mono hUV)

theorem actual_tensor_logVolume_le (i₀ : ι) (k : ℤ) :
    normalizedHaarLogVolume (integralAnchor p L) (sourceRegion p L e i₀ k) ≤
      normalizedHaarLogVolume (integralAnchor p L) (boundRegion p L i₀ k) :=
  normalizedHaarLogVolume_mono _ _ _ (sourceRegion_subset_boundRegion p L e i₀ k)

end CitedLV.ActualTensorHaarBound
