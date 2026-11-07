import Cor312LogVolume.logshell.LogShellAmbientExtension
import Cor312LogVolume.logshell.LocalLogShellBounds
import Cor312LogVolume.Src.IUT4.Section1Proposition12iiTensorLogUnits

noncomputable section
set_option autoImplicit false

namespace CitedLV.LogShellTensorAction

open Src.IUT3.Remark122
open Src.IUT4.Proposition12i Src.IUT4.Proposition12ii
open CitedLV.LocalLogShellCompactness CitedLV.LocalLogShellBounds
open CitedLV.LogShellAmbientExtension
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

section Factor

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]
  [CompleteSpace K] [IsUltrametricDist K] [ProperSpace K]

theorem mem_logUnitsSet_iff_inv_smul_shell (x : K) :
    x ∈ logUnitsSet p K ↔ (((pStar p : ℕ) : ℚ_[p])⁻¹) • x ∈ logShell p := by
  rw [logUnitsSet_eq_principalImage p]
  have heq : ((pStar p : ℕ) : K) * ((((pStar p : ℕ) : ℚ_[p])⁻¹) • x) = x := by
    rw [Algebra.smul_def, map_inv₀, map_natCast, ← mul_assoc,
      mul_inv_cancel₀ (pStar_ne_zero (K := K) p), one_mul]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, heq⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨u, hu, h.symm.trans heq⟩

theorem extend_mem_logUnitsSet_iff
    (e : logShellModule (K := K) p ≃ₗ[ℤ_[p]] logShellModule (K := K) p)
    (x : K) : extend p e x ∈ logUnitsSet p K ↔ x ∈ logUnitsSet p K := by
  have hmem (y : K) : extend p e y ∈ logShell p ↔ y ∈ logShell p := by
    constructor
    · intro hy
      rw [← extend_image_shell p e] at hy
      obtain ⟨z, hz, he⟩ := hy
      exact (extend p e).injective he ▸ hz
    · intro hy
      rw [← extend_image_shell p e]
      exact ⟨y, hy, rfl⟩
  rw [mem_logUnitsSet_iff_inv_smul_shell, mem_logUnitsSet_iff_inv_smul_shell,
    ← (extend p e).map_smul, hmem]

end Factor

section Tensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)]
  [∀ i, ProperSpace (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

def tensorEquiv
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p) :
    (⨂[ℚ_[p]] i, L i) ≃ₗ[ℚ_[p]] (⨂[ℚ_[p]] i, L i) :=
  PiTensorProduct.congr fun i => (ambientAction p (e i)).toLinearEquiv

theorem tensorEquiv_mem_logUnits
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)
    (w : ⨂[ℚ_[p]] i, L i) (hw : w ∈ logUnits p L) :
    tensorEquiv p e w ∈ logUnits p L := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, rfl⟩ := hw
    rw [tensorEquiv, PiTensorProduct.congr_tprod]
    exact Submodule.subset_span ⟨_, fun i =>
      (extend_mem_logUnitsSet_iff p (e i) (y i)).mpr (hy i), rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    change (tensorEquiv p e).toLinearMap (a • x) ∈ _
    rw [(tensorEquiv p e).toLinearMap.map_smul_of_tower a x]
    exact Submodule.smul_mem _ _ hx

theorem tensorEquiv_symm_mem_logUnits
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)
    (w : ⨂[ℚ_[p]] i, L i) (hw : w ∈ logUnits p L) :
    (tensorEquiv p e).symm w ∈ logUnits p L := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, rfl⟩ := hw
    rw [tensorEquiv, PiTensorProduct.congr_symm_tprod]
    refine Submodule.subset_span ⟨_, fun i => ?_, rfl⟩
    apply (extend_mem_logUnitsSet_iff p (e i) _).mp
    change (extend p (e i)) ((extend p (e i)).symm (y i)) ∈ logUnitsSet p (L i)
    simpa only [LinearEquiv.apply_symm_apply] using hy i
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    change (tensorEquiv p e).symm.toLinearMap (a • x) ∈ _
    rw [(tensorEquiv p e).symm.toLinearMap.map_smul_of_tower a x]
    exact Submodule.smul_mem _ _ hx

theorem tensorEquiv_image_logUnits
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p) :
    tensorEquiv p e '' (logUnits p L : Set (⨂[ℚ_[p]] i, L i)) = logUnits p L := by
  apply Set.Subset.antisymm
  · rintro _ ⟨w, hw, rfl⟩
    exact tensorEquiv_mem_logUnits p e w hw
  · intro w hw
    exact ⟨(tensorEquiv p e).symm w, tensorEquiv_symm_mem_logUnits p e w hw,
      (tensorEquiv p e).apply_symm_apply w⟩

end Tensor

section Bounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L B : ι → Type*}
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)]
  [∀ i, ProperSpace (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]
  [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
  [∀ i, Algebra ℤ_[p] (B i)] [∀ i, Algebra (B i) (L i)]
  [∀ i, IsScalarTower ℤ_[p] (B i) (L i)]
  [∀ i, IsIntegralClosure (B i) ℤ_[p] (L i)]
  [∀ i, IsDedekindDomain (B i)] [∀ i, IsFractionRing (B i) (L i)]
  [∀ i, Module.IsTorsionFree ℤ_[p] (B i)]
  [∀ i, Module.Free ℤ_[p] (B i)] [∀ i, Module.Finite ℤ_[p] (B i)]
  [∀ i, IsLocalization (Algebra.algebraMapSubmonoid (B i)
    (nonZeroDivisors ℤ_[p])) (L i)]

theorem shell_tensor_prop12ii_first
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)
    (R : ∀ i, RamificationData p (L i)) (Δ : DifferentData p B R)
    (i₀ : ι) (k : ℤ) (z : ⨂[ℚ_[p]] i, L i) (hz : IsIntegral ℤ_[p] z) :
    ∃ w ∈ logUnits p L, tensorEquiv p e (piAt p R i₀ k * z) =
      ((p : ℚ_[p]) ^ ⌊(k : ℝ) / (R i₀).e - dI p Δ - aI p R⌋) • w :=
  prop12ii_first p R Δ i₀ k (tensorEquiv p e).toLinearMap
    (tensorEquiv_mem_logUnits p e) z hz

theorem shell_tensor_prop12ii
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)
    (R : ∀ i, RamificationData p (L i)) (Δ : DifferentData p B R)
    (i₀ : ι) (k : ℤ) (z : ⨂[ℚ_[p]] i, L i) (hz : IsIntegral ℤ_[p] z) :
    (∃ w ∈ logUnits p L, tensorEquiv p e (piAt p R i₀ k * z) =
      ((p : ℚ_[p]) ^ ⌊(k : ℝ) / (R i₀).e - dI p Δ - aI p R⌋) • w) ∧
    ∃ v, IsIntegral ℤ_[p] v ∧ tensorEquiv p e (piAt p R i₀ k * z) =
      ((p : ℚ_[p]) ^ ⌊(k : ℝ) / (R i₀).e - dI p Δ - aI p R⌋) • (piNegB p R * v) :=
  prop12ii p R Δ i₀ k (tensorEquiv p e).toLinearMap
    (tensorEquiv_mem_logUnits p e) z hz

end Bounds

end CitedLV.LogShellTensorAction
