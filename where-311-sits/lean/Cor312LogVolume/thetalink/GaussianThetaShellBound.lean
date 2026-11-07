import Cor312LogVolume.thetalink.GaussianThetaTensorReadout
import Cor312LogVolume.logshell.ActualTensorProp14Bound
import Cor312LogVolume.Src.IUT4.Section1Theorem110ComponentHull

noncomputable section
set_option autoImplicit false

namespace CitedLV.ThetaLink.GaussianThetaShellBound

open Src.IUT4.Proposition12i Src.IUT4.Proposition12ii
open CitedLV.Theorem311 CitedLV.Theorem311.TensorIntegralLattice
open CitedLV.Theorem311.TensorFactorHaarCharacter
open CitedLV.Theorem311.PadicNormedRamification
open CitedLV.Theorem311.PadicNormIntegerRing CitedLV.Theorem311.PadicNormDifferent
open CitedLV.LogShellAmbientExtension CitedLV.LogShellTensorAction
open CitedLV.ActualTensorHaarBound CitedLV.ActualTensorProp14Bound
open CitedLV.ThetaLink.GaussianMonoidFromThetaValues
open CitedLV.ThetaLink.GaussianThetaLogReadout
open Src.EtTh.ThetaValueArithmetic
open scoped BigOperators TensorProduct

variable (p : ℕ) [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Type*)
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, CompleteSpace (L i)] [∀ i, ProperSpace (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

omit [∀ i, CompleteSpace (L i)] [∀ i, ProperSpace (L i)] in

theorem factorRegion_integralAnchor_eq_of_norm_eq
    (slot : ι) (a b : (L slot)ˣ) (hab : ‖(a : L slot)‖ = ‖(b : L slot)‖) :
    factorRegion p L slot a (integralAnchor p L) =
      factorRegion p L slot b (integralAnchor p L) := by
  have inc (a b : (L slot)ˣ) (hab : ‖(a : L slot)‖ = ‖(b : L slot)‖) :
      (factorRegion p L slot a (integralAnchor p L)).val ⊆
        (factorRegion p L slot b (integralAnchor p L)).val := by
    rintro _ ⟨z, hz, rfl⟩
    change IsIntegral ℤ_[p] z at hz
    let c : L slot := (a : L slot) / (b : L slot)
    have hcNorm : ‖c‖ ≤ 1 := by
      dsimp only [c]
      rw [norm_div, hab, div_self (norm_pos_iff.mpr b.ne_zero).ne']
    have hc : IsIntegral ℤ_[p] ((factorHom p L slot) c) :=
      (SrcLib.PadicLog.isIntegral_of_norm_le_one hcNorm).map
        ((factorHom p L slot).restrictScalars ℤ_[p])
    refine ⟨(factorHom p L slot) c * z, hc.mul hz, ?_⟩
    change (factorHom p L slot) (b : L slot) * ((factorHom p L slot) c * z) =
      (factorHom p L slot) (a : L slot) * z
    rw [← mul_assoc, ← map_mul]
    congr 2
    dsimp only [c]
    field_simp
  exact Subtype.ext (Set.Subset.antisymm (inc a b hab) (inc b a hab.symm))

def shellFactorRegion
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)
    (slot : ι) (a : (L slot)ˣ) : NormalizedHaarRegion (Packet p L) :=
  mapNormalizedHaarRegion
    (show Packet p L ≃ₗ[ℚ_[p]] Packet p L from tensorEquiv p e).toContinuousLinearEquiv.toContinuousAddEquiv
    (factorRegion p L slot a (integralAnchor p L))

private theorem shellFactorRegion_eq_sourceRegion
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)
    (slot : ι) (a : (L slot)ˣ) (k : ℤ)
    (hk : ‖(a : L slot)‖ = ‖(finiteExtensionRamification p (L slot)).pi‖ ^ k) :
    shellFactorRegion p L e slot a = sourceRegion p L e slot k := by
  let b : (L slot)ˣ := Units.mk0 ((finiteExtensionRamification p (L slot)).pi ^ k)
    (zpow_ne_zero _ (pi_ne_zero p (finiteExtensionRamification p (L slot))))
  have hab : ‖(a : L slot)‖ = ‖(b : L slot)‖ := by
    simpa only [b, Units.val_mk0, norm_zpow] using hk
  rw [shellFactorRegion, factorRegion_integralAnchor_eq_of_norm_eq p L slot a b hab]
  apply Subtype.ext
  change (fun z : Packet p L => tensorEquiv p e z) ''
      ((fun z : Packet p L => (factorUnit p L slot b : Packet p L) * z) '' (integralAnchor p L).val) =
    (sourceEquiv p L e slot k) '' (integralAnchor p L).val
  rw [Set.image_image]
  congr 1

private theorem shellFactorRegion_normalizedLogVolume_le
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)
    (slot : ι) (a : (L slot)ˣ) (Istar : Finset ι)
    (hIstar : ∀ i ∉ Istar, (finiteExtensionRamification p (L i)).e + 2 ≤ p) :
    letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
      fun i => normIntegers_discreteValuationRing p (L i)
    let R := fun i => finiteExtensionRamification p (L i)
    let Δ := (actualDifferentData p L).val
    normalizedHaarLogVolume (integralAnchor p L) (shellFactorRegion p L e slot a) /
        (Module.finrank ℚ_[p] (Packet p L) : ℝ) ≤
      Real.log ‖(a : L slot)‖ + (dI p Δ + 1) * Real.log (p : ℝ) +
        ∑ i ∈ Istar, (3 + Real.log (R i).e) := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
    fun i => normIntegers_discreteValuationRing p (L i)
  let R := fun i => finiteExtensionRamification p (L i)
  obtain ⟨k, hk⟩ := (R slot).valueGroup (a : L slot) a.ne_zero
  rw [shellFactorRegion_eq_sourceRegion p L e slot a k hk]
  have hlog : Real.log ‖(a : L slot)‖ =
      -((k : ℝ) / (R slot).e) * Real.log (p : ℝ) := by
    rw [hk, Real.log_zpow, (R slot).norm_pi,
      Real.log_rpow (by exact_mod_cast (Fact.out : p.Prime).pos : 0 < (p : ℝ))]
    ring
  have hb := actual_tensor_prop14iii_second p L e slot k Istar hIstar
  rw [hlog]
  dsimp only [R] at hb ⊢
  nlinarith only [hb]

theorem gaussian_shell_tensor_normalizedLogVolume_le
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)
    (slot : ι) (s i : (L slot)ˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell : ℕ) (hell : 0 < ell)
    (ξ : Labels ell → (L slot)ˣ) (hξ : ξ ∈ actualProfiles s i ell)
    (label : Labels ell) (u : normOneUnits (L slot)) (n : ℕ) (Istar : Finset ι)
    (hIstar : ∀ i ∉ Istar, (finiteExtensionRamification p (L i)).e + 2 ≤ p) :
    letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
      fun i => normIntegers_discreteValuationRing p (L i)
    let R := fun i => finiteExtensionRamification p (L i)
    let Δ := (actualDifferentData p L).val
    normalizedHaarLogVolume (integralAnchor p L)
        (shellFactorRegion p L e slot ((u : (L slot)ˣ) * ξ label ^ n)) /
        (Module.finrank ℚ_[p] (Packet p L) : ℝ) ≤
      (n : ℝ) * (((label.val : ℝ) + 1) ^ 2 / (2 * (ell : ℝ))) *
        Real.log ‖((s ^ 2 : (L slot)ˣ) : L slot)‖ +
      (dI p Δ + 1) * Real.log (p : ℝ) +
        ∑ i ∈ Istar, (3 + Real.log (R i).e) := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
    fun i => normIntegers_discreteValuationRing p (L i)
  have hb := shellFactorRegion_normalizedLogVolume_le p L e slot
    ((u : (L slot)ˣ) * ξ label ^ n) Istar hIstar
  rwa [gaussian_log_norm s i hi h ell hell ξ hξ u n label] at hb

theorem sourceRegion_subset_possibleImages
    (e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p)
    (slot : ι) (k : ℤ) :
    (sourceRegion p L e slot k).val ⊆
      Src.IUT4.Theorem110.possibleImages p L
        (fun i => finiteExtensionRamification p (L i)) slot k := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨tensorEquiv p e, ?_, z, hz, ?_⟩
  · intro w
    constructor
    · exact tensorEquiv_mem_logUnits p e w
    · intro hw
      simpa only [LinearEquiv.symm_apply_apply] using
        tensorEquiv_symm_mem_logUnits p e (tensorEquiv p e w) hw
  · exact sourceEquiv_apply p L e slot k z

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem possibleImageHull_subset_boundRegion (slot : ι) (k : ℤ) :
    (Src.IUT4.Theorem110.possibleImageHull p L
      (fun i => finiteExtensionRamification p (L i)) slot k : Set (⨂[ℚ_[p]] i, L i)) ⊆
        (boundRegion p L slot k).val := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
    fun i => normIntegers_discreteValuationRing p (L i)
  intro x hx
  have hc := Src.IUT4.Theorem110.possibleImageHull_le_container p
    (fun i => finiteExtensionRamification p (L i)) (actualDifferentData p L).val slot k hx
  obtain ⟨y, ⟨z, hz, rfl⟩, heq⟩ := hc
  refine ⟨z, hz, ?_⟩
  change boundEquiv p L slot k z = x
  rw [boundEquiv_apply]
  exact heq

theorem gaussian_shell_union_subset_common_hull
    (slot : ι) (s i : (L slot)ˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell : ℕ) (hell : 0 < ell)
    (ξ : Labels ell → (L slot)ˣ) (hξ : ξ ∈ actualProfiles s i ell)
    (label : Labels ell) (n : ℕ) :
    ∃ k : ℤ,
      ‖(ξ label : L slot)‖ ^ n = ‖(finiteExtensionRamification p (L slot)).pi‖ ^ k ∧
      (⋃ e : ∀ i, logShellModule (K := L i) p ≃ₗ[ℤ_[p]] logShellModule (K := L i) p,
        ⋃ η ∈ actualProfiles s i ell, ⋃ u : normOneUnits (L slot),
          (shellFactorRegion p L e slot ((u : (L slot)ˣ) * η label ^ n)).val) ⊆
        (Src.IUT4.Theorem110.possibleImageHull p L
          (fun i => finiteExtensionRamification p (L i)) slot k : Set (⨂[ℚ_[p]] i, L i)) ∧
      (Src.IUT4.Theorem110.possibleImageHull p L
        (fun i => finiteExtensionRamification p (L i)) slot k : Set (⨂[ℚ_[p]] i, L i)) ⊆
          (boundRegion p L slot k).val := by
  obtain ⟨k, hk⟩ := (finiteExtensionRamification p (L slot)).valueGroup
    ((ξ label ^ n : (L slot)ˣ) : L slot) (Units.ne_zero _)
  have hkn : ‖(ξ label : L slot)‖ ^ n =
      ‖(finiteExtensionRamification p (L slot)).pi‖ ^ k := by
    simpa only [Units.val_pow_eq_pow_val, norm_pow] using hk
  refine ⟨k, hkn, ?_, possibleImageHull_subset_boundRegion p L slot k⟩
  refine Set.iUnion_subset fun e => Set.iUnion_subset fun η =>
    Set.iUnion_subset fun hη => Set.iUnion_subset fun u => ?_
  have hnorm : ‖(((u : (L slot)ˣ) * η label ^ n : (L slot)ˣ) : L slot)‖ =
      ‖(finiteExtensionRamification p (L slot)).pi‖ ^ k := by
    have hu : ‖((u : (L slot)ˣ) : L slot)‖ = 1 := u.property
    rw [Units.val_mul, norm_mul, hu, one_mul, Units.val_pow_eq_pow_val, norm_pow,
      actualProfile_norm_independent s i hi h ell hell η ξ hη hξ label]
    exact hkn
  rw [shellFactorRegion_eq_sourceRegion p L e slot _ k hnorm]
  exact (sourceRegion_subset_possibleImages p L e slot k).trans
    (Src.IUT4.Theorem110.possibleImages_subset_hull p
      (fun i => finiteExtensionRamification p (L i)) slot k)

end CitedLV.ThetaLink.GaussianThetaShellBound
