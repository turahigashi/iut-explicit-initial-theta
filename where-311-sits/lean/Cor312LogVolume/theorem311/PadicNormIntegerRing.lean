import Cor312LogVolume.Src.Lib.PadicLog.FiniteExtensionIntegral
import Mathlib.Topology.Algebra.Valued.NormedValued

set_option autoImplicit false
noncomputable section
namespace CitedLV.Theorem311.PadicNormIntegerRing

open scoped NNReal nonZeroDivisors

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [FiniteDimensional ℚ_[p] K]
  [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]

abbrev Integers := (NormedField.valuation (K := K)).integer

theorem mem_integers_iff_norm (x : K) : x ∈ Integers K ↔ ‖x‖ ≤ 1 := by
  change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
  exact NNReal.coe_le_coe.symm

instance integerAlgebra : Algebra ℤ_[p] (Integers K) :=
  ((algebraMap ℤ_[p] K).codRestrict (Integers K) fun a => by
    rw [mem_integers_iff_norm, SrcLib.PadicLog.norm_algebraMap_padicInt p]
    exact a.norm_le_one).toAlgebra

instance integerScalarTower : IsScalarTower ℤ_[p] (Integers K) K :=
  IsScalarTower.of_algebraMap_eq' rfl

instance integerIntegralClosure : IsIntegralClosure (Integers K) ℤ_[p] K where
  algebraMap_injective := Subtype.coe_injective
  isIntegral_iff := by
    intro x
    rw [SrcLib.PadicLog.isIntegral_iff_norm_le_one]
    constructor
    · intro hx
      exact ⟨⟨x, (mem_integers_iff_norm K x).mpr hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact (mem_integers_iff_norm K x).mp x.property

instance integerModuleFinite : Module.Finite ℤ_[p] (Integers K) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] K (Integers K)

instance fieldTorsionFree : Module.IsTorsionFree ℤ_[p] K :=
  (Module.isTorsionFree_iff_algebraMap_injective).mpr (by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] K]
    exact (algebraMap ℚ_[p] K).injective.comp
      (FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p]))

instance integerModuleFree : Module.Free ℤ_[p] (Integers K) :=
  IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K (Integers K)

instance integerBaseLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid (Integers K) (nonZeroDivisors ℤ_[p])) K :=
  IsIntegralClosure.isLocalization ℤ_[p] ℚ_[p] K (Integers K)

theorem integer_finrank : Module.finrank ℤ_[p] (Integers K) = Module.finrank ℚ_[p] K :=
  IsIntegralClosure.rank ℤ_[p] ℚ_[p] K (Integers K)

end CitedLV.Theorem311.PadicNormIntegerRing
