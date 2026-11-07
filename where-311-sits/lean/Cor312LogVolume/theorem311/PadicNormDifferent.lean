import Cor312LogVolume.theorem311.PadicNormIntegerRing
import Cor312LogVolume.theorem311.PadicNormedRamification
import Cor312LogVolume.Src.IUT4.Section1Proposition12iiTensorLogUnits

set_option autoImplicit false
noncomputable section
namespace CitedLV.Theorem311.PadicNormDifferent

open Src.IUT4.Proposition12i Src.IUT4.Proposition12ii
open CitedLV.Theorem311.PadicNormIntegerRing
open CitedLV.Theorem311.PadicNormedRamification
open scoped NNReal nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [FiniteDimensional ℚ_[p] K]
  [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]

theorem exists_different_generator (R : RamificationData p K) :
    letI : IsDiscreteValuationRing (Integers K) := normIntegers_discreteValuationRing p K
    ∃ (δ : Integers K) (D : ℕ), δ ≠ 0 ∧
      differentIdeal ℤ_[p] (Integers K) = Ideal.span {δ} ∧
      δ ∈ differentIdeal ℤ_[p] (Integers K) ∧ ‖(δ : K)‖ = ‖R.pi‖ ^ D := by
  letI : IsDiscreteValuationRing (Integers K) := normIntegers_discreteValuationRing p K
  let δ := Submodule.IsPrincipal.generator (differentIdeal ℤ_[p] (Integers K))
  have hne : differentIdeal ℤ_[p] (Integers K) ≠ ⊥ := differentIdeal_ne_bot
  have hδ : δ ≠ 0 := by
    exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).not.mp hne
  have hδK : (δ : K) ≠ 0 := by
    intro h
    exact hδ (Subtype.ext h)
  obtain ⟨n, hn⟩ := R.valueGroup (δ : K) hδK
  have hπ0 : 0 < ‖R.pi‖ := by
    rw [R.norm_pi]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  have hπ1 : ‖R.pi‖ < 1 := norm_pi_lt_one p R (by
    exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hn0 : 0 ≤ n := by
    have hle : ‖R.pi‖ ^ n ≤ 1 := by
      rw [← hn]
      exact (mem_integers_iff_norm K δ).mp δ.property
    by_contra h
    have hlt : n < 0 := lt_of_not_ge h
    have hgt : 1 < ‖R.pi‖ ^ n := by
      have ht := zpow_lt_zpow_right_of_lt_one₀ hπ0 hπ1 hlt
      simpa only [zpow_zero] using ht
    exact (not_lt_of_ge hle) hgt
  refine ⟨δ, n.toNat, hδ, (Ideal.span_singleton_generator _).symm,
    Submodule.IsPrincipal.generator_mem _, ?_⟩
  rw [hn, ← zpow_natCast, Int.toNat_of_nonneg hn0]

section Family

variable {ι : Type*} (L : ι → Type*)
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

def actualDifferentData :
    letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
      fun i => normIntegers_discreteValuationRing p (L i)
    {Δ : DifferentData p (fun i => Integers (L i))
        (fun i => finiteExtensionRamification p (L i)) //
      ∀ i, Δ.δ i ≠ 0 ∧ differentIdeal ℤ_[p] (Integers (L i)) = Ideal.span {Δ.δ i}} := by
  classical
  letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
    fun i => normIntegers_discreteValuationRing p (L i)
  choose δ D hne hspan hmem hnorm using fun i =>
    exists_different_generator p (L i) (finiteExtensionRamification p (L i))
  exact ⟨⟨δ, hmem, D, hnorm⟩, fun i => ⟨hne i, hspan i⟩⟩

end Family

end CitedLV.Theorem311.PadicNormDifferent
