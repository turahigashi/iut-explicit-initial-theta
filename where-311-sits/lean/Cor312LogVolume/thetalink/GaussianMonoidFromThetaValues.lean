import Cor312LogVolume.Src.EtTh.Section1ThetaValueArithmetic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

noncomputable section
set_option autoImplicit false

namespace CitedLV.ThetaLink.GaussianMonoidFromThetaValues

section MonoidConstruction

variable {G I : Type*} [CommGroup G]

def gaussianMonoid (U : Subgroup G) (ξ : I → G) : Submonoid (I → G) where
  carrier := {x | ∃ u : U, ∃ n : ℕ, x = fun j => (u : G) * ξ j ^ n}
  one_mem' := by
    refine ⟨1, 0, ?_⟩
    funext j
    simp
  mul_mem' := by
    rintro x y ⟨u, m, rfl⟩ ⟨v, n, rfl⟩
    refine ⟨u * v, m + n, ?_⟩
    funext j
    simp only [Pi.mul_apply, Subgroup.coe_mul, pow_add]
    ac_rfl

theorem gaussianMonoid_le_iff (U : Subgroup G) (ξ : I → G)
    (M : Submonoid (I → G)) :
    gaussianMonoid U ξ ≤ M ↔
      (∀ u : U, (fun _ : I => (u : G)) ∈ M) ∧ ξ ∈ M := by
  constructor
  · intro h
    constructor
    · intro u
      apply h
      exact ⟨u, 0, by simp⟩
    · apply h
      exact ⟨1, 1, by simp⟩
  · rintro ⟨hu, hξ⟩ x ⟨u, n, rfl⟩
    exact M.mul_mem (hu u) (M.pow_mem hξ n)

theorem gaussianMonoid_pow_le (U : Subgroup G) (ξ : I → G) (m : ℕ) :
    gaussianMonoid U (ξ ^ m) ≤ gaussianMonoid U ξ := by
  rintro x ⟨u, n, rfl⟩
  refine ⟨u, m * n, ?_⟩
  funext j
  simp only [Pi.pow_apply, pow_mul]

end MonoidConstruction

open Src.EtTh.ThetaValueArithmetic

def normOneUnits (K : Type*) [NormedField K] : Subgroup Kˣ where
  carrier := {u | ‖(u : K)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change ‖(u : K)‖ = 1 at hu
    change ‖(v : K)‖ = 1 at hv
    change ‖((u * v : Kˣ) : K)‖ = 1
    simp only [Units.val_mul, norm_mul, hu, hv, one_mul]
  inv_mem' := by
    intro u hu
    change ‖(u : K)‖ = 1 at hu
    change ‖((u⁻¹ : Kˣ) : K)‖ = 1
    simp only [Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]

variable {K : Type*} [NormedField K]

abbrev Labels (ell : ℕ) := Fin ((ell - 1) / 2)

def actualProfiles (s i : Kˣ) (ell : ℕ) : Set (Labels ell → Kˣ) :=
  {ξ | ∀ j, ξ j ∈ normalizedRootValues s i ell (j.val + 1)}

def qProfile (s : Kˣ) (ell : ℕ) : Labels ell → Kˣ :=
  fun j => (s ^ 2) ^ ((j.val + 1) * (j.val + 1))

theorem actualProfile_pow_two_ell (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell : ℕ)
    (ξ : Labels ell → Kˣ) (hξ : ξ ∈ actualProfiles s i ell) :
    ξ ^ (2 * ell) = qProfile s ell := by
  funext j
  exact (mem_normalizedRootValues_iff_power s i hi h ell (j.val + 1) (ξ j)).mp
    (hξ j)

theorem canonicalProfile_mem (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell : ℕ) (qRoot : Kˣ)
    (hqRoot : qRoot ^ (2 * ell) = s ^ 2) :
    (fun j : Labels ell => qRoot ^ ((j.val + 1) * (j.val + 1))) ∈
      actualProfiles s i ell := by
  intro j
  apply (normalizedRootValues_profile_iff s i hi h ell (j.val + 1) _ qRoot
    hqRoot).mpr
  exact ⟨1, by simp⟩

theorem gaussianMonoid_two_ell_eq (U : Subgroup Kˣ)
    (s i : Kˣ) (hi : i ^ 2 = -1) (h : PublishedThetaFacts s i)
    (ell : ℕ) (ξ : Labels ell → Kˣ) (hξ : ξ ∈ actualProfiles s i ell) :
    gaussianMonoid U (ξ ^ (2 * ell)) = gaussianMonoid U (qProfile s ell) := by
  rw [actualProfile_pow_two_ell s i hi h ell ξ hξ]

theorem gaussianMonoid_two_ell_independent (U : Subgroup Kˣ)
    (s i : Kˣ) (hi : i ^ 2 = -1) (h : PublishedThetaFacts s i)
    (ell : ℕ) (ξ η : Labels ell → Kˣ)
    (hξ : ξ ∈ actualProfiles s i ell) (hη : η ∈ actualProfiles s i ell) :
    gaussianMonoid U (ξ ^ (2 * ell)) = gaussianMonoid U (η ^ (2 * ell)) := by
  rw [gaussianMonoid_two_ell_eq U s i hi h ell ξ hξ,
    gaussianMonoid_two_ell_eq U s i hi h ell η hη]

theorem commonGaussianMonoid_le (U : Subgroup Kˣ)
    (s i : Kˣ) (hi : i ^ 2 = -1) (h : PublishedThetaFacts s i)
    (ell : ℕ) (ξ : Labels ell → Kˣ) (hξ : ξ ∈ actualProfiles s i ell) :
    gaussianMonoid U (qProfile s ell) ≤ gaussianMonoid U ξ := by
  rw [← gaussianMonoid_two_ell_eq U s i hi h ell ξ hξ]
  exact gaussianMonoid_pow_le U ξ (2 * ell)

theorem commonNormOneGaussianMonoid_le
    (s i : Kˣ) (hi : i ^ 2 = -1) (h : PublishedThetaFacts s i)
    (ell : ℕ) (ξ : Labels ell → Kˣ) (hξ : ξ ∈ actualProfiles s i ell) :
    gaussianMonoid (normOneUnits K) (qProfile s ell) ≤
      gaussianMonoid (normOneUnits K) ξ :=
  commonGaussianMonoid_le (normOneUnits K) s i hi h ell ξ hξ

end CitedLV.ThetaLink.GaussianMonoidFromThetaValues
