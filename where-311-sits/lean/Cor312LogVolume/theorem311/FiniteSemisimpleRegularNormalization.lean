import Cor312LogVolume.theorem311.NonarchTensorBaselineComparison
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Algebraic.Integral

namespace CitedLV.Theorem311

open scoped BigOperators

universe uBase uIndex uComponent uPacket uRaw

theorem isIntegral_finite_pi_iff
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (x : ∀ i, A i) :
    IsIntegral R x ↔ ∀ i, IsIntegral R (x i) := by
  constructor
  · intro hx i
    exact hx.map (Pi.evalAlgHom R A i)
  · intro hcomponents
    classical
    choose polynomial monic annihilates using hcomponents
    refine ⟨∏ i, polynomial i, ?_, ?_⟩
    · exact Polynomial.monic_prod_of_monic Finset.univ polynomial
        (fun i _ => monic i)
    · change Polynomial.aeval x (∏ j, polynomial j) = 0
      rw [Polynomial.aeval_pi_apply]
      apply funext
      intro i
      change Polynomial.aeval (x i) (∏ j, polynomial j) = (0 : A i)
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (annihilates i)

def componentwiseIntegralOrder
    (R : Type uBase) {ι : Type uIndex} (A : ι -> Type uComponent)
    [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] :
    Subalgebra R (∀ i, A i) where
  carrier := {x | ∀ i, IsIntegral R (x i)}
  zero_mem' := fun i => isIntegral_zero
  one_mem' := fun i => isIntegral_one
  add_mem' hx hy := fun i => (hx i).add (hy i)
  mul_mem' hx hy := fun i => (hx i).mul (hy i)
  algebraMap_mem' r := fun i => isIntegral_algebraMap

theorem mem_componentwiseIntegralOrder_iff
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (x : ∀ i, A i) :
    x ∈ componentwiseIntegralOrder R A ↔ ∀ i, IsIntegral R (x i) :=
  Iff.rfl

theorem componentwiseIntegralOrder_eq_integralClosure
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] :
    componentwiseIntegralOrder R A = integralClosure R (∀ i, A i) := by
  ext x
  change (∀ i, IsIntegral R (x i)) ↔ IsIntegral R x
  exact (isIntegral_finite_pi_iff x).symm

def componentwiseIntegralOrderToPi
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] :
    componentwiseIntegralOrder R A →ₐ[R] (∀ i, integralClosure R (A i)) where
  toFun x := fun i => ⟨x.1 i, x.2 i⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem componentwiseIntegralOrderToPi_bijective
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] :
    Function.Bijective (componentwiseIntegralOrderToPi (R := R) (A := A)) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg (fun z => (z i : A i)) hxy
  · intro y
    refine ⟨⟨fun i => (y i : A i), fun i => (y i).2⟩, ?_⟩
    rfl

noncomputable def componentwiseIntegralOrderEquivPi
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] :
    componentwiseIntegralOrder R A ≃ₐ[R]
      (∀ i, integralClosure R (A i)) :=
  AlgEquiv.ofBijective componentwiseIntegralOrderToPi
    componentwiseIntegralOrderToPi_bijective

def regularIntegerOrderOfFiniteSplit
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K]
    (split : K ≃ₐ[R] (∀ i, A i)) : Subalgebra R K :=
  (componentwiseIntegralOrder R A).comap split.toAlgHom

theorem mem_regularIntegerOrderOfFiniteSplit_iff
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K]
    (split : K ≃ₐ[R] (∀ i, A i)) (x : K) :
    x ∈ regularIntegerOrderOfFiniteSplit split ↔
      ∀ i, IsIntegral R (split x i) :=
  Iff.rfl

theorem regularIntegerOrderOfFiniteSplit_eq_integralClosure
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K]
    (split : K ≃ₐ[R] (∀ i, A i)) :
    regularIntegerOrderOfFiniteSplit split = integralClosure R K := by
  ext x
  change (∀ i, IsIntegral R (split x i)) ↔ IsIntegral R x
  rw [← isIntegral_finite_pi_iff]
  exact isIntegral_algEquiv split

theorem isIntegral_over_integral_intermediate_iff
    {R : Type uBase} {Raw : Type uRaw} {K : Type uPacket}
    [CommRing R] [CommRing Raw] [CommRing K]
    [Algebra R Raw] [Algebra R K] [Algebra Raw K]
    [IsScalarTower R Raw K] [Algebra.IsIntegral R Raw]
    (x : K) :
    IsIntegral R x ↔ IsIntegral Raw x := by
  constructor
  · exact IsIntegral.tower_top
  · exact fun hx => isIntegral_trans x hx

theorem integralClosure_over_integral_intermediate_same_subring
    {R : Type uBase} {Raw : Type uRaw} {K : Type uPacket}
    [CommRing R] [CommRing Raw] [CommRing K]
    [Algebra R Raw] [Algebra R K] [Algebra Raw K]
    [IsScalarTower R Raw K] [Algebra.IsIntegral R Raw] :
    (integralClosure R K).toSubring =
      (integralClosure Raw K).toSubring := by
  ext x
  change IsIntegral R x ↔ IsIntegral Raw x
  exact isIntegral_over_integral_intermediate_iff x

theorem regularIntegerOrder_eq_rawIntegralClosure_subring
    {R : Type uBase} {Raw : Type uRaw}
    {ι : Type uIndex} {A : ι -> Type uComponent} {K : Type uPacket}
    [CommRing R] [CommRing Raw] [CommRing K]
    [∀ i, CommRing (A i)] [Fintype ι]
    [Algebra R Raw] [Algebra R K] [Algebra Raw K]
    [∀ i, Algebra R (A i)] [IsScalarTower R Raw K]
    [Algebra.IsIntegral R Raw]
    (split : K ≃ₐ[R] (∀ i, A i)) :
    (regularIntegerOrderOfFiniteSplit split).toSubring =
      (integralClosure Raw K).toSubring := by
  calc
    (regularIntegerOrderOfFiniteSplit split).toSubring =
        (integralClosure R K).toSubring :=
      congrArg Subalgebra.toSubring
        (regularIntegerOrderOfFiniteSplit_eq_integralClosure split)
    _ = (integralClosure Raw K).toSubring :=
      integralClosure_over_integral_intermediate_same_subring

noncomputable def boolPolynomialProfile : Bool -> Polynomial ℚ
  | false => 0
  | true => Polynomial.X

theorem polynomial_X_is_not_integral_over_rat :
    ¬ IsIntegral ℚ (Polynomial.X : Polynomial ℚ) := by
  intro hx
  exact (Polynomial.transcendental_X ℚ) hx.isAlgebraic

theorem zero_polynomial_profile_mem_componentwise_order :
    (fun _ : Bool => (0 : Polynomial ℚ)) ∈
      componentwiseIntegralOrder ℚ (fun _ : Bool => Polynomial ℚ) := by
  intro i
  exact isIntegral_zero

theorem bool_polynomial_profile_not_mem_componentwise_order :
    boolPolynomialProfile ∉
      componentwiseIntegralOrder ℚ (fun _ : Bool => Polynomial ℚ) := by
  intro hmem
  exact polynomial_X_is_not_integral_over_rat (hmem true)

theorem bool_polynomial_profile_not_mem_regular_refl_split :
    boolPolynomialProfile ∉ regularIntegerOrderOfFiniteSplit
      (AlgEquiv.refl : (Bool -> Polynomial ℚ) ≃ₐ[ℚ]
        (Bool -> Polynomial ℚ)) := by
  exact bool_polynomial_profile_not_mem_componentwise_order

end CitedLV.Theorem311
