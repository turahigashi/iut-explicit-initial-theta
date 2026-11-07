import Cor312LogVolume.theorem311.NumberFieldLogDegree
import Cor312LogVolume.geometric.ModelFrobenioid
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Pi

noncomputable section
set_option autoImplicit false
open NumberField
open scoped BigOperators

namespace CitedLV.Theorem311.NumberFieldRealDivisor

universe u
variable (K : Type u) [Field K] [NumberField K]

abbrev Divisor := (FinitePlace K →₀ ℝ) × (InfinitePlace K → ℝ)

variable {K}

theorem finiteLogSupport (a : Kˣ) :
    (Function.support (fun v : FinitePlace K => -Real.log (v (a : K)))).Finite := by
  refine (FinitePlace.hasFiniteMulSupport a.ne_zero).subset ?_
  intro v hv
  change -Real.log (v (a : K)) ≠ 0 at hv
  change v (a : K) ≠ 1
  intro h
  exact hv (by simp [h])

def finitePrincipal (a : Kˣ) : FinitePlace K →₀ ℝ :=
  Finsupp.ofSupportFinite (fun v => -Real.log (v (a : K))) (finiteLogSupport a)

def principalDivisor : Additive Kˣ →+ Divisor K where
  toFun a := (finitePrincipal a.toMul,
    fun w => -(w.mult : ℝ) * Real.log (w (a.toMul : K)))
  map_zero' := by
    apply Prod.ext
    · ext v
      simp [finitePrincipal, Finsupp.ofSupportFinite]
    · funext w
      simp
  map_add' a b := by
    apply Prod.ext
    · ext v
      change -Real.log (v ((a.toMul : K) * (b.toMul : K))) =
        -Real.log (v (a.toMul : K)) + -Real.log (v (b.toMul : K))
      rw [map_mul, Real.log_mul
        (FinitePlace.pos_iff.mpr a.toMul.ne_zero).ne'
        (FinitePlace.pos_iff.mpr b.toMul.ne_zero).ne']
      ring
    · funext w
      change -(w.mult : ℝ) * Real.log (w ((a.toMul : K) * (b.toMul : K))) =
        -(w.mult : ℝ) * Real.log (w (a.toMul : K)) +
          -(w.mult : ℝ) * Real.log (w (b.toMul : K))
      rw [map_mul, Real.log_mul
        (InfinitePlace.pos_iff.mpr a.toMul.ne_zero).ne'
        (InfinitePlace.pos_iff.mpr b.toMul.ne_zero).ne']
      ring

variable (K)

def finiteProjection (v : FinitePlace K) : Divisor K →ₗ[ℝ] ℝ :=
  (Finsupp.lapply v).comp (LinearMap.fst ℝ _ _)

def infiniteProjection (w : InfinitePlace K) : Divisor K →ₗ[ℝ] ℝ :=
  (LinearMap.proj w).comp (LinearMap.snd ℝ _ _)

@[simp] theorem finiteProjection_principal (v : FinitePlace K) (a : Kˣ) :
    finiteProjection K v (principalDivisor (Additive.ofMul a)) =
      -Real.log (v (a : K)) := rfl

@[simp] theorem infiniteProjection_principal (w : InfinitePlace K) (a : Kˣ) :
    infiniteProjection K w (principalDivisor (Additive.ofMul a)) =
      -(w.mult : ℝ) * Real.log (w (a : K)) := rfl

def degree : Divisor K →ₗ[ℝ] ℝ :=
  (Finsupp.lsum ℝ (fun _ : FinitePlace K => LinearMap.id)).comp
      (LinearMap.fst ℝ _ _) +
    (∑ w : InfinitePlace K, infiniteProjection K w)

theorem degree_apply (D : Divisor K) :
    degree K D = D.1.sum (fun _ x => x) + ∑ w, D.2 w := by
  simp [degree, infiniteProjection]
  rfl

theorem finitePrincipal_sum (a : Kˣ) :
    (finitePrincipal a).sum (fun _ x => x) =
      -(∑ᶠ v : FinitePlace K, Real.log (v (a : K))) := by
  have he : (∑ᶠ v : FinitePlace K, -Real.log (v (a : K))) =
      (finitePrincipal a).sum (fun _ x => x) := by
    apply finsum_eq_sum_of_support_subset
    intro v hv
    exact (Finsupp.mem_support_iff).mpr hv
  rw [← he, finsum_neg_distrib]

theorem degree_principal (a : Kˣ) :
    degree K (principalDivisor (Additive.ofMul a)) = 0 := by
  rw [degree_apply]
  change (finitePrincipal a).sum (fun _ x => x) +
    (∑ w : InfinitePlace K, -(w.mult : ℝ) * Real.log (w (a : K))) = 0
  rw [finitePrincipal_sum]
  simp_rw [neg_mul, Finset.sum_neg_distrib]
  have h := NumberFieldLogDegree.all_places_log_sum_zero a.ne_zero
  linarith

def realBirat : Submodule ℝ (Divisor K) :=
  Submodule.span ℝ (Set.range (principalDivisor (K := K)))

theorem principal_mem_realBirat (a : Kˣ) :
    principalDivisor (Additive.ofMul a) ∈ realBirat K :=
  Submodule.subset_span ⟨Additive.ofMul a, rfl⟩

theorem realBirat_le_degree_ker : realBirat K ≤ LinearMap.ker (degree K) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact degree_principal K a.toMul

def effective : AddSubmonoid (Divisor K) where
  carrier D := (∀ v, 0 ≤ D.1 v) ∧ ∀ w, 0 ≤ D.2 w
  zero_mem' := ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  add_mem' hI hJ :=
    ⟨fun v => add_nonneg (hI.1 v) (hJ.1 v),
     fun w => add_nonneg (hI.2 w) (hJ.2 w)⟩

theorem degree_nonneg_of_effective (D : effective K) :
    0 ≤ degree K D.1 := by
  rw [degree_apply]
  exact add_nonneg
    (Finset.sum_nonneg fun v _ => D.2.1 v)
    (Finset.sum_nonneg fun w _ => D.2.2 w)

abbrev realModel : FrdI.Model.Data (CategoryTheory.Discrete PUnit.{u + 1}) where
  Phi _ := effective K
  Phigp _ := Divisor K
  B _ := realBirat K
  phiMap _ := AddMonoidHom.id _
  phigpMap _ := AddMonoidHom.id _
  bMap _ := AddMonoidHom.id _
  incl _ := (effective K).subtype
  div _ := (realBirat K).subtype.toAddMonoidHom
  phigpMap_id _ _ := rfl
  phigpMap_comp _ _ _ := rfl
  phiMap_id _ _ := rfl
  phiMap_comp _ _ _ := rfl
  bMap_id _ _ := rfl
  bMap_comp _ _ _ := rfl
  incl_natural _ _ := rfl
  div_natural _ _ := rfl

theorem realModel_div_degree_zero
    (b : (realModel K).B ⟨PUnit.unit⟩) :
    degree K ((realModel K).div ⟨PUnit.unit⟩ b) = 0 :=
  realBirat_le_degree_ker K b.property

theorem realModel_hom_degree
    {A B : FrdI.Model.Obj (realModel K)}
    (f : FrdI.Model.Hom (realModel K) A B) :
    (f.degFr : ℝ) * degree K A.alpha ≤ degree K B.alpha := by
  have h := congrArg (degree K) f.rel
  change degree K ((f.degFr : ℤ) • (A.alpha : Divisor K) + f.divisor.val) =
    degree K ((B.alpha : Divisor K) + f.unit.val) at h
  rw [map_add, map_zsmul, map_add] at h
  have hu : degree K f.unit.val = 0 :=
    realBirat_le_degree_ker K f.unit.property
  have hz := degree_nonneg_of_effective K f.divisor
  rw [hu, add_zero] at h
  simp only [zsmul_eq_mul, Int.cast_natCast] at h
  linarith

end CitedLV.Theorem311.NumberFieldRealDivisor
