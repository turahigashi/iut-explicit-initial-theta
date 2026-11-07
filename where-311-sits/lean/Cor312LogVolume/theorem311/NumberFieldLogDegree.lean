import Cor312LogVolume.theorem311.GlobalMultiplierDegreeMonotonicity
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
noncomputable section

open scoped nonZeroDivisors
open NumberField

namespace CitedLV.Theorem311.NumberFieldLogDegree

variable {K : Type*} [Field K] [NumberField K]

theorem arch_log_sum {a : K} (ha : a ≠ 0) :
    (∑ w : InfinitePlace K, (w.mult : Real) * Real.log (w a)) =
      Real.log (|(Algebra.norm ℚ a)| : Real) := by
  have h := congrArg Real.log (InfinitePlace.prod_eq_abs_norm a)
  rw [Real.log_prod (fun w _ =>
    pow_ne_zero _ (ne_of_gt (InfinitePlace.pos_iff.mpr ha)))] at h
  simpa only [Real.log_pow, Rat.cast_abs] using h

theorem finite_log_sum {a : K} (ha : a ≠ 0) :
    (∑ᶠ w : FinitePlace K, Real.log (w a)) =
      -Real.log (|(Algebra.norm ℚ a)| : Real) := by
  rw [← Real.log_finprod (fun w => FinitePlace.pos_iff.mpr ha),
    FinitePlace.prod_eq_inv_abs_norm ha]
  simp only [Rat.cast_inv, Rat.cast_abs, Real.log_inv]

theorem all_places_log_sum_zero {a : K} (ha : a ≠ 0) :
    (∑ w : InfinitePlace K, (w.mult : Real) * Real.log (w a)) +
      (∑ᶠ w : FinitePlace K, Real.log (w a)) = 0 := by
  rw [arch_log_sum ha, finite_log_sum ha, add_neg_cancel]

theorem arch_log_weights_eq_zero (c : InfinitePlace K → ℝ)
    (h : ∀ a : K, ∑ w : InfinitePlace K, c w * Real.log (w a) = 0) :
    c = 0 := by
  classical
  funext v
  let z : (w : InfinitePlace K) → WithAbs w.1 :=
    fun w => algebraMap K (WithAbs w.1) (if w = v then 2 else 1)
  let F : ((w : InfinitePlace K) → WithAbs w.1) → ℝ :=
    fun x => ∑ w : InfinitePlace K, c w * Real.log ‖x w‖
  have hz : ∀ w, z w ≠ 0 := by
    intro w
    dsimp [z]
    apply (map_ne_zero (algebraMap K (WithAbs w.1))).mpr
    split_ifs <;> norm_num
  have hF : ContinuousAt F z := by
    apply tendsto_finsetSum
    intro w _
    exact continuousAt_const.mul
      (((continuous_apply w).continuousAt.norm).log (norm_ne_zero_iff.mpr (hz w)))
  have he : F z = 0 := hF.continuousWithinAt.eq_const_of_mem_closure
    (InfinitePlace.denseRange_algebraMap_pi K z) (by
      rintro x ⟨a, rfl⟩
      exact h a)
  have he' : c v * Real.log 2 = 0 := by
    have hn : ∀ w, ‖z w‖ = if w = v then 2 else 1 := by
      intro w
      change w (if w = v then (2 : K) else 1) = _
      split_ifs
      · exact w.map_natCast 2
      · exact map_one w
    simpa only [F, hn, apply_ite Real.log, Real.log_one,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using he
  exact (mul_eq_zero.mp he').resolve_right (ne_of_gt (Real.log_pos (by norm_num)))

theorem arch_weights_eq_mult_of_product_formula (c : InfinitePlace K → ℝ)
    (h : ∀ a : K, a ≠ 0 →
      (∑ w : InfinitePlace K, c w * Real.log (w a)) +
        (∑ᶠ w : FinitePlace K, Real.log (w a)) = 0) :
    c = fun w => (w.mult : ℝ) := by
  have he := arch_log_weights_eq_zero (fun w => c w - (w.mult : ℝ)) (by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    · simp_rw [sub_mul, Finset.sum_sub_distrib]
      have hh := h a ha
      have hp := all_places_log_sum_zero ha
      linarith)
  funext w
  have hw := congrFun he w
  exact sub_eq_zero.mp hw

variable (K)

@[ext] structure Object where
  ideal : FractionalIdeal (𝓞 K)⁰ K
  ideal_ne_zero : ideal ≠ 0
  logRadius : InfinitePlace K → Real

variable {K}

def degree (J : Object K) : Real :=
  -Real.log (FractionalIdeal.absNorm J.ideal : Real) +
    ∑ w : InfinitePlace K, (w.mult : Real) * J.logRadius w

def principalAction (a : Kˣ) (J : Object K) : Object K where
  ideal := FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) * J.ideal
  ideal_ne_zero := mul_ne_zero
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero a)) J.ideal_ne_zero
  logRadius := fun w => J.logRadius w + Real.log (w (a : K))

def Inclusion (I J : Object K) : Prop :=
  I.ideal ≤ J.ideal ∧ ∀ w, I.logRadius w ≤ J.logRadius w

theorem absNorm_pos {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    0 < FractionalIdeal.absNorm I := by
  exact lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I)
    (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hI))

theorem degree_principalAction (a : Kˣ) (J : Object K) :
    degree (principalAction a J) = degree J := by
  have hI : (FractionalIdeal.absNorm J.ideal : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt (absNorm_pos J.ideal_ne_zero))
  have ha : (|(Algebra.norm ℚ (a : K))| : Real) ≠ 0 := by
    exact_mod_cast (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr (Units.ne_zero a)))
  dsimp only [degree, principalAction]
  rw [map_mul, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, Rat.cast_abs,
    Real.log_mul ha hI]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, arch_log_sum (Units.ne_zero a)]
  ring

theorem absNorm_antitone {I J : FractionalIdeal (𝓞 K)⁰ K}
    (hI : I ≠ 0) (hJ : J ≠ 0) (hIJ : I ≤ J) :
    FractionalIdeal.absNorm J ≤ FractionalIdeal.absNorm I := by
  have hmul : I * J⁻¹ ≤ 1 := by
    calc
      I * J⁻¹ ≤ J * J⁻¹ := mul_le_mul_of_nonneg_right hIJ zero_le
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨A, hA⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hmul
  have hA0 : A ≠ ⊥ := by
    intro h0
    have hz : I * J⁻¹ = 0 := by rw [← hA, h0]; simp
    exact (mul_ne_zero hI (inv_ne_zero hJ)) hz
  have hNA : 1 ≤ (Ideal.absNorm A : ℚ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hA0)
  have hquot : 1 ≤ FractionalIdeal.absNorm I / FractionalIdeal.absNorm J := by
    rw [div_eq_mul_inv, ← map_inv₀, ← map_mul, ← hA, FractionalIdeal.coeIdeal_absNorm]
    exact hNA
  simpa using (le_div_iff₀ (absNorm_pos hJ)).mp hquot

theorem degree_mono {I J : Object K} (h : Inclusion I J) :
    degree I ≤ degree J := by
  have hnorm : (FractionalIdeal.absNorm J.ideal : Real) ≤
      (FractionalIdeal.absNorm I.ideal : Real) := by
    exact_mod_cast absNorm_antitone I.ideal_ne_zero J.ideal_ne_zero h.1
  have hpos : (0 : Real) < (FractionalIdeal.absNorm J.ideal : Real) := by
    exact_mod_cast absNorm_pos J.ideal_ne_zero
  have hlog := Real.log_le_log hpos hnorm
  have harch :
      (∑ w : InfinitePlace K, (w.mult : Real) * I.logRadius w) ≤
        ∑ w : InfinitePlace K, (w.mult : Real) * J.logRadius w := by
    exact Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (h.2 w) (Nat.cast_nonneg _)
  dsimp only [degree]
  linarith

def degreeSystem : GlobalMultiplierDegreeMonotonicity.DegreeSystem where
  Obj := Object K
  Multiplier := Kˣ
  act := principalAction
  LE := Inclusion
  degree := degree
  degree_act := degree_principalAction
  degree_mono := degree_mono

def tensorUnit : Object K where
  ideal := 1
  ideal_ne_zero := one_ne_zero
  logRadius := fun _ => 0

def tensorPower (M : Nat) (J : Object K) : Object K where
  ideal := J.ideal ^ M
  ideal_ne_zero := pow_ne_zero M J.ideal_ne_zero
  logRadius := fun w => (M : Real) * J.logRadius w

theorem tensorPower_zero (J : Object K) : tensorPower 0 J = tensorUnit := by
  ext <;> simp [tensorPower, tensorUnit]

theorem tensorPower_one (J : Object K) : tensorPower 1 J = J := by
  ext <;> simp [tensorPower]

theorem degree_tensorPower (M : Nat) (J : Object K) :
    degree (tensorPower M J) = (M : Real) * degree J := by
  dsimp only [degree, tensorPower]
  rw [map_pow, Rat.cast_pow, Real.log_pow]
  have harch :
      (∑ w : InfinitePlace K, (w.mult : Real) * ((M : Real) * J.logRadius w)) =
        (M : Real) * ∑ w : InfinitePlace K, (w.mult : Real) * J.logRadius w := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [harch]
  ring

def tensorDegreeSystem : GlobalMultiplierDegreeMonotonicity.TensorDegreeSystem where
  toDegreeSystem := degreeSystem (K := K)
  tensorUnit := tensorUnit
  tensorPower := tensorPower
  tensor_zero := tensorPower_zero
  tensor_one := tensorPower_one
  degree_tensor := degree_tensorPower

def archConstant (r : Real) : Object K where
  ideal := 1
  ideal_ne_zero := one_ne_zero
  logRadius := fun _ => r

theorem degree_archConstant (r : Real) :
    degree (archConstant (K := K) r) = (Module.finrank ℚ K : Real) * r := by
  simp only [degree, archConstant, FractionalIdeal.absNorm_one, Rat.cast_one,
    Real.log_one, neg_zero, zero_add, ← Finset.sum_mul]
  congr 1
  exact_mod_cast (InfinitePlace.sum_mult_eq (K := K))

theorem degree_archConstant_one_pos : 0 < degree (archConstant (K := K) 1) := by
  rw [degree_archConstant, mul_one]
  exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)

end CitedLV.Theorem311.NumberFieldLogDegree
end
