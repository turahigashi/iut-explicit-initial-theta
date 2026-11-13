-- Arithmetic (non-toy) inhabitation of the FVdash two-square skeleton:
-- rho-normalization weights as scalings of Multiplicative ℝ.
import M3.thetalink.FVdashPrimeStripSkeleton
import M3.relative.Cor312Assembly

/-!
# An arithmetic instance of the prime-strip two-square skeleton

The existing skeleton `M3.thetalink.FVdashPrimeStripSkeleton`
formalises Definition 5.2(iv)'s four-tuple shape with the two
compatibility squares (`PrimeLabelSquare`, `RhoNaturalitySquare`)
kept external, and provides finite toy models.  This module
inhabits the same shape with genuine arithmetic data:

* places `V = Fin 2`;
* local monoids `Multiplicative ℝ` (additive ℝ in multiplicative
  notation — the log-volume world);
* `rho` on the target side given by place-wise positive
  scalings `w v`, standing for the normalised weights of
  Remark 3.1.1(ii) / the `ρ`-normalisations of Example 3.5;
* the isomorphism transports the unnormalised strip to the
  normalised one, and both squares are proved, together with
  nondegeneracy (`FVdashIsoNondegenerate`).

This is *not* an actual Frobenioid or Hodge theatre: it shows
that Principle S ([W] §11, the working draft of the paper), as a typing discipline, is
inhabitable by non-degenerate real-valued data, and pins down
exactly what an inhabitation for the actual source
constructions would have to provide.  No new axioms.
Not independently re-checked.
-/

noncomputable section
set_option autoImplicit false

namespace Kouchiku.M3.FVdashArithmeticInstance

open Grounding.ThetaLink

/-- Scaling equivalence on `Multiplicative ℝ` (= additive
homothety `x ↦ a • x` in log-volume coordinates), as a
continuous multiplicative equivalence. -/
def scaleEquiv (a : ℝ) (ha : a ≠ 0) :
    Multiplicative ℝ ≃ₜ* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (a * Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd (a⁻¹ * Multiplicative.toAdd x)
  left_inv x := by
    apply Multiplicative.toAdd.injective
    show a⁻¹ * (a * Multiplicative.toAdd x)
      = Multiplicative.toAdd x
    rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  right_inv x := by
    apply Multiplicative.toAdd.injective
    show a * (a⁻¹ * Multiplicative.toAdd x)
      = Multiplicative.toAdd x
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    show a * (Multiplicative.toAdd x + Multiplicative.toAdd y)
      = a * Multiplicative.toAdd x + a * Multiplicative.toAdd y
    exact mul_add a _ _
  continuous_toFun := by
    exact continuous_ofAdd.comp
      (continuous_const.mul continuous_toAdd)
  continuous_invFun := by
    exact continuous_ofAdd.comp
      (continuous_const.mul continuous_toAdd)

@[simp] theorem scaleEquiv_apply (a : ℝ) (ha : a ≠ 0)
    (x : Multiplicative ℝ) :
    scaleEquiv a ha x
      = Multiplicative.ofAdd (a * Multiplicative.toAdd x) := rfl

/-- Place-wise normalisation weights, standing for the
`1 / [K_{v} : (F_mod)_v]`-type factors of Remark 3.1.1(ii).
The first place is left unscaled, the second is scaled. -/
def weight : Fin 2 → ℝ := ![1, 2]

theorem weight_ne_zero (v : Fin 2) : weight v ≠ 0 := by
  fin_cases v <;> simp [weight]

abbrev ArithPrime (_ : Unit) := Fin 2
abbrev ArithLocal (_ : Fin 2) := Unit
abbrev ArithGlobalLoc (_ : Unit) (_ : Fin 2) := Multiplicative ℝ
abbrev ArithLocalRlf (_ : Fin 2) (_ : Unit) := Multiplicative ℝ
abbrev ArithGlobalIso (_ _ : Unit) := Unit
abbrev ArithLocalIso (_ : Fin 2) (_ _ : Unit) := Unit

abbrev ArithFVdash :=
  FVdashPrimeStripRaw (Fin 2) Unit ArithPrime ArithLocal
    ArithGlobalLoc ArithLocalRlf

/-- Source strip: unnormalised `rho` (identity scaling). -/
def arithSource : ArithFVdash where
  global := ()
  primeEquiv := Equiv.refl (Fin 2)
  localObj := fun _ => ()
  rho := fun _ => ContinuousMulEquiv.refl (Multiplicative ℝ)

/-- Target strip: `rho` normalised by the place weights. -/
def arithTarget : ArithFVdash where
  global := ()
  primeEquiv := Equiv.refl (Fin 2)
  localObj := fun _ => ()
  rho := fun v => scaleEquiv (weight v) (weight_ne_zero v)

/-- The normalising isomorphism: identity on the global side,
weight scaling on the local realified side. -/
def arithIso :
    FVdashIsoRaw arithSource arithTarget ArithGlobalIso
      ArithLocalIso where
  globalIso := ()
  primeIso := Equiv.refl (Fin 2)
  localIso := fun _ => ()
  globalLocIso := fun _ =>
    ContinuousMulEquiv.refl (Multiplicative ℝ)
  localRlfIso := fun v =>
    scaleEquiv (weight v) (weight_ne_zero v)

theorem arith_prime_square : PrimeLabelSquare arithIso := by
  intro p
  rfl

theorem arith_rho_square : RhoNaturalitySquare arithIso := by
  intro v x
  rfl

/-- ★ The two-square isomorphism for the arithmetic instance. -/
def arithTwoSquare :
    TwoSquareFVdashIso arithSource arithTarget ArithGlobalIso
      ArithLocalIso :=
  arithIso.toTwoSquare arith_prime_square arith_rho_square

/-- The arithmetic instance is nondegenerate: all three
equivalences visibly do not collapse distinctions. -/
theorem arith_nondegenerate : FVdashIsoNondegenerate arithIso := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨0, 1, by decide, by decide⟩
  · refine ⟨1, Multiplicative.ofAdd 0, Multiplicative.ofAdd 1,
      ?_, ?_⟩ <;>
      · intro h
        have h2 : (0 : ℝ) = 1 := congrArg
          (fun z : Multiplicative ℝ => Multiplicative.toAdd z) h
        exact zero_ne_one h2
  · refine ⟨1, Multiplicative.ofAdd 0, Multiplicative.ofAdd 1,
      ?_, ?_⟩
    · intro h
      have h2 : (0 : ℝ) = 1 := congrArg
        (fun z : Multiplicative ℝ => Multiplicative.toAdd z) h
      exact zero_ne_one h2
    · intro h
      have h2 := congrArg
        (fun z : Multiplicative ℝ => Multiplicative.toAdd z) h
      simp [arithIso, weight] at h2

end Kouchiku.M3.FVdashArithmeticInstance

end

#print axioms Kouchiku.M3.FVdashArithmeticInstance.scaleEquiv
#print axioms Kouchiku.M3.FVdashArithmeticInstance.arithTwoSquare
#print axioms
  Kouchiku.M3.FVdashArithmeticInstance.arith_nondegenerate
