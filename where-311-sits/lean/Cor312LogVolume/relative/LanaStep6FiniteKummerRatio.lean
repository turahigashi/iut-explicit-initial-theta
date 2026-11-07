import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Algebra.Group.Action.Units
import Mathlib.Tactic.FieldSimp

noncomputable section

namespace Src.CoreLayer.LanaStep6.FiniteKummerRatio

universe u

variable (K : Type u) [Field K]

abbrev Closure := AlgebraicClosure K
abbrev AbsGal := Field.absoluteGaloisGroup K
abbrev Mu (n : ℕ) := rootsOfUnity n (Closure K)

def toAlgEquiv (s : AbsGal K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
  s

theorem toAlgEquiv_mul (s t : AbsGal K) :
    toAlgEquiv K (s * t) = toAlgEquiv K s * toAlgEquiv K t := rfl

theorem toAlgEquiv_inv (s : AbsGal K) :
    toAlgEquiv K s⁻¹ = (toAlgEquiv K s).symm := rfl

theorem toAlgEquiv_one :
    toAlgEquiv K 1 = AlgEquiv.refl := rfl

theorem toAlgEquiv_commutes (s : AbsGal K) (a : K) :
    toAlgEquiv K s (algebraMap K (AlgebraicClosure K) a) =
      algebraMap K (AlgebraicClosure K) a :=
  (toAlgEquiv K s).commutes a

noncomputable def chosenRoot (n : ℕ) [NeZero n] (a : Kˣ) : Closure K :=
  Classical.choose
    (IsAlgClosed.exists_pow_nat_eq
      (algebraMap K (Closure K) (a : K)) (NeZero.pos n))

theorem chosenRoot_pow (n : ℕ) [NeZero n] (a : Kˣ) :
    chosenRoot K n a ^ n = algebraMap K (Closure K) (a : K) :=
  Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq
      (algebraMap K (Closure K) (a : K)) (NeZero.pos n))

theorem chosenRoot_ne_zero (n : ℕ) [NeZero n] (a : Kˣ) :
    chosenRoot K n a ≠ 0 := by
  intro hzero
  have hpow := chosenRoot_pow K n a
  rw [hzero, zero_pow (NeZero.ne n)] at hpow
  have ha0 : (0 : K) = (a : K) := by
    apply (algebraMap K (Closure K)).injective
    simpa using hpow
  exact (Units.ne_zero a) ha0.symm

def ratioValue (n : ℕ) [NeZero n] (a : Kˣ)
    (sigma : AbsGal K) : Closure K :=
  toAlgEquiv K sigma (chosenRoot K n a) / chosenRoot K n a

theorem ratioValue_pow (n : ℕ) [NeZero n] (a : Kˣ)
    (sigma : AbsGal K) :
    ratioValue K n a sigma ^ n = 1 := by
  have ha :
      algebraMap K (Closure K) (a : K) ≠ 0 := by
    intro hzero
    have : (a : K) = 0 :=
      (algebraMap K (Closure K)).injective (by simpa using hzero)
    exact (Units.ne_zero a) this
  unfold ratioValue
  rw [div_pow, ← map_pow, chosenRoot_pow]
  rw [toAlgEquiv_commutes K sigma]
  exact div_self ha

theorem ratioValue_ne_zero (n : ℕ) [NeZero n] (a : Kˣ)
    (sigma : AbsGal K) :
    ratioValue K n a sigma ≠ 0 := by
  unfold ratioValue
  apply div_ne_zero
  · intro hzero
    apply chosenRoot_ne_zero K n a
    apply (toAlgEquiv K sigma).injective
    simpa using hzero
  · exact chosenRoot_ne_zero K n a

def ratioUnit (n : ℕ) [NeZero n] (a : Kˣ)
    (sigma : AbsGal K) : (Closure K)ˣ :=
  Units.mk0 (ratioValue K n a sigma)
    (ratioValue_ne_zero K n a sigma)

@[simp] theorem ratioUnit_coe (n : ℕ) [NeZero n] (a : Kˣ)
    (sigma : AbsGal K) :
    ((ratioUnit K n a sigma : (Closure K)ˣ) : Closure K) =
      ratioValue K n a sigma := rfl

theorem ratioUnit_pow (n : ℕ) [NeZero n] (a : Kˣ)
    (sigma : AbsGal K) :
    ratioUnit K n a sigma ^ n = 1 := by
  apply Units.ext
  change ratioValue K n a sigma ^ n = 1
  exact ratioValue_pow K n a sigma

def ratioRoot (n : ℕ) [NeZero n] (a : Kˣ)
    (sigma : AbsGal K) : Mu K n :=
  ⟨ratioUnit K n a sigma,
    (mem_rootsOfUnity n (ratioUnit K n a sigma)).2
      (ratioUnit_pow K n a sigma)⟩

@[simp] theorem ratioRoot_coe (n : ℕ) [NeZero n] (a : Kˣ)
    (sigma : AbsGal K) :
    (((ratioRoot K n a sigma : Mu K n) : (Closure K)ˣ) : Closure K) =
      ratioValue K n a sigma := rfl

def galoisOnRoots (n : ℕ) [NeZero n] (sigma : AbsGal K) :
    Mu K n ≃* Mu K n :=
  (toAlgEquiv K sigma).toMulEquiv.restrictRootsOfUnity n

@[simp] theorem galoisOnRoots_coe (n : ℕ) [NeZero n]
    (sigma : AbsGal K) (z : Mu K n) :
    ((((galoisOnRoots K n sigma) z : Mu K n) : (Closure K)ˣ) : Closure K) =
      toAlgEquiv K sigma (((z : Mu K n) : (Closure K)ˣ) : Closure K) := by
  rfl

@[simp] theorem galoisOnRoots_inv (n : ℕ) [NeZero n] (sigma : AbsGal K) :
    galoisOnRoots K n sigma⁻¹ = (galoisOnRoots K n sigma).symm := by
  unfold galoisOnRoots
  rw [toAlgEquiv_inv]
  change
    ((toAlgEquiv K sigma).toMulEquiv).symm.restrictRootsOfUnity n =
      (((toAlgEquiv K sigma).toMulEquiv).restrictRootsOfUnity n).symm
  exact
    (MulEquiv.restrictRootsOfUnity_symm
      (k := n) (toAlgEquiv K sigma).toMulEquiv).symm

theorem ratioRoot_mul (n : ℕ) [NeZero n] (a : Kˣ)
    (sigma tau : AbsGal K) :
    ratioRoot K n a (sigma * tau) =
      galoisOnRoots K n sigma (ratioRoot K n a tau) *
        ratioRoot K n a sigma := by
  apply Subtype.ext
  apply Units.ext
  change
    ratioValue K n a (sigma * tau) =
      toAlgEquiv K sigma (ratioValue K n a tau) * ratioValue K n a sigma
  have hr : chosenRoot K n a ≠ 0 :=
    chosenRoot_ne_zero K n a
  have hsigmar : toAlgEquiv K sigma (chosenRoot K n a) ≠ 0 := by
    intro hzero
    apply hr
    apply (toAlgEquiv K sigma).injective
    simpa using hzero
  unfold ratioValue
  rw [toAlgEquiv_mul, AlgEquiv.mul_apply, map_div₀]
  field_simp [hr, hsigmar]

def finiteKummerRatio (n : ℕ) [NeZero n] (a : Kˣ) :
    AbsGal K → Mu K n :=
  ratioRoot K n a

@[simp] theorem finiteKummerRatio_mul (n : ℕ) [NeZero n] (a : Kˣ)
    (sigma tau : AbsGal K) :
    finiteKummerRatio K n a (sigma * tau) =
      galoisOnRoots K n sigma (finiteKummerRatio K n a tau) *
        finiteKummerRatio K n a sigma :=
  ratioRoot_mul K n a sigma tau

end Src.CoreLayer.LanaStep6.FiniteKummerRatio

end
