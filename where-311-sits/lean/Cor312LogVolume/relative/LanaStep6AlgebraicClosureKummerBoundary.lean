import Cor312LogVolume.relative.LanaStep6FiniteKummerRatio
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.Tactic.NormNum.IsSquare

noncomputable section

namespace Src.CoreLayer.LanaStep6.AlgebraicClosureKummerBoundary

open Src.CoreLayer.LanaStep6.FiniteKummerRatio
open Polynomial

universe u

variable (K : Type u) [Field K]

noncomputable def chosenClosureRoot
    (n : ℕ) [NeZero n] (a : (Closure K)ˣ) : Closure K :=
  Classical.choose
    (IsAlgClosed.exists_pow_nat_eq (a : Closure K) (NeZero.pos n))

theorem chosenClosureRoot_pow
    (n : ℕ) [NeZero n] (a : (Closure K)ˣ) :
    chosenClosureRoot K n a ^ n = (a : Closure K) :=
  Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq (a : Closure K) (NeZero.pos n))

theorem chosenClosureRoot_ne_zero
    (n : ℕ) [NeZero n] (a : (Closure K)ˣ) :
    chosenClosureRoot K n a ≠ 0 := by
  intro hzero
  have hpow := chosenClosureRoot_pow K n a
  rw [hzero, zero_pow (NeZero.ne n)] at hpow
  exact (Units.ne_zero a) hpow.symm

def movingRatioValue
    (n : ℕ) [NeZero n] (a : (Closure K)ˣ)
    (sigma : AbsGal K) : Closure K :=
  toAlgEquiv K sigma (chosenClosureRoot K n a) / chosenClosureRoot K n a

theorem movingRatioValue_pow
    (n : ℕ) [NeZero n] (a : (Closure K)ˣ)
    (sigma : AbsGal K) :
    movingRatioValue K n a sigma ^ n =
      toAlgEquiv K sigma (a : Closure K) / (a : Closure K) := by
  unfold movingRatioValue
  rw [div_pow, ← map_pow, chosenClosureRoot_pow]

theorem movingRatio_pow_eq_one_iff_fixed
    (n : ℕ) [NeZero n] (a : (Closure K)ˣ)
    (sigma : AbsGal K) :
    movingRatioValue K n a sigma ^ n = 1 ↔
      toAlgEquiv K sigma (a : Closure K) = (a : Closure K) := by
  rw [movingRatioValue_pow]
  exact div_eq_one_iff_eq (Units.ne_zero a)

theorem movingRatio_not_root_of_unity_of_not_fixed
    (n : ℕ) [NeZero n] (a : (Closure K)ˣ)
    (sigma : AbsGal K)
    (hmove : toAlgEquiv K sigma (a : Closure K) ≠ (a : Closure K)) :
    movingRatioValue K n a sigma ^ n ≠ 1 := by
  exact (movingRatio_pow_eq_one_iff_fixed K n a sigma).not.mpr hmove

theorem all_movingRatios_are_roots_iff_galois_fixed
    (n : ℕ) [NeZero n] (a : (Closure K)ˣ) :
    (∀ sigma : AbsGal K, movingRatioValue K n a sigma ^ n = 1) ↔
      (∀ sigma : AbsGal K,
        toAlgEquiv K sigma (a : Closure K) = (a : Closure K)) := by
  constructor
  · intro h sigma
    exact (movingRatio_pow_eq_one_iff_fixed K n a sigma).1 (h sigma)
  · intro h sigma
    exact (movingRatio_pow_eq_one_iff_fixed K n a sigma).2 (h sigma)

theorem baseFieldValue_fixed
    (a : Kˣ) (sigma : AbsGal K) :
    toAlgEquiv K sigma (algebraMap K (Closure K) (a : K)) =
      algebraMap K (Closure K) (a : K) := by
  exact toAlgEquiv_commutes K sigma (a : K)

theorem rat_sqrtTwo_moved_witness :
    ∃ (a : (Closure ℚ)ˣ) (sigma : AbsGal ℚ),
      toAlgEquiv ℚ sigma (a : Closure ℚ) ≠ (a : Closure ℚ) := by
  let twoUnit : (Closure ℚ)ˣ :=
    Units.mk0 (2 : Closure ℚ) (by norm_num)
  let r : Closure ℚ := chosenClosureRoot ℚ 2 twoUnit
  have hr2 : r ^ 2 = (2 : Closure ℚ) := by
    simpa [r, twoUnit] using chosenClosureRoot_pow ℚ 2 twoUnit
  have hr0 : r ≠ 0 := by
    intro hr
    rw [hr, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hr2
    norm_num at hr2
  have hnotSquare : ∀ q : ℚ, q ^ 2 ≠ 2 := by
    intro q hq
    have h2 : ¬ IsSquare (2 : ℚ) := by norm_num
    apply h2
    exact ⟨q, by simpa [pow_two] using hq.symm⟩
  let p : ℚ[X] := Polynomial.X ^ 2 - Polynomial.C 2
  have hpIrred : Irreducible p := by
    dsimp [p]
    exact X_pow_sub_C_irreducible_of_prime Nat.prime_two hnotSquare
  have hpRoot : Polynomial.aeval r p = 0 := by
    dsimp [p]
    simp [hr2]
  have hpMonic : p.Monic := by
    dsimp [p]
    exact monic_X_pow_sub_C (2 : ℚ) (by decide)
  have hmin : p = minpoly ℚ r :=
    minpoly.eq_of_irreducible_of_monic hpIrred hpRoot hpMonic
  have hnegRoot : Polynomial.aeval (-r) (minpoly ℚ r) = 0 := by
    rw [← hmin]
    dsimp [p]
    simp [← pow_two, hr2]
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.instIsAlgClosure ℚ
  haveI : Normal ℚ (AlgebraicClosure ℚ) :=
    IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  obtain ⟨s, hs⟩ :=
    minpoly.exists_algEquiv_of_root'
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic r) hnegRoot
  let sigma : AbsGal ℚ := s
  let a : (Closure ℚ)ˣ := Units.mk0 r hr0
  refine ⟨a, sigma, ?_⟩
  have hs' : toAlgEquiv ℚ sigma r = -r := by
    exact hs
  change toAlgEquiv ℚ sigma r ≠ r
  rw [hs']
  intro h
  exact hr0 ((CharZero.neg_eq_self_iff).mp h)

theorem rat_sqrtTwo_moved_with_square :
    ∃ (a : (Closure ℚ)ˣ) (sigma : AbsGal ℚ),
      ((a : (Closure ℚ)ˣ) : Closure ℚ) ^ 2 = (2 : Closure ℚ) ∧
      toAlgEquiv ℚ sigma (a : Closure ℚ) ≠ (a : Closure ℚ) := by
  let twoUnit : (Closure ℚ)ˣ :=
    Units.mk0 (2 : Closure ℚ) (by norm_num)
  let r : Closure ℚ := chosenClosureRoot ℚ 2 twoUnit
  have hr2 : r ^ 2 = (2 : Closure ℚ) := by
    simpa [r, twoUnit] using chosenClosureRoot_pow ℚ 2 twoUnit
  have hr0 : r ≠ 0 := by
    intro hr
    rw [hr, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hr2
    norm_num at hr2
  have hnotSquare : ∀ q : ℚ, q ^ 2 ≠ 2 := by
    intro q hq
    have h2 : ¬ IsSquare (2 : ℚ) := by norm_num
    apply h2
    exact ⟨q, by simpa [pow_two] using hq.symm⟩
  let p : ℚ[X] := Polynomial.X ^ 2 - Polynomial.C 2
  have hpIrred : Irreducible p := by
    dsimp [p]
    exact X_pow_sub_C_irreducible_of_prime Nat.prime_two hnotSquare
  have hpRoot : Polynomial.aeval r p = 0 := by
    dsimp [p]
    simp [hr2]
  have hpMonic : p.Monic := by
    dsimp [p]
    exact monic_X_pow_sub_C (2 : ℚ) (by decide)
  have hmin : p = minpoly ℚ r :=
    minpoly.eq_of_irreducible_of_monic hpIrred hpRoot hpMonic
  have hnegRoot : Polynomial.aeval (-r) (minpoly ℚ r) = 0 := by
    rw [← hmin]
    dsimp [p]
    simp [← pow_two, hr2]
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.instIsAlgClosure ℚ
  haveI : Normal ℚ (AlgebraicClosure ℚ) :=
    IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  obtain ⟨s, hs⟩ :=
    minpoly.exists_algEquiv_of_root'
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic r) hnegRoot
  let sigma : AbsGal ℚ := s
  let a : (Closure ℚ)ˣ := Units.mk0 r hr0
  refine ⟨a, sigma, ?_, ?_⟩
  · exact hr2
  · have hs' : toAlgEquiv ℚ sigma r = -r := hs
    change toAlgEquiv ℚ sigma r ≠ r
    rw [hs']
    intro h
    exact hr0 ((CharZero.neg_eq_self_iff).mp h)

end Src.CoreLayer.LanaStep6.AlgebraicClosureKummerBoundary

end
