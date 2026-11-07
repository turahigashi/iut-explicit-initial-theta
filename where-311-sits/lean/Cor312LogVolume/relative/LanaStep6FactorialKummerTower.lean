import Cor312LogVolume.relative.LanaStep6FiniteKummerRatio
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section

namespace Src.CoreLayer.LanaStep6.FactorialKummerTower

open Src.CoreLayer.LanaStep6.FiniteKummerRatio

universe u

variable (K : Type u) [Field K]

def stageDegree (n : ℕ) : ℕ :=
  Nat.factorial (n + 1)

theorem stageDegree_pos (n : ℕ) : 0 < stageDegree n :=
  Nat.factorial_pos _

theorem stageDegree_ne_zero (n : ℕ) : stageDegree n ≠ 0 :=
  (stageDegree_pos n).ne'

local instance stageDegreeNeZero (n : ℕ) : NeZero (stageDegree n) :=
  ⟨stageDegree_ne_zero n⟩

theorem stageDegree_succ (n : ℕ) :
    stageDegree (n + 1) = (n + 2) * stageDegree n := by
  simp [stageDegree, Nat.factorial_succ, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

noncomputable def rootTower (a : Kˣ) : ℕ → Closure K
  | 0 => algebraMap K (Closure K) (a : K)
  | n + 1 =>
      Classical.choose
        (IsAlgClosed.exists_pow_nat_eq
          (rootTower a n) (n := n + 2) (by omega))

theorem rootTower_succ_pow (a : Kˣ) (n : ℕ) :
    rootTower K a (n + 1) ^ (n + 2) = rootTower K a n := by
  exact Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq
      (rootTower K a n) (n := n + 2) (by omega))

theorem rootTower_pow (a : Kˣ) (n : ℕ) :
    rootTower K a n ^ stageDegree n =
      algebraMap K (Closure K) (a : K) := by
  induction n with
  | zero =>
      simp [rootTower, stageDegree]
  | succ n ih =>
      rw [stageDegree_succ, pow_mul, rootTower_succ_pow, ih]

theorem rootTower_ne_zero (a : Kˣ) (n : ℕ) :
    rootTower K a n ≠ 0 := by
  intro hzero
  have hpow := rootTower_pow K a n
  rw [hzero, zero_pow (stageDegree_ne_zero n)] at hpow
  have ha0 : (0 : K) = (a : K) := by
    apply (algebraMap K (Closure K)).injective
    simpa using hpow
  exact (Units.ne_zero a) ha0.symm

abbrev StageMu (n : ℕ) := rootsOfUnity (stageDegree n) (Closure K)

def transitionMu (n : ℕ) :
    StageMu K (n + 1) →* StageMu K n where
  toFun z :=
    ⟨z.1 ^ (n + 2), by
      apply (mem_rootsOfUnity (stageDegree n) _).2
      rw [← pow_mul, ← stageDegree_succ]
      exact (mem_rootsOfUnity (stageDegree (n + 1)) z.1).1 z.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_pow]

@[simp] theorem transitionMu_coe (n : ℕ) (z : StageMu K (n + 1)) :
    (((transitionMu K n z : StageMu K n) : (Closure K)ˣ) : Closure K) =
      ((((z : StageMu K (n + 1)) : (Closure K)ˣ) : Closure K) ^ (n + 2)) := by
  rfl

def towerRatioValue (a : Kˣ) (n : ℕ) (sigma : AbsGal K) : Closure K :=
  toAlgEquiv K sigma (rootTower K a n) / rootTower K a n

theorem towerRatioValue_ne_zero (a : Kˣ) (n : ℕ) (sigma : AbsGal K) :
    towerRatioValue K a n sigma ≠ 0 := by
  unfold towerRatioValue
  apply div_ne_zero
  · intro hzero
    apply rootTower_ne_zero K a n
    apply (toAlgEquiv K sigma).injective
    simpa using hzero
  · exact rootTower_ne_zero K a n

def towerRatioUnit (a : Kˣ) (n : ℕ) (sigma : AbsGal K) : (Closure K)ˣ :=
  Units.mk0 (towerRatioValue K a n sigma)
    (towerRatioValue_ne_zero K a n sigma)

@[simp] theorem towerRatioUnit_coe
    (a : Kˣ) (n : ℕ) (sigma : AbsGal K) :
    ((towerRatioUnit K a n sigma : (Closure K)ˣ) : Closure K) =
      towerRatioValue K a n sigma := rfl

theorem towerRatioUnit_pow (a : Kˣ) (n : ℕ) (sigma : AbsGal K) :
    towerRatioUnit K a n sigma ^ stageDegree n = 1 := by
  apply Units.ext
  change towerRatioValue K a n sigma ^ stageDegree n = 1
  unfold towerRatioValue
  rw [div_pow, ← map_pow, rootTower_pow]
  simp

def towerRatioRoot (a : Kˣ) (n : ℕ) (sigma : AbsGal K) : StageMu K n :=
  ⟨towerRatioUnit K a n sigma,
    (mem_rootsOfUnity (stageDegree n) _).2
      (towerRatioUnit_pow K a n sigma)⟩

@[simp] theorem towerRatioRoot_coe
    (a : Kˣ) (n : ℕ) (sigma : AbsGal K) :
    (((towerRatioRoot K a n sigma : StageMu K n) : (Closure K)ˣ) : Closure K) =
      towerRatioValue K a n sigma := rfl

theorem towerRatio_compatible
    (a : Kˣ) (n : ℕ) (sigma : AbsGal K) :
    transitionMu K n (towerRatioRoot K a (n + 1) sigma) =
      towerRatioRoot K a n sigma := by
  apply rootsOfUnity.coe_injective
  change towerRatioValue K a (n + 1) sigma ^ (n + 2) =
    towerRatioValue K a n sigma
  unfold towerRatioValue
  rw [div_pow, ← map_pow, rootTower_succ_pow]

abbrev MuFamily := ∀ n : ℕ, StageMu K n

def compatibleMuSubgroup : Subgroup (MuFamily K) where
  carrier :=
    {z | ∀ n, transitionMu K n (z (n + 1)) = z n}
  one_mem' := by
    intro n
    simp [transitionMu]
  mul_mem' := by
    intro x y hx hy n
    simp only [Pi.mul_apply]
    rw [map_mul, hx n, hy n]
  inv_mem' := by
    intro x hx n
    simp only [Pi.inv_apply]
    rw [map_inv, hx n]

abbrev FactorialMu := compatibleMuSubgroup K

def compatibleKummerRatio (a : Kˣ) (sigma : AbsGal K) : FactorialMu K :=
  ⟨fun n => towerRatioRoot K a n sigma,
    fun n => towerRatio_compatible K a n sigma⟩

@[simp] theorem compatibleKummerRatio_coord
    (a : Kˣ) (sigma : AbsGal K) (n : ℕ) :
    (compatibleKummerRatio K a sigma : MuFamily K) n =
      towerRatioRoot K a n sigma := rfl

theorem galois_transition_natural
    (n : ℕ) (sigma : AbsGal K) (z : StageMu K (n + 1)) :
    transitionMu K n
        (galoisOnRoots K (stageDegree (n + 1)) sigma z) =
      galoisOnRoots K (stageDegree n) sigma
        (transitionMu K n z) := by
  apply rootsOfUnity.coe_injective
  simp only [transitionMu_coe, galoisOnRoots_coe]
  rw [map_pow]

def galoisOnFactorialMu (sigma : AbsGal K) :
    FactorialMu K ≃* FactorialMu K where
  toFun z :=
    ⟨fun n => galoisOnRoots K (stageDegree n) sigma (z.1 n), by
      intro n
      rw [galois_transition_natural, z.2 n]⟩
  invFun z :=
    ⟨fun n => galoisOnRoots K (stageDegree n) sigma⁻¹ (z.1 n), by
      intro n
      rw [galois_transition_natural, z.2 n]⟩
  left_inv z := by
    apply Subtype.ext
    funext n
    change
      galoisOnRoots K (stageDegree n) sigma⁻¹
          (galoisOnRoots K (stageDegree n) sigma (z.1 n)) =
        z.1 n
    rw [galoisOnRoots_inv]
    exact (galoisOnRoots K (stageDegree n) sigma).symm_apply_apply (z.1 n)
  right_inv z := by
    apply Subtype.ext
    funext n
    change
      galoisOnRoots K (stageDegree n) sigma
          (galoisOnRoots K (stageDegree n) sigma⁻¹ (z.1 n)) =
        z.1 n
    rw [galoisOnRoots_inv]
    exact (galoisOnRoots K (stageDegree n) sigma).apply_symm_apply (z.1 n)
  map_mul' x y := by
    apply Subtype.ext
    funext n
    apply rootsOfUnity.coe_injective
    simp [galoisOnRoots]

theorem compatibleKummerRatio_mul
    (a : Kˣ) (sigma tau : AbsGal K) :
    compatibleKummerRatio K a (sigma * tau) =
      galoisOnFactorialMu K sigma (compatibleKummerRatio K a tau) *
        compatibleKummerRatio K a sigma := by
  apply Subtype.ext
  funext n
  apply rootsOfUnity.coe_injective
  change towerRatioValue K a n (sigma * tau) =
    toAlgEquiv K sigma (towerRatioValue K a n tau) * towerRatioValue K a n sigma
  unfold towerRatioValue
  rw [toAlgEquiv_mul, AlgEquiv.mul_apply, map_div₀]
  field_simp [rootTower_ne_zero K a n]

end Src.CoreLayer.LanaStep6.FactorialKummerTower

end
