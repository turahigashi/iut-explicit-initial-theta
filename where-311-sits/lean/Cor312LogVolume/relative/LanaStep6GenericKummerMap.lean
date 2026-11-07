import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Cor312LogVolume.Src.Lib.ContinuousH1
import Cor312LogVolume.Src.Lib.ContinuousH1RestrictionColimit
import Cor312LogVolume.relative.LanaStep6FiniteKummerRatio
import Cor312LogVolume.relative.LanaStep6FiniteContinuousKummer
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Constructions
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Algebra.CharP.Two

noncomputable section

namespace Src.CoreLayer.LanaStep6.GenericKummerMap

universe u

def KummerTorsion (A : Type u) [CommGroup A] (n : ℕ) : Subgroup A where
  carrier := {x | x ^ n = 1}
  one_mem' := by
    show (1 : A) ^ n = 1
    rw [one_pow]
  mul_mem' := by
    intro x y hx hy
    show (x * y) ^ n = 1
    rw [mul_pow, show x ^ n = 1 from hx, show y ^ n = 1 from hy, one_mul]
  inv_mem' := by
    intro x hx
    show x⁻¹ ^ n = 1
    rw [inv_pow, show x ^ n = 1 from hx, inv_one]

@[simp] theorem mem_kummerTorsion
    {A : Type u} [CommGroup A] {n : ℕ} (x : A) :
    x ∈ KummerTorsion A n ↔ x ^ n = 1 :=
  Iff.rfl

structure KummerDegree where
  val : ℕ
  pos : 0 < val

instance : Preorder KummerDegree where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ hab hbc := hab.trans hbc

@[simp] theorem kummerDegree_le_iff (a b : KummerDegree) :
    a ≤ b ↔ a.val ∣ b.val :=
  Iff.rfl

def torsionTransition
    {A : Type u} [CommGroup A]
    {m n : KummerDegree} (h : m ≤ n) :
    KummerTorsion A n.val →* KummerTorsion A m.val where
  toFun x :=
    ⟨x.1 ^ (n.val / m.val), by
      show (x.1 ^ (n.val / m.val)) ^ m.val = 1
      rw [← pow_mul, Nat.div_mul_cancel h]
      exact x.2⟩
  map_one' := by
    apply Subtype.ext
    show (1 : A) ^ (n.val / m.val) = 1
    rw [one_pow]
  map_mul' x y := by
    apply Subtype.ext
    show (x.1 * y.1) ^ (n.val / m.val) =
      x.1 ^ (n.val / m.val) * y.1 ^ (n.val / m.val)
    rw [mul_pow]

@[simp] theorem torsionTransition_refl
    {A : Type u} [CommGroup A] (d : KummerDegree) :
    torsionTransition (A := A) (le_refl d) =
      MonoidHom.id (KummerTorsion A d.val) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  show (x : A) ^ (d.val / d.val) = (x : A)
  rw [Nat.div_self d.pos, pow_one]

theorem torsionTransition_comp
    {A : Type u} [CommGroup A]
    {l m n : KummerDegree} (hlm : l ≤ m) (hmn : m ≤ n) :
    torsionTransition (A := A) (hlm.trans hmn) =
      (torsionTransition (A := A) hlm).comp
        (torsionTransition (A := A) hmn) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  show (x : A) ^ (n.val / l.val) =
    ((x : A) ^ (n.val / m.val)) ^ (m.val / l.val)
  rw [← pow_mul, Nat.div_mul_div hmn hlm]

structure KummerCoefficientInput
    (M Mgp : Type u) [CommMonoid M] [CommGroup Mgp] where

  groupification : Algebra.GrothendieckGroup M ≃* Mgp

  divisible :
    ∀ (n : ℕ), n ≠ 0 → ∀ x : Mgp, ∃ y : Mgp, y ^ n = x

  finiteTors :
    ∀ (n : ℕ), n ≠ 0 → Finite (KummerTorsion Mgp n)

namespace KummerCoefficientInput

variable
    {M Mgp : Type u}
    [CommMonoid M] [CommGroup Mgp]
    (I : KummerCoefficientInput M Mgp)

def toGp : M →* Mgp :=
  I.groupification.toMonoidHom.comp Algebra.GrothendieckGroup.of

@[simp] theorem toGp_apply (m : M) :
    I.toGp m =
      I.groupification (Algebra.GrothendieckGroup.of m) :=
  rfl

theorem torsionFinite (I : KummerCoefficientInput M Mgp) (d : KummerDegree) :
    Finite (KummerTorsion Mgp d.val) :=
  I.finiteTors d.val d.pos.ne'

abbrev LambdaFamily (I : KummerCoefficientInput M Mgp) :=
  ∀ d : KummerDegree, KummerTorsion Mgp d.val

def lambdaSubgroup : Subgroup I.LambdaFamily where
  carrier :=
    {z | ∀ {m n : KummerDegree} (h : m ≤ n),
      torsionTransition (A := Mgp) h (z n) = z m}
  one_mem' := by
    intro m n h
    show torsionTransition (A := Mgp) h 1 = 1
    exact map_one _
  mul_mem' := by
    intro x y hx hy m n h
    simp only [Pi.mul_apply]
    show torsionTransition (A := Mgp) h (x n * y n) = x m * y m
    rw [map_mul, hx h, hy h]
  inv_mem' := by
    intro x hx m n h
    simp only [Pi.inv_apply]
    show torsionTransition (A := Mgp) h (x n)⁻¹ = (x m)⁻¹
    rw [map_inv, hx h]

abbrev Lambda :=
  I.lambdaSubgroup

def lambdaProjection (d : KummerDegree) :
    I.Lambda →* KummerTorsion Mgp d.val where
  toFun z := z.1 d
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem lambdaProjection_transition
    {m n : KummerDegree} (h : m ≤ n) (z : I.Lambda) :
    torsionTransition (A := Mgp) h (I.lambdaProjection n z) =
      I.lambdaProjection m z :=
  z.2 h

theorem lambda_ext {x y : I.Lambda}
    (h : ∀ d : KummerDegree,
      I.lambdaProjection d x = I.lambdaProjection d y) :
    x = y := by
  apply Subtype.ext
  funext d
  exact h d

end KummerCoefficientInput

open SrcContinuous.ContinuousH1

instance instKummerTorsionMulDistribMulAction
    (H A : Type u) [Group H] [CommGroup A]
    [MulDistribMulAction H A] (n : ℕ) :
    MulDistribMulAction H (KummerTorsion A n) where
  smul h x :=
    ⟨h • x.1, by
      show (h • x.1) ^ n = 1
      rw [← smul_pow', show x.1 ^ n = 1 from x.2, smul_one]⟩
  one_smul x := by
    apply Subtype.ext
    show (1 : H) • x.1 = x.1
    rw [one_smul]
  mul_smul h k x := by
    apply Subtype.ext
    show (h * k) • x.1 = h • (k • x.1)
    rw [mul_smul]
  smul_one h := by
    apply Subtype.ext
    show h • (1 : A) = 1
    rw [smul_one]
  smul_mul h x y := by
    apply Subtype.ext
    show h • (x.1 * y.1) = (h • x.1) * (h • y.1)
    rw [smul_mul']

@[simp] theorem kummerTorsion_smul_coe
    {H A : Type u} [Group H] [CommGroup A] [MulDistribMulAction H A]
    (n : ℕ) (h : H) (z : KummerTorsion A n) :
    ((h • z : KummerTorsion A n) : A) = h • (z : A) := rfl

instance instKummerTorsionContinuousSMul
    (H A : Type u) [Group H] [CommGroup A]
    [TopologicalSpace H] [TopologicalSpace A]
    [MulDistribMulAction H A] [ContinuousSMul H A]
    (n : ℕ) :
    ContinuousSMul H (KummerTorsion A n) where
  continuous_smul := by
    apply Continuous.subtype_mk
    exact continuous_smul.comp
      (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd))

instance instAdditiveKummerTorsionDistribMulAction
    (H A : Type u) [Group H] [CommGroup A]
    [MulDistribMulAction H A] (n : ℕ) :
    DistribMulAction H (Additive (KummerTorsion A n)) where
  smul h x := Additive.ofMul (h • x.toMul)
  one_smul x := by
    apply Additive.toMul.injective
    show (1 : H) • x.toMul = x.toMul
    rw [one_smul]
  mul_smul h k x := by
    apply Additive.toMul.injective
    show (h * k) • x.toMul = h • (k • x.toMul)
    rw [mul_smul]
  smul_zero h := by
    apply Additive.toMul.injective
    show h • (1 : KummerTorsion A n) = 1
    rw [smul_one]
  smul_add h x y := by
    apply Additive.toMul.injective
    show h • (x.toMul * y.toMul) = (h • x.toMul) * (h • y.toMul)
    rw [smul_mul']

instance instAdditiveKummerTorsionContinuousSMul
    (H A : Type u) [Group H] [CommGroup A]
    [TopologicalSpace H] [TopologicalSpace A]
    [MulDistribMulAction H A] [ContinuousSMul H A]
    (n : ℕ) :
    ContinuousSMul H (Additive (KummerTorsion A n)) where
  continuous_smul := by
    have h :
        Continuous
          (fun p : H × Additive (KummerTorsion A n) =>
            p.1 • p.2.toMul) :=
      continuous_smul.comp
        (continuous_fst.prodMk (continuous_toMul.comp continuous_snd))
    exact continuous_ofMul.comp h

structure KummerSubgroupInput
    (H M Mgp : Type u)
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
    [MulDistribMulAction H M] [ContinuousSMul H M]
    [CommGroup Mgp] [TopologicalSpace Mgp] [IsTopologicalGroup Mgp]
    [MulDistribMulAction H Mgp] [ContinuousSMul H Mgp] where

  coeff : KummerCoefficientInput M Mgp

  equivariant_toGp :
    ∀ (h : H) (m : M),
      KummerCoefficientInput.toGp coeff (h • m) =
        h • KummerCoefficientInput.toGp coeff m

namespace KummerSubgroupInput

variable
    {H M Mgp : Type u}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
    [MulDistribMulAction H M] [ContinuousSMul H M]
    [CommGroup Mgp] [TopologicalSpace Mgp] [IsTopologicalGroup Mgp]
    [MulDistribMulAction H Mgp] [ContinuousSMul H Mgp]
    (I : KummerSubgroupInput H M Mgp)

def fixedSubmonoid (I : KummerSubgroupInput H M Mgp) : Submonoid M where
  carrier := {m | ∀ h : H, h • m = m}
  one_mem' := by
    intro h
    show h • (1 : M) = 1
    rw [smul_one]
  mul_mem' := by
    intro x y hx hy h
    show h • (x * y) = x * y
    rw [smul_mul', hx h, hy h]

abbrev Fixed (I : KummerSubgroupInput H M Mgp) :=
  I.fixedSubmonoid

abbrev LambdaCoeff (I : KummerSubgroupInput H M Mgp) :=
  KummerCoefficientInput.Lambda I.coeff

theorem fixed_toGp
    (I : KummerSubgroupInput H M Mgp)
    (x : I.Fixed) (h : H) :
    h • KummerCoefficientInput.toGp I.coeff x.1 =
      KummerCoefficientInput.toGp I.coeff x.1 := by
  rw [← I.equivariant_toGp h x.1, x.2 h]

theorem torsionTransition_smul
    (I : KummerSubgroupInput H M Mgp)
    {m n : KummerDegree} (hmn : m ≤ n)
    (h : H) (z : KummerTorsion Mgp n.val) :
    torsionTransition (A := Mgp) hmn (h • z) =
      h • torsionTransition (A := Mgp) hmn z := by
  apply Subtype.ext
  show (h • z.1) ^ (n.val / m.val) =
    h • (z.1 ^ (n.val / m.val))
  rw [← smul_pow']

instance instLambdaCoeffMulDistribMulAction
    (I : KummerSubgroupInput H M Mgp) :
    MulDistribMulAction H I.LambdaCoeff where
  smul h z :=
    ⟨fun d => h • z.1 d, by
      intro m n hmn
      rw [I.torsionTransition_smul hmn, z.2 hmn]⟩
  one_smul z := by
    apply Subtype.ext
    funext d
    show (1 : H) • z.1 d = z.1 d
    rw [one_smul]
  mul_smul h k z := by
    apply Subtype.ext
    funext d
    show (h * k) • z.1 d = h • (k • z.1 d)
    rw [mul_smul]
  smul_one h := by
    apply Subtype.ext
    funext d
    show h • (1 : KummerTorsion Mgp d.val) = 1
    rw [smul_one]
  smul_mul h x y := by
    apply Subtype.ext
    funext d
    show h • (x.1 d * y.1 d) = (h • x.1 d) * (h • y.1 d)
    rw [smul_mul']

instance instLambdaCoeffContinuousSMul
    (I : KummerSubgroupInput H M Mgp) :
    ContinuousSMul H I.LambdaCoeff where
  continuous_smul := by
    apply continuous_induced_rng.mpr
    refine continuous_pi fun d => ?_
    have hz :
        Continuous
          (fun p : H × I.LambdaCoeff =>
            (p.2.1 d : KummerTorsion Mgp d.val)) :=
      (continuous_apply d).comp
        (continuous_subtype_val.comp continuous_snd)
    exact continuous_smul.comp (continuous_fst.prodMk hz)

instance instAdditiveLambdaCoeffDistribMulAction
    (I : KummerSubgroupInput H M Mgp) :
    DistribMulAction H (Additive I.LambdaCoeff) where
  smul h z := Additive.ofMul (h • z.toMul)
  one_smul z := by
    apply Additive.toMul.injective
    show (1 : H) • z.toMul = z.toMul
    rw [one_smul]
  mul_smul h k z := by
    apply Additive.toMul.injective
    show (h * k) • z.toMul = h • (k • z.toMul)
    rw [mul_smul]
  smul_zero h := by
    apply Additive.toMul.injective
    show h • (1 : I.LambdaCoeff) = 1
    rw [smul_one]
  smul_add h x y := by
    apply Additive.toMul.injective
    show h • (x.toMul * y.toMul) = (h • x.toMul) * (h • y.toMul)
    rw [smul_mul']

instance instAdditiveLambdaCoeffContinuousSMul
    (I : KummerSubgroupInput H M Mgp) :
    ContinuousSMul H (Additive I.LambdaCoeff) where
  continuous_smul := by
    have h :
        Continuous
          (fun p : H × Additive I.LambdaCoeff =>
            p.1 • p.2.toMul) :=
      continuous_smul.comp
        (continuous_fst.prodMk (continuous_toMul.comp continuous_snd))
    exact continuous_ofMul.comp h

def factorialStageDegree (n : ℕ) : ℕ :=
  Nat.factorial (n + 1)

theorem factorialStageDegree_pos (n : ℕ) :
    0 < factorialStageDegree n :=
  Nat.factorial_pos _

theorem factorialStageDegree_ne_zero (n : ℕ) :
    factorialStageDegree n ≠ 0 :=
  (factorialStageDegree_pos n).ne'

theorem factorialStageDegree_succ (n : ℕ) :
    factorialStageDegree (n + 1) =
      (n + 2) * factorialStageDegree n := by
  simp [factorialStageDegree, Nat.factorial_succ, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

noncomputable def rootTower
    (I : KummerSubgroupInput H M Mgp) (m : M) : ℕ → Mgp
  | 0 => KummerCoefficientInput.toGp I.coeff m
  | n + 1 =>
      Classical.choose
        (I.coeff.divisible (n + 2) (Nat.succ_ne_zero (n + 1))
          (I.rootTower m n))

theorem rootTower_succ_pow
    (I : KummerSubgroupInput H M Mgp) (m : M) (n : ℕ) :
    I.rootTower m (n + 1) ^ (n + 2) =
      I.rootTower m n :=
  Classical.choose_spec
    (I.coeff.divisible (n + 2) (Nat.succ_ne_zero (n + 1))
      (I.rootTower m n))

theorem rootTower_pow
    (I : KummerSubgroupInput H M Mgp) (m : M) (n : ℕ) :
    I.rootTower m n ^ factorialStageDegree n =
      KummerCoefficientInput.toGp I.coeff m := by
  induction n with
  | zero =>
      show I.rootTower m 0 ^ 1 =
        KummerCoefficientInput.toGp I.coeff m
      rw [pow_one]
      rfl
  | succ n ih =>
      rw [factorialStageDegree_succ, pow_mul,
        I.rootTower_succ_pow m n, ih]

theorem rootTower_transition
    (I : KummerSubgroupInput H M Mgp)
    (m : M) {i j : ℕ} (hij : i ≤ j) :
    I.rootTower m j ^
        (factorialStageDegree j / factorialStageDegree i) =
      I.rootTower m i := by
  induction j, hij using Nat.le_induction with
  | base =>
      show I.rootTower m i ^
          (factorialStageDegree i / factorialStageDegree i) =
        I.rootTower m i
      rw [Nat.div_self (factorialStageDegree_pos i), pow_one]
  | succ j hij ih =>
      have hdvd :
          factorialStageDegree i ∣ factorialStageDegree j := by
        change Nat.factorial (i + 1) ∣ Nat.factorial (j + 1)
        exact Nat.factorial_dvd_factorial
          (Nat.add_le_add_right hij 1)
      rw [factorialStageDegree_succ,
        Nat.mul_div_assoc (j + 2) hdvd, pow_mul,
        I.rootTower_succ_pow m j, ih]

theorem degree_dvd_factorialStage (d : KummerDegree) :
    d.val ∣ factorialStageDegree d.val := by
  change d.val ∣ Nat.factorial (d.val + 1)
  exact Nat.dvd_factorial d.pos (Nat.le_succ d.val)

noncomputable def rootAtDegree
    (I : KummerSubgroupInput H M Mgp)
    (m : M) (d : KummerDegree) : Mgp :=
  I.rootTower m d.val ^
    (factorialStageDegree d.val / d.val)

theorem rootAtDegree_pow
    (I : KummerSubgroupInput H M Mgp)
    (m : M) (d : KummerDegree) :
    I.rootAtDegree m d ^ d.val =
      KummerCoefficientInput.toGp I.coeff m := by
  unfold rootAtDegree
  rw [← pow_mul,
    Nat.div_mul_cancel (degree_dvd_factorialStage d),
    I.rootTower_pow m d.val]

theorem rootAtDegree_transition
    (I : KummerSubgroupInput H M Mgp)
    (m : M) {d e : KummerDegree} (hde : d ≤ e) :
    I.rootAtDegree m e ^ (e.val / d.val) =
      I.rootAtDegree m d := by
  have hle : d.val ≤ e.val :=
    Nat.le_of_dvd e.pos hde
  have hfac :
      factorialStageDegree d.val ∣ factorialStageDegree e.val := by
    change Nat.factorial (d.val + 1) ∣ Nat.factorial (e.val + 1)
    exact Nat.factorial_dvd_factorial
      (Nat.add_le_add_right hle 1)
  have he :
      e.val ∣ factorialStageDegree e.val :=
    degree_dvd_factorialStage e
  have hd :
      d.val ∣ factorialStageDegree d.val :=
    degree_dvd_factorialStage d
  unfold rootAtDegree
  calc
    (I.rootTower m e.val ^
        (factorialStageDegree e.val / e.val)) ^ (e.val / d.val)
        =
      I.rootTower m e.val ^
        ((factorialStageDegree e.val / e.val) * (e.val / d.val)) := by
          rw [← pow_mul]
    _ =
      I.rootTower m e.val ^
        (factorialStageDegree e.val / d.val) := by
          rw [Nat.div_mul_div he hde]
    _ =
      (I.rootTower m e.val ^
          (factorialStageDegree e.val / factorialStageDegree d.val)) ^
        (factorialStageDegree d.val / d.val) := by
          rw [← Nat.div_mul_div hfac hd, pow_mul]
    _ =
      I.rootTower m d.val ^
        (factorialStageDegree d.val / d.val) := by
          rw [I.rootTower_transition m hle]

def ratioAtDegree
    (I : KummerSubgroupInput H M Mgp)
    (x : I.Fixed) (d : KummerDegree) (h : H) : Mgp :=
  h • I.rootAtDegree x.1 d / I.rootAtDegree x.1 d

theorem ratioAtDegree_pow
    (I : KummerSubgroupInput H M Mgp)
    (x : I.Fixed) (d : KummerDegree) (h : H) :
    I.ratioAtDegree x d h ^ d.val = 1 := by
  unfold ratioAtDegree
  rw [div_pow, ← smul_pow', I.rootAtDegree_pow,
    I.fixed_toGp x h, div_self']

def ratioTorsion
    (I : KummerSubgroupInput H M Mgp)
    (x : I.Fixed) (d : KummerDegree) (h : H) :
    KummerTorsion Mgp d.val :=
  ⟨I.ratioAtDegree x d h, I.ratioAtDegree_pow x d h⟩

noncomputable def kummerCocycleAtLevel
    (I : KummerSubgroupInput H M Mgp)
    (x : I.Fixed) (d : KummerDegree) :
    Cocycle H (Additive (KummerTorsion Mgp d.val)) where
  toContinuousMap :=
    ⟨fun h => Additive.ofMul (I.ratioTorsion x d h), by
      have hOrbit :
          Continuous (fun h : H => h • I.rootAtDegree x.1 d) :=
        continuous_id.smul continuous_const
      have hRatio :
          Continuous
            (fun h : H =>
              h • I.rootAtDegree x.1 d / I.rootAtDegree x.1 d) :=
        hOrbit.div' continuous_const
      exact continuous_ofMul.comp
        (hRatio.subtype_mk
          (fun h => I.ratioAtDegree_pow x d h))⟩
  cocycle' h k := by
    apply Additive.toMul.injective
    apply Subtype.ext
    show
      (h * k) • I.rootAtDegree x.1 d / I.rootAtDegree x.1 d =
        h •
            (k • I.rootAtDegree x.1 d / I.rootAtDegree x.1 d) *
          (h • I.rootAtDegree x.1 d / I.rootAtDegree x.1 d)
    rw [mul_smul, smul_div']
    simp [div_eq_mul_inv, mul_assoc]

noncomputable def kummerAtLevel
    (I : KummerSubgroupInput H M Mgp)
    (x : I.Fixed) (d : KummerDegree) :
    H1 H (Additive (KummerTorsion Mgp d.val)) :=
  Quotient.mk _ (I.kummerCocycleAtLevel x d)

theorem ratioTorsion_transition
    (I : KummerSubgroupInput H M Mgp)
    (x : I.Fixed) {d e : KummerDegree} (hde : d ≤ e)
    (h : H) :
    torsionTransition (A := Mgp) hde
        (I.ratioTorsion x e h) =
      I.ratioTorsion x d h := by
  apply Subtype.ext
  show
    (h • I.rootAtDegree x.1 e / I.rootAtDegree x.1 e) ^
        (e.val / d.val) =
      h • I.rootAtDegree x.1 d / I.rootAtDegree x.1 d
  rw [div_pow, ← smul_pow',
    I.rootAtDegree_transition x.1 hde]

def lambdaRatio
    (I : KummerSubgroupInput H M Mgp)
    (x : I.Fixed) (h : H) : I.LambdaCoeff :=
  ⟨fun d => I.ratioTorsion x d h,
    fun hde => I.ratioTorsion_transition x hde h⟩

theorem lambdaRatio_continuous
    (I : KummerSubgroupInput H M Mgp)
    (x : I.Fixed) :
    Continuous (fun h : H => I.lambdaRatio x h) := by
  apply continuous_induced_rng.mpr
  refine continuous_pi fun d => ?_
  have h :=
    (I.kummerCocycleAtLevel x d).toContinuousMap.continuous
  exact continuous_toMul.comp h

noncomputable def kummerCocycleAtSubgroup
    (I : KummerSubgroupInput H M Mgp)
    (x : I.Fixed) :
    Cocycle H (Additive I.LambdaCoeff) where
  toContinuousMap :=
    ⟨fun h => Additive.ofMul (I.lambdaRatio x h),
      continuous_ofMul.comp (I.lambdaRatio_continuous x)⟩
  cocycle' h k := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext d
    apply Subtype.ext
    have hc := (I.kummerCocycleAtLevel x d).cocycle' h k
    exact congrArg
      (fun z : Additive (KummerTorsion Mgp d.val) => z.toMul.1) hc

noncomputable def kummerAtSubgroup
    (I : KummerSubgroupInput H M Mgp)
    (x : I.Fixed) :
    H1 H (Additive I.LambdaCoeff) :=
  Quotient.mk _ (I.kummerCocycleAtSubgroup x)

end KummerSubgroupInput

abbrev FiniteOpen
    (G : Type u) [Group G] [TopologicalSpace G] :=
  Src.Lib.ContinuousH1RestrictionColimit.FiniteOpen G

def restrictedOpen
    {G : Type u} [Group G] [TopologicalSpace G]
    (J : FiniteOpen G) : OpenSubgroup G :=
  Src.Lib.ContinuousH1RestrictionColimit.restrictedOpen
    (ContinuousMonoidHom.id G) J

theorem restrictedOpen_le
    {G : Type u} [Group G] [TopologicalSpace G]
    {J K : FiniteOpen G} (h : J ≤ K) :
    (restrictedOpen J).toSubgroup ≤
      (restrictedOpen K).toSubgroup :=
  Src.Lib.ContinuousH1RestrictionColimit.restrictedOpen_le
    (ContinuousMonoidHom.id G) h

structure KummerColimitInput
    (G M Mgp : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
    [MulDistribMulAction G M] [ContinuousSMul G M]
    [CommGroup Mgp] [TopologicalSpace Mgp] [IsTopologicalGroup Mgp]
    [MulDistribMulAction G Mgp] [ContinuousSMul G Mgp]
    extends KummerSubgroupInput G M Mgp where

  unionFixed :
    ∀ m : M, ∃ J : FiniteOpen G,
      ∀ h : (restrictedOpen J).toSubgroup, h • m = m

namespace KummerColimitInput

variable
    {G M Mgp : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
    [MulDistribMulAction G M] [ContinuousSMul G M]
    [CommGroup Mgp] [TopologicalSpace Mgp] [IsTopologicalGroup Mgp]
    [MulDistribMulAction G Mgp] [ContinuousSMul G Mgp]
    (I : KummerColimitInput G M Mgp)

abbrev LambdaCoeff (I : KummerColimitInput G M Mgp) :=
  I.toKummerSubgroupInput.LambdaCoeff

@[reducible] def subgroupInput (J : FiniteOpen G) :
    KummerSubgroupInput (restrictedOpen J).toSubgroup M Mgp where
  coeff := I.toKummerSubgroupInput.coeff
  equivariant_toGp := by
    intro h m
    exact I.toKummerSubgroupInput.equivariant_toGp h.1 m

def restrictFixed
    {J K : FiniteOpen G} (h : J ≤ K)
    (x : (I.subgroupInput K).Fixed) :
    (I.subgroupInput J).Fixed :=
  ⟨x.1, by
    intro g
    exact x.2
      ⟨g.1, restrictedOpen_le h g.2⟩⟩

noncomputable def chosenOpen (m : M) : FiniteOpen G :=
  Classical.choose (I.unionFixed m)

theorem chosenOpen_fixes (m : M) :
    ∀ h : (restrictedOpen (I.chosenOpen m)).toSubgroup,
      h • m = m :=
  Classical.choose_spec (I.unionFixed m)

noncomputable def chosenFixed (m : M) :
    (I.subgroupInput (I.chosenOpen m)).Fixed :=
  ⟨m, I.chosenOpen_fixes m⟩

abbrev infinityH1 : Type u :=
  Src.Lib.ContinuousH1RestrictionColimit.InfinityH1
    (A := Additive I.LambdaCoeff)
    (ContinuousMonoidHom.id G)

noncomputable def stageKummerCocycle
    (J : FiniteOpen G)
    (x : (I.subgroupInput J).Fixed) :
    Cocycle (restrictedOpen J).toSubgroup (Additive I.LambdaCoeff) where
  toContinuousMap :=
    ⟨fun h =>
        Additive.ofMul ((I.subgroupInput J).lambdaRatio x h),
      continuous_ofMul.comp
        ((I.subgroupInput J).lambdaRatio_continuous x)⟩
  cocycle' h k := by
    apply Additive.toMul.injective
    apply Subtype.ext
    funext d
    apply Subtype.ext
    have hc :=
      ((I.subgroupInput J).kummerCocycleAtLevel x d).cocycle' h k
    exact congrArg
      (fun z : Additive (KummerTorsion Mgp d.val) => z.toMul.1) hc

noncomputable def stageKummerClass
    (J : FiniteOpen G)
    (x : (I.subgroupInput J).Fixed) :
    Src.Lib.ContinuousH1RestrictionColimit.Stage
      (A := Additive I.LambdaCoeff)
      (ContinuousMonoidHom.id G) J :=
  Quotient.mk _ (I.stageKummerCocycle J x)

theorem chooseDivisible_congr
    (C : KummerCoefficientInput M Mgp) (k : ℕ) (hk : k ≠ 0)
    {a b : Mgp} (hab : a = b) :
    Classical.choose (C.divisible k hk a) =
      Classical.choose (C.divisible k hk b) := by
  subst hab; rfl

theorem rootTower_subgroupInput
    {J K : FiniteOpen G} (m : M) (n : ℕ) :
    (I.subgroupInput J).rootTower m n =
      (I.subgroupInput K).rootTower m n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [KummerSubgroupInput.rootTower]
      exact chooseDivisible_congr I.toKummerSubgroupInput.coeff (n + 2)
        (Nat.succ_ne_zero (n + 1)) ih

theorem rootAtDegree_subgroupInput
    {J K : FiniteOpen G} (m : M) (d : KummerDegree) :
    (I.subgroupInput J).rootAtDegree m d =
      (I.subgroupInput K).rootAtDegree m d := by
  simp only [KummerSubgroupInput.rootAtDegree,
    I.rootTower_subgroupInput (J := J) (K := K) m]

theorem stageKummerCocycle_restriction
    {J K : FiniteOpen G} (h : J ≤ K)
    (x : (I.subgroupInput K).Fixed) :
    Src.Lib.ContinuousH1RestrictionColimit.restrictCocycle
        (restrictedOpen_le h) (I.stageKummerCocycle K x) =
      I.stageKummerCocycle J (I.restrictFixed h x) := by
  apply Cocycle.ext
  intro g
  apply Additive.toMul.injective
  apply Subtype.ext
  funext d
  apply Subtype.ext
  show (I.subgroupInput K).ratioAtDegree x d
      (Subgroup.inclusion (restrictedOpen_le h) g) =
    (I.subgroupInput J).ratioAtDegree (I.restrictFixed h x) d g
  simp only [KummerSubgroupInput.ratioAtDegree,
    I.rootAtDegree_subgroupInput (J := K) (K := J) x.1 d]
  rfl

theorem stageKummerClass_restriction
    {J K : FiniteOpen G} (h : J ≤ K)
    (x : (I.subgroupInput K).Fixed) :
    Src.Lib.ContinuousH1RestrictionColimit.stageRestriction
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G) h
        (I.stageKummerClass K x) =
      I.stageKummerClass J (I.restrictFixed h x) := by
  change
    Quotient.mk _
        (Src.Lib.ContinuousH1RestrictionColimit.restrictCocycle
          (restrictedOpen_le h) (I.stageKummerCocycle K x)) =
      Quotient.mk _
        (I.stageKummerCocycle J (I.restrictFixed h x))
  exact congrArg (Quotient.mk _)
    (I.stageKummerCocycle_restriction h x)

noncomputable def genericKummerMap : M → I.infinityH1 :=
  fun m =>
    Src.Lib.ContinuousH1RestrictionColimit.stageToInfinityH1
      (A := Additive I.LambdaCoeff)
      (ContinuousMonoidHom.id G)
      (I.chosenOpen m)
      (I.stageKummerClass (I.chosenOpen m) (I.chosenFixed m))

theorem genericKummerMap_eq_of_fixed
    (m : M) (J : FiniteOpen G)
    (hm : ∀ h : (restrictedOpen J).toSubgroup, h • m = m) :
    I.genericKummerMap m =
      Src.Lib.ContinuousH1RestrictionColimit.stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G) J
        (I.stageKummerClass J ⟨m, hm⟩) := by
  let xJ : (I.subgroupInput J).Fixed := ⟨m, hm⟩
  obtain ⟨L, hLchosen, hLJ⟩ :=
    exists_le_le (I.chosenOpen m) J
  let xChosen :
      (I.subgroupInput (I.chosenOpen m)).Fixed :=
    I.chosenFixed m
  let xLchosen : (I.subgroupInput L).Fixed :=
    I.restrictFixed hLchosen xChosen
  let xLJ : (I.subgroupInput L).Fixed :=
    I.restrictFixed hLJ xJ
  have hxL : xLchosen = xLJ := by
    apply Subtype.ext
    rfl
  calc
    I.genericKummerMap m =
        Src.Lib.ContinuousH1RestrictionColimit.stageToInfinityH1
          (A := Additive I.LambdaCoeff)
          (ContinuousMonoidHom.id G)
          (I.chosenOpen m)
          (I.stageKummerClass (I.chosenOpen m) xChosen) := by
            rfl
    _ =
        Src.Lib.ContinuousH1RestrictionColimit.stageToInfinityH1
          (A := Additive I.LambdaCoeff)
          (ContinuousMonoidHom.id G) L
          (Src.Lib.ContinuousH1RestrictionColimit.stageRestriction
            (A := Additive I.LambdaCoeff)
            (ContinuousMonoidHom.id G) hLchosen
            (I.stageKummerClass (I.chosenOpen m) xChosen)) := by
              symm
              exact
                Src.Lib.ContinuousH1RestrictionColimit.stageToInfinityH1_restriction
                  (A := Additive I.LambdaCoeff)
                  (ContinuousMonoidHom.id G) hLchosen _
    _ =
        Src.Lib.ContinuousH1RestrictionColimit.stageToInfinityH1
          (A := Additive I.LambdaCoeff)
          (ContinuousMonoidHom.id G) L
          (I.stageKummerClass L xLchosen) := by
            rw [I.stageKummerClass_restriction hLchosen xChosen]
    _ =
        Src.Lib.ContinuousH1RestrictionColimit.stageToInfinityH1
          (A := Additive I.LambdaCoeff)
          (ContinuousMonoidHom.id G) L
          (I.stageKummerClass L xLJ) := by
            rw [hxL]
    _ =
        Src.Lib.ContinuousH1RestrictionColimit.stageToInfinityH1
          (A := Additive I.LambdaCoeff)
          (ContinuousMonoidHom.id G) L
          (Src.Lib.ContinuousH1RestrictionColimit.stageRestriction
            (A := Additive I.LambdaCoeff)
            (ContinuousMonoidHom.id G) hLJ
            (I.stageKummerClass J xJ)) := by
              rw [I.stageKummerClass_restriction hLJ xJ]
    _ =
        Src.Lib.ContinuousH1RestrictionColimit.stageToInfinityH1
          (A := Additive I.LambdaCoeff)
          (ContinuousMonoidHom.id G) J
          (I.stageKummerClass J xJ) :=
      Src.Lib.ContinuousH1RestrictionColimit.stageToInfinityH1_restriction
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G) hLJ _

end KummerColimitInput

namespace FiniteKummerCheck

open Src.CoreLayer.LanaStep6.FiniteKummerRatio

variable (K : Type u) [Field K]

def ratioFromRoot (r : Closure K) (sigma : AbsGal K) : Closure K :=
  toAlgEquiv K sigma r / r

theorem rootQuotient_pow_eq_one
    (n : ℕ) [NeZero n] (a : Kˣ) (r : Closure K)
    (hrpow :
      r ^ n = algebraMap K (Closure K) (a : K)) :
    (r / chosenRoot K n a) ^ n = 1 := by
  have ha :
      algebraMap K (Closure K) (a : K) ≠ 0 := by
    intro hzero
    have : (a : K) = 0 :=
      (algebraMap K (Closure K)).injective (by simpa using hzero)
    exact (Units.ne_zero a) this
  rw [div_pow, hrpow, chosenRoot_pow, div_self ha]

theorem ratioFromRoot_eq_ratioValue_iff_fixed_quotient
    (n : ℕ) [NeZero n] (a : Kˣ)
    (r : Closure K) (hr : r ≠ 0)
    (sigma : AbsGal K) :
    ratioFromRoot K r sigma = ratioValue K n a sigma ↔
      toAlgEquiv K sigma (r / chosenRoot K n a) =
        r / chosenRoot K n a := by
  have hs : chosenRoot K n a ≠ 0 :=
    chosenRoot_ne_zero K n a
  have hsigmas :
      toAlgEquiv K sigma (chosenRoot K n a) ≠ 0 := by
    intro hzero
    apply hs
    apply (toAlgEquiv K sigma).injective
    simpa using hzero
  unfold ratioFromRoot ratioValue
  rw [map_div₀]
  rw [div_eq_div_iff hr hs, div_eq_div_iff hsigmas hs]
  simp [mul_comm]

theorem ratioFromRoot_eq_ratioValue_of_roots_of_unity_in_base
    (n : ℕ) [NeZero n] (a : Kˣ)
    (r : Closure K) (hr : r ≠ 0)
    (hrpow : r ^ n = algebraMap K (Closure K) (a : K))
    (hmu : ∀ z : Closure K, z ^ n = 1 →
      ∃ c : K, algebraMap K (Closure K) c = z)
    (sigma : AbsGal K) :
    ratioFromRoot K r sigma = ratioValue K n a sigma := by
  rw [ratioFromRoot_eq_ratioValue_iff_fixed_quotient K n a r hr sigma]
  obtain ⟨c, hc⟩ := hmu _ (rootQuotient_pow_eq_one K n a r hrpow)
  rw [← hc]
  exact (toAlgEquiv K sigma).commutes c

theorem rootsOfUnity_two_in_rat :
    ∀ z : Closure ℚ, z ^ 2 = 1 →
      ∃ c : ℚ, algebraMap ℚ (Closure ℚ) c = z := by
  intro z hz
  have h : (z - 1) * (z + 1) = 0 := by ring_nf; linear_combination hz
  rcases mul_eq_zero.mp h with h1 | h1
  · exact ⟨1, by simp [sub_eq_zero.mp h1]⟩
  · exact ⟨-1, by simp [eq_neg_of_add_eq_zero_left h1]⟩

end FiniteKummerCheck

namespace FiniteKummerInstantiationCheck

open Src.CoreLayer.LanaStep6.FiniteKummerRatio

theorem coefficientInput_for_group_implies_pow_surjective
    {A : Type u} [CommGroup A]
    (C : KummerCoefficientInput A (Algebra.GrothendieckGroup A))
    (n : ℕ) (hn : n ≠ 0) (a : A) :
    ∃ b : A, b ^ n = a := by
  obtain ⟨y, hy⟩ :=
    C.divisible n hn (Algebra.GrothendieckGroup.of a)
  let p : Algebra.GrothendieckGroup A →* A :=
    Algebra.GrothendieckGroup.lift (MonoidHom.id A)
  refine ⟨p y, ?_⟩
  have h := congrArg p hy
  simpa [p, Algebra.GrothendieckGroup.lift,
    Submonoid.LocalizationMap.lift_eq] using h

theorem ratUnits_no_genericCoefficientInput :
    KummerCoefficientInput
      ℚˣ (Algebra.GrothendieckGroup ℚˣ) → False := by
  intro C
  let twoUnit : ℚˣ := Units.mk0 2 (by norm_num)
  obtain ⟨b, hb⟩ :=
    coefficientInput_for_group_implies_pow_surjective
      C 2 (by norm_num) twoUnit
  have hbq : (b : ℚ) ^ 2 = 2 := by
    have h := congrArg (fun u : ℚˣ => (u : ℚ)) hb
    simpa [twoUnit] using h
  have hnot : ¬ IsSquare (2 : ℚ) := by
    norm_num
  apply hnot
  exact ⟨(b : ℚ), by simpa [pow_two] using hbq.symm⟩

section ActualColimitInput

variable
    [TopologicalSpace ℚˣ] [ContinuousMul ℚˣ]
    [MulDistribMulAction (AbsGal ℚ) ℚˣ]
    [ContinuousSMul (AbsGal ℚ) ℚˣ]
    [TopologicalSpace (Algebra.GrothendieckGroup ℚˣ)]
    [IsTopologicalGroup (Algebra.GrothendieckGroup ℚˣ)]
    [MulDistribMulAction
      (AbsGal ℚ) (Algebra.GrothendieckGroup ℚˣ)]
    [ContinuousSMul
      (AbsGal ℚ) (Algebra.GrothendieckGroup ℚˣ)]

theorem finiteRatioCarrier_no_colimitInput_over_rat
    (I :
      KummerColimitInput
        (AbsGal ℚ) ℚˣ (Algebra.GrothendieckGroup ℚˣ)) :
    False :=
  ratUnits_no_genericCoefficientInput
    I.toKummerSubgroupInput.coeff

end ActualColimitInput

end FiniteKummerInstantiationCheck

namespace AlgClosureCarrier

open Src.CoreLayer.LanaStep6.FiniteKummerRatio

noncomputable def groupSelfGroupification (A : Type u) [CommGroup A] :
    Algebra.GrothendieckGroup A ≃* A where
  toFun := Algebra.GrothendieckGroup.lift (MonoidHom.id A)
  invFun := Algebra.GrothendieckGroup.of
  left_inv := by
    have h : (Algebra.GrothendieckGroup.of (M := A)).comp
        (Algebra.GrothendieckGroup.lift (MonoidHom.id A))
        = MonoidHom.id (Algebra.GrothendieckGroup A) := by
      apply (Algebra.GrothendieckGroup.lift
        (M := A) (G := Algebra.GrothendieckGroup A)).symm.injective
      ext a
      have hla : Algebra.GrothendieckGroup.lift (MonoidHom.id A)
          (Algebra.GrothendieckGroup.of a) = a :=
        (Localization.monoidOf ⊤).lift_eq (fun _ ↦ Group.isUnit _) a
      simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply,
        Algebra.GrothendieckGroup.lift_symm_apply]
      rw [hla]
    intro x
    exact DFunLike.congr_fun h x
  right_inv := by
    intro a
    exact (Localization.monoidOf ⊤).lift_eq (fun _ ↦ Group.isUnit _) a
  map_mul' := map_mul _

theorem closureUnits_divisible (K : Type u) [Field K]
    (n : ℕ) (hn : n ≠ 0) (x : (Closure K)ˣ) :
    ∃ y : (Closure K)ˣ, y ^ n = x := by
  obtain ⟨z, hz⟩ :=
    IsAlgClosed.exists_pow_nat_eq (x : Closure K) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow hn] at hz
    exact x.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, by ext; simpa using hz⟩

theorem closureUnits_finiteTors (K : Type u) [Field K]
    (n : ℕ) (hn : n ≠ 0) :
    Finite (KummerTorsion (Closure K)ˣ n) := by
  haveI : NeZero n := ⟨hn⟩
  have h : KummerTorsion (Closure K)ˣ n = rootsOfUnity n (Closure K) := rfl
  rw [h]
  infer_instance

noncomputable def closureCoefficientInput (K : Type u) [Field K] :
    KummerCoefficientInput (Closure K)ˣ (Closure K)ˣ where
  groupification := groupSelfGroupification _
  divisible := closureUnits_divisible K
  finiteTors := closureUnits_finiteTors K

open Src.CoreLayer.LanaStep6.FiniteContinuousKummer

local instance closureUnitsTopology (K : Type u) [Field K] :
    TopologicalSpace (Closure K)ˣ :=
  ⊥

local instance closureUnitsDiscreteTopology (K : Type u) [Field K] :
    DiscreteTopology (Closure K)ˣ :=
  discreteTopology_bot _

local instance closureUnitsIsTopologicalGroup (K : Type u) [Field K] :
    IsTopologicalGroup (Closure K)ˣ :=
  {}

def galoisOnClosure (K : Type u) [Field K]
    (sigma : AbsGal K) (x : Closure K) : Closure K :=
  toAlgEquiv K sigma x

def galoisOnClosureUnits (K : Type u) [Field K]
    (sigma : AbsGal K) (u : (Closure K)ˣ) : (Closure K)ˣ :=
  Units.map (toAlgEquiv K sigma : Closure K →ₐ[K] Closure K).toRingHom.toMonoidHom u

@[simp] theorem galoisOnClosureUnits_coe (K : Type u) [Field K]
    (sigma : AbsGal K) (u : (Closure K)ˣ) :
    ((galoisOnClosureUnits K sigma u : (Closure K)ˣ) : Closure K)
      = toAlgEquiv K sigma (u : Closure K) := rfl

local instance closureAction (K : Type u) [Field K] :
    MulAction (AbsGal K) (Closure K) where
  smul sigma x := galoisOnClosure K sigma x
  one_smul x := by
    show galoisOnClosure K 1 x = x
    simp [galoisOnClosure, toAlgEquiv_one]
  mul_smul sigma tau x := by
    show galoisOnClosure K (sigma * tau) x
        = galoisOnClosure K sigma (galoisOnClosure K tau x)
    simp [galoisOnClosure, toAlgEquiv_mul, AlgEquiv.mul_apply]

@[simp] theorem closure_smul_def (K : Type u) [Field K]
    (sigma : AbsGal K) (x : Closure K) :
    sigma • x = toAlgEquiv K sigma x := rfl

local instance closureUnitsAction (K : Type u) [Field K] :
    MulDistribMulAction (AbsGal K) (Closure K)ˣ where
  smul sigma u := galoisOnClosureUnits K sigma u
  one_smul u := by
    show galoisOnClosureUnits K 1 u = u
    apply Units.ext
    simp [toAlgEquiv_one]
  mul_smul sigma tau u := by
    show galoisOnClosureUnits K (sigma * tau) u
        = galoisOnClosureUnits K sigma (galoisOnClosureUnits K tau u)
    apply Units.ext
    simp [toAlgEquiv_mul, AlgEquiv.mul_apply]
  smul_one sigma := by
    show galoisOnClosureUnits K sigma 1 = 1
    apply Units.ext; simp
  smul_mul sigma x y := by
    show galoisOnClosureUnits K sigma (x * y)
        = galoisOnClosureUnits K sigma x * galoisOnClosureUnits K sigma y
    apply Units.ext; simp

@[simp] theorem closureUnits_smul_coe (K : Type u) [Field K]
    (sigma : AbsGal K) (u : (Closure K)ˣ) :
    ((sigma • u : (Closure K)ˣ) : Closure K) = toAlgEquiv K sigma (u : Closure K) := rfl

theorem closureUnits_stabilizer_eq
    (K : Type u) [Field K] (u : (Closure K)ˣ) :
    (MulAction.stabilizer (AbsGal K) u : Set (AbsGal K)) =
      {sigma : AbsGal K |
        toAlgEquiv K sigma (u : Closure K) = (u : Closure K)} := by
  ext sigma
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_setOf_eq]
  constructor
  · intro h
    have h' := congrArg (fun v : (Closure K)ˣ => (v : Closure K)) h
    simpa using h'
  · intro h
    apply Units.ext
    simpa using h

local instance closureUnitsContinuousSMul
    (K : Type u) [Field K] :
    ContinuousSMul (AbsGal K) (Closure K)ˣ :=
  (continuousSMul_iff_stabilizer_isOpen).2 fun u => by
    rw [closureUnits_stabilizer_eq K u]
    exact isOpen_fixingValue K (u : Closure K)

@[simp] theorem closureGroupification_of
    (K : Type u) [Field K] (u : (Closure K)ˣ) :
    (closureCoefficientInput K).groupification
        (Algebra.GrothendieckGroup.of u) = u :=
  (Localization.monoidOf ⊤).lift_eq (fun _ ↦ Group.isUnit _) u

@[simp] theorem closureCoefficientInput_toGp
    (K : Type u) [Field K] (u : (Closure K)ˣ) :
    KummerCoefficientInput.toGp (closureCoefficientInput K) u = u := by
  change
    groupSelfGroupification ((Closure K)ˣ)
        (Algebra.GrothendieckGroup.of u) = u
  exact (groupSelfGroupification ((Closure K)ˣ)).apply_symm_apply u

noncomputable def closureSubgroupInput
    (K : Type u) [Field K] :
    KummerSubgroupInput
      (AbsGal K) (Closure K)ˣ (Closure K)ˣ where
  coeff := closureCoefficientInput K
  equivariant_toGp := by
    intro sigma u
    simp only [closureCoefficientInput_toGp]

theorem closureValue_orbit_finite
    (K : Type u) [Field K] (x : Closure K) :
    (MulAction.orbit (AbsGal K) x).Finite := by
  haveI : Normal K (Closure K) :=
    IsAlgClosure.normal K (Closure K)
  refine ((minpoly K x).rootSet_finite (Closure K)).subset ?_
  intro y hy
  have hmin : minpoly K y = minpoly K x :=
    (Normal.minpoly_eq_iff_mem_orbit
      (F := K) (E := Closure K) (x := y) (y := x)).2 hy
  rw [← hmin]
  exact Polynomial.mem_rootSet.mpr
    ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral y),
      minpoly.aeval K y⟩

theorem closureValue_stabilizer_finiteIndex
    (K : Type u) [Field K] (x : Closure K) :
    (MulAction.stabilizer (AbsGal K) x).FiniteIndex := by
  letI : Finite (MulAction.orbit (AbsGal K) x) :=
    Set.finite_coe_iff.mpr (closureValue_orbit_finite K x)
  letI : Finite
      ((AbsGal K) ⧸ MulAction.stabilizer (AbsGal K) x) :=
    Finite.of_equiv
      (MulAction.orbit (AbsGal K) x)
      (MulAction.orbitEquivQuotientStabilizer (AbsGal K) x)
  exact Subgroup.finiteIndex_of_finite_quotient

noncomputable def closureFixingFiniteOpen
    (K : Type u) [Field K] (x : Closure K) :
    FiniteOpen (AbsGal K) :=
  ⟨⟨MulAction.stabilizer (AbsGal K) x, by
      change IsOpen
        {sigma : AbsGal K | toAlgEquiv K sigma x = x}
      exact isOpen_fixingValue K x⟩,
    closureValue_stabilizer_finiteIndex K x⟩

theorem closureFixingFiniteOpen_fixes
    (K : Type u) [Field K] (u : (Closure K)ˣ) :
    ∀ h :
        (restrictedOpen
          (closureFixingFiniteOpen K (u : Closure K))).toSubgroup,
      h • u = u := by
  intro h
  apply Units.ext
  change toAlgEquiv K h.1 (u : Closure K) = (u : Closure K)
  have hh :
      h.1 ∈
        MulAction.stabilizer (AbsGal K) (u : Closure K) := by
    simpa [restrictedOpen, closureFixingFiniteOpen,
      Src.Lib.ContinuousH1RestrictionColimit.restrictedOpen]
      using h.2
  exact hh

@[reducible] noncomputable def closureColimitInput
    (K : Type u) [Field K] :
    KummerColimitInput
      (AbsGal K) (Closure K)ˣ (Closure K)ˣ where
  toKummerSubgroupInput := closureSubgroupInput K
  unionFixed := by
    intro u
    exact
      ⟨closureFixingFiniteOpen K (u : Closure K),
        closureFixingFiniteOpen_fixes K u⟩

def baseUnitsMap (K : Type u) [Field K] :
    Kˣ →* (Closure K)ˣ :=
  Units.map (algebraMap K (Closure K))

theorem closureUnits_fixed_iff_exists_baseUnit
    (K : Type u) [Field K] [PerfectField K]
    (u : (Closure K)ˣ) :
    (∀ sigma : AbsGal K, sigma • u = u) ↔
      ∃ a : Kˣ, baseUnitsMap K a = u := by
  letI : IsGalois K (Closure K) := inferInstance
  constructor
  · intro hfix
    have hval :
        ∀ sigma : AbsGal K,
          toAlgEquiv K sigma (u : Closure K) =
            (u : Closure K) := by
      intro sigma
      have h := hfix sigma
      have h' :=
        congrArg (fun v : (Closure K)ˣ => (v : Closure K)) h
      simpa [AlgEquiv.smul_units_def] using h'
    obtain ⟨a, ha⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed
        (k := K) (K := Closure K) (u : Closure K)).2 hval
    have ha0 : a ≠ 0 := by
      intro ha0
      apply Units.ne_zero u
      rw [← ha, ha0, map_zero]
    let au : Kˣ := Units.mk0 a ha0
    refine ⟨au, ?_⟩
    apply Units.ext
    simpa [baseUnitsMap, au] using ha
  · rintro ⟨a, rfl⟩ sigma
    apply Units.ext
    exact (toAlgEquiv K sigma).commutes (a : K)

abbrev ImperfectRatFunc := RatFunc (ZMod 2)

theorem imperfectRatFunc_X_not_square :
    ¬ ∃ y : ImperfectRatFunc, y ^ 2 = RatFunc.X := by
  rintro ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hy
    exact RatFunc.X_ne_zero hy.symm
  have hdeg := congrArg RatFunc.intDegree hy
  rw [pow_two, RatFunc.intDegree_mul hy0 hy0, RatFunc.intDegree_X] at hdeg
  omega

noncomputable def imperfectWitnessRoot :
    Closure ImperfectRatFunc :=
  Classical.choose
    (IsAlgClosed.exists_pow_nat_eq
      (algebraMap ImperfectRatFunc (Closure ImperfectRatFunc) RatFunc.X)
      (by norm_num : 0 < (2 : ℕ)))

theorem imperfectWitnessRoot_sq :
    imperfectWitnessRoot ^ 2 =
      algebraMap ImperfectRatFunc (Closure ImperfectRatFunc) RatFunc.X :=
  Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq
      (algebraMap ImperfectRatFunc (Closure ImperfectRatFunc) RatFunc.X)
      (by norm_num : 0 < (2 : ℕ)))

theorem imperfectWitnessRoot_ne_zero :
    imperfectWitnessRoot ≠ 0 := by
  intro h0
  have h := imperfectWitnessRoot_sq
  rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h
  have hx :
      algebraMap ImperfectRatFunc (Closure ImperfectRatFunc) RatFunc.X ≠ 0 :=
    (map_ne_zero (algebraMap ImperfectRatFunc (Closure ImperfectRatFunc))).mpr
      RatFunc.X_ne_zero
  exact hx h.symm

noncomputable def imperfectFixedUnit :
    (Closure ImperfectRatFunc)ˣ :=
  Units.mk0 imperfectWitnessRoot imperfectWitnessRoot_ne_zero

theorem imperfectFixedUnit_fixed
    (sigma : AbsGal ImperfectRatFunc) :
    sigma • imperfectFixedUnit = imperfectFixedUnit := by
  apply Units.ext
  change
    toAlgEquiv ImperfectRatFunc sigma imperfectWitnessRoot =
      imperfectWitnessRoot
  apply CharTwo.sq_injective
  show toAlgEquiv ImperfectRatFunc sigma imperfectWitnessRoot ^ 2
      = imperfectWitnessRoot ^ 2
  rw [← map_pow, imperfectWitnessRoot_sq]
  exact (toAlgEquiv ImperfectRatFunc sigma).commutes RatFunc.X

theorem imperfectFixedUnit_not_base :
    ¬ ∃ a : ImperfectRatFuncˣ,
      baseUnitsMap ImperfectRatFunc a = imperfectFixedUnit := by
  rintro ⟨a, ha⟩
  have hval :=
    congrArg
      (fun u : (Closure ImperfectRatFunc)ˣ =>
        (u : Closure ImperfectRatFunc)) ha
  have hsquare :
      algebraMap ImperfectRatFunc (Closure ImperfectRatFunc)
          ((a : ImperfectRatFunc) ^ 2) =
        algebraMap ImperfectRatFunc (Closure ImperfectRatFunc) RatFunc.X := by
    calc
      algebraMap ImperfectRatFunc (Closure ImperfectRatFunc)
          ((a : ImperfectRatFunc) ^ 2)
          =
        (algebraMap ImperfectRatFunc (Closure ImperfectRatFunc)
          (a : ImperfectRatFunc)) ^ 2 := by rw [map_pow]
      _ = imperfectWitnessRoot ^ 2 := by
        simpa [baseUnitsMap, imperfectFixedUnit] using congrArg
          (fun z : Closure ImperfectRatFunc => z ^ 2) hval
      _ =
        algebraMap ImperfectRatFunc (Closure ImperfectRatFunc) RatFunc.X :=
        imperfectWitnessRoot_sq
  have ha2 : (a : ImperfectRatFunc) ^ 2 = RatFunc.X :=
    (algebraMap ImperfectRatFunc (Closure ImperfectRatFunc)).injective hsquare
  exact imperfectRatFunc_X_not_square ⟨(a : ImperfectRatFunc), ha2⟩

theorem imperfectField_fixed_not_base :
    ∃ u : (Closure ImperfectRatFunc)ˣ,
      (∀ sigma : AbsGal ImperfectRatFunc, sigma • u = u) ∧
      ¬ ∃ a : ImperfectRatFuncˣ,
        baseUnitsMap ImperfectRatFunc a = u :=
  ⟨imperfectFixedUnit, imperfectFixedUnit_fixed,
    imperfectFixedUnit_not_base⟩

def baseUnitToFixed
    (K : Type u) [Field K] :
    Kˣ →* (closureSubgroupInput K).Fixed where
  toFun a :=
    ⟨baseUnitsMap K a, by
      intro sigma
      apply Units.ext
      exact (toAlgEquiv K sigma).commutes (a : K)⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (baseUnitsMap K)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (baseUnitsMap K) a b

theorem baseUnitToFixed_injective
    (K : Type u) [Field K] :
    Function.Injective (baseUnitToFixed K) := by
  intro a b hab
  apply Units.ext
  apply (algebraMap K (Closure K)).injective
  have h :=
    congrArg
      (fun x : (closureSubgroupInput K).Fixed =>
        ((x.1 : (Closure K)ˣ) : Closure K)) hab
  simpa [baseUnitToFixed, baseUnitsMap] using h

theorem baseUnitToFixed_surjective
    (K : Type u) [Field K] [PerfectField K] :
    Function.Surjective (baseUnitToFixed K) := by
  intro x
  obtain ⟨a, ha⟩ :=
    (closureUnits_fixed_iff_exists_baseUnit K x.1).1 x.2
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact ha

noncomputable def baseUnitsEquivFixed
    (K : Type u) [Field K] [PerfectField K] :
    Kˣ ≃* (closureSubgroupInput K).Fixed :=
  MulEquiv.ofBijective (baseUnitToFixed K)
    ⟨baseUnitToFixed_injective K, baseUnitToFixed_surjective K⟩

def kummerDegreeOfNeZero (n : ℕ) [NeZero n] : KummerDegree :=
  ⟨n, NeZero.pos n⟩

noncomputable def genericRootForBaseUnit
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    (Closure K)ˣ :=
  (closureSubgroupInput K).rootAtDegree
    ((baseUnitToFixed K) a).1 (kummerDegreeOfNeZero n)

theorem genericRootForBaseUnit_pow
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    genericRootForBaseUnit K n a ^ n = baseUnitsMap K a := by
  have h :=
    (closureSubgroupInput K).rootAtDegree_pow
      ((baseUnitToFixed K) a).1 (kummerDegreeOfNeZero n)
  have h2 : KummerCoefficientInput.toGp (closureSubgroupInput K).coeff
      (((baseUnitToFixed K) a).1) = ((baseUnitToFixed K) a).1 :=
    closureCoefficientInput_toGp K _
  rw [h2] at h
  exact h

noncomputable def finiteChosenRootUnit
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    (Closure K)ˣ :=
  Units.mk0 (chosenRoot K n a) (chosenRoot_ne_zero K n a)

theorem finiteChosenRootUnit_pow
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    finiteChosenRootUnit K n a ^ n = baseUnitsMap K a := by
  apply Units.ext
  change
    chosenRoot K n a ^ n =
      algebraMap K (Closure K) (a : K)
  exact chosenRoot_pow K n a

noncomputable def rootChoiceTorsion
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    KummerTorsion (Closure K)ˣ n :=
  ⟨genericRootForBaseUnit K n a / finiteChosenRootUnit K n a, by
    show (genericRootForBaseUnit K n a / finiteChosenRootUnit K n a) ^ n = 1
    rw [div_pow, genericRootForBaseUnit_pow, finiteChosenRootUnit_pow]
    exact div_self' _⟩

def finiteRatioTorsionOnGeneric
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ)
    (sigma : AbsGal K) :
    KummerTorsion (Closure K)ˣ n :=
  ⟨ratioUnit K n a sigma, ratioUnit_pow K n a sigma⟩

theorem finiteRatioTorsionOnGeneric_continuous
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    Continuous
      (fun sigma : AbsGal K =>
        Additive.ofMul (finiteRatioTorsionOnGeneric K n a sigma)) := by
  rw [← IsLocallyConstant.iff_continuous]
  apply (IsLocallyConstant.iff_exists_open _).2
  intro sigma
  let r : Closure K := chosenRoot K n a
  let U : Set (AbsGal K) :=
    {tau | toAlgEquiv K (sigma⁻¹ * tau) r = r}
  refine ⟨U, ?_, ?_, ?_⟩
  · have hfix :
        IsOpen {g : AbsGal K | toAlgEquiv K g r = r} :=
      isOpen_fixingValue K r
    have htranslate :
        Continuous (fun tau : AbsGal K => sigma⁻¹ * tau) :=
      continuous_const.mul continuous_id
    simpa [U] using hfix.preimage htranslate
  · show toAlgEquiv K (sigma⁻¹ * sigma) r = r
    rw [inv_mul_cancel, toAlgEquiv_one]
    rfl
  · intro tau ht
    change toAlgEquiv K (sigma⁻¹ * tau) r = r at ht
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    change
      ratioValue K n a tau =
        ratioValue K n a sigma
    have key : toAlgEquiv K tau r = toAlgEquiv K sigma r := by
      have h := congrArg (toAlgEquiv K sigma) ht
      rwa [← AlgEquiv.mul_apply, ← toAlgEquiv_mul,
        mul_inv_cancel_left] at h
    unfold ratioValue
    rw [key]

noncomputable def finiteCocycleOnGenericCoeff
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    Cocycle (AbsGal K)
      (Additive (KummerTorsion (Closure K)ˣ n)) where
  toContinuousMap :=
    ⟨fun sigma =>
      Additive.ofMul (finiteRatioTorsionOnGeneric K n a sigma),
      finiteRatioTorsionOnGeneric_continuous K n a⟩
  cocycle' sigma tau := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    change
      ratioValue K n a (sigma * tau) =
        toAlgEquiv K sigma (ratioValue K n a tau) *
          ratioValue K n a sigma
    have h := ratioRoot_mul K n a sigma tau
    exact congrArg
      (fun z : Mu K n =>
        (((z : Mu K n) : (Closure K)ˣ) : Closure K)) h

@[simp] theorem finiteCocycleOnGenericCoeff_coe
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ)
    (sigma : AbsGal K) :
    (((finiteCocycleOnGenericCoeff K n a sigma).toMul :
        KummerTorsion (Closure K)ˣ n) : (Closure K)ˣ) =
      ratioUnit K n a sigma := rfl

theorem finiteCocycleOnGenericCoeff_matches_existing
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ)
    (sigma : AbsGal K) :
    ((((finiteCocycleOnGenericCoeff K n a sigma).toMul :
        KummerTorsion (Closure K)ˣ n) : (Closure K)ˣ) : Closure K) =
      (((finiteContinuousCocycle K n a sigma).toMul :
        Mu K n) : (Closure K)ˣ) := by
  rfl

theorem genericRatio_eq_finite_mul_principal
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ)
    (sigma : AbsGal K) :
    (closureSubgroupInput K).ratioTorsion
        ((baseUnitToFixed K) a) (kummerDegreeOfNeZero n) sigma =
      finiteRatioTorsionOnGeneric K n a sigma *
        (sigma • rootChoiceTorsion K n a / rootChoiceTorsion K n a) := by
  apply Subtype.ext
  apply Units.ext
  simp only [KummerSubgroupInput.ratioTorsion,
    KummerSubgroupInput.ratioAtDegree,
    finiteRatioTorsionOnGeneric, rootChoiceTorsion, finiteChosenRootUnit,
    genericRootForBaseUnit, kummerTorsion_smul_coe,
    Subgroup.coe_mul, Subgroup.coe_div,
    Units.val_mul, Units.val_div_eq_div_val, closureUnits_smul_coe,
    ratioUnit_coe, ratioValue, Units.val_mk0]
  have hs : chosenRoot K n a ≠ 0 := chosenRoot_ne_zero K n a
  have hss : toAlgEquiv K sigma (chosenRoot K n a) ≠ 0 := fun h0 =>
    hs ((toAlgEquiv K sigma).injective (by simpa using h0))
  rw [map_div₀]
  field_simp

theorem finiteCocycle_genericCohomologous
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    Cohomologous
      (AbsGal K) (Additive (KummerTorsion (Closure K)ˣ n))
      (finiteCocycleOnGenericCoeff K n a)
      ((closureSubgroupInput K).kummerCocycleAtLevel
        ((baseUnitToFixed K) a) (kummerDegreeOfNeZero n)) := by
  refine ⟨Additive.ofMul (rootChoiceTorsion K n a), ?_⟩
  intro sigma
  change
    Additive.ofMul
        ((closureSubgroupInput K).ratioTorsion
          ((baseUnitToFixed K) a) (kummerDegreeOfNeZero n) sigma)
      =
    Additive.ofMul (finiteRatioTorsionOnGeneric K n a sigma) +
      (sigma • Additive.ofMul (rootChoiceTorsion K n a) -
        Additive.ofMul (rootChoiceTorsion K n a))
  apply Additive.toMul.injective
  change
    (closureSubgroupInput K).ratioTorsion
        ((baseUnitToFixed K) a) (kummerDegreeOfNeZero n) sigma =
      finiteRatioTorsionOnGeneric K n a sigma *
        (sigma • rootChoiceTorsion K n a / rootChoiceTorsion K n a)
  exact genericRatio_eq_finite_mul_principal K n a sigma

noncomputable def finiteKummerClassOnGenericCoeff
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    H1 (AbsGal K) (Additive (KummerTorsion (Closure K)ˣ n)) :=
  Quotient.mk _ (finiteCocycleOnGenericCoeff K n a)

theorem finiteKummerClassOnGenericCoeff_eq_genericAtLevel
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    finiteKummerClassOnGenericCoeff K n a =
      (closureSubgroupInput K).kummerAtLevel
        ((baseUnitToFixed K) a) (kummerDegreeOfNeZero n) :=
  Quotient.sound (finiteCocycle_genericCohomologous K n a)

theorem finiteRootsAction_eq_generic
    (K : Type u) [Field K] (n : ℕ) [NeZero n] :
    rootsMulDistribAction K n =
      instKummerTorsionMulDistribMulAction
        (AbsGal K) (Closure K)ˣ n := by
  apply MulDistribMulAction.ext
  funext sigma z
  apply Subtype.ext
  apply Units.ext
  rfl

theorem finiteAdditiveAction_eq_generic
    (K : Type u) [Field K] (n : ℕ) [NeZero n] :
    additiveRootsAction K n =
      instAdditiveKummerTorsionDistribMulAction
        (AbsGal K) (Closure K)ˣ n := by
  apply DistribMulAction.ext
  funext sigma z
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rfl

theorem finiteCoefficientTopology_eq_generic
    (K : Type u) [Field K] (n : ℕ) [NeZero n] :
    Src.CoreLayer.LanaStep6.FiniteContinuousKummer.coefficientTopology K n =
      (inferInstance :
        TopologicalSpace
          (Additive (KummerTorsion (Closure K)ˣ n))) := by
  rfl

abbrev ExistingFiniteH1
    (K : Type u) [Field K] (n : ℕ) [NeZero n] : Type u :=
  @H1
    (AbsGal K) (Additive (Mu K n))
    inferInstance inferInstance inferInstance
    (Src.CoreLayer.LanaStep6.FiniteContinuousKummer.coefficientTopology K n)
    (additiveRootsAction K n)
    (Src.CoreLayer.LanaStep6.FiniteContinuousKummer.coefficientContinuousSMul K n)

abbrev GenericFiniteH1
    (K : Type u) [Field K] (n : ℕ) [NeZero n] : Type u :=
  H1 (AbsGal K)
    (Additive (KummerTorsion (Closure K)ˣ n))

theorem existingFiniteH1_eq_genericFiniteH1
    (K : Type u) [Field K] (n : ℕ) [NeZero n] :
    ExistingFiniteH1 K n = GenericFiniteH1 K n := by
  rfl

theorem finiteContinuousCocycle_heq_generic
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    HEq (finiteContinuousCocycle K n a)
      (finiteCocycleOnGenericCoeff K n a) := by
  exact HEq.rfl

noncomputable def finiteKummerClassAsGeneric
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    GenericFiniteH1 K n :=
  cast (existingFiniteH1_eq_genericFiniteH1 K n)
    (finiteKummerClass K n a)

theorem finiteKummerClassAsGeneric_eq_repackaged
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    finiteKummerClassAsGeneric K n a =
      finiteKummerClassOnGenericCoeff K n a := by
  rfl

theorem finiteKummerClass_eq_genericAtLevel
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    finiteKummerClassAsGeneric K n a =
      (closureSubgroupInput K).kummerAtLevel
        ((baseUnitToFixed K) a) (kummerDegreeOfNeZero n) := by
  rw [finiteKummerClassAsGeneric_eq_repackaged]
  exact finiteKummerClassOnGenericCoeff_eq_genericAtLevel K n a

def closureLambdaProjectionAddHom
    (K : Type u) [Field K] (d : KummerDegree) :
    Additive (closureSubgroupInput K).LambdaCoeff →+
      Additive (KummerTorsion (Closure K)ˣ d.val) where
  toFun z :=
    Additive.ofMul
      ((closureSubgroupInput K).coeff.lambdaProjection d z.toMul)
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl

theorem closureLambdaProjectionAddHom_continuous
    (K : Type u) [Field K] (d : KummerDegree) :
    Continuous (closureLambdaProjectionAddHom K d) := by
  change Continuous
    (fun z : Additive (closureSubgroupInput K).LambdaCoeff =>
      Additive.ofMul
        ((closureSubgroupInput K).coeff.lambdaProjection d z.toMul))
  apply continuous_ofMul.comp
  exact (continuous_apply d).comp
    (continuous_subtype_val.comp continuous_toMul)

theorem closureLambdaProjectionAddHom_smul
    (K : Type u) [Field K] (d : KummerDegree)
    (sigma : AbsGal K)
    (z : Additive (closureSubgroupInput K).LambdaCoeff) :
    closureLambdaProjectionAddHom K d (sigma • z) =
      sigma • closureLambdaProjectionAddHom K d z := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

noncomputable def closureProjectLambdaCocycle
    (K : Type u) [Field K] (d : KummerDegree)
    (c : Cocycle (AbsGal K)
      (Additive (closureSubgroupInput K).LambdaCoeff)) :
    Cocycle (AbsGal K)
      (Additive (KummerTorsion (Closure K)ˣ d.val)) where
  toContinuousMap :=
    ⟨fun sigma => closureLambdaProjectionAddHom K d (c sigma),
      (closureLambdaProjectionAddHom_continuous K d).comp
        c.toContinuousMap.continuous⟩
  cocycle' sigma tau := by
    have h :=
      congrArg (closureLambdaProjectionAddHom K d)
        (c.cocycle' sigma tau)
    simpa [map_add, closureLambdaProjectionAddHom_smul] using h

theorem closureProjectLambda_cohomologous
    (K : Type u) [Field K] (d : KummerDegree)
    {c e : Cocycle (AbsGal K)
      (Additive (closureSubgroupInput K).LambdaCoeff)}
    (hce :
      Cohomologous (AbsGal K)
        (Additive (closureSubgroupInput K).LambdaCoeff) c e) :
    Cohomologous (AbsGal K)
      (Additive (KummerTorsion (Closure K)ˣ d.val))
      (closureProjectLambdaCocycle K d c)
      (closureProjectLambdaCocycle K d e) := by
  obtain ⟨b, hb⟩ := hce
  refine ⟨closureLambdaProjectionAddHom K d b, ?_⟩
  intro sigma
  have h :=
    congrArg (closureLambdaProjectionAddHom K d) (hb sigma)
  simpa [map_add, map_sub, closureLambdaProjectionAddHom_smul] using h

noncomputable def closureProjectLambdaH1
    (K : Type u) [Field K] (d : KummerDegree) :
    H1 (AbsGal K)
        (Additive (closureSubgroupInput K).LambdaCoeff) →
      H1 (AbsGal K)
        (Additive (KummerTorsion (Closure K)ˣ d.val)) :=
  Quotient.map (closureProjectLambdaCocycle K d)
    (fun _ _ h => closureProjectLambda_cohomologous K d h)

theorem closureProjectLambdaCocycle_kummer
    (K : Type u) [Field K]
    (x : (closureSubgroupInput K).Fixed)
    (d : KummerDegree) :
    closureProjectLambdaCocycle K d
        ((closureSubgroupInput K).kummerCocycleAtSubgroup x) =
      (closureSubgroupInput K).kummerCocycleAtLevel x d := by
  apply Cocycle.ext
  intro sigma
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

theorem closureProjectLambdaH1_kummerAtSubgroup
    (K : Type u) [Field K]
    (x : (closureSubgroupInput K).Fixed)
    (d : KummerDegree) :
    closureProjectLambdaH1 K d
        ((closureSubgroupInput K).kummerAtSubgroup x) =
      (closureSubgroupInput K).kummerAtLevel x d := by
  change
    Quotient.mk _
      (closureProjectLambdaCocycle K d
        ((closureSubgroupInput K).kummerCocycleAtSubgroup x)) =
    Quotient.mk _
      ((closureSubgroupInput K).kummerCocycleAtLevel x d)
  exact congrArg (Quotient.mk _)
    (closureProjectLambdaCocycle_kummer K x d)

theorem finiteKummerClass_eq_projection_kummerAtSubgroup
    (K : Type u) [Field K] (n : ℕ) [NeZero n] (a : Kˣ) :
    finiteKummerClassAsGeneric K n a =
      closureProjectLambdaH1 K (kummerDegreeOfNeZero n)
        ((closureSubgroupInput K).kummerAtSubgroup
          ((baseUnitToFixed K) a)) := by
  rw [closureProjectLambdaH1_kummerAtSubgroup]
  exact finiteKummerClass_eq_genericAtLevel K n a

def restrictAmbientClosureCocycle
    (K : Type u) [Field K] (J : FiniteOpen (AbsGal K))
    (c : Cocycle (AbsGal K)
      (Additive (closureSubgroupInput K).LambdaCoeff)) :
    Cocycle (restrictedOpen J).toSubgroup
      (Additive (closureSubgroupInput K).LambdaCoeff) where
  toContinuousMap :=
    ⟨fun h => c h.1,
      c.toContinuousMap.continuous.comp continuous_subtype_val⟩
  cocycle' h k := c.cocycle' h.1 k.1

theorem restrictAmbientClosure_cohomologous
    (K : Type u) [Field K] (J : FiniteOpen (AbsGal K))
    {c e : Cocycle (AbsGal K)
      (Additive (closureSubgroupInput K).LambdaCoeff)}
    (hce :
      Cohomologous (AbsGal K)
        (Additive (closureSubgroupInput K).LambdaCoeff) c e) :
    Cohomologous (restrictedOpen J).toSubgroup
      (Additive (closureSubgroupInput K).LambdaCoeff)
      (restrictAmbientClosureCocycle K J c)
      (restrictAmbientClosureCocycle K J e) := by
  obtain ⟨b, hb⟩ := hce
  exact ⟨b, fun h => hb h.1⟩

noncomputable def restrictAmbientClosureH1
    (K : Type u) [Field K] (J : FiniteOpen (AbsGal K)) :
    H1 (AbsGal K)
        (Additive (closureSubgroupInput K).LambdaCoeff) →
      H1 (restrictedOpen J).toSubgroup
        (Additive (closureSubgroupInput K).LambdaCoeff) :=
  Quotient.map (restrictAmbientClosureCocycle K J)
    (fun _ _ h => restrictAmbientClosure_cohomologous K J h)

theorem baseUnitFixedAtFiniteOpen_fixes
    (K : Type u) [Field K] (J : FiniteOpen (AbsGal K)) (a : Kˣ) :
    ∀ h : (restrictedOpen J).toSubgroup,
      h • baseUnitsMap K a = baseUnitsMap K a := by
  intro h
  apply Units.ext
  exact (toAlgEquiv K h.1).commutes (a : K)

def baseUnitFixedAtFiniteOpen
    (K : Type u) [Field K] (J : FiniteOpen (AbsGal K)) (a : Kˣ) :
    ((closureColimitInput K).subgroupInput J).Fixed :=
  ⟨baseUnitsMap K a, baseUnitFixedAtFiniteOpen_fixes K J a⟩

theorem closureRootTower_stage_eq_ambient
    (K : Type u) [Field K] (J : FiniteOpen (AbsGal K))
    (m : (Closure K)ˣ) (r : ℕ) :
    ((closureColimitInput K).subgroupInput J).rootTower m r =
      (closureSubgroupInput K).rootTower m r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [KummerSubgroupInput.rootTower]
      exact KummerColimitInput.chooseDivisible_congr
        (closureCoefficientInput K) (r + 2)
        (Nat.succ_ne_zero (r + 1)) ih

theorem closureRootAtDegree_stage_eq_ambient
    (K : Type u) [Field K] (J : FiniteOpen (AbsGal K))
    (m : (Closure K)ˣ) (d : KummerDegree) :
    ((closureColimitInput K).subgroupInput J).rootAtDegree m d =
      (closureSubgroupInput K).rootAtDegree m d := by
  simp only [KummerSubgroupInput.rootAtDegree,
    closureRootTower_stage_eq_ambient K J m d.val]

theorem closureStageKummerCocycle_eq_restrictAmbient
    (K : Type u) [Field K] (J : FiniteOpen (AbsGal K)) (a : Kˣ) :
    (closureColimitInput K).stageKummerCocycle J
        (baseUnitFixedAtFiniteOpen K J a) =
      restrictAmbientClosureCocycle K J
        ((closureSubgroupInput K).kummerCocycleAtSubgroup
          ((baseUnitToFixed K) a)) := by
  apply Cocycle.ext
  intro h
  apply Additive.toMul.injective
  apply Subtype.ext
  funext d
  apply Subtype.ext
  show
    ((closureColimitInput K).subgroupInput J).ratioAtDegree
        (baseUnitFixedAtFiniteOpen K J a) d h =
      (closureSubgroupInput K).ratioAtDegree
        ((baseUnitToFixed K) a) d h.1
  simp only [KummerSubgroupInput.ratioAtDegree,
    closureRootAtDegree_stage_eq_ambient K J (baseUnitsMap K a) d,
    closureUnits_smul_coe, baseUnitFixedAtFiniteOpen, baseUnitToFixed]
  rfl

theorem closureStageKummerClass_eq_restrictAmbient
    (K : Type u) [Field K] (J : FiniteOpen (AbsGal K)) (a : Kˣ) :
    (closureColimitInput K).stageKummerClass J
        (baseUnitFixedAtFiniteOpen K J a) =
      restrictAmbientClosureH1 K J
        ((closureSubgroupInput K).kummerAtSubgroup
          ((baseUnitToFixed K) a)) := by
  change
    Quotient.mk _
      ((closureColimitInput K).stageKummerCocycle J
        (baseUnitFixedAtFiniteOpen K J a)) =
    Quotient.mk _
      (restrictAmbientClosureCocycle K J
        ((closureSubgroupInput K).kummerCocycleAtSubgroup
          ((baseUnitToFixed K) a)))
  exact congrArg (Quotient.mk _)
    (closureStageKummerCocycle_eq_restrictAmbient K J a)

theorem closureGenericKummerMap_baseUnit_eq_colimitOfGlobalClass
    (K : Type u) [Field K] (J : FiniteOpen (AbsGal K)) (a : Kˣ) :
    (closureColimitInput K).genericKummerMap (baseUnitsMap K a) =
      Src.Lib.ContinuousH1RestrictionColimit.stageToInfinityH1
        (A := Additive (closureColimitInput K).LambdaCoeff)
        (ContinuousMonoidHom.id (AbsGal K)) J
        (restrictAmbientClosureH1 K J
          ((closureSubgroupInput K).kummerAtSubgroup
            ((baseUnitToFixed K) a))) := by
  calc
    (closureColimitInput K).genericKummerMap (baseUnitsMap K a) =
        Src.Lib.ContinuousH1RestrictionColimit.stageToInfinityH1
          (A := Additive (closureColimitInput K).LambdaCoeff)
          (ContinuousMonoidHom.id (AbsGal K)) J
          ((closureColimitInput K).stageKummerClass J
            (baseUnitFixedAtFiniteOpen K J a)) := by
              simpa [baseUnitFixedAtFiniteOpen] using
                (closureColimitInput K).genericKummerMap_eq_of_fixed
                  (baseUnitsMap K a) J
                  (baseUnitFixedAtFiniteOpen_fixes K J a)
    _ =
        Src.Lib.ContinuousH1RestrictionColimit.stageToInfinityH1
          (A := Additive (closureColimitInput K).LambdaCoeff)
          (ContinuousMonoidHom.id (AbsGal K)) J
          (restrictAmbientClosureH1 K J
            ((closureSubgroupInput K).kummerAtSubgroup
              ((baseUnitToFixed K) a))) := by
                rw [closureStageKummerClass_eq_restrictAmbient K J a]

end AlgClosureCarrier

end Src.CoreLayer.LanaStep6.GenericKummerMap

end
