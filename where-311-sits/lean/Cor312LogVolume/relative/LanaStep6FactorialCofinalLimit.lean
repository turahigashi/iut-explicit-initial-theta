import Cor312LogVolume.relative.LanaStep6FactorialKummerTower
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorial.Basic

noncomputable section

namespace Src.CoreLayer.LanaStep6.FactorialCofinalLimit

open CategoryTheory CategoryTheory.Limits
open Src.CoreLayer.LanaStep6.FiniteKummerRatio
open Src.CoreLayer.LanaStep6.FactorialKummerTower

universe u

variable (K : Type u) [Field K]

structure CyclotomicDegree where
  val : ℕ
  pos : 0 < val

instance : Preorder CyclotomicDegree where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ hab hbc := hab.trans hbc

@[simp] theorem cyclotomicDegree_le_iff (a b : CyclotomicDegree) :
    a ≤ b ↔ a.val ∣ b.val :=
  Iff.rfl

def factorialDegree (n : ℕ) : CyclotomicDegree :=
  ⟨stageDegree n, stageDegree_pos n⟩

theorem factorialDegree_monotone : Monotone factorialDegree := by
  intro m n hmn
  change Nat.factorial (m + 1) ∣ Nat.factorial (n + 1)
  exact Nat.factorial_dvd_factorial (Nat.add_le_add_right hmn 1)

theorem factorial_degrees_cofinal (d : CyclotomicDegree) :
    ∃ n : ℕ, d ≤ factorialDegree n := by
  refine ⟨d.val, ?_⟩
  change d.val ∣ Nat.factorial (d.val + 1)
  exact Nat.dvd_factorial d.pos (Nat.le_succ d.val)

abbrev FullIndex := OrderDual CyclotomicDegree

abbrev FactorialIndex := OrderDual ℕ

def factorialInclusionFn : FactorialIndex → FullIndex :=
  OrderDual.toDual ∘ factorialDegree ∘ OrderDual.ofDual

theorem factorialInclusion_monotone : Monotone factorialInclusionFn :=
  factorialDegree_monotone.dual

def factorialInclusion : FactorialIndex ⥤ FullIndex :=
  factorialInclusion_monotone.functor

instance factorialInclusion_initial : factorialInclusion.Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro j
    obtain ⟨n, hn⟩ := factorial_degrees_cofinal (OrderDual.ofDual j)
    exact ⟨OrderDual.toDual n, ⟨homOfLE (by exact hn)⟩⟩
  · intro d c s s'
    exact ⟨c, 𝟙 c, Subsingleton.elim _ _⟩

def rootsTransition {m n : CyclotomicDegree} (h : m ≤ n) :
    rootsOfUnity n.val (Closure K) →* rootsOfUnity m.val (Closure K) where
  toFun z :=
    ⟨z.1 ^ (n.val / m.val), by
      apply (mem_rootsOfUnity m.val _).2
      rw [← pow_mul, Nat.div_mul_cancel h]
      exact (mem_rootsOfUnity n.val z.1).1 z.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_pow]

@[simp] theorem rootsTransition_refl
    (d : CyclotomicDegree) :
    rootsTransition K (le_refl d) =
      MonoidHom.id (rootsOfUnity d.val (Closure K)) := by
  apply MonoidHom.ext
  intro z
  apply rootsOfUnity.coe_injective
  show ((z : (Closure K)ˣ) : Closure K) ^ (d.val / d.val) = _
  rw [Nat.div_self d.pos, pow_one]
  rfl

theorem rootsTransition_comp
    {l m n : CyclotomicDegree}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    rootsTransition K (hlm.trans hmn) =
      (rootsTransition K hlm).comp (rootsTransition K hmn) := by
  apply MonoidHom.ext
  intro z
  apply rootsOfUnity.coe_injective
  change
    ((((z : rootsOfUnity n.val (Closure K)) : (Closure K)ˣ) : Closure K) ^
        (n.val / l.val)) =
      ((((z : rootsOfUnity n.val (Closure K)) : (Closure K)ˣ) : Closure K) ^
          (n.val / m.val)) ^ (m.val / l.val)
  rw [← pow_mul, Nat.div_mul_div hmn hlm]

def fullCyclotomicDiagram : FullIndex ⥤ CommGrpCat.{u} where
  obj j :=
    CommGrpCat.of (rootsOfUnity (OrderDual.ofDual j).val (Closure K))
  map {X Y} f :=
    CommGrpCat.ofHom
      (rootsTransition K
        (show OrderDual.ofDual Y ≤ OrderDual.ofDual X from leOfHom f))
  map_id X := by
    apply CommGrpCat.Hom.ext
    simpa using rootsTransition_refl K (OrderDual.ofDual X)
  map_comp {X Y Z} f g := by
    apply CommGrpCat.Hom.ext
    have hXY : OrderDual.ofDual Y ≤ OrderDual.ofDual X := leOfHom f
    have hYZ : OrderDual.ofDual Z ≤ OrderDual.ofDual Y := leOfHom g
    simpa using rootsTransition_comp K hYZ hXY

abbrev factorialCyclotomicDiagram : FactorialIndex ⥤ CommGrpCat.{u} :=
  factorialInclusion ⋙ fullCyclotomicDiagram K

def factorialRootsTransition {m n : ℕ} (h : m ≤ n) :
    StageMu K n →* StageMu K m :=
  rootsTransition K (factorialDegree_monotone h)

theorem factorialRootsTransition_succ (n : ℕ) :
    factorialRootsTransition K (Nat.le_succ n) = transitionMu K n := by
  apply MonoidHom.ext
  intro z
  apply rootsOfUnity.coe_injective
  change
    ((((z : StageMu K (n + 1)) : (Closure K)ˣ) : Closure K) ^
        (stageDegree (n + 1) / stageDegree n)) =
      ((((z : StageMu K (n + 1)) : (Closure K)ˣ) : Closure K) ^ (n + 2))
  rw [stageDegree_succ, Nat.mul_div_cancel _ (stageDegree_pos n)]

theorem factorialMu_transition
    (z : FactorialMu K) {m n : ℕ} (hmn : m ≤ n) :
    factorialRootsTransition K hmn (z.1 n) = z.1 m := by
  induction n, hmn using Nat.le_induction with
  | base =>
      change rootsTransition K (factorialDegree_monotone (le_refl m)) (z.1 m) = z.1 m
      rw [rootsTransition_refl]
      rfl
  | succ n hmn ih =>
      calc
        factorialRootsTransition K (hmn.trans (Nat.le_succ n)) (z.1 (n + 1))
            =
          factorialRootsTransition K hmn
            (factorialRootsTransition K (Nat.le_succ n) (z.1 (n + 1))) := by
              change
                rootsTransition K
                    (factorialDegree_monotone
                      (hmn.trans (Nat.le_succ n))) (z.1 (n + 1))
                  =
                rootsTransition K (factorialDegree_monotone hmn)
                  (rootsTransition K
                    (factorialDegree_monotone (Nat.le_succ n))
                    (z.1 (n + 1)))
              rw [rootsTransition_comp K (factorialDegree_monotone hmn)
                    (factorialDegree_monotone (Nat.le_succ n))]
              rfl
        _ = factorialRootsTransition K hmn (z.1 n) := by
              rw [factorialRootsTransition_succ, z.2 n]
        _ = z.1 m := ih

def factorialProjection (n : ℕ) :
    FactorialMu K →* StageMu K n where
  toFun z := z.1 n
  map_one' := rfl
  map_mul' _ _ := rfl

def factorialCone : Cone (factorialCyclotomicDiagram K) where
  pt := CommGrpCat.of (FactorialMu K)
  π :=
    { app := fun j =>
        CommGrpCat.ofHom (factorialProjection K (OrderDual.ofDual j))
      naturality := by
        intro i j f
        apply CommGrpCat.Hom.ext
        ext z
        exact (factorialMu_transition K z (leOfHom f)).symm }

noncomputable def factorialConeIsLimit :
    IsLimit (factorialCone K) where
  lift s :=
    CommGrpCat.ofHom
      { toFun := fun x =>
          ⟨fun n => (s.π.app (OrderDual.toDual n)).hom x, by
            intro n
            let f :
                (OrderDual.toDual (n + 1) : FactorialIndex) ⟶
                  OrderDual.toDual n :=
              homOfLE (Nat.le_succ n)
            have hs := CategoryTheory.ConcreteCategory.congr_hom (s.w f) x
            change
              factorialRootsTransition K (Nat.le_succ n)
                  ((s.π.app (OrderDual.toDual (n + 1))).hom x) =
                (s.π.app (OrderDual.toDual n)).hom x at hs
            rwa [factorialRootsTransition_succ] at hs⟩
        map_one' := by
          apply Subtype.ext
          funext n
          exact map_one (s.π.app (OrderDual.toDual n)).hom
        map_mul' := by
          intro x y
          apply Subtype.ext
          funext n
          exact map_mul (s.π.app (OrderDual.toDual n)).hom x y }
  fac s j := by
    apply CommGrpCat.Hom.ext
    apply MonoidHom.ext
    intro x
    rfl
  uniq s m hm := by
    apply CommGrpCat.Hom.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    funext n
    have h :=
      CategoryTheory.ConcreteCategory.congr_hom
        (hm (OrderDual.toDual n)) x
    exact h

noncomputable def factorialMuIsoFactorialLimit :
    CommGrpCat.of (FactorialMu K) ≅
      limit (factorialCyclotomicDiagram K) :=
  (factorialConeIsLimit K).conePointUniqueUpToIso
    (limit.isLimit (factorialCyclotomicDiagram K))

noncomputable def factorialLimitIsoFullCyclotomicLimit :
    limit (factorialCyclotomicDiagram K) ≅
      limit (fullCyclotomicDiagram K) :=
  CategoryTheory.Functor.Initial.limitIso
    factorialInclusion (fullCyclotomicDiagram K)

noncomputable def factorialMuEquivFullCyclotomicLimit :
    FactorialMu K ≃* (limit (fullCyclotomicDiagram K)).carrier :=
  (factorialMuIsoFactorialLimit K ≪≫
    factorialLimitIsoFullCyclotomicLimit K).commGroupIsoToMulEquiv

end Src.CoreLayer.LanaStep6.FactorialCofinalLimit

end
