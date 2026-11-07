import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

set_option maxRecDepth 8000

namespace FrdI.Model

open CategoryTheory

universe u v

variable {D : Type u} [Category.{v} D]

structure Data (D : Type u) [Category.{v} D] where

  Phi : D → Type u
  [phiMon : ∀ d, AddCommMonoid (Phi d)]

  Phigp : D → Type u
  [phigpGrp : ∀ d, AddCommGroup (Phigp d)]

  B : D → Type u
  [bGrp : ∀ d, AddCommGroup (B d)]

  phiMap : ∀ {d e : D}, (d ⟶ e) → Phi e →+ Phi d

  phigpMap : ∀ {d e : D}, (d ⟶ e) → Phigp e →+ Phigp d

  bMap : ∀ {d e : D}, (d ⟶ e) → B e →+ B d

  incl : ∀ d, Phi d →+ Phigp d

  div : ∀ d, B d →+ Phigp d

  phigpMap_id : ∀ (d : D) (x : Phigp d), phigpMap (𝟙 d) x = x

  phigpMap_comp : ∀ {d e f : D} (g : d ⟶ e) (h : e ⟶ f) (x : Phigp f),
    phigpMap (g ≫ h) x = phigpMap g (phigpMap h x)
  phiMap_id : ∀ (d : D) (x : Phi d), phiMap (𝟙 d) x = x
  phiMap_comp : ∀ {d e f : D} (g : d ⟶ e) (h : e ⟶ f) (x : Phi f),
    phiMap (g ≫ h) x = phiMap g (phiMap h x)
  bMap_id : ∀ (d : D) (x : B d), bMap (𝟙 d) x = x
  bMap_comp : ∀ {d e f : D} (g : d ⟶ e) (h : e ⟶ f) (x : B f),
    bMap (g ≫ h) x = bMap g (bMap h x)

  incl_natural : ∀ {d e : D} (g : d ⟶ e) (x : Phi e),
    incl d (phiMap g x) = phigpMap g (incl e x)

  div_natural : ∀ {d e : D} (g : d ⟶ e) (x : B e),
    div d (bMap g x) = phigpMap g (div e x)

attribute [instance] Data.phiMon Data.phigpGrp Data.bGrp

variable (Ω : Data D)

structure Obj where
  base : D
  alpha : Ω.Phigp base

structure Hom (A B : Obj Ω) where

  degFr : ℕ
  degFr_pos : 0 < degFr

  baseHom : A.base ⟶ B.base

  divisor : Ω.Phi A.base

  unit : Ω.B A.base

  rel : (degFr : ℤ) • A.alpha + Ω.incl A.base divisor
      = Ω.phigpMap baseHom B.alpha + Ω.div A.base unit

namespace Hom

def id (A : Obj Ω) : Hom Ω A A where
  degFr := 1
  degFr_pos := Nat.one_pos
  baseHom := 𝟙 A.base
  divisor := 0
  unit := 0
  rel := by simp [Ω.phigpMap_id]

def comp {A B C : Obj Ω} (φ : Hom Ω A B) (ψ : Hom Ω B C) : Hom Ω A C where
  degFr := ψ.degFr * φ.degFr
  degFr_pos := Nat.mul_pos ψ.degFr_pos φ.degFr_pos
  baseHom := φ.baseHom ≫ ψ.baseHom
  divisor := Ω.phiMap φ.baseHom ψ.divisor + ψ.degFr • φ.divisor
  unit := Ω.bMap φ.baseHom ψ.unit + ψ.degFr • φ.unit
  rel := by
    have hφ := φ.rel
    have hψ := ψ.rel
    have hincl : Ω.incl A.base (Ω.phiMap φ.baseHom ψ.divisor)
        = Ω.phigpMap φ.baseHom (Ω.incl B.base ψ.divisor) := Ω.incl_natural _ _
    have hdiv : Ω.div A.base (Ω.bMap φ.baseHom ψ.unit)
        = Ω.phigpMap φ.baseHom (Ω.div B.base ψ.unit) := Ω.div_natural _ _
    have hcomp : Ω.phigpMap (φ.baseHom ≫ ψ.baseHom) C.alpha
        = Ω.phigpMap φ.baseHom (Ω.phigpMap ψ.baseHom C.alpha) := Ω.phigpMap_comp _ _ _

    have hψ' : Ω.phigpMap φ.baseHom ((ψ.degFr : ℤ) • B.alpha + Ω.incl B.base ψ.divisor)
        = Ω.phigpMap φ.baseHom (Ω.phigpMap ψ.baseHom C.alpha + Ω.div B.base ψ.unit) := by
      rw [hψ]
    simp only [map_add, map_zsmul] at hψ'

    have hφ' : (ψ.degFr : ℤ) • ((φ.degFr : ℤ) • A.alpha + Ω.incl A.base φ.divisor)
        = (ψ.degFr : ℤ) • (Ω.phigpMap φ.baseHom B.alpha + Ω.div A.base φ.unit) := by
      rw [hφ]
    simp only [smul_add, smul_smul] at hφ'
    simp only [map_add, map_nsmul, hincl, hdiv, hcomp, Nat.cast_mul]
    simp only [← natCast_zsmul] at hφ' hψ' ⊢
    push_cast at hφ' hψ' ⊢
    linear_combination (norm := abel) hφ' + hψ'

end Hom

theorem Hom.ext' {A B : Obj Ω} : ∀ {φ ψ : Hom Ω A B},
    φ.degFr = ψ.degFr → φ.baseHom = ψ.baseHom →
    φ.divisor = ψ.divisor → φ.unit = ψ.unit → φ = ψ
  | ⟨_, _, _, _, _, _⟩, ⟨_, _, _, _, _, _⟩, h1, h2, h3, h4 => by
      cases h1; cases h2; cases h3; cases h4; rfl

instance category : Category (Obj Ω) where
  Hom A B := Hom Ω A B
  id A := Hom.id Ω A
  comp φ ψ := Hom.comp Ω φ ψ
  id_comp := by
    intro A B φ
    refine Hom.ext' Ω ?_ ?_ ?_ ?_
    · show φ.degFr * 1 = φ.degFr; exact Nat.mul_one _
    · show 𝟙 A.base ≫ φ.baseHom = φ.baseHom; exact Category.id_comp _
    · show Ω.phiMap (𝟙 A.base) φ.divisor + φ.degFr • (0 : Ω.Phi A.base) = φ.divisor
      rw [Ω.phiMap_id, smul_zero, add_zero]
    · show Ω.bMap (𝟙 A.base) φ.unit + φ.degFr • (0 : Ω.B A.base) = φ.unit
      rw [Ω.bMap_id, smul_zero, add_zero]
  comp_id := by
    intro A B φ
    refine Hom.ext' Ω ?_ ?_ ?_ ?_
    · show 1 * φ.degFr = φ.degFr; exact Nat.one_mul _
    · show φ.baseHom ≫ 𝟙 B.base = φ.baseHom; exact Category.comp_id _
    · show Ω.phiMap φ.baseHom (0 : Ω.Phi B.base) + 1 • φ.divisor = φ.divisor
      rw [map_zero, zero_add, one_smul]
    · show Ω.bMap φ.baseHom (0 : Ω.B B.base) + 1 • φ.unit = φ.unit
      rw [map_zero, zero_add, one_smul]
  assoc := by
    intro A B C E φ ψ χ
    refine Hom.ext' Ω ?_ ?_ ?_ ?_
    · show χ.degFr * (ψ.degFr * φ.degFr) = χ.degFr * ψ.degFr * φ.degFr
      exact (Nat.mul_assoc _ _ _).symm
    · show (φ.baseHom ≫ ψ.baseHom) ≫ χ.baseHom = φ.baseHom ≫ ψ.baseHom ≫ χ.baseHom
      exact Category.assoc _ _ _
    · show Ω.phiMap (φ.baseHom ≫ ψ.baseHom) χ.divisor
            + χ.degFr • (Ω.phiMap φ.baseHom ψ.divisor + ψ.degFr • φ.divisor)
          = Ω.phiMap φ.baseHom (Ω.phiMap ψ.baseHom χ.divisor + χ.degFr • ψ.divisor)
            + (χ.degFr * ψ.degFr) • φ.divisor
      rw [Ω.phiMap_comp, map_add, map_nsmul, smul_add, smul_smul, add_assoc]
    · show Ω.bMap (φ.baseHom ≫ ψ.baseHom) χ.unit
            + χ.degFr • (Ω.bMap φ.baseHom ψ.unit + ψ.degFr • φ.unit)
          = Ω.bMap φ.baseHom (Ω.bMap ψ.baseHom χ.unit + χ.degFr • ψ.unit)
            + (χ.degFr * ψ.degFr) • φ.unit
      rw [Ω.bMap_comp, map_add, map_nsmul, smul_add, smul_smul, add_assoc]

def degFrOf {A B : Obj Ω} (φ : A ⟶ B) : ℕ := Hom.degFr φ

theorem degFr_comp {A B C : Obj Ω} (φ : A ⟶ B) (ψ : B ⟶ C) :
    degFrOf Ω (φ ≫ ψ) = degFrOf Ω ψ * degFrOf Ω φ := rfl

theorem degFr_id (A : Obj Ω) : degFrOf Ω (𝟙 A) = 1 := rfl

theorem degFr_pos {A B : Obj Ω} (φ : A ⟶ B) : 0 < degFrOf Ω φ := Hom.degFr_pos φ

def Base (A : Obj Ω) : D := A.base

theorem obj_ne_of_base_ne {A B : Obj Ω} (h : A.base ≠ B.base) : A ≠ B := by
  intro hAB; exact h (congrArg Obj.base hAB)

end FrdI.Model
