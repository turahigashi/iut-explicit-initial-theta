import Mathlib.Algebra.Group.End
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace CitedLV.Labels

noncomputable section

def plusMinusUnits (l : ℕ) : Subgroup (ZMod l)ˣ where
  carrier := {u | u = 1 ∨ u = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  inv_mem' := by
    intro a ha
    rcases ha with rfl | rfl <;> simp

abbrev FlStar (l : ℕ) := (ZMod l)ˣ ⧸ plusMinusUnits l

theorem flStar_identifies_signs (l : ℕ) (u : (ZMod l)ˣ) :
    QuotientGroup.mk' (plusMinusUnits l) u =
      QuotientGroup.mk' (plusMinusUnits l) (-u) := by
  apply (QuotientGroup.mk'_eq_mk' (plusMinusUnits l)).2
  refine ⟨-1, Or.inr rfl, ?_⟩
  simp

def twoUnitModFive : (ZMod 5)ˣ where
  val := 2
  inv := 3
  val_inv := by decide
  inv_val := by decide

theorem flStar_mod_five_nontrivial :
    QuotientGroup.mk' (plusMinusUnits 5) (1 : (ZMod 5)ˣ) ≠
      QuotientGroup.mk' (plusMinusUnits 5) twoUnitModFive := by
  intro h
  obtain ⟨z, hz, hmul⟩ :=
    (QuotientGroup.mk'_eq_mk' (plusMinusUnits 5)).1 h
  rcases hz with rfl | rfl
  · have hv := congrArg Units.val hmul
    change (1 : ZMod 5) = 2 at hv
    exact (by decide : (1 : ZMod 5) ≠ 2) hv
  · have hv := congrArg Units.val hmul
    change (-1 : ZMod 5) = 2 at hv
    exact (by decide : (-1 : ZMod 5) ≠ 2) hv

abbrev AdditiveLabelGroup (l : ℕ) := Multiplicative (ZMod l)

def signAction (l : ℕ) :
    plusMinusUnits l →* MulAut (AdditiveLabelGroup l) :=
  (MulAutMultiplicative (ZMod l)).symm.toMonoidHom.comp
    ((DistribMulAction.toAddAut (ZMod l)ˣ (ZMod l)).comp (plusMinusUnits l).subtype)

abbrev SignedAffineLabelGroup (l : ℕ) :=
  AdditiveLabelGroup l ⋊[signAction l] plusMinusUnits l

def signedAffinePerm (l : ℕ) (g : SignedAffineLabelGroup l) : Equiv.Perm (ZMod l) where
  toFun z := g.left.toAdd + (g.right.1 : ZMod l) * z
  invFun z := (g.right.1⁻¹ : ZMod l) * (z - g.left.toAdd)
  left_inv z := by
    simp
  right_inv z := by
    simp

def signedAffineAction (l : ℕ) :
    SignedAffineLabelGroup l →* Equiv.Perm (ZMod l) where
  toFun := signedAffinePerm l
  map_one' := by
    ext z
    simp [signedAffinePerm]
  map_mul' g h := by
    ext z
    simp [signedAffinePerm, signAction, Units.smul_def]
    ring

def translationLabel (l : ℕ) (a : ZMod l) : SignedAffineLabelGroup l :=
  ⟨Multiplicative.ofAdd a, 1⟩

theorem translationLabel_apply (l : ℕ) (a z : ZMod l) :
    signedAffinePerm l (translationLabel l a) z = a + z := by
  simp [signedAffinePerm, translationLabel]

theorem signedAffinePerm_preserves_distinct (l : ℕ)
    (g : SignedAffineLabelGroup l) {x y : ZMod l} (hxy : x ≠ y) :
    signedAffinePerm l g x ≠ signedAffinePerm l g y :=
  (signedAffinePerm l g).injective.ne hxy

theorem translation_nontrivial_mod_five :
    signedAffinePerm 5 (translationLabel 5 1) 0 = 1 ∧
      (0 : ZMod 5) ≠ 1 := by
  constructor
  · norm_num [translationLabel_apply]
  · decide

theorem phaseD1_summary :
    signedAffinePerm 5 (translationLabel 5 1) 0 = 1 ∧
      (0 : ZMod 5) ≠ 1 ∧
      signedAffinePerm 5 (translationLabel 5 1) 0 ≠
        signedAffinePerm 5 (translationLabel 5 1) 1 := by
  refine ⟨translation_nontrivial_mod_five.1,
    translation_nontrivial_mod_five.2, ?_⟩
  exact signedAffinePerm_preserves_distinct 5 (translationLabel 5 1) (by decide)

end

end CitedLV.Labels
