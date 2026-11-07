import Mathlib.Algebra.Group.End
import Mathlib.Data.Bool.Basic

namespace CitedLV.ThetaLink

universe u v

structure ProcessionShape (Label : Type u) where
  transition : Label → Label → Prop

abbrev Procession (Label : Type u) (Strip : Type v) := Label → Strip

structure ProcessionAutomorphism
    {Label : Type u} (S : ProcessionShape Label) (Strip : Type v) where
  labelPerm : Equiv.Perm Label
  preservesTransition : ∀ i j,
    S.transition i j ↔ S.transition (labelPerm i) (labelPerm j)
  stripPerm : Label → Equiv.Perm Strip

def processionEquiv {Label : Type u} {Strip : Type v}
    {S : ProcessionShape Label} (A : ProcessionAutomorphism S Strip) :
    Equiv.Perm (Procession Label Strip) where
  toFun P i := A.stripPerm i (P (A.labelPerm.symm i))
  invFun P i :=
    (A.stripPerm (A.labelPerm i)).symm (P (A.labelPerm i))
  left_inv := by
    intro P
    funext i
    simp
  right_inv := by
    intro P
    funext i
    simp

def ProcessionAutomorphism.refl
    {Label : Type u} (S : ProcessionShape Label) (Strip : Type v) :
    ProcessionAutomorphism S Strip where
  labelPerm := Equiv.refl Label
  preservesTransition := by
    intro i j
    rfl
  stripPerm _ := Equiv.refl Strip

def ProcessionAutomorphism.trans
    {Label : Type u} {Strip : Type v}
    {S : ProcessionShape Label}
    (A B : ProcessionAutomorphism S Strip) :
    ProcessionAutomorphism S Strip where
  labelPerm := A.labelPerm.trans B.labelPerm
  preservesTransition := by
    intro i j
    exact (A.preservesTransition i j).trans
      (B.preservesTransition (A.labelPerm i) (A.labelPerm j))
  stripPerm i :=
    (A.stripPerm (B.labelPerm.symm i)).trans (B.stripPerm i)

def ProcessionAutomorphism.symm
    {Label : Type u} {Strip : Type v}
    {S : ProcessionShape Label}
    (A : ProcessionAutomorphism S Strip) :
    ProcessionAutomorphism S Strip where
  labelPerm := A.labelPerm.symm
  preservesTransition := by
    intro i j
    simpa using
      (A.preservesTransition (A.labelPerm.symm i)
        (A.labelPerm.symm j)).symm
  stripPerm i := (A.stripPerm (A.labelPerm i)).symm

theorem processionEquiv_refl
    {Label : Type u} (S : ProcessionShape Label) (Strip : Type v) :
    processionEquiv (ProcessionAutomorphism.refl S Strip) =
      Equiv.refl (Procession Label Strip) := by
  ext P i
  rfl

theorem processionEquiv_trans
    {Label : Type u} {Strip : Type v}
    {S : ProcessionShape Label}
    (A B : ProcessionAutomorphism S Strip) :
    processionEquiv (A.trans B) =
      (processionEquiv A).trans (processionEquiv B) := by
  ext P i
  rfl

theorem processionEquiv_symm
    {Label : Type u} {Strip : Type v}
    {S : ProcessionShape Label}
    (A : ProcessionAutomorphism S Strip) :
    processionEquiv A.symm = (processionEquiv A).symm := by
  ext P i
  rfl

theorem procession_action_is_reversible
    {Label : Type u} {Strip : Type v}
    {S : ProcessionShape Label}
    (A : ProcessionAutomorphism S Strip)
    (P : Procession Label Strip) :
    processionEquiv A.symm (processionEquiv A P) = P := by
  rw [processionEquiv_symm]
  exact (processionEquiv A).symm_apply_apply P

def IsLabelOnly {Label : Type u} {Strip : Type v}
    {S : ProcessionShape Label}
    (A : ProcessionAutomorphism S Strip) : Prop :=
  ∀ i, A.stripPerm i = Equiv.refl Strip

def IsStripOnly {Label : Type u} {Strip : Type v}
    {S : ProcessionShape Label}
    (A : ProcessionAutomorphism S Strip) : Prop :=
  A.labelPerm = Equiv.refl Label

def boolProcession : Procession Bool Bool := fun b ↦ b

def boolProcessionShape : ProcessionShape Bool where
  transition i j := i ≠ j

def asymmetricBoolProcessionShape : ProcessionShape Bool where
  transition i j := i = false ∧ j = true

def ind1BoolSwap : Equiv.Perm Bool := Equiv.swap false true

theorem ind1BoolSwap_fails_asymmetric_transition :
    ¬ ∀ i j,
      asymmetricBoolProcessionShape.transition i j ↔
        asymmetricBoolProcessionShape.transition
          (ind1BoolSwap i) (ind1BoolSwap j) := by
  intro h
  have hft := (h false true).mp (by
    simp [asymmetricBoolProcessionShape])
  simpa [asymmetricBoolProcessionShape, ind1BoolSwap] using hft

def boolLabelInd1 : ProcessionAutomorphism boolProcessionShape Bool where
  labelPerm := ind1BoolSwap
  preservesTransition := by
    intro i j
    constructor
    · intro hij heq
      exact hij (ind1BoolSwap.injective heq)
    · intro hij heq
      exact hij (congrArg ind1BoolSwap heq)
  stripPerm _ := Equiv.refl Bool

def boolStripInd1 : ProcessionAutomorphism boolProcessionShape Bool where
  labelPerm := Equiv.refl Bool
  preservesTransition := by
    intro i j
    rfl
  stripPerm i := if i then ind1BoolSwap else Equiv.refl Bool

theorem boolLabelInd1_is_label_only : IsLabelOnly boolLabelInd1 := by
  intro i
  rfl

theorem boolStripInd1_is_strip_only : IsStripOnly boolStripInd1 :=
  rfl

theorem boolLabelInd1_moves_procession :
    processionEquiv boolLabelInd1 boolProcession ≠ boolProcession := by
  intro h
  have htrue := congrFun h true
  exact (by decide : false ≠ true) (by
    simpa [processionEquiv, boolLabelInd1, boolProcession, ind1BoolSwap]
      using htrue)

theorem boolStripInd1_changes_true_component :
    processionEquiv boolStripInd1 boolProcession true = false ∧
      processionEquiv boolStripInd1 boolProcession false = false := by
  constructor <;>
    rfl

theorem label_and_strip_ind1_are_distinct :
    processionEquiv boolLabelInd1 ≠ processionEquiv boolStripInd1 := by
  intro h
  have happ := congrArg
    (fun e : Equiv.Perm (Procession Bool Bool) ↦ e boolProcession false) h
  exact (by decide : true ≠ false) (by
    simpa [processionEquiv, boolLabelInd1, boolStripInd1, boolProcession,
      ind1BoolSwap] using happ)

theorem identity_procession_automorphism_moves_nothing
    {Label : Type u} {Strip : Type v}
    (S : ProcessionShape Label)
    (P : Procession Label Strip) :
    processionEquiv (ProcessionAutomorphism.refl S Strip) P = P := by
  rfl

end CitedLV.ThetaLink
