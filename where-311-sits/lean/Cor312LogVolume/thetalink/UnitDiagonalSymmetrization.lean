import Mathlib.Logic.Equiv.Bool

namespace CitedLV.ThetaLink

universe uU uL uC

structure LabelledUnitCopiesRaw
    (U : Type uU) (L : Type uL) (Copy : L → Type uC)
    (SymmRel : L → L → Prop) where
  embed : (j : L) → U → Copy j
  symmetrize : {i j : L} → SymmRel i j → Copy i ≃ Copy j
  readout : U → ((j : L) → Copy j)

def embeddedUnitProfile
    {U : Type uU} {L : Type uL} {Copy : L → Type uC}
    {SymmRel : L → L → Prop}
    (D : LabelledUnitCopiesRaw U L Copy SymmRel) :
    U → ((j : L) → Copy j) :=
  fun u j ↦ D.embed j u

def UnitDiagonal
    {U : Type uU} {L : Type uL} {Copy : L → Type uC}
    {SymmRel : L → L → Prop}
    (D : LabelledUnitCopiesRaw U L Copy SymmRel) : Prop :=
  ∀ u j, D.readout u j = D.embed j u

def SymmetrizationRespectsReferenceUnit
    {U : Type uU} {L : Type uL} {Copy : L → Type uC}
    {SymmRel : L → L → Prop}
    (D : LabelledUnitCopiesRaw U L Copy SymmRel) : Prop :=
  ∀ {i j} (hij : SymmRel i j) u,
    D.symmetrize hij (D.embed i u) = D.embed j u

def SymmetrizationSelfIdentity
    {U : Type uU} {L : Type uL} {Copy : L → Type uC}
    {SymmRel : L → L → Prop}
    (D : LabelledUnitCopiesRaw U L Copy SymmRel) : Prop :=
  ∀ (i : L) (hii : SymmRel i i),
    D.symmetrize hii = Equiv.refl (Copy i)

def SymmetrizationComposition
    {U : Type uU} {L : Type uL} {Copy : L → Type uC}
    {SymmRel : L → L → Prop}
    (D : LabelledUnitCopiesRaw U L Copy SymmRel) : Prop :=
  ∀ {i j k : L} (hij : SymmRel i j) (hjk : SymmRel j k)
      (hik : SymmRel i k),
    (D.symmetrize hij).trans (D.symmetrize hjk) = D.symmetrize hik

def UnitReadoutFaithful
    {U : Type uU} {L : Type uL} {Copy : L → Type uC}
    {SymmRel : L → L → Prop}
    (D : LabelledUnitCopiesRaw U L Copy SymmRel) : Prop :=
  Function.Injective D.readout

def UnitReadoutNonconstant
    {U : Type uU} {L : Type uL} {Copy : L → Type uC}
    {SymmRel : L → L → Prop}
    (D : LabelledUnitCopiesRaw U L Copy SymmRel) : Prop :=
  ∃ u v, D.readout u ≠ D.readout v

def ToyUnitCopy : Bool → Type
  | false => Bool
  | true => Fin 2

def ToySymmRel (_ _ : Bool) : Prop := True

def toyUnitEmbed : (j : Bool) → Bool → ToyUnitCopy j
  | false => fun u ↦ u
  | true => finTwoEquiv.symm

def toyUnitSymmetrize (i j : Bool) : ToyUnitCopy i ≃ ToyUnitCopy j :=
  match i, j with
  | false, false => Equiv.refl Bool
  | false, true => finTwoEquiv.symm
  | true, false => finTwoEquiv
  | true, true => Equiv.refl (Fin 2)

def toyUnitReadout (u : Bool) (j : Bool) : ToyUnitCopy j :=
  toyUnitEmbed j u

def toyLabelledUnitCopies :
    LabelledUnitCopiesRaw Bool Bool ToyUnitCopy ToySymmRel where
  embed := toyUnitEmbed
  symmetrize := fun {i j} _ ↦ toyUnitSymmetrize i j
  readout := toyUnitReadout

theorem toy_unit_diagonal : UnitDiagonal toyLabelledUnitCopies := by
  intro u j
  rfl

theorem toy_symmetrization_respects_reference_unit :
    SymmetrizationRespectsReferenceUnit toyLabelledUnitCopies := by
  intro i j hij u
  cases i <;> cases j <;> cases u <;> rfl

theorem toy_symmetrization_self_identity :
    SymmetrizationSelfIdentity toyLabelledUnitCopies := by
  intro i hii
  cases i <;> rfl

theorem toy_symmetrization_composition :
    SymmetrizationComposition toyLabelledUnitCopies := by
  intro i j k hij hjk hik
  cases i <;> cases j <;> cases k <;>
    apply Equiv.ext <;> intro x
  all_goals first
    | rfl
    | exact finTwoEquiv.apply_symm_apply x
    | exact finTwoEquiv.symm_apply_apply x

theorem toy_unit_readout_faithful :
    UnitReadoutFaithful toyLabelledUnitCopies := by
  intro u v h
  have hfalse := congrFun h false
  simpa [toyLabelledUnitCopies, toyUnitReadout, toyUnitEmbed] using hfalse

theorem toy_unit_readout_nonconstant :
    UnitReadoutNonconstant toyLabelledUnitCopies := by
  refine ⟨false, true, ?_⟩
  intro h
  have hfalse := congrFun h false
  simpa [toyLabelledUnitCopies, toyUnitReadout, toyUnitEmbed] using hfalse

theorem toy_dependent_copy_boundary :
    ToyUnitCopy false = Bool ∧ ToyUnitCopy true = Fin 2 :=
  ⟨rfl, rfl⟩

def flippedUnitReadout (u : Bool) (j : Bool) : ToyUnitCopy j :=
  toyUnitEmbed j (!u)

def flippedReadoutData :
    LabelledUnitCopiesRaw Bool Bool ToyUnitCopy ToySymmRel where
  embed := toyUnitEmbed
  symmetrize := fun {i j} _ ↦ toyUnitSymmetrize i j
  readout := flippedUnitReadout

theorem flipped_readout_is_faithful :
    UnitReadoutFaithful flippedReadoutData := by
  intro u v h
  have hfalse := congrFun h false
  change (!u : Bool) = !v at hfalse
  simpa using Bool.not_injective hfalse

theorem flipped_readout_is_nonconstant :
    UnitReadoutNonconstant flippedReadoutData := by
  refine ⟨false, true, ?_⟩
  intro h
  have hfalse := congrFun h false
  change (!false : Bool) = !true at hfalse
  simpa using hfalse

theorem flipped_readout_not_unit_diagonal :
    ¬ UnitDiagonal flippedReadoutData := by
  intro h
  have hf := h false false
  change (!false : Bool) = false at hf
  simpa using hf

theorem flipped_readout_keeps_reference_symmetrization :
    SymmetrizationRespectsReferenceUnit flippedReadoutData :=
  toy_symmetrization_respects_reference_unit

def badUnitSymmetrize (i j : Bool) : ToyUnitCopy i ≃ ToyUnitCopy j :=
  match i, j with
  | false, false => Equiv.boolNot
  | false, true => finTwoEquiv.symm
  | true, false => finTwoEquiv
  | true, true => Equiv.refl (Fin 2)

def badSymmetrizationData :
    LabelledUnitCopiesRaw Bool Bool ToyUnitCopy ToySymmRel where
  embed := toyUnitEmbed
  symmetrize := fun {i j} _ ↦ badUnitSymmetrize i j
  readout := toyUnitReadout

theorem bad_symmetrization_still_unit_diagonal :
    UnitDiagonal badSymmetrizationData := by
  intro u j
  rfl

theorem bad_symmetrization_fails_reference_compatibility :
    ¬ SymmetrizationRespectsReferenceUnit badSymmetrizationData := by
  intro h
  have hf := h (i := false) (j := false) trivial false
  change (!false : Bool) = false at hf
  simpa using hf

theorem bad_symmetrization_fails_self_identity :
    ¬ SymmetrizationSelfIdentity badSymmetrizationData := by
  intro h
  have hf := h false trivial
  have hpoint := congrArg
    (fun e : ToyUnitCopy false ≃ ToyUnitCopy false ↦ e false) hf
  change (!false : Bool) = false at hpoint
  simpa using hpoint

def collapsedUnitEmbed : (j : Bool) → Bool → ToyUnitCopy j
  | false => fun _ ↦ false
  | true => fun _ ↦ finTwoEquiv.symm false

def collapsedUnitReadout (u : Bool) (j : Bool) : ToyUnitCopy j :=
  collapsedUnitEmbed j u

def collapsedUnitData :
    LabelledUnitCopiesRaw Bool Bool ToyUnitCopy ToySymmRel where
  embed := collapsedUnitEmbed
  symmetrize := fun {i j} _ ↦ toyUnitSymmetrize i j
  readout := collapsedUnitReadout

theorem collapsed_data_is_unit_diagonal : UnitDiagonal collapsedUnitData := by
  intro u j
  rfl

theorem collapsed_data_has_reference_symmetrization :
    SymmetrizationRespectsReferenceUnit collapsedUnitData := by
  intro i j hij u
  cases i <;> cases j <;> cases u <;> rfl

theorem collapsed_data_readout_not_faithful :
    ¬ UnitReadoutFaithful collapsedUnitData := by
  intro h
  apply Bool.false_ne_true
  apply h
  funext j
  cases j <;> rfl

theorem unit_diagonal_and_faithfulness_are_independent :
    (UnitDiagonal collapsedUnitData ∧
      ¬ UnitReadoutFaithful collapsedUnitData) ∧
    (UnitReadoutFaithful flippedReadoutData ∧
      ¬ UnitDiagonal flippedReadoutData) :=
  ⟨⟨collapsed_data_is_unit_diagonal,
      collapsed_data_readout_not_faithful⟩,
    ⟨flipped_readout_is_faithful,
      flipped_readout_not_unit_diagonal⟩⟩

end CitedLV.ThetaLink
