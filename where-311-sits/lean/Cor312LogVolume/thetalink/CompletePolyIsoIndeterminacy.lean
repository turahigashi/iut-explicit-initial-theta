import Cor312LogVolume.thetalink.NonarchInd2Action
import Cor312LogVolume.thetalink.Ind1ProcessionAction

namespace CitedLV.ThetaLink

noncomputable section

universe uG uO uG' uO' uG'' uO'' u v

theorem completePolyIso_trans_mem
    {D : RetainedThetaSide.{uG, uO}}
    {E : RetainedThetaSide.{uG', uO'}}
    {F : RetainedThetaSide.{uG'', uO''}}
    (e : AdmissibleIso D E) (f : AdmissibleIso E F)
    (_he : e ∈ CompletePolyIso D E)
    (_hf : f ∈ CompletePolyIso E F) :
    e.trans f ∈ CompletePolyIso D F :=
  mem_completePolyIso _

theorem completePolyIso_symm_mem
    {D : RetainedThetaSide.{uG, uO}}
    {E : RetainedThetaSide.{uG', uO'}}
    (e : AdmissibleIso D E)
    (_he : e ∈ CompletePolyIso D E) :
    e.symm ∈ CompletePolyIso E D :=
  mem_completePolyIso _

theorem completePolyIso_nonempty_iff
    {D : RetainedThetaSide.{uG, uO}}
    {E : RetainedThetaSide.{uG', uO'}} :
    (CompletePolyIso D E).Nonempty ↔ Nonempty (AdmissibleIso D E) := by
  constructor
  · rintro ⟨e, _he⟩
    exact ⟨e⟩
  · rintro ⟨e⟩
    exact ⟨e, mem_completePolyIso e⟩

def FixesRetainedGroup
    (D : RetainedThetaSide.{uG, uO}) (e : AdmissibleIso D D) : Prop :=
  e.groupEquiv = ContinuousMulEquiv.refl D.G

def AdmissibleIso.toNonarchLocalIsm
    (D : RetainedThetaSide.{uG, uO})
    (e : AdmissibleIso D D) (hG : FixesRetainedGroup D e) :
    NonarchLocalIsm D := by
  refine ⟨e.monoidEquiv.toMulEquiv, ?_⟩
  refine ⟨e.monoidEquiv.continuous_toFun,
    e.monoidEquiv.continuous_invFun, ?_, ?_⟩
  · intro g x
    have h := e.equivariant g x
    rw [hG] at h
    simpa using h
  · intro H x
    have h := e.preservesLattices H x
    rw [hG] at h
    simpa using h

theorem localIsm_toAdmissible_toLocal
    (D : RetainedThetaSide.{uG, uO}) (e : NonarchLocalIsm D) :
    AdmissibleIso.toNonarchLocalIsm D
      (NonarchLocalIsm.toAdmissible D e) rfl = e := by
  apply Subtype.ext
  rfl

theorem admissible_toLocal_toAdmissible_monoid_apply
    (D : RetainedThetaSide.{uG, uO}) (e : AdmissibleIso D D)
    (hG : FixesRetainedGroup D e) (x : D.O) :
    (NonarchLocalIsm.toAdmissible D
      (AdmissibleIso.toNonarchLocalIsm D e hG)).monoidEquiv x =
        e.monoidEquiv x :=
  rfl

def FixedGAdmissible (D : RetainedThetaSide.{uG, uO}) :=
  {e : AdmissibleIso D D //
    e.groupEquiv = ContinuousMulEquiv.refl D.G}

def FixedGAdmissible.toNonarchLocalIsm
    {D : RetainedThetaSide.{uG, uO}} (e : FixedGAdmissible D) :
    NonarchLocalIsm D :=
  AdmissibleIso.toNonarchLocalIsm D e.1 e.2

def NonarchLocalIsm.toFixedGAdmissible
    (D : RetainedThetaSide.{uG, uO}) (e : NonarchLocalIsm D) :
    FixedGAdmissible D :=
  ⟨NonarchLocalIsm.toAdmissible D e, rfl⟩

@[simp] theorem local_fixedG_local
    (D : RetainedThetaSide.{uG, uO}) (e : NonarchLocalIsm D) :
    (NonarchLocalIsm.toFixedGAdmissible D e).toNonarchLocalIsm = e := by
  apply Subtype.ext
  rfl

@[simp] theorem fixedG_local_fixedG
    (D : RetainedThetaSide.{uG, uO}) (e : FixedGAdmissible D) :
    NonarchLocalIsm.toFixedGAdmissible D e.toNonarchLocalIsm = e := by
  rcases e with ⟨⟨g, o, heq, hlat⟩, hg⟩
  dsimp [FixedGAdmissible, FixedGAdmissible.toNonarchLocalIsm,
    AdmissibleIso.toNonarchLocalIsm] at hg ⊢
  subst g
  rfl

def fixedGAdmissibleEquivNonarchLocalIsm
    (D : RetainedThetaSide.{uG, uO}) :
    FixedGAdmissible D ≃ NonarchLocalIsm D where
  toFun := FixedGAdmissible.toNonarchLocalIsm
  invFun := NonarchLocalIsm.toFixedGAdmissible D
  left_inv := fixedG_local_fixedG D
  right_inv := local_fixedG_local D

def fixedGAdmissibleFamilyToIndependent
    {I : Type*} (D : I → RetainedThetaSide.{uG, uO})
    (a : (i : I) → AdmissibleIso (D i) (D i))
    (hG : ∀ i, FixesRetainedGroup (D i) (a i)) :
    IndependentNonarchIsm D :=
  fun i ↦ AdmissibleIso.toNonarchLocalIsm (D i) (a i) (hG i)

theorem fixedGAdmissibleFamily_action_apply
    {I : Type*} (D : I → RetainedThetaSide.{uG, uO})
    (a : (i : I) → AdmissibleIso (D i) (D i))
    (hG : ∀ i, FixesRetainedGroup (D i) (a i))
    (x : NonarchComponentPacket D) (i : I) :
    (fixedGAdmissibleFamilyToIndependent D a hG • x) i =
      (a i).monoidEquiv (x i) :=
  rfl

theorem c3SquareSwapAll_not_fixesRetainedGroup :
    ¬ FixesRetainedGroup c3SquareAll c3SquareSwapAll := by
  intro h
  have happ := congrArg
    (fun e : C3Square ≃ₜ* C3Square ↦ e c3AxisWitness) h
  have hfirst := congrArg Prod.fst happ
  exact c3Generator_ne_one (by
    simpa [FixesRetainedGroup, c3SquareSwapAll, c3SquareSwap,
      c3AxisWitness] using hfirst.symm)

theorem complete_member_need_not_be_nonarchInd2 :
    c3SquareSwapAll ∈ CompletePolyIso c3SquareAll c3SquareAll ∧
      ¬ FixesRetainedGroup c3SquareAll c3SquareSwapAll :=
  ⟨c3SquareSwap_passes_universal_lattices,
    c3SquareSwapAll_not_fixesRetainedGroup⟩

theorem complete_all_to_marked_empty :
    ¬ (CompletePolyIso c3SquareAll c3SquareMarked).Nonempty := by
  rintro ⟨e, _he⟩
  let y : C3Square := c3SquareSwap c3AxisWitness
  let x : C3Square := e.monoidEquiv.symm y
  have hx : x ∈ c3SquareAll.datum.lattice
      (⊤ : OpenSubgroup c3SquareAll.G) := by
    simp [c3SquareAll]
  have hy := (e.preservesLattices
    (⊤ : OpenSubgroup c3SquareAll.G) x).mp hx
  have hexy : e.monoidEquiv x = y := e.monoidEquiv.apply_symm_apply y
  apply c3SquareSwap_moves_axis_witness
  simpa [c3SquareMarked, hexy, y] using hy

theorem fixedG_extraction_changes_toy_target :
    let a : (i : ToyNonarchCoordinate) →
        AdmissibleIso (toyNonarchSides i) (toyNonarchSides i) :=
      fun i ↦ NonarchLocalIsm.toAdmissible
        (toyNonarchSides i) (toySingleSwap i)
    let hG : ∀ i, FixesRetainedGroup (toyNonarchSides i) (a i) := by
      intro i
      rfl
    (fixedGAdmissibleFamilyToIndependent toyNonarchSides a hG •
      toyAxisPacket) toyTargetCoordinate ≠
        toyAxisPacket toyTargetCoordinate := by
  dsimp only
  simpa [fixedGAdmissibleFamilyToIndependent,
    AdmissibleIso.toNonarchLocalIsm,
    NonarchLocalIsm.toAdmissible] using toySingleSwap_changes_target

abbrev Ind1RawLift
    {Label : Type u}
    (S : ProcessionShape Label) (Strip : Type v)
    (D : RetainedThetaSide.{uG, uO}) :=
  ProcessionAutomorphism S Strip → AdmissibleIso D D

def Ind1LiftPreservesIdentity
    {Label : Type u} (S : ProcessionShape Label) (Strip : Type v)
    (D : RetainedThetaSide.{uG, uO})
    (L : Ind1RawLift S Strip D) : Prop :=
  L (ProcessionAutomorphism.refl S Strip) = AdmissibleIso.refl D

def Ind1LiftPreservesComposition
    {Label : Type u} (S : ProcessionShape Label) (Strip : Type v)
    (D : RetainedThetaSide.{uG, uO})
    (L : Ind1RawLift S Strip D) : Prop :=
  ∀ A B, L (A.trans B) = (L A).trans (L B)

def Ind1LiftDetectsAt
    {Label : Type u} {S : ProcessionShape Label} (Strip : Type v)
    (D : RetainedThetaSide.{uG, uO})
    (L : Ind1RawLift S Strip D)
    (A : ProcessionAutomorphism S Strip) : Prop :=
  L A ≠ AdmissibleIso.refl D

def constantIdentityInd1Lift
    {Label : Type u} (S : ProcessionShape Label) (Strip : Type v)
    (D : RetainedThetaSide.{uG, uO}) :
    Ind1RawLift S Strip D :=
  fun _ ↦ AdmissibleIso.refl D

theorem constantIdentityInd1Lift_preservesIdentity
    {Label : Type u} (S : ProcessionShape Label) (Strip : Type v)
    (D : RetainedThetaSide.{uG, uO}) :
    Ind1LiftPreservesIdentity S Strip D
      (constantIdentityInd1Lift S Strip D) :=
  rfl

theorem constantIdentityInd1Lift_preservesComposition
    {Label : Type u} (S : ProcessionShape Label) (Strip : Type v)
    (D : RetainedThetaSide.{uG, uO}) :
    Ind1LiftPreservesComposition S Strip D
      (constantIdentityInd1Lift S Strip D) := by
  intro A B
  rfl

theorem constantFunctorLaws_do_not_generate_ind1 :
    processionEquiv boolLabelInd1 boolProcession ≠ boolProcession ∧
      Ind1LiftPreservesIdentity boolProcessionShape Bool c3TrivialAll
        (constantIdentityInd1Lift boolProcessionShape Bool c3TrivialAll) ∧
      Ind1LiftPreservesComposition boolProcessionShape Bool c3TrivialAll
        (constantIdentityInd1Lift boolProcessionShape Bool c3TrivialAll) ∧
      ¬ Ind1LiftDetectsAt Bool c3TrivialAll
        (constantIdentityInd1Lift boolProcessionShape Bool c3TrivialAll)
        boolLabelInd1 := by
  refine ⟨boolLabelInd1_moves_procession,
    constantIdentityInd1Lift_preservesIdentity _ _ _,
    constantIdentityInd1Lift_preservesComposition _ _ _, ?_⟩
  simp [Ind1LiftDetectsAt, constantIdentityInd1Lift]

def constantSwapInd1Lift :
    Ind1RawLift boolProcessionShape Bool c3TrivialAll :=
  fun _ ↦ NonarchLocalIsm.toAdmissible c3TrivialAll c3SwapNonarchIsm

theorem constantInd1Lifts_land_in_complete :
    (∀ A, constantIdentityInd1Lift boolProcessionShape Bool c3TrivialAll A ∈
      CompletePolyIso c3TrivialAll c3TrivialAll) ∧
    (∀ A, constantSwapInd1Lift A ∈
      CompletePolyIso c3TrivialAll c3TrivialAll) := by
  constructor <;> intro A <;> exact mem_completePolyIso _

theorem constantIdentityAndSwapInd1Lifts_ne :
    constantIdentityInd1Lift boolProcessionShape Bool c3TrivialAll ≠
      constantSwapInd1Lift := by
  intro h
  have happ := congrArg
    (fun L : Ind1RawLift boolProcessionShape Bool c3TrivialAll ↦
      (L boolLabelInd1).monoidEquiv c3AxisWitness) h
  have hfst := congrArg Prod.fst happ
  exact c3Generator_ne_one (by
    simpa [constantIdentityInd1Lift, constantSwapInd1Lift,
      NonarchLocalIsm.toAdmissible, c3SwapNonarchIsm,
      AdmissibleIso.refl, c3SquareSwap, c3AxisWitness] using hfst)

end

end CitedLV.ThetaLink
