import Cor312LogVolume.theorem311.CompletePolyComponentAction
import Cor312LogVolume.theorem311.LabeledGlobalNumberFieldInclusion

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.CompletePolyFieldCopyTransport

theorem inclusionExt {L : Type*} {P : Type*} {Cp : L -> Type*}
    {LP : L -> P -> Type*}
    {a b : LabeledNumberFieldGlobalInclusionRaw L P Cp LP}
    (h : a.embed = b.embed) : a = b := by
  cases a
  cases b
  simp_all

open CitedLV.ThetaLink
open CitedLV.Theorem311.ProcessionPolyFunctorBoundary
open CitedLV.Theorem311.CompletePolyComponentAction

universe uObj uG uO uLabel uPlace uCopy uLocal

variable
  {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
  (F : ProcessionPolyFunctorRaw G)
  {Label : Type uLabel} {Place : Type uPlace}
  (Copy : Obj -> Label -> Type uCopy)
  (LocalPacket : Obj -> Label -> Place -> Type uLocal)

structure CarrierActionRaw where
  copyEquiv :
    {p q : Obj} ->
      AdmissibleIso (F.side p) (F.side q) ->
        (j : Label) -> Copy p j ≃ Copy q j
  localEquiv :
    {p q : Obj} ->
      AdmissibleIso (F.side p) (F.side q) ->
        (j : Label) -> (v : Place) ->
          LocalPacket p j v ≃ LocalPacket q j v

abbrev Output (p : Obj) :=
  LabeledNumberFieldGlobalInclusionRaw
    Label Place (Copy p) (LocalPacket p)

def transport
    (C : CarrierActionRaw F Copy LocalPacket)
    {p q : Obj}
    (e : AdmissibleIso (F.side p) (F.side q))
    (R : Output Copy LocalPacket p) :
    Output Copy LocalPacket q where
  embed := fun j x v =>
    C.localEquiv e j v
      (R.embed j ((C.copyEquiv e j).symm x) v)

def polyAction
    (C : CarrierActionRaw F Copy LocalPacket) :
    CompletePolyActionRaw F (Output Copy LocalPacket) where
  map := fun e => transport F Copy LocalPacket C e

def CarrierIdentityLaw
    (C : CarrierActionRaw F Copy LocalPacket) : Prop :=
  (forall p j,
      C.copyEquiv (AdmissibleIso.refl (F.side p)) j = Equiv.refl _) /\
  (forall p j v,
      C.localEquiv (AdmissibleIso.refl (F.side p)) j v = Equiv.refl _)

def CarrierCompositionLaw
    (C : CarrierActionRaw F Copy LocalPacket) : Prop :=
  (forall {p q r}
      (e : AdmissibleIso (F.side p) (F.side q))
      (f : AdmissibleIso (F.side q) (F.side r)) j,
      C.copyEquiv (e.trans f) j =
        (C.copyEquiv e j).trans (C.copyEquiv f j)) /\
  (forall {p q r}
      (e : AdmissibleIso (F.side p) (F.side q))
      (f : AdmissibleIso (F.side q) (F.side r)) j v,
      C.localEquiv (e.trans f) j v =
        (C.localEquiv e j v).trans (C.localEquiv f j v))

theorem action_preservesIdentity
    (C : CarrierActionRaw F Copy LocalPacket)
    (h : CarrierIdentityLaw F Copy LocalPacket C) :
    ActionPreservesIdentity (polyAction F Copy LocalPacket C) := by
  intro p R
  rcases h with ⟨hCopy, hLocal⟩
  cases R with
  | mk embed =>
      apply inclusionExt
      funext j x v
      simp [polyAction, transport, hCopy p j, hLocal p j v]

theorem action_preservesComposition
    (C : CarrierActionRaw F Copy LocalPacket)
    (h : CarrierCompositionLaw F Copy LocalPacket C) :
    ActionPreservesComposition (polyAction F Copy LocalPacket C) := by
  intro p q r e f R
  rcases h with ⟨hCopy, hLocal⟩
  cases R with
  | mk embed =>
      apply inclusionExt
      funext j x v
      simp [polyAction, transport, hCopy e f j, hLocal e f j v]

theorem everyPolyTransportInjective
    (C : CarrierActionRaw F Copy LocalPacket) :
    EveryPolyTransportInjective (polyAction F Copy LocalPacket C) := by
  intro p q e R S hRS
  apply inclusionExt
  funext j x v
  have h :=
    congrArg
      (fun T : Output Copy LocalPacket q =>
        T.embed j (C.copyEquiv e j x) v) hRS

  simp only [polyAction, transport, Equiv.symm_apply_apply,
    MulEquiv.symm_apply_apply, ContinuousMulEquiv.symm_apply_apply] at h
  exact (C.localEquiv e j v).injective h

def EmbedNaturalitySquare
    (C : CarrierActionRaw F Copy LocalPacket)
    (build : (p : Obj) -> Output Copy LocalPacket p) : Prop :=
  forall {p q}
    (e : G.Hom p q) (j : Label) (x : Copy p j) (v : Place),
    C.localEquiv (F.map e) j v ((build p).embed j x v) =
      (build q).embed j (C.copyEquiv (F.map e) j x) v

theorem buildNatural_of_embedSquare
    (C : CarrierActionRaw F Copy LocalPacket)
    (build : (p : Obj) -> Output Copy LocalPacket p)
    (h : EmbedNaturalitySquare F Copy LocalPacket C build) :
    BuildNatural (polyAction F Copy LocalPacket C) build := by
  intro p q e
  apply inclusionExt
  funext j x v
  change
    C.localEquiv (F.map e) j v
      ((build p).embed j ((C.copyEquiv (F.map e) j).symm x) v) =
      (build q).embed j x v
  have hs :=
    h e j ((C.copyEquiv (F.map e) j).symm x) v
  rw [(C.copyEquiv (F.map e) j).apply_symm_apply] at hs
  exact hs

theorem componentCoherent_of_carriers
    (C : CarrierActionRaw F Copy LocalPacket)
    (build : (p : Obj) -> Output Copy LocalPacket p)
    (hFid : PreservesIdentity F)
    (hFcomp : PreservesComposition F)
    (hId : CarrierIdentityLaw F Copy LocalPacket C)
    (hComp : CarrierCompositionLaw F Copy LocalPacket C)
    (hSquare : EmbedNaturalitySquare F Copy LocalPacket C build) :
    ComponentCoherent F (polyAction F Copy LocalPacket C) build := by
  exact
    ⟨hFid, hFcomp,
      action_preservesIdentity F Copy LocalPacket C hId,
      action_preservesComposition F Copy LocalPacket C hComp,
      everyPolyTransportInjective F Copy LocalPacket C,
      buildNatural_of_embedSquare F Copy LocalPacket C build hSquare⟩

end CitedLV.Theorem311.CompletePolyFieldCopyTransport
end
