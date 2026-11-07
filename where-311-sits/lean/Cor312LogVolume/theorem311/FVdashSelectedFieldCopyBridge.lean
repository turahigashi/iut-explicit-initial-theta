import Cor312LogVolume.theorem311.StructuredFieldCopyCarrierBridge

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.FVdashSelectedFieldCopyBridge

open CitedLV.ThetaLink
open CitedLV.Theorem311.ProcessionPolyFunctorBoundary
open CitedLV.Theorem311.CompletePolyFieldCopyTransport
open CitedLV.Theorem311.StructuredFieldCopyCarrierBridge

universe
  uObj uG uO uV uGlobal uPrime uLocal uGLoc uLRlf
  uGIso uLIso uLabel uPlace uCopy

variable
  {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
  (F : ProcessionPolyFunctorRaw G)
  {V : Type uV} {Global : Type uGlobal}
  {Prime : Global -> Type uPrime}
  {Local : V -> Type uLocal}
  {GlobalLoc : (C : Global) -> Prime C -> Type uGLoc}
  {LocalRlf : (v : V) -> Local v -> Type uLRlf}
  [forall C p, TopologicalSpace (GlobalLoc C p)]
  [forall C p, CommMonoid (GlobalLoc C p)]
  [forall v L, TopologicalSpace (LocalRlf v L)]
  [forall v L, CommMonoid (LocalRlf v L)]
  (GlobalIso : Global -> Global -> Type uGIso)
  (LocalIso : (v : V) -> Local v -> Local v -> Type uLIso)
  (Strip : Obj ->
    FVdashPrimeStripRaw V Global Prime Local GlobalLoc LocalRlf)
  {Label : Type uLabel} {Place : Type uPlace}
  (Copy : Obj -> Label -> Type uCopy)
  (sourcePlace : Place -> V)
  (P : PolyToFVdashRaw F GlobalIso LocalIso Strip)

abbrev SelectedLocalPacket
    (p : Obj) (_j : Label) (v : Place) : Type uLRlf :=
  LocalRlf (sourcePlace v)
    ((Strip p).localObj (sourcePlace v))

structure GlobalCopyActionRaw where
  copyEquiv :
    {p q : Obj} ->
      AdmissibleIso (F.side p) (F.side q) ->
      (j : Label) -> Copy p j ≃ Copy q j

def carrierAction
    (C : GlobalCopyActionRaw F Copy) :
    CarrierActionRaw F Copy
      (SelectedLocalPacket Strip sourcePlace) where
  copyEquiv := C.copyEquiv
  localEquiv := fun e _j v =>
    ((P.map e).localRlfIso (sourcePlace v)).toMulEquiv.toEquiv

def GlobalCopyIdentityLaw
    (C : GlobalCopyActionRaw F Copy) : Prop :=
  forall p j,
    C.copyEquiv (AdmissibleIso.refl (F.side p)) j = Equiv.refl _

def GlobalCopyCompositionLaw
    (C : GlobalCopyActionRaw F Copy) : Prop :=
  forall {p q r}
    (e : AdmissibleIso (F.side p) (F.side q))
    (f : AdmissibleIso (F.side q) (F.side r)) j,
    C.copyEquiv (e.trans f) j =
      (C.copyEquiv e j).trans (C.copyEquiv f j)

def LocalRlfIdentityLaw : Prop :=
  forall p v,
    (P.map (AdmissibleIso.refl (F.side p))).localRlfIso v =
      ContinuousMulEquiv.refl _

def LocalRlfCompositionLaw : Prop :=
  forall {p q r}
    (e : AdmissibleIso (F.side p) (F.side q))
    (f : AdmissibleIso (F.side q) (F.side r)) v,
    (P.map (e.trans f)).localRlfIso v =
      ((P.map e).localRlfIso v).trans ((P.map f).localRlfIso v)

theorem carrierIdentityLaw
    (C : GlobalCopyActionRaw F Copy)
    (hCopy : GlobalCopyIdentityLaw F Copy C)
    (hLocal : LocalRlfIdentityLaw F GlobalIso LocalIso Strip P) :
    CarrierIdentityLaw F Copy
      (SelectedLocalPacket Strip sourcePlace)
      (carrierAction F GlobalIso LocalIso Strip Copy sourcePlace P C) := by
  constructor
  · exact hCopy
  · intro p j v
    have h := hLocal p (sourcePlace v)
    ext x
    exact congrArg (fun e => e x) h

theorem carrierCompositionLaw
    (C : GlobalCopyActionRaw F Copy)
    (hCopy : GlobalCopyCompositionLaw F Copy C)
    (hLocal : LocalRlfCompositionLaw F GlobalIso LocalIso Strip P) :
    CarrierCompositionLaw F Copy
      (SelectedLocalPacket Strip sourcePlace)
      (carrierAction F GlobalIso LocalIso Strip Copy sourcePlace P C) := by
  constructor
  · exact hCopy
  · intro p q r e f j v
    have h := hLocal e f (sourcePlace v)
    ext x
    exact congrArg (fun g => g x) h

theorem componentCoherent
    (C : GlobalCopyActionRaw F Copy)
    (build : (p : Obj) ->
      CompletePolyFieldCopyTransport.Output
        Copy (SelectedLocalPacket Strip sourcePlace) p)
    (hFid : ProcessionPolyFunctorBoundary.PreservesIdentity F)
    (hFcomp : ProcessionPolyFunctorBoundary.PreservesComposition F)
    (hCopyId : GlobalCopyIdentityLaw F Copy C)
    (hCopyComp : GlobalCopyCompositionLaw F Copy C)
    (hLocalId : LocalRlfIdentityLaw F GlobalIso LocalIso Strip P)
    (hLocalComp : LocalRlfCompositionLaw F GlobalIso LocalIso Strip P)
    (hSquare : EmbedNaturalitySquare F Copy
      (SelectedLocalPacket Strip sourcePlace)
      (carrierAction F GlobalIso LocalIso Strip Copy sourcePlace P C)
      build) :
    CompletePolyComponentAction.ComponentCoherent F
      (CompletePolyFieldCopyTransport.polyAction F Copy
        (SelectedLocalPacket Strip sourcePlace)
        (carrierAction F GlobalIso LocalIso Strip Copy sourcePlace P C))
      build := by
  exact CompletePolyFieldCopyTransport.componentCoherent_of_carriers
    F Copy (SelectedLocalPacket Strip sourcePlace)
    (carrierAction F GlobalIso LocalIso Strip Copy sourcePlace P C)
    build hFid hFcomp
    (carrierIdentityLaw F GlobalIso LocalIso Strip Copy sourcePlace P C hCopyId hLocalId)
    (carrierCompositionLaw F GlobalIso LocalIso Strip Copy sourcePlace P C hCopyComp hLocalComp)
    hSquare

end CitedLV.Theorem311.FVdashSelectedFieldCopyBridge
end
