import Cor312LogVolume.theorem311.CompletePolyFieldCopyTransport
import Cor312LogVolume.thetalink.FVdashPrimeStripSkeleton

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.StructuredFieldCopyCarrierBridge

open CitedLV.ThetaLink
open CitedLV.Theorem311.ProcessionPolyFunctorBoundary
open CitedLV.Theorem311.CompletePolyFieldCopyTransport

universe
  uObj uG uO uV uGlobal uPrime uLocal uGLoc uLRlf
  uGIso uLIso uLabel uPlace uCopy uPacket

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
  (LocalPacket : Obj -> Label -> Place -> Type uPacket)

structure PolyToFVdashRaw where
  map :
    {p q : Obj} ->
      AdmissibleIso (F.side p) (F.side q) ->
        FVdashIsoRaw (Strip p) (Strip q) GlobalIso LocalIso

structure StructuredFieldCopyCarrierBridge
    (P : PolyToFVdashRaw F GlobalIso LocalIso Strip) where
  copyEquiv :
    {p q : Obj} ->
      (e : AdmissibleIso (F.side p) (F.side q)) ->
      (j : Label) ->
        Copy p j ≃ Copy q j
  localEquiv :
    {p q : Obj} ->
      (e : AdmissibleIso (F.side p) (F.side q)) ->
      (j : Label) -> (v : Place) ->
        LocalPacket p j v ≃ LocalPacket q j v

def toCarrierAction
    (P : PolyToFVdashRaw F GlobalIso LocalIso Strip)
    (B : StructuredFieldCopyCarrierBridge
      F GlobalIso LocalIso Strip Copy LocalPacket P) :
    CarrierActionRaw F Copy LocalPacket where
  copyEquiv := B.copyEquiv
  localEquiv := B.localEquiv

def PreservesIdentity
    (P : PolyToFVdashRaw F GlobalIso LocalIso Strip)
    (B : StructuredFieldCopyCarrierBridge
      F GlobalIso LocalIso Strip Copy LocalPacket P) : Prop :=
  CarrierIdentityLaw F Copy LocalPacket
    (toCarrierAction F GlobalIso LocalIso Strip Copy LocalPacket P B)

def PreservesComposition
    (P : PolyToFVdashRaw F GlobalIso LocalIso Strip)
    (B : StructuredFieldCopyCarrierBridge
      F GlobalIso LocalIso Strip Copy LocalPacket P) : Prop :=
  CarrierCompositionLaw F Copy LocalPacket
    (toCarrierAction F GlobalIso LocalIso Strip Copy LocalPacket P B)

def InclusionNaturality
    (P : PolyToFVdashRaw F GlobalIso LocalIso Strip)
    (B : StructuredFieldCopyCarrierBridge
      F GlobalIso LocalIso Strip Copy LocalPacket P)
    (build : (p : Obj) ->
      CompletePolyFieldCopyTransport.Output Copy LocalPacket p) : Prop :=
  EmbedNaturalitySquare F Copy LocalPacket
    (toCarrierAction F GlobalIso LocalIso Strip Copy LocalPacket P B)
    build

theorem componentCoherent
    (P : PolyToFVdashRaw F GlobalIso LocalIso Strip)
    (B : StructuredFieldCopyCarrierBridge
      F GlobalIso LocalIso Strip Copy LocalPacket P)
    (build : (p : Obj) ->
      CompletePolyFieldCopyTransport.Output Copy LocalPacket p)
    (hFid : ProcessionPolyFunctorBoundary.PreservesIdentity F)
    (hFcomp : ProcessionPolyFunctorBoundary.PreservesComposition F)
    (hId : PreservesIdentity F GlobalIso LocalIso Strip Copy LocalPacket P B)
    (hComp : PreservesComposition F GlobalIso LocalIso Strip Copy LocalPacket P B)
    (hSquare : InclusionNaturality F GlobalIso LocalIso Strip
      Copy LocalPacket P B build) :
    CompletePolyComponentAction.ComponentCoherent F
      (CompletePolyFieldCopyTransport.polyAction
        F Copy LocalPacket
        (toCarrierAction F GlobalIso LocalIso Strip Copy LocalPacket P B))
      build := by
  exact CompletePolyFieldCopyTransport.componentCoherent_of_carriers
    F Copy LocalPacket
    (toCarrierAction F GlobalIso LocalIso Strip Copy LocalPacket P B)
    build hFid hFcomp hId hComp hSquare

structure LocalRlfSelection where
  sourcePlace : Place -> V
  sourceLabelObject :
    (p : Obj) -> (j : Label) -> (v : Place) ->
      Local (sourcePlace v)

abbrev SelectedLocalRlf
    (S : LocalRlfSelection
      (Obj := Obj) (V := V) (Local := Local)
      (Label := Label) (Place := Place))
    (p : Obj) (j : Label) (v : Place) :=
  LocalRlf (S.sourcePlace v) (S.sourceLabelObject p j v)

def SelectionMatchesStrip
    (S : LocalRlfSelection
      (Obj := Obj) (V := V) (Local := Local)
      (Label := Label) (Place := Place)) : Prop :=
  forall p j v,
    S.sourceLabelObject p j v = (Strip p).localObj (S.sourcePlace v)

end CitedLV.Theorem311.StructuredFieldCopyCarrierBridge
end
