import Cor312LogVolume.theorem311.CompletePolySplittingTransport

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.RetainedMonoidSplittingAdapter

open CitedLV.ThetaLink
open CitedLV.Theorem311.ProcessionPolyFunctorBoundary
open CitedLV.Theorem311.CompletePolyComponentAction
open CitedLV.Theorem311.CompletePolySplittingTransport

universe uObj uG uO uBad uLabel

variable
  {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
  (F : ProcessionPolyFunctorRaw G)
  (Bad : Type uBad) (Label : Type uLabel)

abbrev Psi (B : Type uBad) (p : Obj) (_ : B) := (F.side p).O

abbrev Packet (B : Type uBad) (L : Type uLabel) (p : Obj) (_ : B) (_ : L) :=
  (F.side p).O

def carrierAction :
    CarrierActionRaw F (Psi F Bad) (Packet F Bad Label) where
  psiEquiv := fun e _ => e.monoidEquiv.toMulEquiv
  packetEquiv := fun e _ _ => e.monoidEquiv.toMulEquiv.toEquiv

theorem carrierIdentityLaw :
    CarrierIdentityLaw F (Psi F Bad) (Packet F Bad Label) (carrierAction F Bad Label) := by
  constructor
  · intro p v
    ext x
    rfl
  · intro p v j
    ext x
    rfl

theorem carrierCompositionLaw :
    CarrierCompositionLaw F (Psi F Bad) (Packet F Bad Label) (carrierAction F Bad Label) := by
  constructor
  · intro p q r e f v
    ext x
    rfl
  · intro p q r e f v j
    ext x
    rfl

def action :
    CompletePolyActionRaw F
      (CompletePolySplittingTransport.Output (Psi F Bad) (Packet F Bad Label)) :=
  polyAction F (Psi F Bad) (Packet F Bad Label) (carrierAction F Bad Label)

theorem actionPreservesIdentity :
    ActionPreservesIdentity (action F Bad Label) :=
  action_preservesIdentity F (Psi F Bad) (Packet F Bad Label)
    (carrierAction F Bad Label) (carrierIdentityLaw F Bad Label)

theorem actionPreservesComposition :
    ActionPreservesComposition (action F Bad Label) :=
  action_preservesComposition F (Psi F Bad) (Packet F Bad Label)
    (carrierAction F Bad Label) (carrierCompositionLaw F Bad Label)

theorem actionInjective :
    EveryPolyTransportInjective (action F Bad Label) :=
  CompletePolySplittingTransport.everyPolyTransportInjective
    F (Psi F Bad) (Packet F Bad Label) (carrierAction F Bad Label)

def SourceBuildNaturality
    (build : (p : Obj) ->
      CompletePolySplittingTransport.Output (Psi F Bad) (Packet F Bad Label) p) : Prop :=
  CompletePolySplittingTransport.BuildNaturality
    F (Psi F Bad) (Packet F Bad Label) (carrierAction F Bad Label) build

theorem componentCoherent_of_buildNaturality
    (build : (p : Obj) ->
      CompletePolySplittingTransport.Output (Psi F Bad) (Packet F Bad Label) p)
    (hFid : PreservesIdentity F)
    (hFcomp : PreservesComposition F)
    (hBuild : SourceBuildNaturality F Bad Label build) :
    ComponentCoherent F (action F Bad Label) build := by
  exact
    ⟨hFid, hFcomp,
      actionPreservesIdentity F Bad Label,
      actionPreservesComposition F Bad Label,
      actionInjective F Bad Label,
      (CompletePolySplittingTransport.buildNaturality_iff
        F (Psi F Bad) (Packet F Bad Label) (carrierAction F Bad Label) build).1 hBuild⟩

end CitedLV.Theorem311.RetainedMonoidSplittingAdapter
end
