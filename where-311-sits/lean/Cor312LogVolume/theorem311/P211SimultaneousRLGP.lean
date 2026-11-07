import Cor312LogVolume.theorem311.RLGPSimultaneousBuild
import Cor312LogVolume.theorem311.P211InnerComponentBCoherence
import Cor312LogVolume.theorem311.P211GaloisFieldCopyAction
import Cor312LogVolume.theorem311.P211PacketSystem

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211SimultaneousRLGP

open CitedLV.Theorem311
open CitedLV.Theorem311.InnerArithmeticArrowTransport
open CitedLV.Theorem311.ArithmeticCanonicalSplittingCoherence
open CitedLV.Theorem311.CompletePolyComponentAction
open CitedLV.Theorem311.RLGPSimultaneousBuild
open Src.CoreLayer.LanaStep6.FiniteKummerRatio

abbrev G : ProcessionIsoRaw Unit :=
  galoisProcessionIsoRaw (K := ℚ_[211])

abbrev F := P211GaloisFieldCopyAction.F

variable (Bad : Type) (Label : Type)

abbrev PacketFam (_p : Unit) := P211Packet.p211PacketSystem.Regions

def packetAlgorithm : ProcessionAlgorithmRaw G PacketFam where
  build := fun _ => P211Packet.p211QRegion
  transport := fun _ x => x

theorem packet_identity : TransportIdentityLaw packetAlgorithm :=
  fun _ _ => rfl

theorem packet_composition : TransportCompositionLaw packetAlgorithm :=
  fun _ _ _ => rfl

theorem packet_construction : ConstructionCommutes packetAlgorithm :=
  fun _ => rfl

theorem packet_injective : EveryTransportInjective packetAlgorithm :=
  fun _ => Function.injective_id

theorem packet_nontrivial : EveryPacketFiberNontrivial PacketFam := by
  intro p
  refine ⟨fun _ _ => (∅ : Set ℚ_[211]), fun _ _ => (Set.univ : Set ℚ_[211]), ?_⟩
  intro h
  have h1 := congrFun (congrFun h ()) (0 : Fin (P211Packet.p211PacketSystem.lstar + 1))
  have h2 : (0 : ℚ_[211]) ∈ (∅ : Set ℚ_[211]) := by
    rw [h1]
    exact Set.mem_univ _
  exact h2

abbrev SplittingFam (p : Unit) :=
  CompletePolySplittingTransport.Output
    (RetainedMonoidSplittingAdapter.Psi F Bad)
    (RetainedMonoidSplittingAdapter.Packet F Bad Label) p

def splittingAlgorithm : ProcessionAlgorithmRaw G (SplittingFam Bad Label) :=
  CompletePolyComponentAction.toProcessionAlgorithmRaw F
    (RetainedMonoidSplittingAdapter.action F Bad Label)
    (splittingBuild
      (galoisProcessionIsoRaw (K := ℚ_[211]))
      (fun _ : Unit => ℚ_[211])
      (WithZero (Multiplicative ℤ))
      (fun _ => v211)
      p211Transport
      Bad Label)

theorem splitting_laws :
    TransportIdentityLaw (splittingAlgorithm Bad Label) /\
    TransportCompositionLaw (splittingAlgorithm Bad Label) /\
    ConstructionCommutes (splittingAlgorithm Bad Label) /\
    EveryTransportInjective (splittingAlgorithm Bad Label) :=
  componentCoherent_gives_algorithm_laws F _ _
    (P211InnerComponentB.coherent Bad Label)

abbrev FieldFam (p : Unit) :=
  CompletePolyFieldCopyTransport.Output
    P211GaloisFieldCopyAction.Copy
    P211GaloisFieldCopyAction.LocalPacket p

def fieldAlgorithm : ProcessionAlgorithmRaw G FieldFam :=
  CompletePolyComponentAction.toProcessionAlgorithmRaw F
    (CompletePolyFieldCopyTransport.polyAction F
      P211GaloisFieldCopyAction.Copy
      P211GaloisFieldCopyAction.LocalPacket
      P211GaloisFieldCopyAction.carrierAction)
    P211GaloisFieldCopyAction.build

theorem field_laws :
    TransportIdentityLaw fieldAlgorithm /\
    TransportCompositionLaw fieldAlgorithm /\
    ConstructionCommutes fieldAlgorithm /\
    EveryTransportInjective fieldAlgorithm :=
  componentCoherent_gives_algorithm_laws F _ _
    P211GaloisFieldCopyAction.componentC_coherent

def algorithm :
    ProcessionAlgorithmRaw G
      (fun p => RLGPRawComponents (PacketFam p) (SplittingFam Bad Label p) (FieldFam p)) :=
  algorithmOfComponents G
    packetAlgorithm (splittingAlgorithm Bad Label) fieldAlgorithm

theorem every_pair_connected : EveryObjectPairConnected G :=
  fun _ _ => ⟨(1 : AbsGal ℚ_[211])⟩

theorem checked :
    CheckedProcessionFunctorialAlgorithm (algorithm Bad Label) := by
  obtain ⟨hSid, hScomp, hSbuild, hSinj⟩ := splitting_laws Bad Label
  obtain ⟨hFid, hFcomp, hFbuild, hFinj⟩ := field_laws
  exact checked_algorithmOfComponents
    packetAlgorithm (splittingAlgorithm Bad Label) fieldAlgorithm
    ⟨()⟩ every_pair_connected packet_nontrivial
    galoisProcession_groupoidLaws
    packet_identity hSid hFid
    packet_composition hScomp hFcomp
    packet_construction hSbuild hFbuild
    packet_injective hSinj hFinj

theorem algorithm_packet_is_qRegion (p : Unit) :
    ((algorithm Bad Label).build p).packet = P211Packet.p211QRegion := rfl

end CitedLV.Theorem311.P211SimultaneousRLGP
end
