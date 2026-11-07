import Cor312LogVolume.theorem311.P211ComponentCRadialXiF
import Cor312LogVolume.theorem311.P211SimultaneousRLGP

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211SourceFacingSimultaneousXiF

open Src.IUT3.Theorem311
open Src.CoreLayer.RelativeXiFFamily
open CitedLV.Theorem311
open CitedLV.Theorem311.RLGPSimultaneousBuild
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211RLGPRaw
open CitedLV.Theorem311.P211ComponentCTraceBridge
open CitedLV.Theorem311.P211ComponentCRadialXiF
open CitedLV.Theorem311.PacketOutputTraceFrontier
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Theorem311.PacketHullPipelineAdapter
open CitedLV.Theorem311.PacketProcessionNormalizationAdapter
open CitedLV.Theorem311.NormBallHullTransport

abbrev Bad := P211RLGPRaw.Bad
abbrev Label := P211RLGPRaw.Label
abbrev G := P211SimultaneousRLGP.G

abbrev PacketFam (_p : Unit) := p211PacketSystem.Regions

def sourcePacketAlgorithm : ProcessionAlgorithmRaw G PacketFam where
  build := fun _ => integralContainer
  transport := fun _ x => x

theorem sourcePacket_identity :
    TransportIdentityLaw sourcePacketAlgorithm :=
  fun _ _ => rfl

theorem sourcePacket_composition :
    TransportCompositionLaw sourcePacketAlgorithm :=
  fun _ _ _ => rfl

theorem sourcePacket_construction :
    ConstructionCommutes sourcePacketAlgorithm :=
  fun _ => rfl

theorem sourcePacket_injective :
    EveryTransportInjective sourcePacketAlgorithm :=
  fun _ => Function.injective_id

theorem sourcePacket_nontrivial :
    EveryPacketFiberNontrivial PacketFam :=
  P211SimultaneousRLGP.packet_nontrivial

def sourceAlgorithm :
    ProcessionAlgorithmRaw G
      (fun p =>
        RLGPRawComponents
          (PacketFam p)
          (P211SimultaneousRLGP.SplittingFam Bad Label p)
          (P211SimultaneousRLGP.FieldFam p)) :=
  algorithmOfComponents G
    sourcePacketAlgorithm
    (P211SimultaneousRLGP.splittingAlgorithm Bad Label)
    P211SimultaneousRLGP.fieldAlgorithm

theorem sourceAlgorithm_checked :
    CheckedProcessionFunctorialAlgorithm sourceAlgorithm := by
  obtain ⟨hSid, hScomp, hSbuild, hSinj⟩ :=
    P211SimultaneousRLGP.splitting_laws Bad Label
  obtain ⟨hFid, hFcomp, hFbuild, hFinj⟩ :=
    P211SimultaneousRLGP.field_laws
  exact checked_algorithmOfComponents
    sourcePacketAlgorithm
    (P211SimultaneousRLGP.splittingAlgorithm Bad Label)
    P211SimultaneousRLGP.fieldAlgorithm
    ⟨()⟩
    P211SimultaneousRLGP.every_pair_connected
    sourcePacket_nontrivial
    InnerArithmeticArrowTransport.galoisProcession_groupoidLaws
    sourcePacket_identity hSid hFid
    sourcePacket_composition hScomp hFcomp
    sourcePacket_construction hSbuild hFbuild
    sourcePacket_injective hSinj hFinj

@[simp] theorem sourceAlgorithm_packet :
    (sourceAlgorithm.build ()).packet = integralContainer := rfl

@[simp] theorem sourceAlgorithm_fieldCopy :
    (sourceAlgorithm.build ()).fieldCopy =
      P211RLGPRaw.Global.fieldCopy := rfl

def simultaneousFiniteValue
    (x : P211RLGPRaw.Global.GlobalCopy selectedLabel) : V211LocalField :=
  (((sourceAlgorithm.build ()).fieldCopy.embed
      selectedLabel x (Sum.inl P211PlaceOver211.v211)
      : V211LocalFieldˣ) : V211LocalField)

theorem simultaneousFiniteValue_eq_fieldCopyFiniteValue
    (x : P211RLGPRaw.Global.GlobalCopy selectedLabel) :
    simultaneousFiniteValue x = fieldCopyFiniteValue x := by
  unfold simultaneousFiniteValue fieldCopyFiniteValue
  rw [sourceAlgorithm_fieldCopy, sourceFacingComponents_fieldCopy]

def simultaneousPadicScalar
    (x : P211RLGPRaw.Global.GlobalCopy selectedLabel) : ℚ_[211] :=
  v211CompletionToPadic (simultaneousFiniteValue x)

theorem simultaneousPadicScalar_eq_fieldCopyPadicScalar
    (x : P211RLGPRaw.Global.GlobalCopy selectedLabel) :
    simultaneousPadicScalar x = fieldCopyPadicScalar x := by
  unfold simultaneousPadicScalar fieldCopyPadicScalar
  rw [simultaneousFiniteValue_eq_fieldCopyFiniteValue]

def realizedRegion (i : ComponentCInput) : p211PacketSystem.Regions :=
  fun vQ j =>
    (fun z : ℚ_[211] =>
      (simultaneousPadicScalar i.globalElement ^ i.exponent) * z) ''
      (sourceAlgorithm.build ()).packet vQ j

theorem realizedRegion_eq_inputRegion (i : ComponentCInput) :
    realizedRegion i = inputRegion i := by
  funext vQ j
  unfold realizedRegion inputRegion fieldCopyActOnContainer
  rw [sourceAlgorithm_packet, sourceFacingComponents_packet,
    simultaneousPadicScalar_eq_fieldCopyPadicScalar]

theorem realizedRegion_p211 :
    realizedRegion p211Input = p211QRegion := by
  rw [realizedRegion_eq_inputRegion, p211Input_region_eq_qRegion]

def simultaneousTrace :
    PacketOutputTrace p211PacketSystem ComponentCInput where
  Trace := fun i R =>
    PLift
      (Quot.mk p211PacketSystem.IndRel R =
        Quot.mk p211PacketSystem.IndRel (realizedRegion i))

theorem simultaneousTrace_p211_qRegion :
    Nonempty (simultaneousTrace.Trace p211Input p211QRegion) := by
  refine ⟨PLift.up ?_⟩
  rw [realizedRegion_p211]

theorem simultaneous_tracedRegions_p211 :
    tracedRegions simultaneousTrace p211Input = {p211QRegion} := by
  ext R
  constructor
  · rintro ⟨h⟩
    have hq := h.down
    rw [realizedRegion_p211] at hq
    exact Set.mem_singleton_iff.mpr ((quotient_eq_iff).1 hq)
  · intro hR
    have hR' : R = p211QRegion := Set.mem_singleton_iff.mp hR
    subst R
    exact simultaneousTrace_p211_qRegion

abbrev simultaneousNormHulls : HullFamily p211PacketSystem :=
  p211NormHulls

theorem simultaneous_union_admissible :
    UnionAdmissible p211PacketSystem simultaneousNormHulls
      (tracedRegions simultaneousTrace p211Input) := by
  rw [simultaneous_tracedRegions_p211]
  intro vQ j
  rw [unionProfile_singleton]
  change Bounded (qBall 29)
  rw [qBall_eq]
  exact ⟨((211 : ℝ)⁻¹) ^ 29, by positivity, Set.Subset.rfl⟩

theorem simultaneous_hull_eq_qRegion :
    hullProfile p211PacketSystem simultaneousNormHulls
        (tracedRegions simultaneousTrace p211Input) =
      p211QRegion := by
  rw [simultaneous_tracedRegions_p211]
  unfold hullProfile
  rw [unionProfile_singleton]
  funext vQ j
  change (normHull ℚ_[211]).φ (qBall 29) = qBall 29
  rw [qBall_eq]
  exact hull_closedBall (by positivity)

theorem simultaneous_endpoint_eq_inputReadout :
    endpoint p211PacketSystem simultaneousNormHulls
        (tracedRegions simultaneousTrace p211Input) =
      componentCInputReadout p211Input := by
  unfold endpoint
  rw [simultaneous_hull_eq_qRegion, p211_procVol,
    p211Input_readout_eq_obligationE]

abbrev simultaneousPresentation :=
  packetFamilyPresentation simultaneousTrace componentCInputReadout

def simultaneousProducedFamily :
    ProducedFamily simultaneousPresentation (b := ()) p211Input where
  output := regionToOutputFamily p211PacketSystem p211QRegion
  trace := by
    change simultaneousTrace.Trace p211Input
      (outputFamilyToRegion p211PacketSystem
        (regionToOutputFamily p211PacketSystem p211QRegion))
    rw [outputFamilyToRegion_regionToOutputFamily]
    exact simultaneousTrace_p211_qRegion.some

def simultaneousFiniteReadout :
    FiniteFamilyReadout
      simultaneousPresentation
      (packetRegularHull
        simultaneousTrace componentCInputReadout simultaneousNormHulls)
      (packetProcessionNormalization
        p211PacketSystem simultaneousTrace componentCInputReadout)
      (b := ()) p211Input :=
  packetFiniteReadout
    simultaneousTrace componentCInputReadout simultaneousNormHulls p211Input
    simultaneousProducedFamily simultaneous_union_admissible

theorem simultaneousFiniteReadout_value :
    simultaneousFiniteReadout.value =
      componentCInputReadout p211Input := by
  calc
    simultaneousFiniteReadout.value =
        endpoint p211PacketSystem simultaneousNormHulls
          (tracedRegions simultaneousTrace p211Input) :=
      packetFiniteReadout_value_eq_endpoint
        simultaneousTrace componentCInputReadout simultaneousNormHulls p211Input
        simultaneousFiniteReadout
    _ = componentCInputReadout p211Input :=
      simultaneous_endpoint_eq_inputReadout

def simultaneousXiFGenerated :
    XiFGenerated
      simultaneousPresentation
      (packetRegularHull
        simultaneousTrace componentCInputReadout simultaneousNormHulls)
      (packetProcessionNormalization
        p211PacketSystem simultaneousTrace componentCInputReadout)
      (b := ()) p211Input where
  readout := simultaneousFiniteReadout
  generates_q := simultaneousFiniteReadout_value

theorem simultaneousXiFGenerated_nonempty :
    Nonempty
      (XiFGenerated
        simultaneousPresentation
        (packetRegularHull
          simultaneousTrace componentCInputReadout simultaneousNormHulls)
        (packetProcessionNormalization
          p211PacketSystem simultaneousTrace componentCInputReadout)
        (b := ()) p211Input) :=
  ⟨simultaneousXiFGenerated⟩

end CitedLV.Theorem311.P211SourceFacingSimultaneousXiF
end
