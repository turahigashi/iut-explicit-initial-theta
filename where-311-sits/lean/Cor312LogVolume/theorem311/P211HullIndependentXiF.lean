import Cor312LogVolume.theorem311.P211SourceFacingSimultaneousXiF

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211HullIndependentXiF

open Src.IUT3.Theorem311
open Src.CoreLayer.RelativeXiFFamily
open CitedLV.Theorem311
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211ComponentCTraceBridge
open CitedLV.Theorem311.P211SourceFacingSimultaneousXiF
open CitedLV.Theorem311.PacketOutputTraceFrontier
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Theorem311.PacketHullPipelineAdapter
open CitedLV.Theorem311.PacketProcessionNormalizationAdapter

def QRegionIsHull (H : HullFamily p211PacketSystem) : Prop :=
  ∀ vQ j, (H vQ j).isHull (p211QRegion vQ j)

def ScalarIntegralIsHull (H : HullFamily p211PacketSystem) : Prop :=
  ∀ vQ j (c : ℚ_[211]), c ≠ 0 →
    (H vQ j).isHull
      ((fun z : ℚ_[211] => c * z) '' p211PacketSystem.integral vQ j)

theorem qRegionIsHull_of_scalarIntegralIsHull
    (H : HullFamily p211PacketSystem)
    (hscalar : ScalarIntegralIsHull H) :
    QRegionIsHull H := by
  intro vQ j
  change (H vQ j).isHull (qBall 29)
  unfold qBall
  change
    (H vQ j).isHull
      ((fun z : ℚ_[211] => (pElt ^ 29) * z) ''
        p211PacketSystem.integral vQ j)
  exact hscalar vQ j (pElt ^ 29) (pow_ne_zero _ pElt_ne_zero)

theorem qRegion_is_componentC_image_of_container :
    fieldCopyActOnContainer componentCGlobal211 29 = p211QRegion :=
  fieldCopyActOnContainer_y211_eq_qRegion

theorem union_admissible_of_qRegion_isHull
    (H : HullFamily p211PacketSystem)
    (hq : QRegionIsHull H) :
    UnionAdmissible p211PacketSystem H
      (tracedRegions simultaneousTrace p211Input) := by
  rw [simultaneous_tracedRegions_p211]
  intro vQ j
  rw [unionProfile_singleton]
  exact (H vQ j).hull_sub_domain (hq vQ j)

theorem hull_eq_qRegion_of_qRegion_isHull
    (H : HullFamily p211PacketSystem)
    (hq : QRegionIsHull H) :
    hullProfile p211PacketSystem H
        (tracedRegions simultaneousTrace p211Input) =
      p211QRegion := by
  rw [simultaneous_tracedRegions_p211]
  unfold hullProfile
  rw [unionProfile_singleton]
  funext vQ j
  exact (H vQ j).P1 (hq vQ j)

theorem endpoint_eq_inputReadout_of_qRegion_isHull
    (H : HullFamily p211PacketSystem)
    (hq : QRegionIsHull H) :
    endpoint p211PacketSystem H
        (tracedRegions simultaneousTrace p211Input) =
      componentCInputReadout p211Input := by
  unfold endpoint
  rw [hull_eq_qRegion_of_qRegion_isHull H hq, p211_procVol,
    p211Input_readout_eq_obligationE]

def producedFamily :
    ProducedFamily simultaneousPresentation (b := ()) p211Input :=
  simultaneousProducedFamily

def finiteReadout
    (H : HullFamily p211PacketSystem)
    (hq : QRegionIsHull H) :
    FiniteFamilyReadout
      simultaneousPresentation
      (packetRegularHull simultaneousTrace componentCInputReadout H)
      (packetProcessionNormalization
        p211PacketSystem simultaneousTrace componentCInputReadout)
      (b := ()) p211Input :=
  packetFiniteReadout
    simultaneousTrace componentCInputReadout H p211Input
    producedFamily
    (union_admissible_of_qRegion_isHull H hq)

theorem finiteReadout_value
    (H : HullFamily p211PacketSystem)
    (hq : QRegionIsHull H) :
    (finiteReadout H hq).value = componentCInputReadout p211Input := by
  calc
    (finiteReadout H hq).value =
        endpoint p211PacketSystem H
          (tracedRegions simultaneousTrace p211Input) :=
      packetFiniteReadout_value_eq_endpoint
        simultaneousTrace componentCInputReadout H p211Input
        (finiteReadout H hq)
    _ = componentCInputReadout p211Input :=
      endpoint_eq_inputReadout_of_qRegion_isHull H hq

def xifGenerated
    (H : HullFamily p211PacketSystem)
    (hq : QRegionIsHull H) :
    XiFGenerated
      simultaneousPresentation
      (packetRegularHull simultaneousTrace componentCInputReadout H)
      (packetProcessionNormalization
        p211PacketSystem simultaneousTrace componentCInputReadout)
      (b := ()) p211Input where
  readout := finiteReadout H hq
  generates_q := finiteReadout_value H hq

theorem xifGenerated_nonempty
    (H : HullFamily p211PacketSystem)
    (hq : QRegionIsHull H) :
    Nonempty
      (XiFGenerated
        simultaneousPresentation
        (packetRegularHull simultaneousTrace componentCInputReadout H)
        (packetProcessionNormalization
          p211PacketSystem simultaneousTrace componentCInputReadout)
        (b := ()) p211Input) :=
  ⟨xifGenerated H hq⟩

theorem xifGenerated_nonempty_of_scalarIntegralIsHull
    (H : HullFamily p211PacketSystem)
    (hscalar : ScalarIntegralIsHull H) :
    Nonempty
      (XiFGenerated
        simultaneousPresentation
        (packetRegularHull simultaneousTrace componentCInputReadout H)
        (packetProcessionNormalization
          p211PacketSystem simultaneousTrace componentCInputReadout)
        (b := ()) p211Input) :=
  xifGenerated_nonempty H (qRegionIsHull_of_scalarIntegralIsHull H hscalar)

end CitedLV.Theorem311.P211HullIndependentXiF
end
