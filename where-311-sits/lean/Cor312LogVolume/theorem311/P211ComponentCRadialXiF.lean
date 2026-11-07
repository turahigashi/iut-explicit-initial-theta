import Cor312LogVolume.theorem311.P211ComponentCTraceBridge
import Cor312LogVolume.theorem311.PacketHullPipelineAdapter
import Cor312LogVolume.theorem311.logkummer.NormBallHullTransport

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211ComponentCRadialXiF

open Src.IUT3.Theorem311
open Src.CoreLayer.RelativeXiFFamily
open CitedLV.Theorem311
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211ComponentCTraceBridge
open CitedLV.Theorem311.PacketOutputTraceFrontier
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Theorem311.PacketHullPipelineAdapter
open CitedLV.Theorem311.PacketProcessionNormalizationAdapter
open CitedLV.Theorem311.NormBallHullTransport

theorem ind1_eq {R T : p211PacketSystem.Regions}
    (h : p211PacketSystem.Ind1 R T) : T = R := by
  obtain ⟨a, rfl⟩ := h
  funext vQ j
  change (a.packetAut vQ j) '' R vQ j = R vQ j
  have hfun :
      (a.packetAut vQ j : ℚ_[211] → ℚ_[211]) = id := by
    funext x
    rfl
  rw [hfun]
  exact Set.image_id _

theorem ind2_eq {R T : p211PacketSystem.Regions}
    (h : p211PacketSystem.Ind2 R T) : T = R := by
  obtain ⟨g, rfl⟩ := h
  funext vQ j
  change p211PacketSystem.ismAct vQ j (g vQ j) '' R vQ j = R vQ j
  have hfun :
      (p211PacketSystem.ismAct vQ j (g vQ j) : ℚ_[211] → ℚ_[211]) = id := by
    funext x
    rfl
  rw [hfun]
  exact Set.image_id _

theorem indRel_eq {R T : p211PacketSystem.Regions}
    (h : p211PacketSystem.IndRel R T) : T = R := by
  rcases h with h | h
  · exact ind1_eq h
  · exact ind2_eq h

theorem eqvGen_eq {R T : p211PacketSystem.Regions}
    (h : Relation.EqvGen p211PacketSystem.IndRel R T) : T = R := by
  induction h with
  | rel _ _ hRT =>
      exact indRel_eq hRT
  | refl _ =>
      rfl
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₂.trans ih₁

theorem quotient_eq_iff {R T : p211PacketSystem.Regions} :
    Quot.mk p211PacketSystem.IndRel R =
        Quot.mk p211PacketSystem.IndRel T ↔ R = T := by
  constructor
  · intro h
    rw [Quot.eq] at h
    exact (eqvGen_eq h).symm
  · rintro rfl
    rfl

theorem tracedRegions_p211Input :
    tracedRegions componentCTrace p211Input = {p211QRegion} := by
  ext R
  constructor
  · rintro ⟨htrace⟩
    have hq := htrace.down
    rw [p211Input_region_eq_qRegion] at hq
    exact Set.mem_singleton_iff.mpr ((quotient_eq_iff).1 hq)
  · intro hR
    have hR' : R = p211QRegion := Set.mem_singleton_iff.mp hR
    subst R
    exact componentCTrace_qRegion

def p211NormHulls : HullFamily p211PacketSystem :=
  fun _ _ => normHull ℚ_[211]

theorem traced_union_admissible :
    UnionAdmissible p211PacketSystem p211NormHulls
      (tracedRegions componentCTrace p211Input) := by
  rw [tracedRegions_p211Input]
  intro vQ j
  rw [unionProfile_singleton]
  change Bounded (qBall 29)
  rw [qBall_eq]
  exact ⟨((211 : ℝ)⁻¹) ^ 29, by positivity, Set.Subset.rfl⟩

theorem traced_hull_eq_qRegion :
    hullProfile p211PacketSystem p211NormHulls
        (tracedRegions componentCTrace p211Input) =
      p211QRegion := by
  rw [tracedRegions_p211Input]
  unfold hullProfile
  rw [unionProfile_singleton]
  funext vQ j
  change (normHull ℚ_[211]).φ (qBall 29) = qBall 29
  rw [qBall_eq]
  exact hull_closedBall (by positivity)

theorem traced_endpoint_eq_obligationE :
    endpoint p211PacketSystem p211NormHulls
        (tracedRegions componentCTrace p211Input) =
      -(29 / 7) * Real.log 211 := by
  unfold endpoint
  rw [traced_hull_eq_qRegion]
  exact p211_procVol

theorem traced_endpoint_eq_inputReadout :
    endpoint p211PacketSystem p211NormHulls
        (tracedRegions componentCTrace p211Input) =
      componentCInputReadout p211Input := by
  rw [traced_endpoint_eq_obligationE, p211Input_readout_eq_obligationE]

abbrev p211Presentation :=
  packetFamilyPresentation componentCTrace componentCInputReadout

def p211ProducedFamily :
    ProducedFamily p211Presentation (b := ()) p211Input where
  output := regionToOutputFamily p211PacketSystem p211QRegion
  trace := by
    change componentCTrace.Trace p211Input
      (outputFamilyToRegion p211PacketSystem
        (regionToOutputFamily p211PacketSystem p211QRegion))
    rw [outputFamilyToRegion_regionToOutputFamily]
    change PLift
      (Quot.mk p211PacketSystem.IndRel p211QRegion =
        Quot.mk p211PacketSystem.IndRel (inputRegion p211Input))
    exact PLift.up (by rw [p211Input_region_eq_qRegion])

def p211FiniteReadout :
    FiniteFamilyReadout
      p211Presentation
      (packetRegularHull componentCTrace componentCInputReadout p211NormHulls)
      (packetProcessionNormalization
        p211PacketSystem componentCTrace componentCInputReadout)
      (b := ()) p211Input :=
  packetFiniteReadout
    componentCTrace componentCInputReadout p211NormHulls p211Input
    p211ProducedFamily traced_union_admissible

theorem p211FiniteReadout_value :
    p211FiniteReadout.value = componentCInputReadout p211Input := by
  calc
    p211FiniteReadout.value =
        endpoint p211PacketSystem p211NormHulls
          (tracedRegions componentCTrace p211Input) :=
      packetFiniteReadout_value_eq_endpoint
        componentCTrace componentCInputReadout p211NormHulls p211Input
        p211FiniteReadout
    _ = componentCInputReadout p211Input :=
      traced_endpoint_eq_inputReadout

def p211RadialXiFGenerated :
    XiFGenerated
      p211Presentation
      (packetRegularHull componentCTrace componentCInputReadout p211NormHulls)
      (packetProcessionNormalization
        p211PacketSystem componentCTrace componentCInputReadout)
      (b := ()) p211Input where
  readout := p211FiniteReadout
  generates_q := by
    change p211FiniteReadout.value = componentCInputReadout p211Input
    exact p211FiniteReadout_value

theorem p211RadialXiFGenerated_nonempty :
    Nonempty
      (XiFGenerated
        p211Presentation
        (packetRegularHull componentCTrace componentCInputReadout p211NormHulls)
        (packetProcessionNormalization
          p211PacketSystem componentCTrace componentCInputReadout)
        (b := ()) p211Input) :=
  ⟨p211RadialXiFGenerated⟩

end CitedLV.Theorem311.P211ComponentCRadialXiF
end
