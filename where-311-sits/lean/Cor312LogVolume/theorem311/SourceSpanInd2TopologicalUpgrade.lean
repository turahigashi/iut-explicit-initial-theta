import Cor312LogVolume.theorem311.SourceSpanInd2RegionAction
import Mathlib.Topology.Homeomorph.Lemmas

namespace CitedLV.Theorem311

universe uPacket

structure FixedStagePacketTopologicalTransportRaw
    {n : Nat} (Packet : Fin n -> Type uPacket) where
  topology : (j : Fin n) -> TopologicalSpace (Packet j)
  packetHomeomorph : (j : Fin n) ->
    @Homeomorph (Packet j) (Packet j) (topology j) (topology j)

def FixedStagePacketTopologicalTransportRaw.toRegionTransport
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (H : FixedStagePacketTopologicalTransportRaw Packet) :
    FixedStagePacketRegionTransportRaw Packet where
  packetEquiv := fun j =>
    @Homeomorph.toEquiv (Packet j) (Packet j)
      (H.topology j) (H.topology j) (H.packetHomeomorph j)

def TopologicalTransportAgreesWith
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (T : FixedStagePacketRegionTransportRaw Packet)
    (H : FixedStagePacketTopologicalTransportRaw Packet) : Prop :=
  ∀ j x, H.packetHomeomorph j x = T.packetEquiv j x

theorem topological_transport_eq_algebraic_transport
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (T : FixedStagePacketRegionTransportRaw Packet)
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (hcoh : TopologicalTransportAgreesWith T H) :
    transportRegionProfile H.toRegionTransport = transportRegionProfile T := by
  funext region j
  apply Set.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hcoh j x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hcoh j x⟩

def NonarchPacketRegionAdmissible
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (j : Fin n) (S : Set (Packet j)) : Prop :=
  letI : TopologicalSpace (Packet j) := H.topology j
  S.Nonempty ∧ IsCompact S ∧ IsOpen S

def ArchPacketRegionAdmissible
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (j : Fin n) (K : Set (Packet j)) : Prop :=
  letI : TopologicalSpace (Packet j) := H.topology j
  ∃ U : Set (Packet j),
    U.Nonempty ∧ IsOpen U ∧ IsCompact (closure U) ∧ K = closure U

theorem homeomorph_preserves_nonarch_packet_admissibility
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (H : FixedStagePacketTopologicalTransportRaw Packet) :
    RegionAdmissibilityPreservedUnder
      (NonarchPacketRegionAdmissible H) H.toRegionTransport := by
  intro j S hS
  letI : TopologicalSpace (Packet j) := H.topology j
  change NonarchPacketRegionAdmissible H j
    (H.packetHomeomorph j '' S)
  rcases hS with ⟨hne, hcompact, hopen⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases hne with ⟨x, hx⟩
    exact ⟨H.packetHomeomorph j x, x, hx, rfl⟩
  · exact (H.packetHomeomorph j).isCompact_image.mpr hcompact
  · exact (H.packetHomeomorph j).isOpenMap S hopen

theorem homeomorph_preserves_arch_packet_admissibility
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (H : FixedStagePacketTopologicalTransportRaw Packet) :
    RegionAdmissibilityPreservedUnder
      (ArchPacketRegionAdmissible H) H.toRegionTransport := by
  intro j S hS
  letI : TopologicalSpace (Packet j) := H.topology j
  change ArchPacketRegionAdmissible H j
    (H.packetHomeomorph j '' S)
  rcases hS with ⟨U, hne, hopen, hcompact, rfl⟩
  refine ⟨H.packetHomeomorph j '' U, ?_, ?_, ?_, ?_⟩
  · rcases hne with ⟨x, hx⟩
    exact ⟨H.packetHomeomorph j x, x, hx, rfl⟩
  · exact (H.packetHomeomorph j).isOpenMap U hopen
  · have himage := (H.packetHomeomorph j).isCompact_image.mpr hcompact
    rw [(H.packetHomeomorph j).image_closure] at himage
    exact himage
  · exact (H.packetHomeomorph j).image_closure U

theorem coherent_topological_upgrade_preserves_nonarch_for_algebraic_action
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (T : FixedStagePacketRegionTransportRaw Packet)
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (hcoh : TopologicalTransportAgreesWith T H) :
    RegionAdmissibilityPreservedUnder (NonarchPacketRegionAdmissible H) T := by
  intro j S hS
  have htop := homeomorph_preserves_nonarch_packet_admissibility H j S hS
  change NonarchPacketRegionAdmissible H j
    (H.packetHomeomorph j '' S) at htop
  have hset : T.packetEquiv j '' S = H.packetHomeomorph j '' S := by
    apply Set.image_congr
    intro x hx
    exact (hcoh j x).symm
  rw [hset]
  exact htop

theorem coherent_topological_upgrade_preserves_arch_for_algebraic_action
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (T : FixedStagePacketRegionTransportRaw Packet)
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (hcoh : TopologicalTransportAgreesWith T H) :
    RegionAdmissibilityPreservedUnder (ArchPacketRegionAdmissible H) T := by
  intro j S hS
  have htop := homeomorph_preserves_arch_packet_admissibility H j S hS
  change ArchPacketRegionAdmissible H j
    (H.packetHomeomorph j '' S) at htop
  have hset : T.packetEquiv j '' S = H.packetHomeomorph j '' S := by
    apply Set.image_congr
    intro x hx
    exact (hcoh j x).symm
  rw [hset]
  exact htop

def HomeomorphReadoutCompatible
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (readout : ProcessionRegionReadout Packet)
    (H : FixedStagePacketTopologicalTransportRaw Packet) : Prop :=
  ∀ j S, readout j (H.packetHomeomorph j '' S) = readout j S

theorem coherent_homeomorph_readout_yields_algebraic_invariance
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (readout : ProcessionRegionReadout Packet)
    (T : FixedStagePacketRegionTransportRaw Packet)
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (hcoh : TopologicalTransportAgreesWith T H)
    (hread : HomeomorphReadoutCompatible readout H) :
    RegionReadoutInvariantUnder readout T := by
  intro j S
  have hset : T.packetEquiv j '' S = H.packetHomeomorph j '' S := by
    apply Set.image_congr
    intro x hx
    exact (hcoh j x).symm
  rw [hset]
  exact hread j S

theorem coherent_topological_upgrade_preserves_nonarch_and_mean
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (readout : ProcessionRegionReadout Packet)
    (T : FixedStagePacketRegionTransportRaw Packet)
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (hcoh : TopologicalTransportAgreesWith T H)
    (hread : HomeomorphReadoutCompatible readout H)
    (region : ProcessionRegionProfile Packet)
    (hregion : SelectedRegionsAdmissible
      (NonarchPacketRegionAdmissible H)
      (regionProfileLogVolumeRaw readout region)) :
    SelectedRegionsAdmissible (NonarchPacketRegionAdmissible H)
        (regionProfileLogVolumeRaw readout (transportRegionProfile T region)) /\
      regionProfileNormalizedLogVolume readout (transportRegionProfile T region) =
        regionProfileNormalizedLogVolume readout region := by
  exact ⟨fixed_stage_transport_preserves_selected_admissibility
      (NonarchPacketRegionAdmissible H) readout T
      (coherent_topological_upgrade_preserves_nonarch_for_algebraic_action
        T H hcoh) region hregion,
    fixed_stage_transport_preserves_normalized_mean readout T
      (coherent_homeomorph_readout_yields_algebraic_invariance
        readout T H hcoh hread) region⟩

theorem coherent_topological_upgrade_preserves_arch_and_mean
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (readout : ProcessionRegionReadout Packet)
    (T : FixedStagePacketRegionTransportRaw Packet)
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (hcoh : TopologicalTransportAgreesWith T H)
    (hread : HomeomorphReadoutCompatible readout H)
    (region : ProcessionRegionProfile Packet)
    (hregion : SelectedRegionsAdmissible
      (ArchPacketRegionAdmissible H)
      (regionProfileLogVolumeRaw readout region)) :
    SelectedRegionsAdmissible (ArchPacketRegionAdmissible H)
        (regionProfileLogVolumeRaw readout (transportRegionProfile T region)) /\
      regionProfileNormalizedLogVolume readout (transportRegionProfile T region) =
        regionProfileNormalizedLogVolume readout region := by
  exact ⟨fixed_stage_transport_preserves_selected_admissibility
      (ArchPacketRegionAdmissible H) readout T
      (coherent_topological_upgrade_preserves_arch_for_algebraic_action
        T H hcoh) region hregion,
    fixed_stage_transport_preserves_normalized_mean readout T
      (coherent_homeomorph_readout_yields_algebraic_invariance
        readout T H hcoh hread) region⟩

def boolIdentityTopologicalTransport :
    FixedStagePacketTopologicalTransportRaw boolStagePacket where
  topology := fun _ => inferInstance
  packetHomeomorph := fun _ => Homeomorph.refl Bool

def boolNotTopologicalTransport :
    FixedStagePacketTopologicalTransportRaw boolStagePacket where
  topology := fun _ => inferInstance
  packetHomeomorph := fun _ => Homeomorph.ofDiscrete boolNotEquiv

theorem bool_not_topological_transport_agrees_with_all_not :
    TopologicalTransportAgreesWith allStagesNotTransport
      boolNotTopologicalTransport := by
  intro j b
  rfl

theorem identity_topological_transport_does_not_agree_with_all_not :
    ¬ TopologicalTransportAgreesWith allStagesNotTransport
      boolIdentityTopologicalTransport := by
  intro h
  have := h 0 false
  simp [boolIdentityTopologicalTransport, allStagesNotTransport,
    boolNotEquiv] at this
  exact Bool.noConfusion this

theorem coherent_homeomorph_preserves_both_source_admissibility_shapes :
    RegionAdmissibilityPreservedUnder
        (NonarchPacketRegionAdmissible boolNotTopologicalTransport)
        allStagesNotTransport /\
      RegionAdmissibilityPreservedUnder
        (ArchPacketRegionAdmissible boolNotTopologicalTransport)
        allStagesNotTransport :=
  ⟨coherent_topological_upgrade_preserves_nonarch_for_algebraic_action
      allStagesNotTransport boolNotTopologicalTransport
        bool_not_topological_transport_agrees_with_all_not,
    coherent_topological_upgrade_preserves_arch_for_algebraic_action
      allStagesNotTransport boolNotTopologicalTransport
        bool_not_topological_transport_agrees_with_all_not⟩

theorem topological_admissibility_does_not_force_readout_invariance :
    RegionAdmissibilityPreservedUnder
        (NonarchPacketRegionAdmissible boolNotTopologicalTransport)
        allStagesNotTransport /\
      ¬ RegionReadoutInvariantUnder falseMembershipReadout
        allStagesNotTransport :=
  ⟨coherent_homeomorph_preserves_both_source_admissibility_shapes.1,
    false_membership_readout_not_invariant_under_all_not⟩

end CitedLV.Theorem311
