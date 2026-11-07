import Cor312LogVolume.theorem311.SourceSpanInd2TopologicalUpgrade

namespace CitedLV.Theorem311

universe uPacket

inductive PacketPlaceKind where
  | nonarch
  | arch
deriving DecidableEq

def SourcePacketRegionAdmissible
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (kind : PacketPlaceKind)
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (j : Fin n) (K : Set (Packet j)) : Prop :=
  match kind with
  | .nonarch => NonarchPacketRegionAdmissible H j K
  | .arch => ArchPacketRegionAdmissible H j K

abbrev SourceAdmissiblePacketRegion
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (kind : PacketPlaceKind)
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (j : Fin n) :=
  {K : Set (Packet j) // SourcePacketRegionAdmissible kind H j K}

def transportSourceAdmissiblePacketRegion
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (kind : PacketPlaceKind)
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (j : Fin n) (R : SourceAdmissiblePacketRegion kind H j) :
    SourceAdmissiblePacketRegion kind H j := by
  refine ⟨H.packetHomeomorph j '' R.1, ?_⟩
  cases kind with
  | nonarch =>
      exact homeomorph_preserves_nonarch_packet_admissibility H j R.1 R.2
  | arch =>
      exact homeomorph_preserves_arch_packet_admissibility H j R.1 R.2

abbrev SourceAdmissibleRegionProfile
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (kind : PacketPlaceKind)
    (H : FixedStagePacketTopologicalTransportRaw Packet) :=
  (j : Fin n) -> SourceAdmissiblePacketRegion kind H j

abbrev SourceAdmissibleRegionReadout
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (kind : PacketPlaceKind)
    (H : FixedStagePacketTopologicalTransportRaw Packet) :=
  (j : Fin n) -> SourceAdmissiblePacketRegion kind H j -> Real

def transportSourceAdmissibleRegionProfile
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (kind : PacketPlaceKind)
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (region : SourceAdmissibleRegionProfile kind H) :
    SourceAdmissibleRegionProfile kind H :=
  fun j => transportSourceAdmissiblePacketRegion kind H j (region j)

def SourceAdmissibleReadoutCompatible
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (kind : PacketPlaceKind)
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (readout : SourceAdmissibleRegionReadout kind H) : Prop :=
  ∀ j R,
    readout j (transportSourceAdmissiblePacketRegion kind H j R) = readout j R

structure SourceAdmissibleProcessionLogVolumeRaw
    {n : Nat} (Packet : Fin n -> Type uPacket)
    (kind : PacketPlaceKind)
    (H : FixedStagePacketTopologicalTransportRaw Packet) where
  region : SourceAdmissibleRegionProfile kind H
  packetLogVolume : SourceAdmissibleRegionReadout kind H

noncomputable def sourceAdmissibleProcessionPacketValue
    {n : Nat} {Packet : Fin n -> Type uPacket}
    {kind : PacketPlaceKind}
    {H : FixedStagePacketTopologicalTransportRaw Packet}
    (V : SourceAdmissibleProcessionLogVolumeRaw Packet kind H)
    (j : Fin n) : Real :=
  V.packetLogVolume j (V.region j)

noncomputable def sourceAdmissibleProcessionNormalizedLogVolume
    {n : Nat} {Packet : Fin n -> Type uPacket}
    {kind : PacketPlaceKind}
    {H : FixedStagePacketTopologicalTransportRaw Packet}
    (V : SourceAdmissibleProcessionLogVolumeRaw Packet kind H) : Real :=
  ordinaryFinMean (fun j => sourceAdmissibleProcessionPacketValue V j)

def transportSourceAdmissibleProcessionLogVolumeRaw
    {n : Nat} {Packet : Fin n -> Type uPacket}
    {kind : PacketPlaceKind}
    {H : FixedStagePacketTopologicalTransportRaw Packet}
    (V : SourceAdmissibleProcessionLogVolumeRaw Packet kind H) :
    SourceAdmissibleProcessionLogVolumeRaw Packet kind H where
  region := transportSourceAdmissibleRegionProfile kind H V.region
  packetLogVolume := V.packetLogVolume

theorem source_admissible_readout_compatibility_preserves_packet_value
    {n : Nat} {Packet : Fin n -> Type uPacket}
    {kind : PacketPlaceKind}
    {H : FixedStagePacketTopologicalTransportRaw Packet}
    (V : SourceAdmissibleProcessionLogVolumeRaw Packet kind H)
    (hcompat : SourceAdmissibleReadoutCompatible kind H V.packetLogVolume)
    (j : Fin n) :
    sourceAdmissibleProcessionPacketValue
        (transportSourceAdmissibleProcessionLogVolumeRaw V) j =
      sourceAdmissibleProcessionPacketValue V j := by
  exact hcompat j (V.region j)

theorem source_admissible_readout_compatibility_preserves_normalized_mean
    {n : Nat} {Packet : Fin n -> Type uPacket}
    {kind : PacketPlaceKind}
    {H : FixedStagePacketTopologicalTransportRaw Packet}
    (V : SourceAdmissibleProcessionLogVolumeRaw Packet kind H)
    (hcompat : SourceAdmissibleReadoutCompatible kind H V.packetLogVolume) :
    sourceAdmissibleProcessionNormalizedLogVolume
        (transportSourceAdmissibleProcessionLogVolumeRaw V) =
      sourceAdmissibleProcessionNormalizedLogVolume V := by
  unfold sourceAdmissibleProcessionNormalizedLogVolume
  congr 1
  funext j
  exact source_admissible_readout_compatibility_preserves_packet_value
    V hcompat j

def forgetSourceAdmissibleRegionProfile
    {n : Nat} {Packet : Fin n -> Type uPacket}
    {kind : PacketPlaceKind}
    {H : FixedStagePacketTopologicalTransportRaw Packet}
    (region : SourceAdmissibleRegionProfile kind H) :
    ProcessionRegionProfile Packet :=
  fun j => (region j).1

theorem forget_admissible_transport_eq_topological_set_transport
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (kind : PacketPlaceKind)
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (region : SourceAdmissibleRegionProfile kind H) :
    forgetSourceAdmissibleRegionProfile
        (transportSourceAdmissibleRegionProfile kind H region) =
      transportRegionProfile H.toRegionTransport
        (forgetSourceAdmissibleRegionProfile region) :=
  rfl

theorem forget_admissible_transport_eq_algebraic_set_transport
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (kind : PacketPlaceKind)
    (T : FixedStagePacketRegionTransportRaw Packet)
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (hcoh : TopologicalTransportAgreesWith T H)
    (region : SourceAdmissibleRegionProfile kind H) :
    forgetSourceAdmissibleRegionProfile
        (transportSourceAdmissibleRegionProfile kind H region) =
      transportRegionProfile T (forgetSourceAdmissibleRegionProfile region) := by
  rw [forget_admissible_transport_eq_topological_set_transport]
  exact congrFun (topological_transport_eq_algebraic_transport T H hcoh)
    (forgetSourceAdmissibleRegionProfile region)

theorem source_admissible_region_is_never_empty
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (kind : PacketPlaceKind)
    (H : FixedStagePacketTopologicalTransportRaw Packet)
    (j : Fin n) (R : SourceAdmissiblePacketRegion kind H j) :
    R.1 ≠ ∅ := by
  letI : TopologicalSpace (Packet j) := H.topology j
  cases kind with
  | nonarch =>
      exact R.2.1.ne_empty
  | arch =>
      rcases R.2 with ⟨U, hne, hopen, hcompact, hR⟩
      rw [hR]
      exact (hne.mono subset_closure).ne_empty

def boolFalseNonarchRegion (j : Fin 2) :
    SourceAdmissiblePacketRegion .nonarch boolNotTopologicalTransport j := by
  letI : TopologicalSpace Bool := boolNotTopologicalTransport.topology j
  letI : DiscreteTopology Bool := ⟨by rfl⟩
  refine ⟨{false}, ?_⟩
  exact ⟨Set.singleton_nonempty false, isCompact_singleton, isOpen_discrete _⟩

def boolUnivNonarchRegion (j : Fin 2) :
    SourceAdmissiblePacketRegion .nonarch boolNotTopologicalTransport j := by
  letI : TopologicalSpace Bool := boolNotTopologicalTransport.topology j
  refine ⟨Set.univ, ?_⟩
  exact ⟨Set.univ_nonempty, isCompact_univ, isOpen_univ⟩

theorem equiv_image_eq_univ_iff {X : Type*} (e : X ≃ X) (S : Set X) :
    e '' S = Set.univ ↔ S = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro x
    have hx : e x ∈ e '' S := by
      rw [h]
      trivial
    rcases hx with ⟨y, hy, heq⟩
    have hyx : y = x := e.injective heq
    simpa [hyx] using hy
  · intro h
    subst S
    apply Set.eq_univ_of_forall
    intro y
    exact ⟨e.symm y, Set.mem_univ _, by simp⟩

noncomputable def regionIsUnivReadout
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (kind : PacketPlaceKind)
    (H : FixedStagePacketTopologicalTransportRaw Packet) :
    SourceAdmissibleRegionReadout kind H := by
  classical
  exact fun _ R => if R.1 = Set.univ then 2 else 1

theorem region_is_univ_readout_is_homeomorph_compatible
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (kind : PacketPlaceKind)
    (H : FixedStagePacketTopologicalTransportRaw Packet) :
    SourceAdmissibleReadoutCompatible kind H
      (regionIsUnivReadout kind H) := by
  classical
  intro j R
  unfold regionIsUnivReadout
  exact if_congr
    (equiv_image_eq_univ_iff (H.toRegionTransport.packetEquiv j) R.1)
    rfl rfl

theorem bool_region_is_univ_readout_is_nonconstant :
    regionIsUnivReadout .nonarch boolNotTopologicalTransport 0
        (boolFalseNonarchRegion 0) ≠
      regionIsUnivReadout .nonarch boolNotTopologicalTransport 0
        (boolUnivNonarchRegion 0) := by
  have hne : ({false} : Set Bool) ≠ ({false, true} : Set Bool) := by
    intro h
    have htrue : true ∈ ({false} : Set Bool) := by
      rw [h]
      simp
    simp at htrue
  simp [regionIsUnivReadout, boolFalseNonarchRegion,
    boolUnivNonarchRegion, hne]

noncomputable def boolFalseMembershipAdmissibleReadout :
    SourceAdmissibleRegionReadout .nonarch boolNotTopologicalTransport := by
  classical
  exact fun _ R => if false ∈ R.1 then 1 else 0

theorem bool_false_membership_readout_is_not_homeomorph_compatible :
    ¬ SourceAdmissibleReadoutCompatible .nonarch boolNotTopologicalTransport
      boolFalseMembershipAdmissibleReadout := by
  classical
  intro h
  have heq := h 0 (boolFalseNonarchRegion 0)
  dsimp [boolFalseMembershipAdmissibleReadout,
    transportSourceAdmissiblePacketRegion, boolFalseNonarchRegion] at heq
  have hnot : false ∉
      boolNotTopologicalTransport.packetHomeomorph 0 '' ({false} : Set Bool) := by
    rintro ⟨x, hx, hxmap⟩
    have hxf : x = false := by simpa using hx
    subst x
    have hmove :
        boolNotTopologicalTransport.packetHomeomorph 0 false = true := rfl
    rw [hmove] at hxmap
    exact Bool.noConfusion hxmap
  rw [if_neg hnot] at heq
  norm_num at heq

noncomputable def totalNonemptyExtensionZero (_j : Fin 2)
    (S : Set Bool) : Real := by
  classical
  exact if S.Nonempty then 1 else 0

noncomputable def totalNonemptyExtensionSeven (_j : Fin 2)
    (S : Set Bool) : Real := by
  classical
  exact if S.Nonempty then 1 else 7

theorem two_total_extensions_agree_on_every_source_admissible_region
    (j : Fin 2)
    (R : SourceAdmissiblePacketRegion .nonarch
      boolNotTopologicalTransport j) :
    totalNonemptyExtensionZero j R.1 = totalNonemptyExtensionSeven j R.1 := by
  have hne : R.1.Nonempty := R.2.1
  simp [totalNonemptyExtensionZero, totalNonemptyExtensionSeven, hne]

theorem two_total_extensions_disagree_outside_source_domain :
    totalNonemptyExtensionZero 0 (∅ : Set Bool) ≠
      totalNonemptyExtensionSeven 0 ∅ := by
  norm_num [totalNonemptyExtensionZero, totalNonemptyExtensionSeven]

def restrictBoolNonarchTotalReadout
    (F : (j : Fin 2) -> Set Bool -> Real) :
    SourceAdmissibleRegionReadout .nonarch boolNotTopologicalTransport :=
  fun j R => F j R.1

theorem restriction_to_source_admissible_domain_is_not_injective :
    ¬ Function.Injective restrictBoolNonarchTotalReadout := by
  intro hinj
  have hrestricted :
      restrictBoolNonarchTotalReadout totalNonemptyExtensionZero =
        restrictBoolNonarchTotalReadout totalNonemptyExtensionSeven := by
    funext j R
    exact two_total_extensions_agree_on_every_source_admissible_region j R
  have htotal := hinj hrestricted
  exact two_total_extensions_disagree_outside_source_domain
    (congrArg (fun F => F 0 (∅ : Set Bool)) htotal)

end CitedLV.Theorem311
