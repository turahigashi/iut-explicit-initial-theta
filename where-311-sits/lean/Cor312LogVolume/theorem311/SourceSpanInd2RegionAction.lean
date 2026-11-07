import Cor312LogVolume.theorem311.SourceSpanInd2PacketAction
import Cor312LogVolume.theorem311.FixedStageRegionMeanInvariance

namespace CitedLV.Theorem311

universe uBase uAbove uStrip uK uAllowed uPacket

structure SourceProcessionInd2Realization
    {Strip : Type uStrip} {n : Nat}
    (P : DPrimeStripProcessionCandidate Strip (n + 1))
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {arity : Strip -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (Q : SourceShapedLocalMonoanalyticQSpanRaw Base Above Strip arity K)
    (vQ : Base) where
  stage : (j : Fin n) ->
    SourceSpanInd2Realization.{uBase,uAbove,uStrip,uK,uAllowed}
      Q (finalNonzeroProcessionLabel P j) vQ

abbrev SourceProcessionInd2Choice
    {Strip : Type uStrip} {n : Nat}
    {P : DPrimeStripProcessionCandidate Strip (n + 1)}
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {arity : Strip -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    {Q : SourceShapedLocalMonoanalyticQSpanRaw Base Above Strip arity K}
    {vQ : Base}
    (R : SourceProcessionInd2Realization.{uBase,uAbove,uStrip,uK,uAllowed}
      P Q vQ) :=
  (j : Fin n) -> SourceSpanInd2Choice (R.stage j)

noncomputable def sourceProcessionInd2RegionTransport
    {Strip : Type uStrip} {n : Nat}
    (P : DPrimeStripProcessionCandidate Strip (n + 1))
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {arity : Strip -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (Q : SourceShapedLocalMonoanalyticQSpanRaw Base Above Strip arity K)
    (vQ : Base)
    (R : SourceProcessionInd2Realization.{uBase,uAbove,uStrip,uK,uAllowed}
      P Q vQ)
    (a : SourceProcessionInd2Choice R) :
    FixedStagePacketRegionTransportRaw (SourceProcessionPacketQ P Q vQ) where
  packetEquiv := fun j =>
    (sourceSpanInd2PacketEquiv Q (finalNonzeroProcessionLabel P j) vQ
      (R.stage j) (a j)).toEquiv

theorem sourceProcessionInd2RegionTransport_apply
    {Strip : Type uStrip} {n : Nat}
    (P : DPrimeStripProcessionCandidate Strip (n + 1))
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {arity : Strip -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (Q : SourceShapedLocalMonoanalyticQSpanRaw Base Above Strip arity K)
    (vQ : Base)
    (R : SourceProcessionInd2Realization.{uBase,uAbove,uStrip,uK,uAllowed}
      P Q vQ)
    (a : SourceProcessionInd2Choice R)
    (j : Fin n) (x : SourceProcessionPacketQ P Q vQ j) :
    (sourceProcessionInd2RegionTransport P Q vQ R a).packetEquiv j x =
      sourceSpanInd2PacketEquiv Q (finalNonzeroProcessionLabel P j) vQ
        (R.stage j) (a j) x :=
  rfl

def RegionAdmissibilityPreservedUnder
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (Admissible : (j : Fin n) -> Set (Packet j) -> Prop)
    (T : FixedStagePacketRegionTransportRaw Packet) : Prop :=
  ∀ j S, Admissible j S -> Admissible j (T.packetEquiv j '' S)

theorem fixed_stage_transport_preserves_selected_admissibility
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (Admissible : (j : Fin n) -> Set (Packet j) -> Prop)
    (readout : ProcessionRegionReadout Packet)
    (T : FixedStagePacketRegionTransportRaw Packet)
    (hpres : RegionAdmissibilityPreservedUnder Admissible T)
    (region : ProcessionRegionProfile Packet)
    (hregion : SelectedRegionsAdmissible Admissible
      (regionProfileLogVolumeRaw readout region)) :
    SelectedRegionsAdmissible Admissible
      (regionProfileLogVolumeRaw readout (transportRegionProfile T region)) := by
  intro j
  exact hpres j (region j) (hregion j)

theorem transportRegionProfile_injective
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (T : FixedStagePacketRegionTransportRaw Packet) :
    Function.Injective (transportRegionProfile T) := by
  intro R S hRS
  funext j
  apply Set.ext
  intro x
  have hj := congrFun hRS j
  change T.packetEquiv j '' R j = T.packetEquiv j '' S j at hj
  constructor
  · intro hx
    have himage : T.packetEquiv j x ∈ T.packetEquiv j '' R j :=
      ⟨x, hx, rfl⟩
    rw [hj] at himage
    rcases himage with ⟨y, hy, heq⟩
    have hyx : y = x := (T.packetEquiv j).injective heq
    simpa [hyx] using hy
  · intro hx
    have himage : T.packetEquiv j x ∈ T.packetEquiv j '' S j :=
      ⟨x, hx, rfl⟩
    rw [← hj] at himage
    rcases himage with ⟨y, hy, heq⟩
    have hyx : y = x := (T.packetEquiv j).injective heq
    simpa [hyx] using hy

def nonemptyRegionAdmissible
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (_j : Fin n) (S : Set (Packet _j)) : Prop :=
  S.Nonempty

theorem every_equiv_preserves_nonempty_region_admissibility
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (T : FixedStagePacketRegionTransportRaw Packet) :
    RegionAdmissibilityPreservedUnder nonemptyRegionAdmissible T := by
  intro j S hS
  rcases hS with ⟨x, hx⟩
  exact ⟨T.packetEquiv j x, x, hx, rfl⟩

noncomputable def nonemptyIndicatorReadout
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (_j : Fin n) (S : Set (Packet _j)) : Real := by
  classical
  exact if S.Nonempty then 1 else 0

theorem every_equiv_preserves_nonempty_indicator_readout
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (T : FixedStagePacketRegionTransportRaw Packet) :
    RegionReadoutInvariantUnder nonemptyIndicatorReadout T := by
  classical
  intro j S
  have himage : (T.packetEquiv j '' S).Nonempty ↔ S.Nonempty := by
    constructor
    · rintro ⟨y, x, hx, rfl⟩
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨T.packetEquiv j x, x, hx, rfl⟩
  exact if_congr himage rfl rfl

theorem source_procession_ind2_preserves_admissibility_and_mean
    {Strip : Type uStrip} {n : Nat}
    (P : DPrimeStripProcessionCandidate Strip (n + 1))
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {arity : Strip -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (Q : SourceShapedLocalMonoanalyticQSpanRaw Base Above Strip arity K)
    (vQ : Base)
    (R : SourceProcessionInd2Realization.{uBase,uAbove,uStrip,uK,uAllowed}
      P Q vQ)
    (a : SourceProcessionInd2Choice R)
    (Admissible : (j : Fin n) ->
      Set (SourceProcessionPacketQ P Q vQ j) -> Prop)
    (readout : ProcessionRegionReadout (SourceProcessionPacketQ P Q vQ))
    (region : ProcessionRegionProfile (SourceProcessionPacketQ P Q vQ))
    (hpres : RegionAdmissibilityPreservedUnder Admissible
      (sourceProcessionInd2RegionTransport P Q vQ R a))
    (hinv : RegionReadoutInvariantUnder readout
      (sourceProcessionInd2RegionTransport P Q vQ R a))
    (hregion : SelectedRegionsAdmissible Admissible
      (regionProfileLogVolumeRaw readout region)) :
    SelectedRegionsAdmissible Admissible
        (regionProfileLogVolumeRaw readout
          (transportRegionProfile
            (sourceProcessionInd2RegionTransport P Q vQ R a) region)) /\
      regionProfileNormalizedLogVolume readout
          (transportRegionProfile
            (sourceProcessionInd2RegionTransport P Q vQ R a) region) =
        regionProfileNormalizedLogVolume readout region := by
  exact ⟨fixed_stage_transport_preserves_selected_admissibility
      Admissible readout _ hpres region hregion,
    fixed_stage_transport_preserves_normalized_mean readout _ hinv region⟩

def visibleUnitLengthTwoProcession :
    DPrimeStripProcessionCandidate Unit 2 where
  stage := fun _ => { component := fun _ => () }

noncomputable def visibleUnitProcessionInd2 :
    SourceProcessionInd2Realization visibleUnitLengthTwoProcession
      visibleUnitSourceSpan () where
  stage := fun _ => visibleBoolInd2Realization

def visibleUnitProcessionNegChoice :
    SourceProcessionInd2Choice visibleUnitProcessionInd2 :=
  fun _ => visibleNegInd2Choice

noncomputable def visibleUnitProcessionInd2Transport :
    FixedStagePacketRegionTransportRaw
      (SourceProcessionPacketQ visibleUnitLengthTwoProcession
        visibleUnitSourceSpan ()) :=
  sourceProcessionInd2RegionTransport visibleUnitLengthTwoProcession
    visibleUnitSourceSpan () visibleUnitProcessionInd2
    visibleUnitProcessionNegChoice

def visibleUnitSelectedRegion :
    ProcessionRegionProfile
      (SourceProcessionPacketQ visibleUnitLengthTwoProcession
        visibleUnitSourceSpan ()) :=
  fun _ => {visibleUnitPurePacket}

theorem visible_unit_procession_transport_moves_region :
    transportRegionProfile visibleUnitProcessionInd2Transport
        visibleUnitSelectedRegion ≠
      visibleUnitSelectedRegion := by
  intro h
  have hstage := congrFun h (0 : Fin 1)
  have hmem :
      sourceSpanInd2PacketEquiv visibleUnitSourceSpan () ()
          visibleBoolInd2Realization visibleNegInd2Choice
          visibleUnitPurePacket ∈
        transportRegionProfile visibleUnitProcessionInd2Transport
          visibleUnitSelectedRegion 0 := by
    exact ⟨visibleUnitPurePacket, by simp [visibleUnitSelectedRegion], rfl⟩
  rw [hstage] at hmem
  have heq :
      sourceSpanInd2PacketEquiv visibleUnitSourceSpan () ()
          visibleBoolInd2Realization visibleNegInd2Choice
          visibleUnitPurePacket = visibleUnitPurePacket := by
    simpa [visibleUnitSelectedRegion] using hmem
  exact visible_neg_ind2_moves_packet heq

def containsVisiblePacketAdmissible
    (_j : Fin 1)
    (S : Set (SourceProcessionPacketQ visibleUnitLengthTwoProcession
      visibleUnitSourceSpan () _j)) : Prop :=
  visibleUnitPurePacket ∈ S

theorem visible_selected_region_contains_anchor :
    SelectedRegionsAdmissible containsVisiblePacketAdmissible
      (regionProfileLogVolumeRaw (fun _ _ => 0) visibleUnitSelectedRegion) := by
  intro j
  change visibleUnitPurePacket ∈ visibleUnitSelectedRegion j
  simp [visibleUnitSelectedRegion]

theorem transported_visible_region_does_not_contain_anchor :
    ¬ containsVisiblePacketAdmissible 0
      (transportRegionProfile visibleUnitProcessionInd2Transport
        visibleUnitSelectedRegion 0) := by
  rintro ⟨x, hx, heq⟩
  have hx' : x = visibleUnitPurePacket := by
    simpa [visibleUnitSelectedRegion] using hx
  subst x
  exact visible_neg_ind2_moves_packet heq

theorem algebraic_ind2_does_not_force_arbitrary_admissibility :
    ¬ RegionAdmissibilityPreservedUnder containsVisiblePacketAdmissible
      visibleUnitProcessionInd2Transport := by
  intro h
  exact transported_visible_region_does_not_contain_anchor
    (h 0 (visibleUnitSelectedRegion 0)
      (by simp [containsVisiblePacketAdmissible, visibleUnitSelectedRegion]))

noncomputable def visibleAnchorReadout
    (_j : Fin 1)
    (S : Set (SourceProcessionPacketQ visibleUnitLengthTwoProcession
      visibleUnitSourceSpan () _j)) : Real := by
  classical
  exact if visibleUnitPurePacket ∈ S then 1 else 0

theorem algebraic_ind2_does_not_force_readout_invariance :
    ¬ RegionReadoutInvariantUnder visibleAnchorReadout
      visibleUnitProcessionInd2Transport := by
  intro h
  have heq := h 0 (visibleUnitSelectedRegion 0)
  have hnot := transported_visible_region_does_not_contain_anchor
  have hnot' :
      visibleUnitPurePacket ∉
        (visibleUnitProcessionInd2Transport.packetEquiv 0 :
          SourceProcessionPacketQ visibleUnitLengthTwoProcession
              visibleUnitSourceSpan () 0 ->
            SourceProcessionPacketQ visibleUnitLengthTwoProcession
              visibleUnitSourceSpan () 0) ''
          visibleUnitSelectedRegion 0 := by
    simpa [containsVisiblePacketAdmissible, transportRegionProfile] using hnot
  simp only [visibleAnchorReadout] at heq
  rw [if_neg hnot'] at heq
  have hmem : visibleUnitPurePacket ∈ visibleUnitSelectedRegion 0 := by
    simp [visibleUnitSelectedRegion]
  rw [if_pos hmem] at heq
  norm_num at heq

theorem visible_ind2_readout_invariance_does_not_supply_pointed_admissibility :
    RegionReadoutInvariantUnder nonemptyIndicatorReadout
        visibleUnitProcessionInd2Transport /\
      ¬ RegionAdmissibilityPreservedUnder containsVisiblePacketAdmissible
        visibleUnitProcessionInd2Transport :=
  ⟨every_equiv_preserves_nonempty_indicator_readout _,
    algebraic_ind2_does_not_force_arbitrary_admissibility⟩

theorem visible_ind2_nonempty_admissibility_does_not_supply_anchor_invariance :
    RegionAdmissibilityPreservedUnder nonemptyRegionAdmissible
        visibleUnitProcessionInd2Transport /\
      ¬ RegionReadoutInvariantUnder visibleAnchorReadout
        visibleUnitProcessionInd2Transport :=
  ⟨every_equiv_preserves_nonempty_region_admissibility _,
    algebraic_ind2_does_not_force_readout_invariance⟩

end CitedLV.Theorem311
