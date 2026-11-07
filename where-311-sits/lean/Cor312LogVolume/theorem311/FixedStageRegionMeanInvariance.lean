import Cor312LogVolume.theorem311.ProcessionNormalizedLogVolume
import Cor312LogVolume.theorem311.IndeterminacyQuotientTransport

namespace CitedLV.Theorem311

universe uPacket uInd1 uInd2

abbrev ProcessionRegionProfile
    {n : Nat} (Packet : Fin n -> Type uPacket) :=
  (j : Fin n) -> Set (Packet j)

abbrev ProcessionRegionReadout
    {n : Nat} (Packet : Fin n -> Type uPacket) :=
  (j : Fin n) -> Set (Packet j) -> Real

def regionProfileLogVolumeRaw
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (readout : ProcessionRegionReadout Packet)
    (region : ProcessionRegionProfile Packet) :
    ProcessionPacketLogVolumeRaw Packet where
  region := region
  packetLogVolume := readout

noncomputable def regionProfileNormalizedLogVolume
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (readout : ProcessionRegionReadout Packet)
    (region : ProcessionRegionProfile Packet) : Real :=
  processionNormalizedLogVolume (regionProfileLogVolumeRaw readout region)

structure FixedStagePacketRegionTransportRaw
    {n : Nat} (Packet : Fin n -> Type uPacket) where
  packetEquiv : (j : Fin n) -> Packet j ≃ Packet j

def transportRegionProfile
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (T : FixedStagePacketRegionTransportRaw Packet)
    (region : ProcessionRegionProfile Packet) :
    ProcessionRegionProfile Packet :=
  fun j => T.packetEquiv j '' region j

def RegionReadoutInvariantUnder
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (readout : ProcessionRegionReadout Packet)
    (T : FixedStagePacketRegionTransportRaw Packet) : Prop :=
  ∀ j S, readout j (T.packetEquiv j '' S) = readout j S

theorem fixed_stage_transport_preserves_packet_values
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (readout : ProcessionRegionReadout Packet)
    (T : FixedStagePacketRegionTransportRaw Packet)
    (hinv : RegionReadoutInvariantUnder readout T)
    (region : ProcessionRegionProfile Packet) (j : Fin n) :
    processionPacketValue
        (regionProfileLogVolumeRaw readout (transportRegionProfile T region)) j =
      processionPacketValue (regionProfileLogVolumeRaw readout region) j := by
  exact hinv j (region j)

theorem fixed_stage_transport_preserves_normalized_mean
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (readout : ProcessionRegionReadout Packet)
    (T : FixedStagePacketRegionTransportRaw Packet)
    (hinv : RegionReadoutInvariantUnder readout T)
    (region : ProcessionRegionProfile Packet) :
    regionProfileNormalizedLogVolume readout (transportRegionProfile T region) =
      regionProfileNormalizedLogVolume readout region := by
  unfold regionProfileNormalizedLogVolume processionNormalizedLogVolume
  congr 1
  funext j
  exact fixed_stage_transport_preserves_packet_values readout T hinv region j

structure ProcessionRegionAmbiguityActionsRaw
    {n : Nat} (Packet : Fin n -> Type uPacket) where
  Ind1Choice : Type uInd1
  Ind2Choice : Type uInd2
  ind1Transport : Ind1Choice -> FixedStagePacketRegionTransportRaw Packet
  ind2Transport : Ind2Choice -> FixedStagePacketRegionTransportRaw Packet

def regionProfileAmbiguity
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (A : ProcessionRegionAmbiguityActionsRaw Packet) :
    AmbiguityGenerators (fun _ : Unit => ProcessionRegionProfile Packet) where
  ind1Step := fun _ x y =>
    ∃ a : A.Ind1Choice, y = transportRegionProfile (A.ind1Transport a) x
  ind2Step := fun _ x y =>
    ∃ a : A.Ind2Choice, y = transportRegionProfile (A.ind2Transport a) x

def RegionReadoutInvariantUnderInd1
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (A : ProcessionRegionAmbiguityActionsRaw Packet)
    (readout : ProcessionRegionReadout Packet) : Prop :=
  ∀ a, RegionReadoutInvariantUnder readout (A.ind1Transport a)

def RegionReadoutInvariantUnderInd2
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (A : ProcessionRegionAmbiguityActionsRaw Packet)
    (readout : ProcessionRegionReadout Packet) : Prop :=
  ∀ a, RegionReadoutInvariantUnder readout (A.ind2Transport a)

noncomputable def regionProfileMeanObservable
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (A : ProcessionRegionAmbiguityActionsRaw Packet)
    (readout : ProcessionRegionReadout Packet)
    (h1 : RegionReadoutInvariantUnderInd1 A readout)
    (h2 : RegionReadoutInvariantUnderInd2 A readout) :
    AmbiguityObservable (regionProfileAmbiguity A) (fun _ : Unit => Real) where
  observe := fun _ region => regionProfileNormalizedLogVolume readout region
  ind1Invariant := by
    intro p x y h
    rcases h with ⟨a, rfl⟩
    exact (fixed_stage_transport_preserves_normalized_mean
      readout (A.ind1Transport a) (h1 a) x).symm
  ind2Invariant := by
    intro p x y h
    rcases h with ⟨a, rfl⟩
    exact (fixed_stage_transport_preserves_normalized_mean
      readout (A.ind2Transport a) (h2 a) x).symm

abbrev boolStagePacket (_ : Fin 2) := Bool

def boolNotEquiv : Bool ≃ Bool where
  toFun := fun b => !b
  invFun := fun b => !b
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro b; cases b <;> rfl

def allStagesNotTransport :
    FixedStagePacketRegionTransportRaw boolStagePacket where
  packetEquiv := fun _ => boolNotEquiv

def zeroStageNotTransport :
    FixedStagePacketRegionTransportRaw boolStagePacket where
  packetEquiv := fun j =>
    if j = 0 then boolNotEquiv else Equiv.refl Bool

def checkRegionActions :
    ProcessionRegionAmbiguityActionsRaw boolStagePacket where
  Ind1Choice := Unit
  Ind2Choice := Unit
  ind1Transport := fun _ => allStagesNotTransport
  ind2Transport := fun _ => zeroStageNotTransport

noncomputable def nonemptyStageReadout
    (j : Fin 2) (S : Set Bool) : Real := by
  classical
  exact if S.Nonempty then (j.val + 1 : Nat) else 0

noncomputable def falseMembershipReadout
    (_j : Fin 2) (S : Set Bool) : Real := by
  classical
  exact if false ∈ S then 1 else 0

def falseSingletonRegion : ProcessionRegionProfile boolStagePacket :=
  fun _ => {false}

theorem nonempty_readout_invariant_under_every_transport
    (T : FixedStagePacketRegionTransportRaw boolStagePacket) :
    RegionReadoutInvariantUnder nonemptyStageReadout T := by
  classical
  intro j S
  simp only [nonemptyStageReadout]
  have himage : ((T.packetEquiv j : Bool -> Bool) '' S).Nonempty ↔
      S.Nonempty := by
    constructor
    · rintro ⟨y, x, hx, rfl⟩
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨T.packetEquiv j x, x, hx, rfl⟩
  exact if_congr himage rfl rfl

theorem nonempty_readout_invariant_under_all_not :
    RegionReadoutInvariantUnder nonemptyStageReadout
      allStagesNotTransport :=
  nonempty_readout_invariant_under_every_transport allStagesNotTransport

theorem nonempty_readout_invariant_under_zero_stage_not :
    RegionReadoutInvariantUnder nonemptyStageReadout
      zeroStageNotTransport :=
  nonempty_readout_invariant_under_every_transport zeroStageNotTransport

theorem check_readout_ind1_invariant :
    RegionReadoutInvariantUnderInd1 checkRegionActions
      nonemptyStageReadout := by
  intro a
  rcases a with ⟨⟩
  exact nonempty_readout_invariant_under_all_not

theorem check_readout_ind2_invariant :
    RegionReadoutInvariantUnderInd2 checkRegionActions
      nonemptyStageReadout := by
  intro a
  rcases a with ⟨⟩
  exact nonempty_readout_invariant_under_zero_stage_not

theorem all_not_actually_moves_selected_regions :
    transportRegionProfile allStagesNotTransport falseSingletonRegion ≠
      falseSingletonRegion := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  have hmem : true ∈
      transportRegionProfile allStagesNotTransport falseSingletonRegion 0 := by
    exact ⟨false, by simp [falseSingletonRegion], rfl⟩
  rw [h0] at hmem
  simpa [falseSingletonRegion] using hmem

theorem zero_stage_not_actually_moves_selected_regions :
    transportRegionProfile zeroStageNotTransport falseSingletonRegion ≠
      falseSingletonRegion := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  have hmem : true ∈
      transportRegionProfile zeroStageNotTransport falseSingletonRegion 0 := by
    exact ⟨false, by simp [falseSingletonRegion], by
      simp [zeroStageNotTransport, boolNotEquiv]⟩
  rw [h0] at hmem
  simpa [falseSingletonRegion] using hmem

theorem ind1_and_ind2_move_profiles_differ :
    transportRegionProfile allStagesNotTransport falseSingletonRegion ≠
      transportRegionProfile zeroStageNotTransport falseSingletonRegion := by
  intro h
  have h1 := congrFun h (1 : Fin 2)
  have hmem : true ∈
      transportRegionProfile allStagesNotTransport falseSingletonRegion 1 := by
    exact ⟨false, by simp [falseSingletonRegion], rfl⟩
  rw [h1] at hmem
  simpa [transportRegionProfile, zeroStageNotTransport,
    falseSingletonRegion] using hmem

theorem false_membership_readout_not_invariant_under_all_not :
    ¬ RegionReadoutInvariantUnder falseMembershipReadout
      allStagesNotTransport := by
  intro h
  have hbad := h (0 : Fin 2) ({false} : Set Bool)
  have himage : boolNotEquiv '' ({false} : Set Bool) = {true} := by
    ext b
    cases b <;> simp [boolNotEquiv]
  change falseMembershipReadout 0 (boolNotEquiv '' {false}) =
    falseMembershipReadout 0 {false} at hbad
  rw [himage] at hbad
  norm_num [falseMembershipReadout] at hbad

theorem check_normalized_mean_invariant_under_ind1 :
    regionProfileNormalizedLogVolume nonemptyStageReadout
        (transportRegionProfile allStagesNotTransport falseSingletonRegion) =
      regionProfileNormalizedLogVolume nonemptyStageReadout
        falseSingletonRegion :=
  fixed_stage_transport_preserves_normalized_mean nonemptyStageReadout
    allStagesNotTransport nonempty_readout_invariant_under_all_not
    falseSingletonRegion

noncomputable def checkMeanObservable :=
  regionProfileMeanObservable checkRegionActions nonemptyStageReadout
    check_readout_ind1_invariant check_readout_ind2_invariant

def emptyStageRegion : ProcessionRegionProfile boolStagePacket :=
  fun _ => ∅

theorem selected_nonempty_region_mean_is_three_halves :
    regionProfileNormalizedLogVolume nonemptyStageReadout
      falseSingletonRegion = (3 : Real) / 2 := by
  norm_num [regionProfileNormalizedLogVolume,
    processionNormalizedLogVolume, ordinaryFinMean,
    processionPacketValue, regionProfileLogVolumeRaw,
    nonemptyStageReadout, falseSingletonRegion, Fin.sum_univ_two]

theorem empty_region_mean_is_zero :
    regionProfileNormalizedLogVolume nonemptyStageReadout
      emptyStageRegion = 0 := by
  norm_num [regionProfileNormalizedLogVolume,
    processionNormalizedLogVolume, ordinaryFinMean,
    processionPacketValue, regionProfileLogVolumeRaw,
    nonemptyStageReadout, emptyStageRegion, Fin.sum_univ_two]

theorem check_mean_observable_separates_two_quotient_classes :
    (Quotient.mk _ falseSingletonRegion :
        RLGPAmbiguityQuotientV2 (regionProfileAmbiguity checkRegionActions) ()) ≠
      Quotient.mk _ emptyStageRegion := by
  intro h
  have hvalue := congrArg (quotientObservable checkMeanObservable ()) h
  rw [quotient_observable_on_representative,
    quotient_observable_on_representative] at hvalue
  change regionProfileNormalizedLogVolume nonemptyStageReadout
      falseSingletonRegion =
    regionProfileNormalizedLogVolume nonemptyStageReadout emptyStageRegion
    at hvalue
  rw [selected_nonempty_region_mean_is_three_halves,
    empty_region_mean_is_zero] at hvalue
  norm_num at hvalue

end CitedLV.Theorem311
