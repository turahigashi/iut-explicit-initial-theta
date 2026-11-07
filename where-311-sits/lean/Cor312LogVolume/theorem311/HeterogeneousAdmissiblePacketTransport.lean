import Cor312LogVolume.theorem311.AdmissiblePacketLogVolume

namespace CitedLV.Theorem311

universe uX uY

structure HeterogeneousStagewiseHomeomorphRaw
    {n : Nat} (PacketX : Fin n -> Type uX) (PacketY : Fin n -> Type uY) where
  sourceTopology : (j : Fin n) -> TopologicalSpace (PacketX j)
  targetTopology : (j : Fin n) -> TopologicalSpace (PacketY j)
  packetHomeomorph : (j : Fin n) ->
    @Homeomorph (PacketX j) (PacketY j)
      (sourceTopology j) (targetTopology j)

def PacketRegionAdmissibleForTopology
    {n : Nat} {Packet : Fin n -> Type uX}
    (kind : PacketPlaceKind)
    (topology : (j : Fin n) -> TopologicalSpace (Packet j))
    (j : Fin n) (K : Set (Packet j)) : Prop :=
  letI : TopologicalSpace (Packet j) := topology j
  match kind with
  | .nonarch => K.Nonempty ∧ IsCompact K ∧ IsOpen K
  | .arch => ∃ U : Set (Packet j),
      U.Nonempty ∧ IsOpen U ∧ IsCompact (closure U) ∧ K = closure U

abbrev HeterogeneousSourceAdmissibleRegion
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (j : Fin n) :=
  {K : Set (PacketX j) //
    PacketRegionAdmissibleForTopology kind H.sourceTopology j K}

abbrev HeterogeneousTargetAdmissibleRegion
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (j : Fin n) :=
  {K : Set (PacketY j) //
    PacketRegionAdmissibleForTopology kind H.targetTopology j K}

theorem heterogeneous_homeomorph_preserves_nonarch_admissibility
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (j : Fin n) (K : Set (PacketX j))
    (hK : PacketRegionAdmissibleForTopology .nonarch
      H.sourceTopology j K) :
    PacketRegionAdmissibleForTopology .nonarch H.targetTopology j
      (H.packetHomeomorph j '' K) := by
  letI : TopologicalSpace (PacketX j) := H.sourceTopology j
  letI : TopologicalSpace (PacketY j) := H.targetTopology j
  change K.Nonempty ∧ IsCompact K ∧ IsOpen K at hK
  change (H.packetHomeomorph j '' K).Nonempty ∧
    IsCompact (H.packetHomeomorph j '' K) ∧
      IsOpen (H.packetHomeomorph j '' K)
  exact ⟨Set.image_nonempty.mpr hK.1,
    (H.packetHomeomorph j).isCompact_image.mpr hK.2.1,
    (H.packetHomeomorph j).isOpenMap K hK.2.2⟩

theorem heterogeneous_homeomorph_preserves_arch_admissibility
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (j : Fin n) (K : Set (PacketX j))
    (hK : PacketRegionAdmissibleForTopology .arch
      H.sourceTopology j K) :
    PacketRegionAdmissibleForTopology .arch H.targetTopology j
      (H.packetHomeomorph j '' K) := by
  letI : TopologicalSpace (PacketX j) := H.sourceTopology j
  letI : TopologicalSpace (PacketY j) := H.targetTopology j
  change ∃ U : Set (PacketX j),
    U.Nonempty ∧ IsOpen U ∧ IsCompact (closure U) ∧ K = closure U at hK
  change ∃ V : Set (PacketY j),
    V.Nonempty ∧ IsOpen V ∧ IsCompact (closure V) ∧
      H.packetHomeomorph j '' K = closure V
  rcases hK with ⟨U, hne, hopen, hcompact, rfl⟩
  refine ⟨H.packetHomeomorph j '' U, ?_, ?_, ?_, ?_⟩
  · exact Set.image_nonempty.mpr hne
  · exact (H.packetHomeomorph j).isOpenMap U hopen
  · rw [← (H.packetHomeomorph j).image_closure]
    exact (H.packetHomeomorph j).isCompact_image.mpr hcompact
  · exact (H.packetHomeomorph j).image_closure U

theorem heterogeneous_homeomorph_preserves_admissibility
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (j : Fin n) (K : Set (PacketX j))
    (hK : PacketRegionAdmissibleForTopology kind H.sourceTopology j K) :
    PacketRegionAdmissibleForTopology kind H.targetTopology j
      (H.packetHomeomorph j '' K) := by
  cases kind with
  | nonarch =>
      exact heterogeneous_homeomorph_preserves_nonarch_admissibility
        H j K hK
  | arch =>
      exact heterogeneous_homeomorph_preserves_arch_admissibility
        H j K hK

def transportHeterogeneousAdmissibleRegion
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (j : Fin n) (R : HeterogeneousSourceAdmissibleRegion kind H j) :
    HeterogeneousTargetAdmissibleRegion kind H j :=
  ⟨H.packetHomeomorph j '' R.1,
    heterogeneous_homeomorph_preserves_admissibility kind H j R.1 R.2⟩

theorem transport_heterogeneous_admissible_region_injective
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (j : Fin n) :
    Function.Injective (transportHeterogeneousAdmissibleRegion kind H j) := by
  letI : TopologicalSpace (PacketX j) := H.sourceTopology j
  letI : TopologicalSpace (PacketY j) := H.targetTopology j
  intro R S hRS
  apply Subtype.ext
  have himage : H.packetHomeomorph j '' R.1 =
      H.packetHomeomorph j '' S.1 := congrArg Subtype.val hRS
  apply Set.ext
  intro x
  constructor
  · intro hx
    have hex : H.packetHomeomorph j x ∈ H.packetHomeomorph j '' S.1 := by
      rw [← himage]
      exact ⟨x, hx, rfl⟩
    rcases hex with ⟨y, hy, hyx⟩
    have : y = x := (H.packetHomeomorph j).injective hyx
    simpa [this] using hy
  · intro hx
    have hex : H.packetHomeomorph j x ∈ H.packetHomeomorph j '' R.1 := by
      rw [himage]
      exact ⟨x, hx, rfl⟩
    rcases hex with ⟨y, hy, hyx⟩
    have : y = x := (H.packetHomeomorph j).injective hyx
    simpa [this] using hy

abbrev HeterogeneousSourceAdmissibleProfile
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY) :=
  (j : Fin n) -> HeterogeneousSourceAdmissibleRegion kind H j

abbrev HeterogeneousTargetAdmissibleProfile
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY) :=
  (j : Fin n) -> HeterogeneousTargetAdmissibleRegion kind H j

abbrev HeterogeneousSourceAdmissibleReadout
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY) :=
  (j : Fin n) -> HeterogeneousSourceAdmissibleRegion kind H j -> Real

abbrev HeterogeneousTargetAdmissibleReadout
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY) :=
  (j : Fin n) -> HeterogeneousTargetAdmissibleRegion kind H j -> Real

def transportHeterogeneousAdmissibleProfile
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (profile : HeterogeneousSourceAdmissibleProfile kind H) :
    HeterogeneousTargetAdmissibleProfile kind H :=
  fun j => transportHeterogeneousAdmissibleRegion kind H j (profile j)

def HeterogeneousAdmissibleReadoutCompatible
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (sourceReadout : HeterogeneousSourceAdmissibleReadout kind H)
    (targetReadout : HeterogeneousTargetAdmissibleReadout kind H) : Prop :=
  ∀ j R, targetReadout j (transportHeterogeneousAdmissibleRegion kind H j R) =
    sourceReadout j R

noncomputable def heterogeneousSourcePacketValue
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    {kind : PacketPlaceKind}
    {H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY}
    (sourceReadout : HeterogeneousSourceAdmissibleReadout kind H)
    (profile : HeterogeneousSourceAdmissibleProfile kind H)
    (j : Fin n) : Real :=
  sourceReadout j (profile j)

noncomputable def heterogeneousTargetPacketValue
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    {kind : PacketPlaceKind}
    {H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY}
    (targetReadout : HeterogeneousTargetAdmissibleReadout kind H)
    (profile : HeterogeneousTargetAdmissibleProfile kind H)
    (j : Fin n) : Real :=
  targetReadout j (profile j)

theorem heterogeneous_compatible_packet_values
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (sourceReadout : HeterogeneousSourceAdmissibleReadout kind H)
    (targetReadout : HeterogeneousTargetAdmissibleReadout kind H)
    (hcompat : HeterogeneousAdmissibleReadoutCompatible kind H
      sourceReadout targetReadout)
    (profile : HeterogeneousSourceAdmissibleProfile kind H)
    (j : Fin n) :
    heterogeneousTargetPacketValue targetReadout
        (transportHeterogeneousAdmissibleProfile kind H profile) j =
      heterogeneousSourcePacketValue sourceReadout profile j :=
  hcompat j (profile j)

noncomputable def heterogeneousSourceNormalizedMean
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    {kind : PacketPlaceKind}
    {H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY}
    (sourceReadout : HeterogeneousSourceAdmissibleReadout kind H)
    (profile : HeterogeneousSourceAdmissibleProfile kind H) : Real :=
  ordinaryFinMean (fun j => heterogeneousSourcePacketValue sourceReadout profile j)

noncomputable def heterogeneousTargetNormalizedMean
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    {kind : PacketPlaceKind}
    {H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY}
    (targetReadout : HeterogeneousTargetAdmissibleReadout kind H)
    (profile : HeterogeneousTargetAdmissibleProfile kind H) : Real :=
  ordinaryFinMean (fun j => heterogeneousTargetPacketValue targetReadout profile j)

theorem heterogeneous_compatible_normalized_means
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (sourceReadout : HeterogeneousSourceAdmissibleReadout kind H)
    (targetReadout : HeterogeneousTargetAdmissibleReadout kind H)
    (hcompat : HeterogeneousAdmissibleReadoutCompatible kind H
      sourceReadout targetReadout)
    (profile : HeterogeneousSourceAdmissibleProfile kind H) :
    heterogeneousTargetNormalizedMean targetReadout
        (transportHeterogeneousAdmissibleProfile kind H profile) =
      heterogeneousSourceNormalizedMean sourceReadout profile := by
  unfold heterogeneousTargetNormalizedMean heterogeneousSourceNormalizedMean
  congr 1
  funext j
  exact heterogeneous_compatible_packet_values kind H sourceReadout
    targetReadout hcompat profile j

def forgetHeterogeneousSourceProfile
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    {kind : PacketPlaceKind}
    {H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY}
    (profile : HeterogeneousSourceAdmissibleProfile kind H) :
    (j : Fin n) -> Set (PacketX j) :=
  fun j => (profile j).1

def forgetHeterogeneousTargetProfile
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    {kind : PacketPlaceKind}
    {H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY}
    (profile : HeterogeneousTargetAdmissibleProfile kind H) :
    (j : Fin n) -> Set (PacketY j) :=
  fun j => (profile j).1

def transportHeterogeneousSetProfile
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (profile : (j : Fin n) -> Set (PacketX j)) :
    (j : Fin n) -> Set (PacketY j) :=
  fun j => H.packetHomeomorph j '' profile j

theorem forget_heterogeneous_admissible_transport_is_set_image
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (H : HeterogeneousStagewiseHomeomorphRaw PacketX PacketY)
    (profile : HeterogeneousSourceAdmissibleProfile kind H) :
    forgetHeterogeneousTargetProfile
        (transportHeterogeneousAdmissibleProfile kind H profile) =
      transportHeterogeneousSetProfile H
        (forgetHeterogeneousSourceProfile profile) :=
  rfl

abbrev boolPacketX (_j : Fin 2) := Bool
abbrev finTwoPacketY (_j : Fin 2) := Fin 2

def boolFinTwoEquiv : Bool ≃ Fin 2 where
  toFun := fun b => if b then 1 else 0
  invFun := fun i => if i = 0 then false else true
  left_inv := by
    intro b
    cases b <;> simp
  right_inv := by
    intro i
    fin_cases i <;> simp

def boolFinTwoTopologicalTransport :
    HeterogeneousStagewiseHomeomorphRaw boolPacketX finTwoPacketY where
  sourceTopology := fun _ => inferInstance
  targetTopology := fun _ => inferInstance
  packetHomeomorph := fun _ => Homeomorph.ofDiscrete boolFinTwoEquiv

def boolSingletonSourceRegion (j : Fin 2) :
    HeterogeneousSourceAdmissibleRegion .nonarch
      boolFinTwoTopologicalTransport j := by
  refine ⟨{false}, ?_⟩
  change ({false} : Set Bool).Nonempty ∧ IsCompact ({false} : Set Bool) ∧
    IsOpen ({false} : Set Bool)
  exact ⟨Set.singleton_nonempty false, isCompact_singleton, isOpen_discrete _⟩

def boolUnivSourceRegion (j : Fin 2) :
    HeterogeneousSourceAdmissibleRegion .nonarch
      boolFinTwoTopologicalTransport j := by
  refine ⟨Set.univ, ?_⟩
  change (Set.univ : Set Bool).Nonempty ∧ IsCompact (Set.univ : Set Bool) ∧
    IsOpen (Set.univ : Set Bool)
  exact ⟨Set.univ_nonempty, isCompact_univ, isOpen_univ⟩

noncomputable def boolSourceUnivReadout :
    HeterogeneousSourceAdmissibleReadout .nonarch
      boolFinTwoTopologicalTransport := by
  classical
  exact fun _ R => if R.1 = Set.univ then 2 else 1

noncomputable def finTwoTargetUnivReadout :
    HeterogeneousTargetAdmissibleReadout .nonarch
      boolFinTwoTopologicalTransport := by
  classical
  exact fun _ R => if R.1 = Set.univ then 2 else 1

theorem heterogeneous_equiv_image_eq_univ_iff
    {X : Type uX} {Y : Type uY} (e : X ≃ Y) (S : Set X) :
    e '' S = Set.univ ↔ S = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro x
    have hx : e x ∈ e '' S := by rw [h]; trivial
    rcases hx with ⟨z, hz, hzx⟩
    exact e.injective hzx |>.symm ▸ hz
  · intro h
    subst S
    apply Set.eq_univ_of_forall
    intro y
    exact ⟨e.symm y, Set.mem_univ _, by simp⟩

theorem bool_fin_two_univ_readouts_compatible :
    HeterogeneousAdmissibleReadoutCompatible .nonarch
      boolFinTwoTopologicalTransport boolSourceUnivReadout
        finTwoTargetUnivReadout := by
  classical
  intro j R
  unfold boolSourceUnivReadout finTwoTargetUnivReadout
  exact if_congr
    (heterogeneous_equiv_image_eq_univ_iff
      (boolFinTwoTopologicalTransport.packetHomeomorph j).toEquiv R.1)
    rfl rfl

theorem bool_source_univ_readout_is_nonconstant :
    boolSourceUnivReadout 0 (boolSingletonSourceRegion 0) ≠
      boolSourceUnivReadout 0 (boolUnivSourceRegion 0) := by
  have hne : ({false} : Set Bool) ≠ Set.univ := by
    intro h
    have htrue : true ∈ ({false} : Set Bool) := by
      rw [h]
      trivial
    simp at htrue
  unfold boolSourceUnivReadout
  dsimp [boolSingletonSourceRegion, boolUnivSourceRegion]
  rw [if_neg hne, if_pos rfl]
  norm_num

theorem bool_singleton_and_univ_transports_are_distinct :
    transportHeterogeneousAdmissibleRegion .nonarch
        boolFinTwoTopologicalTransport 0 (boolSingletonSourceRegion 0) ≠
      transportHeterogeneousAdmissibleRegion .nonarch
        boolFinTwoTopologicalTransport 0 (boolUnivSourceRegion 0) := by
  intro htransport
  have h := transport_heterogeneous_admissible_region_injective .nonarch
    boolFinTwoTopologicalTransport 0 htransport
  exact bool_source_univ_readout_is_nonconstant
    (congrArg (boolSourceUnivReadout 0) h)

noncomputable def boolFalseMembershipSourceReadout :
    HeterogeneousSourceAdmissibleReadout .nonarch
      boolFinTwoTopologicalTransport := by
  classical
  exact fun _ R => if false ∈ R.1 then 1 else 0

noncomputable def finTwoOneMembershipTargetReadout :
    HeterogeneousTargetAdmissibleReadout .nonarch
      boolFinTwoTopologicalTransport := by
  classical
  exact fun _ R => if (1 : Fin 2) ∈ R.1 then 1 else 0

theorem mismatched_distinguished_point_readouts_are_not_compatible :
    ¬ HeterogeneousAdmissibleReadoutCompatible .nonarch
      boolFinTwoTopologicalTransport boolFalseMembershipSourceReadout
        finTwoOneMembershipTargetReadout := by
  intro h
  have hbad := h 0 (boolSingletonSourceRegion 0)
  norm_num [boolFalseMembershipSourceReadout,
    finTwoOneMembershipTargetReadout,
    transportHeterogeneousAdmissibleRegion, boolSingletonSourceRegion,
    boolFinTwoTopologicalTransport, boolFinTwoEquiv] at hbad
  have hmap :
      boolFinTwoTopologicalTransport.packetHomeomorph 0 false = (0 : Fin 2) := rfl
  rw [hmap] at hbad
  norm_num at hbad

def boolSingletonSourceProfile :
    HeterogeneousSourceAdmissibleProfile .nonarch
      boolFinTwoTopologicalTransport :=
  fun j => boolSingletonSourceRegion j

theorem bool_fin_two_nonconstant_model_mean_invariant :
    heterogeneousTargetNormalizedMean finTwoTargetUnivReadout
        (transportHeterogeneousAdmissibleProfile .nonarch
          boolFinTwoTopologicalTransport boolSingletonSourceProfile) =
      heterogeneousSourceNormalizedMean boolSourceUnivReadout
        boolSingletonSourceProfile :=
  heterogeneous_compatible_normalized_means .nonarch
    boolFinTwoTopologicalTransport boolSourceUnivReadout
      finTwoTargetUnivReadout bool_fin_two_univ_readouts_compatible
        boolSingletonSourceProfile

theorem mismatched_source_mean_eq_one :
    heterogeneousSourceNormalizedMean boolFalseMembershipSourceReadout
      boolSingletonSourceProfile = 1 := by
  norm_num [heterogeneousSourceNormalizedMean,
    heterogeneousSourcePacketValue, boolFalseMembershipSourceReadout,
    boolSingletonSourceProfile, boolSingletonSourceRegion, ordinaryFinMean,
    Fin.sum_univ_two]

theorem mismatched_target_mean_eq_zero :
    heterogeneousTargetNormalizedMean finTwoOneMembershipTargetReadout
        (transportHeterogeneousAdmissibleProfile .nonarch
          boolFinTwoTopologicalTransport boolSingletonSourceProfile) = 0 := by
  norm_num [heterogeneousTargetNormalizedMean,
    heterogeneousTargetPacketValue, finTwoOneMembershipTargetReadout,
    transportHeterogeneousAdmissibleProfile,
    transportHeterogeneousAdmissibleRegion, boolSingletonSourceProfile,
    boolSingletonSourceRegion, boolFinTwoTopologicalTransport,
    boolFinTwoEquiv, ordinaryFinMean, Fin.sum_univ_two]

theorem raw_heterogeneous_transport_does_not_force_mean_equality :
    heterogeneousTargetNormalizedMean finTwoOneMembershipTargetReadout
        (transportHeterogeneousAdmissibleProfile .nonarch
          boolFinTwoTopologicalTransport boolSingletonSourceProfile) ≠
      heterogeneousSourceNormalizedMean boolFalseMembershipSourceReadout
        boolSingletonSourceProfile := by
  rw [mismatched_target_mean_eq_zero, mismatched_source_mean_eq_one]
  norm_num

end CitedLV.Theorem311
