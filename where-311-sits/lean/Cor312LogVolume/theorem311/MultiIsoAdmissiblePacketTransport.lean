import Cor312LogVolume.theorem311.HeterogeneousAdmissiblePacketTransport

namespace CitedLV.Theorem311

universe uX uY uChoice

structure HeterogeneousStagewiseMultiHomeomorphRaw
    {n : Nat} (PacketX : Fin n -> Type uX) (PacketY : Fin n -> Type uY) where
  Choice : Type uChoice
  sourceTopology : (j : Fin n) -> TopologicalSpace (PacketX j)
  targetTopology : (j : Fin n) -> TopologicalSpace (PacketY j)
  packetHomeomorph : Choice -> (j : Fin n) ->
    @Homeomorph (PacketX j) (PacketY j)
      (sourceTopology j) (targetTopology j)

def selectHeterogeneousHomeomorph
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY)
    (c : M.Choice) :
    HeterogeneousStagewiseHomeomorphRaw PacketX PacketY where
  sourceTopology := M.sourceTopology
  targetTopology := M.targetTopology
  packetHomeomorph := M.packetHomeomorph c

def MultiIsoChoiceNonempty
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY) : Prop :=
  Nonempty M.Choice

abbrev MultiIsoSourceAdmissibleRegion
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY)
    (j : Fin n) :=
  {K : Set (PacketX j) //
    PacketRegionAdmissibleForTopology kind M.sourceTopology j K}

abbrev MultiIsoTargetAdmissibleRegion
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY)
    (j : Fin n) :=
  {K : Set (PacketY j) //
    PacketRegionAdmissibleForTopology kind M.targetTopology j K}

def transportMultiIsoAdmissibleRegion
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY)
    (c : M.Choice) (j : Fin n)
    (R : MultiIsoSourceAdmissibleRegion kind M j) :
    MultiIsoTargetAdmissibleRegion kind M j :=
  transportHeterogeneousAdmissibleRegion kind
    (selectHeterogeneousHomeomorph M c) j R

theorem transport_multiIso_admissible_region_injective
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY)
    (c : M.Choice) (j : Fin n) :
    Function.Injective (transportMultiIsoAdmissibleRegion kind M c j) :=
  transport_heterogeneous_admissible_region_injective kind
    (selectHeterogeneousHomeomorph M c) j

abbrev MultiIsoSourceAdmissibleProfile
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY) :=
  (j : Fin n) -> MultiIsoSourceAdmissibleRegion kind M j

abbrev MultiIsoTargetAdmissibleProfile
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY) :=
  (j : Fin n) -> MultiIsoTargetAdmissibleRegion kind M j

abbrev MultiIsoSourceAdmissibleReadout
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY) :=
  (j : Fin n) -> MultiIsoSourceAdmissibleRegion kind M j -> Real

abbrev MultiIsoTargetAdmissibleReadout
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY) :=
  (j : Fin n) -> MultiIsoTargetAdmissibleRegion kind M j -> Real

def transportMultiIsoAdmissibleProfile
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY)
    (c : M.Choice) (profile : MultiIsoSourceAdmissibleProfile kind M) :
    MultiIsoTargetAdmissibleProfile kind M :=
  fun j => transportMultiIsoAdmissibleRegion kind M c j (profile j)

def MultiIsoAdmissibleReadoutCompatible
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY)
    (sourceReadout : MultiIsoSourceAdmissibleReadout kind M)
    (targetReadout : MultiIsoTargetAdmissibleReadout kind M) : Prop :=
  ∀ c j R,
    targetReadout j (transportMultiIsoAdmissibleRegion kind M c j R) =
      sourceReadout j R

def NaturalMultiIsoReadoutContract
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY)
    (sourceReadout : MultiIsoSourceAdmissibleReadout kind M)
    (targetReadout : MultiIsoTargetAdmissibleReadout kind M) : Prop :=
  MultiIsoChoiceNonempty M ∧
    MultiIsoAdmissibleReadoutCompatible kind M sourceReadout targetReadout

noncomputable def multiIsoSourceNormalizedMean
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    {kind : PacketPlaceKind}
    {M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY}
    (sourceReadout : MultiIsoSourceAdmissibleReadout kind M)
    (profile : MultiIsoSourceAdmissibleProfile kind M) : Real :=
  ordinaryFinMean (fun j => sourceReadout j (profile j))

noncomputable def multiIsoTargetNormalizedMean
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    {kind : PacketPlaceKind}
    {M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY}
    (targetReadout : MultiIsoTargetAdmissibleReadout kind M)
    (profile : MultiIsoTargetAdmissibleProfile kind M) : Real :=
  ordinaryFinMean (fun j => targetReadout j (profile j))

theorem multiIso_compatible_normalized_means_for_each_representative
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY)
    (sourceReadout : MultiIsoSourceAdmissibleReadout kind M)
    (targetReadout : MultiIsoTargetAdmissibleReadout kind M)
    (hcompat : MultiIsoAdmissibleReadoutCompatible kind M
      sourceReadout targetReadout)
    (c : M.Choice) (profile : MultiIsoSourceAdmissibleProfile kind M) :
    multiIsoTargetNormalizedMean targetReadout
        (transportMultiIsoAdmissibleProfile kind M c profile) =
      multiIsoSourceNormalizedMean sourceReadout profile := by
  unfold multiIsoTargetNormalizedMean multiIsoSourceNormalizedMean
  congr 1
  funext j
  exact hcompat c j (profile j)

theorem natural_multiIso_contract_has_a_mean_comparison
    {n : Nat} {PacketX : Fin n -> Type uX} {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (M : HeterogeneousStagewiseMultiHomeomorphRaw PacketX PacketY)
    (sourceReadout : MultiIsoSourceAdmissibleReadout kind M)
    (targetReadout : MultiIsoTargetAdmissibleReadout kind M)
    (hcontract : NaturalMultiIsoReadoutContract kind M
      sourceReadout targetReadout)
    (profile : MultiIsoSourceAdmissibleProfile kind M) :
    ∃ c : M.Choice,
      multiIsoTargetNormalizedMean targetReadout
          (transportMultiIsoAdmissibleProfile kind M c profile) =
        multiIsoSourceNormalizedMean sourceReadout profile := by
  rcases hcontract.1 with ⟨c⟩
  exact ⟨c, multiIso_compatible_normalized_means_for_each_representative
    kind M sourceReadout targetReadout hcontract.2 c profile⟩

abbrev boolOrbitPacket (_j : Fin 1) := Bool

def boolNegEquiv : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro b; cases b <;> rfl

def boolOrbitMultiTransport :
    HeterogeneousStagewiseMultiHomeomorphRaw
      boolOrbitPacket boolOrbitPacket where
  Choice := Bool
  sourceTopology := fun _ => inferInstance
  targetTopology := fun _ => inferInstance
  packetHomeomorph := fun c _ =>
    Homeomorph.ofDiscrete (if c then boolNegEquiv else Equiv.refl Bool)

theorem bool_orbit_choice_nonempty :
    MultiIsoChoiceNonempty boolOrbitMultiTransport :=
  ⟨false⟩

def boolOrbitSingletonRegion :
    MultiIsoSourceAdmissibleRegion .nonarch boolOrbitMultiTransport 0 := by
  refine ⟨{false}, ?_⟩
  change ({false} : Set Bool).Nonempty ∧ IsCompact ({false} : Set Bool) ∧
    IsOpen ({false} : Set Bool)
  exact ⟨Set.singleton_nonempty false, isCompact_singleton, isOpen_discrete _⟩

def boolOrbitUnivRegion :
    MultiIsoSourceAdmissibleRegion .nonarch boolOrbitMultiTransport 0 := by
  refine ⟨Set.univ, ?_⟩
  change (Set.univ : Set Bool).Nonempty ∧ IsCompact (Set.univ : Set Bool) ∧
    IsOpen (Set.univ : Set Bool)
  exact ⟨Set.univ_nonempty, isCompact_univ, isOpen_univ⟩

noncomputable def boolOrbitSourceUnivReadout :
    MultiIsoSourceAdmissibleReadout .nonarch boolOrbitMultiTransport := by
  classical
  exact fun _ R => if R.1 = Set.univ then 2 else 1

noncomputable def boolOrbitTargetUnivReadout :
    MultiIsoTargetAdmissibleReadout .nonarch boolOrbitMultiTransport := by
  classical
  exact fun _ R => if R.1 = Set.univ then 2 else 1

theorem bool_orbit_univ_readouts_compatible :
    MultiIsoAdmissibleReadoutCompatible .nonarch boolOrbitMultiTransport
      boolOrbitSourceUnivReadout boolOrbitTargetUnivReadout := by
  classical
  intro c j R
  unfold boolOrbitSourceUnivReadout boolOrbitTargetUnivReadout
  exact if_congr
    (heterogeneous_equiv_image_eq_univ_iff
      (boolOrbitMultiTransport.packetHomeomorph c j).toEquiv R.1)
    rfl rfl

theorem bool_orbit_natural_contract :
    NaturalMultiIsoReadoutContract .nonarch boolOrbitMultiTransport
      boolOrbitSourceUnivReadout boolOrbitTargetUnivReadout :=
  ⟨bool_orbit_choice_nonempty, bool_orbit_univ_readouts_compatible⟩

theorem bool_orbit_source_readout_nonconstant :
    boolOrbitSourceUnivReadout 0 boolOrbitSingletonRegion ≠
      boolOrbitSourceUnivReadout 0 boolOrbitUnivRegion := by
  have hne : ({false} : Set Bool) ≠ Set.univ := by
    intro h
    have : true ∈ ({false} : Set Bool) := by rw [h]; trivial
    simp at this
  unfold boolOrbitSourceUnivReadout
  dsimp [boolOrbitSingletonRegion, boolOrbitUnivRegion]
  rw [if_neg hne, if_pos rfl]
  norm_num

theorem bool_orbit_representatives_move_singleton :
    transportMultiIsoAdmissibleRegion .nonarch boolOrbitMultiTransport
        false 0 boolOrbitSingletonRegion ≠
      transportMultiIsoAdmissibleRegion .nonarch boolOrbitMultiTransport
        true 0 boolOrbitSingletonRegion := by
  intro h
  have hm := congrArg
    (fun R : MultiIsoTargetAdmissibleRegion .nonarch
      boolOrbitMultiTransport 0 => false ∈ R.1) h
  norm_num [transportMultiIsoAdmissibleRegion,
    selectHeterogeneousHomeomorph, transportHeterogeneousAdmissibleRegion,
    boolOrbitMultiTransport, boolOrbitSingletonRegion, boolNegEquiv] at hm
  change false = true at hm
  exact Bool.noConfusion hm

theorem compatible_readouts_do_not_identify_orbit_images :
    MultiIsoAdmissibleReadoutCompatible .nonarch boolOrbitMultiTransport
        boolOrbitSourceUnivReadout boolOrbitTargetUnivReadout ∧
      transportMultiIsoAdmissibleRegion .nonarch boolOrbitMultiTransport
          false 0 boolOrbitSingletonRegion ≠
        transportMultiIsoAdmissibleRegion .nonarch boolOrbitMultiTransport
          true 0 boolOrbitSingletonRegion :=
  ⟨bool_orbit_univ_readouts_compatible,
    bool_orbit_representatives_move_singleton⟩

abbrev emptyChoicePacket (_j : Fin 1) := Bool

def emptyChoiceMultiTransport :
    HeterogeneousStagewiseMultiHomeomorphRaw
      emptyChoicePacket emptyChoicePacket where
  Choice := Empty
  sourceTopology := fun _ => inferInstance
  targetTopology := fun _ => inferInstance
  packetHomeomorph := fun c => nomatch c

def emptyChoiceSourceRegion :
    MultiIsoSourceAdmissibleRegion .nonarch emptyChoiceMultiTransport 0 := by
  refine ⟨{false}, ?_⟩
  change ({false} : Set Bool).Nonempty ∧ IsCompact ({false} : Set Bool) ∧
    IsOpen ({false} : Set Bool)
  exact ⟨Set.singleton_nonempty false, isCompact_singleton, isOpen_discrete _⟩

def emptyChoiceTargetRegion :
    MultiIsoTargetAdmissibleRegion .nonarch emptyChoiceMultiTransport 0 := by
  refine ⟨{false}, ?_⟩
  change ({false} : Set Bool).Nonempty ∧ IsCompact ({false} : Set Bool) ∧
    IsOpen ({false} : Set Bool)
  exact ⟨Set.singleton_nonempty false, isCompact_singleton, isOpen_discrete _⟩

noncomputable def emptyChoiceSourceOneReadout :
    MultiIsoSourceAdmissibleReadout .nonarch emptyChoiceMultiTransport :=
  fun _ _ => 1

noncomputable def emptyChoiceTargetZeroReadout :
    MultiIsoTargetAdmissibleReadout .nonarch emptyChoiceMultiTransport :=
  fun _ _ => 0

theorem empty_choice_all_representative_compatibility_is_vacuous :
    MultiIsoAdmissibleReadoutCompatible .nonarch emptyChoiceMultiTransport
      emptyChoiceSourceOneReadout emptyChoiceTargetZeroReadout := by
  intro c
  exact Empty.elim c

theorem empty_choice_readouts_really_disagree :
    emptyChoiceSourceOneReadout 0 emptyChoiceSourceRegion ≠
      emptyChoiceTargetZeroReadout 0 emptyChoiceTargetRegion := by
  norm_num [emptyChoiceSourceOneReadout, emptyChoiceTargetZeroReadout]

theorem empty_choice_fails_nonempty_gate :
    ¬ MultiIsoChoiceNonempty emptyChoiceMultiTransport := by
  rintro ⟨c⟩
  exact Empty.elim c

theorem empty_choice_vacuity_is_rejected_by_source_contract :
    MultiIsoAdmissibleReadoutCompatible .nonarch emptyChoiceMultiTransport
        emptyChoiceSourceOneReadout emptyChoiceTargetZeroReadout ∧
      ¬ NaturalMultiIsoReadoutContract .nonarch emptyChoiceMultiTransport
        emptyChoiceSourceOneReadout emptyChoiceTargetZeroReadout := by
  refine ⟨empty_choice_all_representative_compatibility_is_vacuous, ?_⟩
  intro hcontract
  exact empty_choice_fails_nonempty_gate hcontract.1

end CitedLV.Theorem311
