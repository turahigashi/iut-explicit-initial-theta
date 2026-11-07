import Cor312LogVolume.theorem311.MultiIsoAdmissiblePacketTransport

namespace CitedLV.Theorem311

universe uX uI uY uLeft uRight

structure HeterogeneousTwoOrbitPacketChainRaw
    {n : Nat}
    (PacketX : Fin n -> Type uX)
    (PacketI : Fin n -> Type uI)
    (PacketY : Fin n -> Type uY) where
  LeftChoice : Type uLeft
  RightChoice : Type uRight
  sourceTopology : (j : Fin n) -> TopologicalSpace (PacketX j)
  middleTopology : (j : Fin n) -> TopologicalSpace (PacketI j)
  targetTopology : (j : Fin n) -> TopologicalSpace (PacketY j)
  leftHomeomorph : LeftChoice -> (j : Fin n) ->
    @Homeomorph (PacketX j) (PacketI j)
      (sourceTopology j) (middleTopology j)
  rightHomeomorph : RightChoice -> (j : Fin n) ->
    @Homeomorph (PacketI j) (PacketY j)
      (middleTopology j) (targetTopology j)

def selectTwoOrbitLeftHomeomorph
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (l : C.LeftChoice) :
    HeterogeneousStagewiseHomeomorphRaw PacketX PacketI where
  sourceTopology := C.sourceTopology
  targetTopology := C.middleTopology
  packetHomeomorph := C.leftHomeomorph l

def selectTwoOrbitRightHomeomorph
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (r : C.RightChoice) :
    HeterogeneousStagewiseHomeomorphRaw PacketI PacketY where
  sourceTopology := C.middleTopology
  targetTopology := C.targetTopology
  packetHomeomorph := C.rightHomeomorph r

def selectTwoOrbitCompositeHomeomorph
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (l : C.LeftChoice) (r : C.RightChoice) :
    HeterogeneousStagewiseHomeomorphRaw PacketX PacketY where
  sourceTopology := C.sourceTopology
  targetTopology := C.targetTopology
  packetHomeomorph := fun j => by
    letI : TopologicalSpace (PacketX j) := C.sourceTopology j
    letI : TopologicalSpace (PacketI j) := C.middleTopology j
    letI : TopologicalSpace (PacketY j) := C.targetTopology j
    exact (C.leftHomeomorph l j).trans (C.rightHomeomorph r j)

abbrev TwoOrbitCompatiblePair
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY) :=
  C.LeftChoice -> C.RightChoice -> Prop

def CompatibleChainPairNonempty
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (compatiblePair : TwoOrbitCompatiblePair C) : Prop :=
  ∃ l r, compatiblePair l r

abbrev TwoOrbitSourceAdmissibleRegion
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (j : Fin n) :=
  {K : Set (PacketX j) //
    PacketRegionAdmissibleForTopology kind C.sourceTopology j K}

abbrev TwoOrbitMiddleAdmissibleRegion
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (j : Fin n) :=
  {K : Set (PacketI j) //
    PacketRegionAdmissibleForTopology kind C.middleTopology j K}

abbrev TwoOrbitTargetAdmissibleRegion
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (j : Fin n) :=
  {K : Set (PacketY j) //
    PacketRegionAdmissibleForTopology kind C.targetTopology j K}

def transportTwoOrbitLeftRegion
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (l : C.LeftChoice) (j : Fin n)
    (R : TwoOrbitSourceAdmissibleRegion kind C j) :
    TwoOrbitMiddleAdmissibleRegion kind C j :=
  transportHeterogeneousAdmissibleRegion kind
    (selectTwoOrbitLeftHomeomorph C l) j R

def transportTwoOrbitRightRegion
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (r : C.RightChoice) (j : Fin n)
    (R : TwoOrbitMiddleAdmissibleRegion kind C j) :
    TwoOrbitTargetAdmissibleRegion kind C j :=
  transportHeterogeneousAdmissibleRegion kind
    (selectTwoOrbitRightHomeomorph C r) j R

def transportTwoOrbitCompositeRegion
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (l : C.LeftChoice) (r : C.RightChoice) (j : Fin n)
    (R : TwoOrbitSourceAdmissibleRegion kind C j) :
    TwoOrbitTargetAdmissibleRegion kind C j :=
  transportTwoOrbitRightRegion kind C r j
    (transportTwoOrbitLeftRegion kind C l j R)

def transportTwoOrbitDirectCompositeRegion
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (l : C.LeftChoice) (r : C.RightChoice) (j : Fin n)
    (R : TwoOrbitSourceAdmissibleRegion kind C j) :
    TwoOrbitTargetAdmissibleRegion kind C j :=
  transportHeterogeneousAdmissibleRegion kind
    (selectTwoOrbitCompositeHomeomorph C l r) j R

theorem sequential_two_orbit_transport_eq_direct_composite
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (l : C.LeftChoice) (r : C.RightChoice) (j : Fin n)
    (R : TwoOrbitSourceAdmissibleRegion kind C j) :
    transportTwoOrbitCompositeRegion kind C l r j R =
      transportTwoOrbitDirectCompositeRegion kind C l r j R := by
  letI : TopologicalSpace (PacketX j) := C.sourceTopology j
  letI : TopologicalSpace (PacketI j) := C.middleTopology j
  letI : TopologicalSpace (PacketY j) := C.targetTopology j
  apply Subtype.ext
  change C.rightHomeomorph r j '' (C.leftHomeomorph l j '' R.1) =
    ((C.leftHomeomorph l j).trans (C.rightHomeomorph r j)) '' R.1
  exact Set.image_image _ _ R.1

theorem transport_two_orbit_composite_injective
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (l : C.LeftChoice) (r : C.RightChoice) (j : Fin n) :
    Function.Injective (transportTwoOrbitCompositeRegion kind C l r j) :=
  (transport_heterogeneous_admissible_region_injective kind
    (selectTwoOrbitRightHomeomorph C r) j).comp
      (transport_heterogeneous_admissible_region_injective kind
        (selectTwoOrbitLeftHomeomorph C l) j)

abbrev TwoOrbitSourceAdmissibleProfile
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY) :=
  (j : Fin n) -> TwoOrbitSourceAdmissibleRegion kind C j

abbrev TwoOrbitMiddleAdmissibleProfile
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY) :=
  (j : Fin n) -> TwoOrbitMiddleAdmissibleRegion kind C j

abbrev TwoOrbitTargetAdmissibleProfile
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY) :=
  (j : Fin n) -> TwoOrbitTargetAdmissibleRegion kind C j

def transportTwoOrbitLeftProfile
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (l : C.LeftChoice)
    (profile : TwoOrbitSourceAdmissibleProfile kind C) :
    TwoOrbitMiddleAdmissibleProfile kind C :=
  fun j => transportTwoOrbitLeftRegion kind C l j (profile j)

def transportTwoOrbitCompositeProfile
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (l : C.LeftChoice) (r : C.RightChoice)
    (profile : TwoOrbitSourceAdmissibleProfile kind C) :
    TwoOrbitTargetAdmissibleProfile kind C :=
  fun j => transportTwoOrbitCompositeRegion kind C l r j (profile j)

abbrev TwoOrbitSourceAdmissibleReadout
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY) :=
  (j : Fin n) -> TwoOrbitSourceAdmissibleRegion kind C j -> Real

abbrev TwoOrbitMiddleAdmissibleReadout
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY) :=
  (j : Fin n) -> TwoOrbitMiddleAdmissibleRegion kind C j -> Real

abbrev TwoOrbitTargetAdmissibleReadout
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY) :=
  (j : Fin n) -> TwoOrbitTargetAdmissibleRegion kind C j -> Real

def CompatibleTwoOrbitChainReadouts
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (compatiblePair : TwoOrbitCompatiblePair C)
    (sourceReadout : TwoOrbitSourceAdmissibleReadout kind C)
    (middleReadout : TwoOrbitMiddleAdmissibleReadout kind C)
    (targetReadout : TwoOrbitTargetAdmissibleReadout kind C) : Prop :=
  ∀ l r, compatiblePair l r ->
    (∀ j R,
      middleReadout j (transportTwoOrbitLeftRegion kind C l j R) =
        sourceReadout j R) ∧
    (∀ j Q,
      targetReadout j (transportTwoOrbitRightRegion kind C r j Q) =
        middleReadout j Q)

def NaturalTwoOrbitChainReadoutContract
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (compatiblePair : TwoOrbitCompatiblePair C)
    (sourceReadout : TwoOrbitSourceAdmissibleReadout kind C)
    (middleReadout : TwoOrbitMiddleAdmissibleReadout kind C)
    (targetReadout : TwoOrbitTargetAdmissibleReadout kind C) : Prop :=
  CompatibleChainPairNonempty C compatiblePair ∧
    CompatibleTwoOrbitChainReadouts kind C compatiblePair
      sourceReadout middleReadout targetReadout

noncomputable def twoOrbitSourceNormalizedMean
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    {kind : PacketPlaceKind}
    {C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY}
    (sourceReadout : TwoOrbitSourceAdmissibleReadout kind C)
    (profile : TwoOrbitSourceAdmissibleProfile kind C) : Real :=
  ordinaryFinMean (fun j => sourceReadout j (profile j))

noncomputable def twoOrbitTargetNormalizedMean
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    {kind : PacketPlaceKind}
    {C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY}
    (targetReadout : TwoOrbitTargetAdmissibleReadout kind C)
    (profile : TwoOrbitTargetAdmissibleProfile kind C) : Real :=
  ordinaryFinMean (fun j => targetReadout j (profile j))

theorem compatible_two_orbit_chain_gives_mean_equality
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (compatiblePair : TwoOrbitCompatiblePair C)
    (sourceReadout : TwoOrbitSourceAdmissibleReadout kind C)
    (middleReadout : TwoOrbitMiddleAdmissibleReadout kind C)
    (targetReadout : TwoOrbitTargetAdmissibleReadout kind C)
    (hcompat : CompatibleTwoOrbitChainReadouts kind C compatiblePair
      sourceReadout middleReadout targetReadout)
    (l : C.LeftChoice) (r : C.RightChoice) (hlr : compatiblePair l r)
    (profile : TwoOrbitSourceAdmissibleProfile kind C) :
    twoOrbitTargetNormalizedMean targetReadout
        (transportTwoOrbitCompositeProfile kind C l r profile) =
      twoOrbitSourceNormalizedMean sourceReadout profile := by
  unfold twoOrbitTargetNormalizedMean twoOrbitSourceNormalizedMean
  congr 1
  funext j
  calc
    targetReadout j
        (transportTwoOrbitCompositeRegion kind C l r j (profile j)) =
      middleReadout j
        (transportTwoOrbitLeftRegion kind C l j (profile j)) :=
          (hcompat l r hlr).2 j
            (transportTwoOrbitLeftRegion kind C l j (profile j))
    _ = sourceReadout j (profile j) :=
          (hcompat l r hlr).1 j (profile j)

theorem natural_two_orbit_contract_has_mean_comparison
    {n : Nat}
    {PacketX : Fin n -> Type uX} {PacketI : Fin n -> Type uI}
    {PacketY : Fin n -> Type uY}
    (kind : PacketPlaceKind)
    (C : HeterogeneousTwoOrbitPacketChainRaw PacketX PacketI PacketY)
    (compatiblePair : TwoOrbitCompatiblePair C)
    (sourceReadout : TwoOrbitSourceAdmissibleReadout kind C)
    (middleReadout : TwoOrbitMiddleAdmissibleReadout kind C)
    (targetReadout : TwoOrbitTargetAdmissibleReadout kind C)
    (hcontract : NaturalTwoOrbitChainReadoutContract kind C compatiblePair
      sourceReadout middleReadout targetReadout)
    (profile : TwoOrbitSourceAdmissibleProfile kind C) :
    ∃ l r, compatiblePair l r ∧
      twoOrbitTargetNormalizedMean targetReadout
          (transportTwoOrbitCompositeProfile kind C l r profile) =
        twoOrbitSourceNormalizedMean sourceReadout profile := by
  rcases hcontract.1 with ⟨l, r, hlr⟩
  exact ⟨l, r, hlr, compatible_two_orbit_chain_gives_mean_equality
    kind C compatiblePair sourceReadout middleReadout targetReadout
      hcontract.2 l r hlr profile⟩

abbrev boolChainPacket (_j : Fin 1) := Bool

def boolTwoOrbitChain :
    HeterogeneousTwoOrbitPacketChainRaw
      boolChainPacket boolChainPacket boolChainPacket where
  LeftChoice := Bool
  RightChoice := Bool
  sourceTopology := fun _ => inferInstance
  middleTopology := fun _ => inferInstance
  targetTopology := fun _ => inferInstance
  leftHomeomorph := fun l _ =>
    Homeomorph.ofDiscrete (if l then boolNegEquiv else Equiv.refl Bool)
  rightHomeomorph := fun r _ =>
    Homeomorph.ofDiscrete (if r then boolNegEquiv else Equiv.refl Bool)

def boolChainCompatiblePair (l r : Bool) : Prop :=
  l = r

theorem bool_chain_compatible_pair_nonempty :
    CompatibleChainPairNonempty boolTwoOrbitChain boolChainCompatiblePair :=
  ⟨false, false, rfl⟩

theorem bool_chain_pair_relation_is_not_total :
    ¬ ∀ l r, boolChainCompatiblePair l r := by
  intro h
  exact Bool.noConfusion (h false true)

def boolChainSourceSingleton :
    TwoOrbitSourceAdmissibleRegion .nonarch boolTwoOrbitChain 0 := by
  refine ⟨{false}, ?_⟩
  change ({false} : Set Bool).Nonempty ∧ IsCompact ({false} : Set Bool) ∧
    IsOpen ({false} : Set Bool)
  exact ⟨Set.singleton_nonempty false, isCompact_singleton, isOpen_discrete _⟩

def boolChainTargetSingleton :
    TwoOrbitTargetAdmissibleRegion .nonarch boolTwoOrbitChain 0 := by
  refine ⟨{false}, ?_⟩
  change ({false} : Set Bool).Nonempty ∧ IsCompact ({false} : Set Bool) ∧
    IsOpen ({false} : Set Bool)
  exact ⟨Set.singleton_nonempty false, isCompact_singleton, isOpen_discrete _⟩

def boolChainSourceUniv :
    TwoOrbitSourceAdmissibleRegion .nonarch boolTwoOrbitChain 0 := by
  refine ⟨Set.univ, ?_⟩
  change (Set.univ : Set Bool).Nonempty ∧ IsCompact (Set.univ : Set Bool) ∧
    IsOpen (Set.univ : Set Bool)
  exact ⟨Set.univ_nonempty, isCompact_univ, isOpen_univ⟩

noncomputable def boolChainSourceUnivReadout :
    TwoOrbitSourceAdmissibleReadout .nonarch boolTwoOrbitChain := by
  classical
  exact fun _ R => if R.1 = Set.univ then 2 else 1

noncomputable def boolChainMiddleUnivReadout :
    TwoOrbitMiddleAdmissibleReadout .nonarch boolTwoOrbitChain := by
  classical
  exact fun _ R => if R.1 = Set.univ then 2 else 1

noncomputable def boolChainTargetUnivReadout :
    TwoOrbitTargetAdmissibleReadout .nonarch boolTwoOrbitChain := by
  classical
  exact fun _ R => if R.1 = Set.univ then 2 else 1

theorem bool_chain_readouts_compatible :
    CompatibleTwoOrbitChainReadouts .nonarch boolTwoOrbitChain
      boolChainCompatiblePair boolChainSourceUnivReadout
        boolChainMiddleUnivReadout boolChainTargetUnivReadout := by
  classical
  intro l r _
  constructor
  · intro j R
    unfold boolChainSourceUnivReadout boolChainMiddleUnivReadout
    exact if_congr
      (heterogeneous_equiv_image_eq_univ_iff
        (boolTwoOrbitChain.leftHomeomorph l j).toEquiv R.1)
      rfl rfl
  · intro j R
    unfold boolChainMiddleUnivReadout boolChainTargetUnivReadout
    exact if_congr
      (heterogeneous_equiv_image_eq_univ_iff
        (boolTwoOrbitChain.rightHomeomorph r j).toEquiv R.1)
      rfl rfl

theorem bool_chain_natural_contract :
    NaturalTwoOrbitChainReadoutContract .nonarch boolTwoOrbitChain
      boolChainCompatiblePair boolChainSourceUnivReadout
        boolChainMiddleUnivReadout boolChainTargetUnivReadout :=
  ⟨bool_chain_compatible_pair_nonempty, bool_chain_readouts_compatible⟩

theorem bool_chain_source_readout_nonconstant :
    boolChainSourceUnivReadout 0 boolChainSourceSingleton ≠
      boolChainSourceUnivReadout 0 boolChainSourceUniv := by
  have hne : ({false} : Set Bool) ≠ Set.univ := by
    intro h
    have : true ∈ ({false} : Set Bool) := by rw [h]; trivial
    simp at this
  unfold boolChainSourceUnivReadout
  dsimp [boolChainSourceSingleton, boolChainSourceUniv]
  rw [if_neg hne, if_pos rfl]
  norm_num

theorem bool_two_orbit_matched_point (c b : Bool) :
    boolTwoOrbitChain.rightHomeomorph c 0
        (boolTwoOrbitChain.leftHomeomorph c 0 b) = b := by
  cases c <;> cases b <;> rfl

theorem bool_two_orbit_unmatched_false_point :
    boolTwoOrbitChain.rightHomeomorph true 0
        (boolTwoOrbitChain.leftHomeomorph false 0 false) = true :=
  rfl

theorem bool_chain_matched_pair_fixes_singleton
    (l r : Bool) (hlr : boolChainCompatiblePair l r) :
    transportTwoOrbitCompositeRegion .nonarch boolTwoOrbitChain
        l r 0 boolChainSourceSingleton = boolChainTargetSingleton := by
  subst r
  apply Subtype.ext
  change boolTwoOrbitChain.rightHomeomorph l 0 ''
      (boolTwoOrbitChain.leftHomeomorph l 0 '' ({false} : Set Bool)) =
    ({false} : Set Bool)
  rw [Set.image_image]
  have hfun :
      (fun b => boolTwoOrbitChain.rightHomeomorph l 0
        (boolTwoOrbitChain.leftHomeomorph l 0 b)) = fun b => b := by
    funext b
    exact bool_two_orbit_matched_point l b
  rw [hfun, Set.image_id']

theorem bool_chain_unmatched_pair_image_eq_true_singleton :
    (transportTwoOrbitCompositeRegion .nonarch boolTwoOrbitChain
      false true 0 boolChainSourceSingleton).1 = ({true} : Set Bool) := by
  change boolTwoOrbitChain.rightHomeomorph true 0 ''
      (boolTwoOrbitChain.leftHomeomorph false 0 '' ({false} : Set Bool)) =
    ({true} : Set Bool)
  rw [Set.image_image]
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxfalse : x = false := by simpa using hx
    subst x
    simpa using bool_two_orbit_unmatched_false_point
  · intro hb
    have hbtrue : b = true := by simpa using hb
    subst b
    exact ⟨false, Set.mem_singleton false, bool_two_orbit_unmatched_false_point⟩

theorem bool_chain_unmatched_pair_moves_singleton :
    transportTwoOrbitCompositeRegion .nonarch boolTwoOrbitChain
        false true 0 boolChainSourceSingleton ≠ boolChainTargetSingleton := by
  intro h
  have hsets := congrArg Subtype.val h
  rw [bool_chain_unmatched_pair_image_eq_true_singleton] at hsets
  have htarget : (boolChainTargetSingleton :
      TwoOrbitTargetAdmissibleRegion .nonarch boolTwoOrbitChain 0).1 =
      ({false} : Set Bool) := rfl
  rw [htarget] at hsets
  have hfalse : false ∈ ({true} : Set Bool) := by
    rw [hsets]
    simp
  simp at hfalse

theorem bool_chain_scalar_readout_does_not_recover_pair_relation :
    boolChainTargetUnivReadout 0
        (transportTwoOrbitCompositeRegion .nonarch boolTwoOrbitChain
          false true 0 boolChainSourceSingleton) =
      boolChainSourceUnivReadout 0 boolChainSourceSingleton ∧
    transportTwoOrbitCompositeRegion .nonarch boolTwoOrbitChain
        false true 0 boolChainSourceSingleton ≠ boolChainTargetSingleton := by
  constructor
  · unfold boolChainTargetUnivReadout boolChainSourceUnivReadout
    rw [bool_chain_unmatched_pair_image_eq_true_singleton]
    dsimp [boolChainSourceSingleton]
    have htrue : ({true} : Set Bool) ≠ Set.univ := by
      intro h
      have : false ∈ ({true} : Set Bool) := by rw [h]; trivial
      simp at this
    have hfalse : ({false} : Set Bool) ≠ Set.univ := by
      intro h
      have : true ∈ ({false} : Set Bool) := by rw [h]; trivial
      simp at this
    rw [if_neg htrue, if_neg hfalse]
  · exact bool_chain_unmatched_pair_moves_singleton

end CitedLV.Theorem311
