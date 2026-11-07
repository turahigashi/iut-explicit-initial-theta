import Cor312LogVolume.theorem311.FiberArithmeticDivisorDegree
import Cor312LogVolume.thetalink.TorsionQuotientSplittingBoundary

namespace CitedLV.Theorem311

universe uBad uLabel uPsi uPacket uProcession uQuot

structure BadPlaceIndexRaw (Slot : Type uBad) (Place : Type uPsi) where
  place : Slot -> Place

def IndexesOnlyBad
    {Slot : Type uBad} {Place : Type uPsi}
    (I : BadPlaceIndexRaw Slot Place) (IsBad : Place -> Prop) : Prop :=
  forall s, IsBad (I.place s)

def IndexesEveryBad
    {Slot : Type uBad} {Place : Type uPsi}
    (I : BadPlaceIndexRaw Slot Place) (IsBad : Place -> Prop) : Prop :=
  forall v, IsBad v -> exists s, I.place s = v

def IndexesExactlyBad
    {Slot : Type uBad} {Place : Type uPsi}
    (I : BadPlaceIndexRaw Slot Place) (IsBad : Place -> Prop) : Prop :=
  Function.Injective I.place /\ IndexesOnlyBad I IsBad /\
    IndexesEveryBad I IsBad

abbrev SelectedPacketProduct
    {Bad : Type uBad} (Label : Type uLabel)
    (Packet : Bad -> Label -> Type uPacket) (v : Bad) :=
  (j : Label) -> Packet v j

structure BadPlaceLGPSplittingRaw
    (Bad : Type uBad) (Label : Type uLabel)
    (Psi : Bad -> Type uPsi) (Packet : Bad -> Label -> Type uPacket)
    [forall v, Monoid (Psi v)] where
  split : (v : Bad) -> Submonoid (Psi v)
  profile : (v : Bad) -> split v -> SelectedPacketProduct Label Packet v
  act : (v : Bad) -> split v -> SelectedPacketProduct Label Packet v ->
    SelectedPacketProduct Label Packet v

structure BadPlaceLGPSplittingAlgorithmRaw
    (Procession : Type uProcession)
    (Bad : Type uBad) (Label : Type uLabel)
    (Psi : Procession -> Bad -> Type uPsi)
    (Packet : Procession -> Bad -> Label -> Type uPacket)
    [forall p v, Monoid (Psi p v)] where
  build : (p : Procession) ->
    BadPlaceLGPSplittingRaw Bad Label (Psi p) (Packet p)

def SplitProfileMultiplicativeLaws
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)] [forall v j, Monoid (Packet v j)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet) : Prop :=
  forall v, CitedLV.ThetaLink.MultiplicativeMapLaws (R.profile v)

def SplitProfileInjective
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet) : Prop :=
  forall v, Function.Injective (R.profile v)

def SingleMultiplicativeActionLaws
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet) : Prop :=
  (forall v p, R.act v 1 p = p) /\
    (forall v a b p, R.act v (a * b) p = R.act v a (R.act v b p))

def ActionExposesSplitProfile
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet)
    (neutral : (v : Bad) -> SelectedPacketProduct Label Packet v) : Prop :=
  forall v x, R.act v x (neutral v) = R.profile v x

def SplitFamilyNontrivial
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet) : Prop :=
  forall v, exists x : R.split v, x ≠ 1

def SplitProfileVisible
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet) : Prop :=
  forall v, exists x y : R.split v, x ≠ y /\ R.profile v x ≠ R.profile v y

def EveryLabelCoordinateVisible
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet) : Prop :=
  forall v j, exists x y : R.split v,
    x ≠ y /\ R.profile v x j ≠ R.profile v y j

def SplitActionVisible
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet) : Prop :=
  forall v, exists x : R.split v,
    exists p : SelectedPacketProduct Label Packet v, R.act v x p ≠ p

def SplitUnitsExactlyAmbientLevelTorsion
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet) (level : Nat) : Prop :=
  forall v (y : Psi v),
    (exists x : R.split v, IsUnit x /\ (x.1 : Psi v) = y) <->
      IsUnit y /\ y ^ level = 1

def SplitUnitsExactlyAmbientTwoLTorsion
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet) (l : Nat) : Prop :=
  SplitUnitsExactlyAmbientLevelTorsion R (2 * l)

def CheckedBadPlaceSplitting
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet)
    (neutral : (v : Bad) -> SelectedPacketProduct Label Packet v) : Prop :=
  Nonempty Bad /\ Nonempty Label /\
    SplitProfileInjective R /\ SingleMultiplicativeActionLaws R /\
    ActionExposesSplitProfile R neutral /\ SplitFamilyNontrivial R /\
    EveryLabelCoordinateVisible R /\ SplitActionVisible R

def CheckedBadPlaceFamily
    {Bad : Type uBad} {Place : Type uPsi} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)]
    (I : BadPlaceIndexRaw Bad Place) (IsBad : Place -> Prop)
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet)
    (neutral : (v : Bad) -> SelectedPacketProduct Label Packet v) : Prop :=
  IndexesExactlyBad I IsBad /\ CheckedBadPlaceSplitting R neutral

def productImageSet
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet) (v : Bad) :
    Set (SelectedPacketProduct Label Packet v) :=
  Set.range (R.profile v)

def splitProfileMonoidHom
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)] [forall v j, Monoid (Packet v j)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet)
    (hmul : SplitProfileMultiplicativeLaws R) (v : Bad) :
    R.split v →* SelectedPacketProduct Label Packet v :=
  CitedLV.ThetaLink.multiplicativeMapMonoidHom (R.profile v) (hmul v)

def splitProfileEmbedding
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet)
    (hinj : SplitProfileInjective R) (v : Bad) :
    R.split v ↪ SelectedPacketProduct Label Packet v where
  toFun := R.profile v
  inj' := hinj v

def productImageSubmonoid
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)] [forall v j, Monoid (Packet v j)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet)
    (hmul : SplitProfileMultiplicativeLaws R) (v : Bad) :
    Submonoid (SelectedPacketProduct Label Packet v) :=
  (Submonoid.map (splitProfileMonoidHom R hmul v)
    (⊤ : Submonoid (R.split v)))

@[reducible]
def actionLawsGiveProductMulAction
    {Bad : Type uBad} {Label : Type uLabel}
    {Psi : Bad -> Type uPsi} {Packet : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Psi v)]
    (R : BadPlaceLGPSplittingRaw Bad Label Psi Packet)
    (hact : SingleMultiplicativeActionLaws R) (v : Bad) :
    MulAction (R.split v) (SelectedPacketProduct Label Packet v) where
  smul := R.act v
  one_smul := hact.1 v
  mul_smul := hact.2 v

structure BadPlaceTorsionQuotientRaw
    (Split : Type uPsi) (Quotient : Type uQuot) where
  quotient : Split -> Quotient

def TorsionQuotientSurjective
    {Split : Type uPsi} {Quotient : Type uQuot}
    (Q : BadPlaceTorsionQuotientRaw Split Quotient) : Prop :=
  Function.Surjective Q.quotient

def TorsionQuotientInjective
    {Split : Type uPsi} {Quotient : Type uQuot}
    (Q : BadPlaceTorsionQuotientRaw Split Quotient) : Prop :=
  Function.Injective Q.quotient

def TorsionQuotientMultiplicativeLaws
    {Split : Type uPsi} {Quotient : Type uQuot}
    [Monoid Split] [Monoid Quotient]
    (Q : BadPlaceTorsionQuotientRaw Split Quotient) : Prop :=
  CitedLV.ThetaLink.MultiplicativeMapLaws Q.quotient

def TorsionQuotientKernelExactly
    {Split : Type uPsi} {Quotient : Type uQuot}
    [One Split] [One Quotient]
    (Q : BadPlaceTorsionQuotientRaw Split Quotient)
    (Torsion : Split -> Prop) : Prop :=
  forall x, Q.quotient x = Q.quotient 1 <-> Torsion x

def CheckIsBad (v : Bool) : Prop := v = false

abbrev CheckBadPlace := {v : Bool // CheckIsBad v}

abbrev CheckPsi (_ : CheckBadPlace) := ℤˣ
abbrev CheckPacket (_ : CheckBadPlace) (_ : Bool) := ℤˣ

def checkBadIndex : BadPlaceIndexRaw CheckBadPlace Bool where
  place := Subtype.val

def checkWrongGoodIndex : BadPlaceIndexRaw Unit Bool where
  place := fun _ => true

def checkGoodRaw :
    BadPlaceLGPSplittingRaw CheckBadPlace Bool CheckPsi CheckPacket where
  split := fun _ => ⊤
  profile := fun _ x _ => x.1
  act := fun _ x p j => x.1 * p j

def checkConstantRaw :
    BadPlaceLGPSplittingRaw CheckBadPlace Bool CheckPsi CheckPacket where
  split := fun _ => ⊤
  profile := fun _ _ _ => 1
  act := fun _ _ p => p

def checkIdentityActionRaw :
    BadPlaceLGPSplittingRaw CheckBadPlace Bool CheckPsi CheckPacket where
  split := fun _ => ⊤
  profile := fun _ x _ => x.1
  act := fun _ _ p => p

def checkOneLabelRaw :
    BadPlaceLGPSplittingRaw CheckBadPlace Bool CheckPsi CheckPacket where
  split := fun _ => ⊤
  profile := fun _ x j => if j then 1 else x.1
  act := fun _ x p j => if j then p j else x.1 * p j

def checkBottomRaw :
    BadPlaceLGPSplittingRaw CheckBadPlace Bool CheckPsi CheckPacket where
  split := fun _ => ⊥
  profile := fun _ x _ => x.1
  act := fun _ x p j => x.1 * p j

def checkNeutralProduct (_ : CheckBadPlace) : Bool -> ℤˣ := fun _ => 1

theorem check_bad_index_is_exact :
    IndexesExactlyBad checkBadIndex CheckIsBad := by
  refine ⟨?_, ?_, ?_⟩
  · exact Subtype.val_injective
  · intro v
    exact v.2
  · intro v hv
    exact ⟨⟨v, hv⟩, rfl⟩

theorem check_wrong_good_index_is_rejected :
    ¬ (IndexesOnlyBad checkWrongGoodIndex CheckIsBad) := by
  intro h
  have hbad := h ()
  simp [checkWrongGoodIndex, CheckIsBad] at hbad

theorem check_good_profile_multiplicative :
    SplitProfileMultiplicativeLaws checkGoodRaw := by
  intro v
  constructor
  · funext j
    rfl
  · intro x y
    funext j
    rfl

theorem check_good_profile_injective :
    SplitProfileInjective checkGoodRaw := by
  intro v x y hxy
  apply Subtype.ext
  exact congrFun hxy false

theorem check_good_action_laws :
    SingleMultiplicativeActionLaws checkGoodRaw := by
  constructor
  · intro v p
    funext j
    simp [checkGoodRaw]
  · intro v a b p
    funext j
    change (a.1 * b.1) * p j = a.1 * (b.1 * p j)
    exact mul_assoc _ _ _

theorem check_good_action_exposes_profile :
    ActionExposesSplitProfile checkGoodRaw checkNeutralProduct := by
  intro v x
  funext j
  simp [checkGoodRaw, checkNeutralProduct]

theorem check_good_split_nontrivial :
    SplitFamilyNontrivial checkGoodRaw := by
  intro v
  refine ⟨⟨(-1 : ℤˣ), by simp [checkGoodRaw]⟩, ?_⟩
  intro h
  have : (-1 : ℤˣ) = 1 := congrArg Subtype.val h
  exact (by decide : (-1 : ℤˣ) ≠ 1) this

theorem check_good_profile_visible :
    SplitProfileVisible checkGoodRaw := by
  intro v
  refine ⟨⟨(1 : ℤˣ), by simp [checkGoodRaw]⟩,
    ⟨(-1 : ℤˣ), by simp [checkGoodRaw]⟩, ?_, ?_⟩
  · intro h
    have : (1 : ℤˣ) = -1 := congrArg Subtype.val h
    exact (by decide : (1 : ℤˣ) ≠ -1) this
  · intro h
    have : (1 : ℤˣ) = -1 := congrFun h false
    exact (by decide : (1 : ℤˣ) ≠ -1) this

theorem check_good_every_label_visible :
    EveryLabelCoordinateVisible checkGoodRaw := by
  intro v j
  refine ⟨⟨(1 : ℤˣ), by simp [checkGoodRaw]⟩,
    ⟨(-1 : ℤˣ), by simp [checkGoodRaw]⟩, ?_, ?_⟩
  · intro h
    have : (1 : ℤˣ) = -1 := congrArg Subtype.val h
    exact (by decide : (1 : ℤˣ) ≠ -1) this
  · exact (by decide : (1 : ℤˣ) ≠ -1)

theorem check_good_action_visible :
    SplitActionVisible checkGoodRaw := by
  intro v
  refine ⟨⟨(-1 : ℤˣ), by simp [checkGoodRaw]⟩,
    checkNeutralProduct v, ?_⟩
  intro h
  have : (-1 : ℤˣ) = 1 := congrFun h false
  exact (by decide : (-1 : ℤˣ) ≠ 1) this

theorem check_good_passes_combined_gate :
    CheckedBadPlaceSplitting checkGoodRaw checkNeutralProduct := by
  exact ⟨⟨⟨false, rfl⟩⟩, ⟨false⟩,
    check_good_profile_injective, check_good_action_laws,
    check_good_action_exposes_profile, check_good_split_nontrivial,
    check_good_every_label_visible, check_good_action_visible⟩

theorem check_good_passes_full_bad_place_gate :
    CheckedBadPlaceFamily checkBadIndex CheckIsBad
      checkGoodRaw checkNeutralProduct := by
  exact ⟨check_bad_index_is_exact, check_good_passes_combined_gate⟩

theorem check_good_units_are_exactly_level_two_torsion :
    SplitUnitsExactlyAmbientLevelTorsion checkGoodRaw 2 := by
  intro v y
  constructor
  · intro h
    have hall : forall z : ℤˣ, z ^ 2 = 1 := by decide
    exact ⟨isUnit_iff_exists_inv.mpr ⟨y⁻¹, mul_inv_cancel y⟩, hall y⟩
  · intro h
    refine ⟨⟨y, by simp [checkGoodRaw]⟩, ?_, rfl⟩
    refine isUnit_iff_exists_inv.mpr
      ⟨⟨y⁻¹, by simp [checkGoodRaw]⟩, ?_⟩
    apply Subtype.ext
    exact mul_inv_cancel y

theorem check_good_units_fail_level_one_torsion :
    ¬ (SplitUnitsExactlyAmbientLevelTorsion checkGoodRaw 1) := by
  intro h
  let v : CheckBadPlace := ⟨false, rfl⟩
  let x : checkGoodRaw.split v :=
    ⟨(-1 : ℤˣ), by simp [checkGoodRaw]⟩
  have hxunit : IsUnit x := by
    refine isUnit_iff_exists_inv.mpr
      ⟨⟨(-1 : ℤˣ), by simp [checkGoodRaw]⟩, ?_⟩
    rfl
  have hright := (h v (-1)).mp ⟨x, hxunit, rfl⟩
  norm_num at hright

theorem check_one_label_profile_injective :
    SplitProfileInjective checkOneLabelRaw := by
  intro v x y hxy
  apply Subtype.ext
  have hfalse := congrFun hxy false
  simpa [checkOneLabelRaw] using hfalse

theorem check_one_label_action_laws :
    SingleMultiplicativeActionLaws checkOneLabelRaw := by
  constructor
  · intro v p
    funext j
    fin_cases j <;> simp [checkOneLabelRaw]
  · intro v a b p
    funext j
    cases j with
    | false =>
      change (a.1 * b.1) * p false = a.1 * (b.1 * p false)
      exact mul_assoc _ _ _
    | true => rfl

theorem check_one_label_exposes_profile :
    ActionExposesSplitProfile checkOneLabelRaw checkNeutralProduct := by
  intro v x
  funext j
  fin_cases j <;> simp [checkOneLabelRaw, checkNeutralProduct]

theorem check_one_label_erasure_is_rejected :
    ¬ (EveryLabelCoordinateVisible checkOneLabelRaw) := by
  intro h
  obtain ⟨x, y, hxy, hvisible⟩ := h ⟨false, rfl⟩ true
  apply hvisible
  simp [checkOneLabelRaw]

theorem check_constant_passes_weak_laws :
    SplitProfileMultiplicativeLaws checkConstantRaw /\
      SingleMultiplicativeActionLaws checkConstantRaw := by
  constructor
  · intro v
    constructor
    · funext j
      rfl
    · intro x y
      funext j
      rfl
  · constructor
    · intro v p
      rfl
    · intro v a b p
      rfl

theorem check_constant_profile_not_injective :
    ¬ (SplitProfileInjective checkConstantRaw) := by
  intro h
  let v : CheckBadPlace := ⟨false, rfl⟩
  let x : checkConstantRaw.split v :=
    ⟨(1 : ℤˣ), by simp [checkConstantRaw]⟩
  let y : checkConstantRaw.split v :=
    ⟨(-1 : ℤˣ), by simp [checkConstantRaw]⟩
  have hprofile : checkConstantRaw.profile v x =
      checkConstantRaw.profile v y := by
    funext j
    rfl
  have heq : (1 : ℤˣ) = -1 := congrArg Subtype.val (h v hprofile)
  exact (by decide : (1 : ℤˣ) ≠ -1) heq

theorem check_constant_profile_not_visible :
    ¬ (SplitProfileVisible checkConstantRaw) := by
  intro h
  obtain ⟨x, y, hxy, hprofile⟩ := h ⟨false, rfl⟩
  apply hprofile
  funext j
  rfl

theorem check_constant_action_not_visible :
    ¬ (SplitActionVisible checkConstantRaw) := by
  intro h
  obtain ⟨x, p, hp⟩ := h ⟨false, rfl⟩
  exact hp rfl

theorem check_identity_action_fails_exposure :
    ¬ (ActionExposesSplitProfile checkIdentityActionRaw checkNeutralProduct) := by
  intro h
  have heq := congrFun (h ⟨false, rfl⟩
    (⟨(-1 : ℤˣ), by simp [checkIdentityActionRaw]⟩ :
      checkIdentityActionRaw.split ⟨false, rfl⟩)) false
  exact (by decide : (1 : ℤˣ) ≠ -1) heq

theorem check_bottom_fails_nontriviality :
    ¬ (SplitFamilyNontrivial checkBottomRaw) := by
  intro h
  obtain ⟨x, hx⟩ := h ⟨false, rfl⟩
  apply hx
  apply Subtype.ext
  exact Submonoid.mem_bot.mp x.2

theorem check_good_place_not_indexed :
    ¬ (exists v : CheckBadPlace, v.1 = true) := by
  rintro ⟨v, hv⟩
  have hbad : v.1 = false := v.2
  simp [hv] at hbad

def checkTorsionQuotient : BadPlaceTorsionQuotientRaw ℤˣ Unit where
  quotient := fun _ => ()

theorem check_torsion_quotient_surjective :
    TorsionQuotientSurjective checkTorsionQuotient := by
  intro y
  exact ⟨1, Subsingleton.elim _ _⟩

theorem check_torsion_quotient_multiplicative :
    TorsionQuotientMultiplicativeLaws checkTorsionQuotient := by
  constructor
  · rfl
  · intro x y
    rfl

theorem check_torsion_quotient_kernel_is_all :
    TorsionQuotientKernelExactly checkTorsionQuotient (fun _ => True) := by
  intro x
  simp [checkTorsionQuotient]

theorem check_torsion_quotient_not_injective :
    ¬ (TorsionQuotientInjective checkTorsionQuotient) := by
  intro h
  have heq : (1 : ℤˣ) = -1 := h rfl
  exact (by decide : (1 : ℤˣ) ≠ -1) heq

end CitedLV.Theorem311
