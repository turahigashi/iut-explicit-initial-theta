import Cor312LogVolume.theorem311.P211PacketSystem
import Cor312LogVolume.theorem311.BadPlaceLGPSplittingAction
import Cor312LogVolume.theorem311.LabeledGlobalNumberFieldInclusion
import Cor312LogVolume.theorem311.ProcessionFunctorialPolyTransport
import Cor312LogVolume.dispute.Prop310OrdinaryGlobalLocalization

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211RLGPRaw

open CitedLV.Theorem311.P211Packet

abbrev Label := Fin 3
abbrev Bad := Unit

abbrev Psi (_ : Bad) := ℚ_[211]ˣ

abbrev SplitPacket (_ : Bad) (_ : Label) := ℚ_[211]ˣ

def fourteenTorsion : Submonoid (ℚ_[211]ˣ) where
  carrier := {x | x ^ 14 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_pow, ha, hb, one_mul]

def negOneSplit : fourteenTorsion :=
  ⟨-1, by

    show (-1 : ℚ_[211]ˣ) ^ 14 = 1
    exact Even.neg_one_pow (by decide)⟩

theorem negOneSplit_ne_one : negOneSplit ≠ 1 := by
  intro h
  have hval : (-1 : ℚ_[211]ˣ) = 1 :=
    congrArg (fun z : fourteenTorsion => z.1) h
  have hfield : (-1 : ℚ_[211]) = 1 :=
    congrArg (fun z : ℚ_[211]ˣ => (z : ℚ_[211])) hval
  norm_num at hfield

def splitting :
    BadPlaceLGPSplittingRaw Bad Label Psi SplitPacket where
  split := fun _ => fourteenTorsion
  profile := fun _ x _ => x.1
  act := fun _ x p j => x.1 * p j

def neutral (_ : Bad) : SelectedPacketProduct Label SplitPacket () :=
  fun _ => 1

theorem splitting_profile_injective :
    SplitProfileInjective splitting := by
  intro v x y hxy
  apply Subtype.ext
  exact congrFun hxy (0 : Label)

theorem splitting_action_laws :
    SingleMultiplicativeActionLaws splitting := by
  constructor
  · intro v p
    funext j
    simp [splitting]
  · intro v a b p
    funext j
    change (a.1 * b.1) * p j = a.1 * (b.1 * p j)
    exact mul_assoc _ _ _

theorem splitting_action_exposes_profile :
    ActionExposesSplitProfile splitting neutral := by
  intro v x
  funext j
  simp [splitting, neutral]

theorem splitting_nontrivial :
    SplitFamilyNontrivial splitting := by
  intro v
  exact ⟨negOneSplit, negOneSplit_ne_one⟩

theorem splitting_every_label_visible :
    EveryLabelCoordinateVisible splitting := by
  intro v j
  refine ⟨1, negOneSplit, ?_, ?_⟩
  · exact fun h => negOneSplit_ne_one h.symm
  · change (1 : ℚ_[211]ˣ) ≠ -1
    intro h
    have hfield : (1 : ℚ_[211]) = -1 :=
      congrArg (fun z : ℚ_[211]ˣ => (z : ℚ_[211])) h
    norm_num at hfield

theorem splitting_action_visible :
    SplitActionVisible splitting := by
  intro v
  refine ⟨negOneSplit, neutral v, ?_⟩
  intro h
  apply negOneSplit_ne_one
  apply Subtype.ext
  have h0 := congrFun h (0 : Label)
  simpa [splitting, neutral] using h0

theorem splitting_checked :
    CheckedBadPlaceSplitting splitting neutral := by
  exact ⟨⟨()⟩, ⟨(0 : Label)⟩,
    splitting_profile_injective,
    splitting_action_laws,
    splitting_action_exposes_profile,
    splitting_nontrivial,
    splitting_every_label_visible,
    splitting_action_visible⟩

theorem psi_isUnit (y : ℚ_[211]ˣ) : IsUnit y := by
  refine isUnit_iff_exists_inv.mpr ⟨y⁻¹, ?_⟩
  exact mul_inv_cancel y

theorem fourteenTorsion_isUnit (x : fourteenTorsion) : IsUnit x := by
  let z : fourteenTorsion :=
    ⟨x.1⁻¹, by

      show (x.1⁻¹ : ℚ_[211]ˣ) ^ 14 = 1
      rw [inv_pow, show (x.1 : ℚ_[211]ˣ) ^ 14 = 1 from x.2, inv_one]⟩
  refine isUnit_iff_exists_inv.mpr ⟨z, ?_⟩
  apply Subtype.ext
  exact mul_inv_cancel x.1

theorem splitting_units_exactly_two_l_torsion :
    SplitUnitsExactlyAmbientTwoLTorsion splitting 7 := by
  intro v y
  constructor
  · rintro ⟨x, _hxunit, rfl⟩
    refine ⟨psi_isUnit x.1, ?_⟩

    show (x.1 : ℚ_[211]ˣ) ^ (2 * 7) = 1
    norm_num
    exact x.2
  · rintro ⟨_hyunit, hy⟩
    let x : fourteenTorsion :=
      ⟨y, by
        show (y : ℚ_[211]ˣ) ^ 14 = 1
        have := hy
        norm_num at this
        exact this⟩
    exact ⟨x, fourteenTorsion_isUnit x, rfl⟩

namespace Global

open Dispute.Prop310OrdinaryGlobalLocalization
open scoped NumberField

abbrev Place := Dispute.Prop310OrdinaryGlobalLocalization.Place ℚ
abbrev GlobalCopy (_ : Label) := ℚˣ
abbrev GlobalLocalPacket (_ : Label) (w : Place) :=
  (Dispute.Prop310OrdinaryGlobalLocalization.LocalField ℚ w)ˣ

def fieldCopy :
    LabeledNumberFieldGlobalInclusionRaw
      Label Place GlobalCopy GlobalLocalPacket where
  embed := fun _ x w =>
    Dispute.Prop310OrdinaryGlobalLocalization.localizeUnits ℚ w x

theorem fieldCopy_injective :
    GlobalInclusionInjective fieldCopy := by
  intro j
  simpa [fieldCopy] using
    (Dispute.Prop310OrdinaryGlobalLocalization.ordinaryGlobalInclusion_injective ℚ) ()

theorem fieldCopy_nontrivial :
    EveryCopyNontrivial GlobalCopy := by
  intro j
  exact ⟨1, -1, by norm_num⟩

theorem fieldCopy_checked :
    CheckedLabeledGlobalInclusion fieldCopy := by
  exact ⟨⟨(0 : Label)⟩,
    ⟨Sum.inr ((inferInstance : Nonempty (ℚ →+* ℂ)).some)⟩,
    fieldCopy_nontrivial, fieldCopy_injective⟩

end Global

abbrev SplittingDatum :=
  BadPlaceLGPSplittingRaw Bad Label Psi SplitPacket

abbrev FieldCopyDatum :=
  LabeledNumberFieldGlobalInclusionRaw
    Label Global.Place Global.GlobalCopy Global.GlobalLocalPacket

def components :
    RLGPRawComponents
      p211PacketSystem.Regions SplittingDatum FieldCopyDatum where
  packet := p211QRegion
  splitting := splitting
  fieldCopy := Global.fieldCopy

theorem components_check :
    p211PacketSystem.procVol components.packet =
        -(29 / 7) * Real.log 211 ∧
      CheckedBadPlaceSplitting components.splitting neutral ∧
      SplitUnitsExactlyAmbientTwoLTorsion components.splitting 7 ∧
      CheckedLabeledGlobalInclusion components.fieldCopy := by
  exact ⟨p211_procVol, splitting_checked,
    splitting_units_exactly_two_l_torsion, Global.fieldCopy_checked⟩

end CitedLV.Theorem311.P211RLGPRaw
end
