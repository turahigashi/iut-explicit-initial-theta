import Cor312LogVolume.theorem311.SourceSpanTensorPacket

namespace CitedLV.Theorem311

universe uProcession uLabel uPlace uCopy uPacket uBase uAbove uK

abbrev GlobalLocalPacketProduct
    (Label : Type uLabel) (Place : Type uPlace)
    (LocalPacket : Label -> Place -> Type uPacket) (j : Label) :=
  (vQ : Place) -> LocalPacket j vQ

structure LabeledNumberFieldGlobalInclusionRaw
    (Label : Type uLabel) (Place : Type uPlace)
    (Copy : Label -> Type uCopy)
    (LocalPacket : Label -> Place -> Type uPacket) where
  embed : (j : Label) -> Copy j ->
    GlobalLocalPacketProduct Label Place LocalPacket j

structure LabeledNumberFieldGlobalAlgorithmRaw
    (Procession : Type uProcession)
    (Label : Type uLabel) (Place : Type uPlace)
    (Copy : Procession -> Label -> Type uCopy)
    (LocalPacket : Procession -> Label -> Place -> Type uPacket) where
  build : (p : Procession) ->
    LabeledNumberFieldGlobalInclusionRaw Label Place (Copy p) (LocalPacket p)

def GlobalInclusionInjective
    {Label : Type uLabel} {Place : Type uPlace}
    {Copy : Label -> Type uCopy}
    {LocalPacket : Label -> Place -> Type uPacket}
    (R : LabeledNumberFieldGlobalInclusionRaw Label Place Copy LocalPacket) : Prop :=
  forall j, Function.Injective (R.embed j)

def EveryCopyNontrivial
    {Label : Type uLabel} (Copy : Label -> Type uCopy) : Prop :=
  forall j, exists x y : Copy j, x ≠ y

def EveryLabelCopyVisible
    {Label : Type uLabel} {Place : Type uPlace}
    {Copy : Label -> Type uCopy}
    {LocalPacket : Label -> Place -> Type uPacket}
    (R : LabeledNumberFieldGlobalInclusionRaw Label Place Copy LocalPacket) : Prop :=
  forall j, exists x y : Copy j, x ≠ y /\ R.embed j x ≠ R.embed j y

def EveryPlaceCoordinateVisible
    {Label : Type uLabel} {Place : Type uPlace}
    {Copy : Label -> Type uCopy}
    {LocalPacket : Label -> Place -> Type uPacket}
    (R : LabeledNumberFieldGlobalInclusionRaw Label Place Copy LocalPacket) : Prop :=
  forall j vQ, exists x y : Copy j,
    x ≠ y /\ R.embed j x vQ ≠ R.embed j y vQ

def CheckedLabeledGlobalInclusion
    {Label : Type uLabel} {Place : Type uPlace}
    {Copy : Label -> Type uCopy}
    {LocalPacket : Label -> Place -> Type uPacket}
    (R : LabeledNumberFieldGlobalInclusionRaw Label Place Copy LocalPacket) : Prop :=
  Nonempty Label /\ Nonempty Place /\
    EveryCopyNontrivial Copy /\ GlobalInclusionInjective R

theorem injective_nontrivial_gives_label_visibility
    {Label : Type uLabel} {Place : Type uPlace}
    {Copy : Label -> Type uCopy}
    {LocalPacket : Label -> Place -> Type uPacket}
    (R : LabeledNumberFieldGlobalInclusionRaw Label Place Copy LocalPacket)
    (hnontrivial : EveryCopyNontrivial Copy)
    (hinjective : GlobalInclusionInjective R) :
    EveryLabelCopyVisible R := by
  intro j
  obtain ⟨x, y, hxy⟩ := hnontrivial j
  exact ⟨x, y, hxy, fun h => hxy (hinjective j h)⟩

def labeledCopyImage
    {Label : Type uLabel} {Place : Type uPlace}
    {Copy : Label -> Type uCopy}
    {LocalPacket : Label -> Place -> Type uPacket}
    (R : LabeledNumberFieldGlobalInclusionRaw Label Place Copy LocalPacket)
    (j : Label) :
    Set (GlobalLocalPacketProduct Label Place LocalPacket j) :=
  Set.range (R.embed j)

def labeledCopyEmbedding
    {Label : Type uLabel} {Place : Type uPlace}
    {Copy : Label -> Type uCopy}
    {LocalPacket : Label -> Place -> Type uPacket}
    (R : LabeledNumberFieldGlobalInclusionRaw Label Place Copy LocalPacket)
    (hinj : GlobalInclusionInjective R) (j : Label) :
    Copy j ↪ GlobalLocalPacketProduct Label Place LocalPacket j where
  toFun := R.embed j
  inj' := hinj j

abbrev TotalLabeledCopy
    {Label : Type uLabel} (Copy : Label -> Type uCopy) :=
  Sigma Copy

abbrev TotalLabeledGlobalPacket
    (Label : Type uLabel) (Place : Type uPlace)
    (LocalPacket : Label -> Place -> Type uPacket) :=
  Sigma (fun j => GlobalLocalPacketProduct Label Place LocalPacket j)

def totalLabeledEmbed
    {Label : Type uLabel} {Place : Type uPlace}
    {Copy : Label -> Type uCopy}
    {LocalPacket : Label -> Place -> Type uPacket}
    (R : LabeledNumberFieldGlobalInclusionRaw Label Place Copy LocalPacket) :
    TotalLabeledCopy Copy ->
      TotalLabeledGlobalPacket Label Place LocalPacket
  | ⟨j, x⟩ => ⟨j, R.embed j x⟩

theorem total_labeled_embed_preserves_index
    {Label : Type uLabel} {Place : Type uPlace}
    {Copy : Label -> Type uCopy}
    {LocalPacket : Label -> Place -> Type uPacket}
    (R : LabeledNumberFieldGlobalInclusionRaw Label Place Copy LocalPacket)
    (z : TotalLabeledCopy Copy) :
    (totalLabeledEmbed R z).fst = z.fst := by
  cases z
  rfl

theorem total_labeled_embed_separates_distinct_labels
    {Label : Type uLabel} {Place : Type uPlace}
    {Copy : Label -> Type uCopy}
    {LocalPacket : Label -> Place -> Type uPacket}
    (R : LabeledNumberFieldGlobalInclusionRaw Label Place Copy LocalPacket)
    {j k : Label} (x : Copy j) (y : Copy k) (hjk : j ≠ k) :
    totalLabeledEmbed R ⟨j, x⟩ ≠ totalLabeledEmbed R ⟨k, y⟩ := by
  intro h
  apply hjk
  exact congrArg Sigma.fst h

theorem total_labeled_embed_injective
    {Label : Type uLabel} {Place : Type uPlace}
    {Copy : Label -> Type uCopy}
    {LocalPacket : Label -> Place -> Type uPacket}
    (R : LabeledNumberFieldGlobalInclusionRaw Label Place Copy LocalPacket)
    (hinj : GlobalInclusionInjective R) :
    Function.Injective (totalLabeledEmbed R) := by
  rintro ⟨j, x⟩ ⟨k, y⟩ h
  have hjk : j = k := congrArg Sigma.fst h
  subst k
  have hembHeq : HEq (R.embed j x) (R.embed j y) :=
    (Sigma.mk.inj_iff.mp h).2
  have hemb : R.embed j x = R.embed j y := eq_of_heq hembHeq
  have hxy : x = y := hinj j hemb
  subst y
  rfl

abbrev GlobalSourceSpanTensorPacketQ
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) :=
  (vQ : Base) -> SourceSpanTensorPacketQ P j vQ

abbrev SourceSpanNumberFieldGlobalInclusionRaw
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (Copy : Label -> Type uCopy) :=
  LabeledNumberFieldGlobalInclusionRaw Label Base Copy
    (fun j vQ => SourceSpanTensorPacketQ P j vQ)

abbrev GlobalInclusionCheckCopy (_ : Bool) := ℤˣ
abbrev GlobalInclusionCheckPacket (_ : Bool) (_ : Bool) := ℤˣ

def globalInclusionGoodRaw :
    LabeledNumberFieldGlobalInclusionRaw Bool Bool
      GlobalInclusionCheckCopy GlobalInclusionCheckPacket where
  embed := fun _ x _ => x

def globalInclusionConstantRaw :
    LabeledNumberFieldGlobalInclusionRaw Bool Bool
      GlobalInclusionCheckCopy GlobalInclusionCheckPacket where
  embed := fun _ _ _ => 1

def globalInclusionOnePlaceRaw :
    LabeledNumberFieldGlobalInclusionRaw Bool Bool
      GlobalInclusionCheckCopy GlobalInclusionCheckPacket where
  embed := fun _ x vQ => if vQ = false then x else 1

abbrev GlobalInclusionUnitCopy (_ : Bool) := Unit

def globalInclusionUnitRaw :
    LabeledNumberFieldGlobalInclusionRaw Bool Bool
      GlobalInclusionUnitCopy GlobalInclusionCheckPacket where
  embed := fun _ _ _ => 1

def globalInclusionEmptyLabelRaw :
    LabeledNumberFieldGlobalInclusionRaw Empty Bool
      (fun _ => Unit) (fun _ _ => Unit) where
  embed := fun j => nomatch j

def globalInclusionEmptyPlaceUnitRaw :
    LabeledNumberFieldGlobalInclusionRaw Bool Empty
      GlobalInclusionUnitCopy (fun _ _ => Unit) where
  embed := fun _ _ v => nomatch v

theorem global_inclusion_good_injective :
    GlobalInclusionInjective globalInclusionGoodRaw := by
  intro j x y h
  exact congrFun h false

theorem global_inclusion_good_nontrivial :
    EveryCopyNontrivial GlobalInclusionCheckCopy := by
  intro j
  have hne : (1 : ℤˣ) ≠ -1 := by decide
  exact ⟨(1 : GlobalInclusionCheckCopy j),
    (-1 : GlobalInclusionCheckCopy j), hne⟩

theorem global_inclusion_good_every_label_visible :
    EveryLabelCopyVisible globalInclusionGoodRaw :=
  injective_nontrivial_gives_label_visibility
    globalInclusionGoodRaw global_inclusion_good_nontrivial
    global_inclusion_good_injective

theorem global_inclusion_good_every_place_visible :
    EveryPlaceCoordinateVisible globalInclusionGoodRaw := by
  intro j vQ
  have hne : (1 : ℤˣ) ≠ -1 := by decide
  refine ⟨(1 : GlobalInclusionCheckCopy j),
    (-1 : GlobalInclusionCheckCopy j), hne, ?_⟩
  exact hne

theorem global_inclusion_good_checked :
    CheckedLabeledGlobalInclusion globalInclusionGoodRaw :=
  ⟨⟨false⟩, ⟨false⟩, global_inclusion_good_nontrivial,
    global_inclusion_good_injective⟩

theorem global_inclusion_constant_not_injective :
    ¬ GlobalInclusionInjective globalInclusionConstantRaw := by
  intro h
  have heq : (1 : ℤˣ) = -1 := h false (by funext vQ; rfl)
  exact (by decide : (1 : ℤˣ) ≠ -1) heq

theorem global_inclusion_one_place_injective :
    GlobalInclusionInjective globalInclusionOnePlaceRaw := by
  intro j x y h
  have hfalse := congrFun h false
  simpa [globalInclusionOnePlaceRaw] using hfalse

theorem global_inclusion_one_place_not_every_place_visible :
    ¬ EveryPlaceCoordinateVisible globalInclusionOnePlaceRaw := by
  intro h
  obtain ⟨x, y, hxy, hcoord⟩ := h false true
  apply hcoord
  simp [globalInclusionOnePlaceRaw]

theorem global_inclusion_unit_injective :
    GlobalInclusionInjective globalInclusionUnitRaw := by
  intro j x y h
  exact Subsingleton.elim _ _

theorem global_inclusion_unit_not_nontrivial :
    ¬ EveryCopyNontrivial GlobalInclusionUnitCopy := by
  intro h
  obtain ⟨x, y, hxy⟩ := h false
  exact hxy (Subsingleton.elim _ _)

theorem global_inclusion_unit_not_checked :
    ¬ CheckedLabeledGlobalInclusion globalInclusionUnitRaw := by
  intro h
  exact global_inclusion_unit_not_nontrivial h.2.2.1

theorem global_inclusion_empty_label_injective_vacuously :
    GlobalInclusionInjective globalInclusionEmptyLabelRaw := by
  intro j
  exact nomatch j

theorem global_inclusion_empty_label_not_checked :
    ¬ CheckedLabeledGlobalInclusion globalInclusionEmptyLabelRaw := by
  intro h
  rcases h.1 with ⟨j⟩
  exact nomatch j

theorem global_inclusion_empty_place_unit_injective :
    GlobalInclusionInjective globalInclusionEmptyPlaceUnitRaw := by
  intro j x y h
  exact Subsingleton.elim _ _

theorem global_inclusion_empty_place_not_checked :
    ¬ CheckedLabeledGlobalInclusion globalInclusionEmptyPlaceUnitRaw := by
  intro h
  rcases h.2.1 with ⟨v⟩
  exact nomatch v

theorem global_inclusion_good_lands_in_image
    (j : Bool) (x : GlobalInclusionCheckCopy j) :
    globalInclusionGoodRaw.embed j x ∈ labeledCopyImage globalInclusionGoodRaw j :=
  ⟨x, rfl⟩

def globalInclusionEraseLabel :
    TotalLabeledCopy GlobalInclusionCheckCopy -> (Bool -> ℤˣ)
  | ⟨_, x⟩ => fun _ => x

theorem global_inclusion_erasing_map_collapses_labels :
    globalInclusionEraseLabel ⟨false, (1 : ℤˣ)⟩ =
      globalInclusionEraseLabel ⟨true, (1 : ℤˣ)⟩ := by
  rfl

theorem global_inclusion_source_labels_are_distinct :
    (Sigma.mk false (1 : GlobalInclusionCheckCopy false)) ≠
      Sigma.mk true (1 : GlobalInclusionCheckCopy true) := by
  intro h
  have : false = true := congrArg Sigma.fst h
  contradiction

theorem global_inclusion_total_good_injective :
    Function.Injective (totalLabeledEmbed globalInclusionGoodRaw) :=
  total_labeled_embed_injective globalInclusionGoodRaw
    global_inclusion_good_injective

theorem global_inclusion_total_good_separates_labels :
    totalLabeledEmbed globalInclusionGoodRaw
        ⟨false, (1 : GlobalInclusionCheckCopy false)⟩ ≠
      totalLabeledEmbed globalInclusionGoodRaw
        ⟨true, (1 : GlobalInclusionCheckCopy true)⟩ :=
  total_labeled_embed_separates_distinct_labels
    globalInclusionGoodRaw (1 : GlobalInclusionCheckCopy false)
      (1 : GlobalInclusionCheckCopy true) (by decide)

end CitedLV.Theorem311
