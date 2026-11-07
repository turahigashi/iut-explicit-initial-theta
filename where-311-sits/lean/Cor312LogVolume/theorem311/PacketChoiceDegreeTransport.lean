import Cor312LogVolume.theorem311.PacketDegreeWeightedNormalization

namespace CitedLV.Theorem311

open scoped BigOperators TensorProduct

universe uLift uDegreeBase uBase uAbove uLabel uK

def choiceReindexMap
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    (toBase : Lift -> DegreeBase) (n : Nat) :
    (Fin n -> Lift) -> (Fin n -> DegreeBase) :=
  fun choice alpha => toBase (choice alpha)

def choiceReindexEquiv
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    (e : Lift ≃ DegreeBase) (n : Nat) :
    (Fin n -> Lift) ≃ (Fin n -> DegreeBase) :=
  Equiv.piCongrRight (fun _ => e)

structure LiftBaseTransportCandidate
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    (D : RawPacketDegreeData Lift DegreeBase) where
  placeEquiv : Lift ≃ DegreeBase
  toBase_compat : forall u, placeEquiv u = D.toBase u

noncomputable def liftBaseTransportOfBijective
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    (D : RawPacketDegreeData Lift DegreeBase)
    (h : LiftToBaseBijective D) : LiftBaseTransportCandidate D where
  placeEquiv := Equiv.ofBijective D.toBase h
  toBase_compat := fun _ => rfl

theorem choice_reindex_eq_baseChoice
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    {D : RawPacketDegreeData Lift DegreeBase}
    (T : LiftBaseTransportCandidate D) (n : Nat)
    (choice : Fin n -> Lift) :
    choiceReindexEquiv T.placeEquiv n choice = baseChoiceOfLift D choice := by
  funext alpha
  exact T.toBase_compat (choice alpha)

theorem choice_reindex_bijective_iff_of_index
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    (toBase : Lift -> DegreeBase) (n : Nat) (alpha0 : Fin n) :
    Function.Bijective (choiceReindexMap toBase n) <->
      Function.Bijective toBase := by
  constructor
  · intro h
    constructor
    · intro x y hxy
      let cx : Fin n -> Lift := fun _ => x
      let cy : Fin n -> Lift := fun _ => y
      have hc : choiceReindexMap toBase n cx = choiceReindexMap toBase n cy := by
        funext alpha
        exact hxy
      exact congrFun (h.1 hc) alpha0
    · intro y
      let target : Fin n -> DegreeBase := fun _ => y
      obtain ⟨choice, hchoice⟩ := h.2 target
      refine ⟨choice alpha0, ?_⟩
      exact congrFun hchoice alpha0
  · intro h
    let e : Lift ≃ DegreeBase := Equiv.ofBijective toBase h
    simpa [choiceReindexMap, choiceReindexEquiv, e] using
      (choiceReindexEquiv e n).bijective

theorem zero_choice_reindex_can_hide_nonbijectivity :
    Function.Bijective (choiceReindexMap (fun _ : Bool => ()) 0) /\
      ¬ Function.Bijective (fun _ : Bool => ()) := by
  constructor
  · constructor
    · intro f g _
      funext alpha
      exact Fin.elim0 alpha
    · intro g
      refine ⟨fun alpha => Fin.elim0 alpha, ?_⟩
      funext alpha
      exact Fin.elim0 alpha
  · intro h
    have hinj : Function.Injective (fun _ : Bool => ()) := h.1
    have hfalseTrue : false = true := hinj (by rfl)
    exact Bool.noConfusion hfalseTrue

def transportedBaseDegree
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    {D : RawPacketDegreeData Lift DegreeBase}
    (T : LiftBaseTransportCandidate D) : Lift -> Real :=
  fun u => D.baseDegree (T.placeEquiv u)

def ExactTransportedDegree
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    {D : RawPacketDegreeData Lift DegreeBase}
    (T : LiftBaseTransportCandidate D) (liftDegree : Lift -> Real) : Prop :=
  forall u, liftDegree u = D.baseDegree (T.placeEquiv u)

theorem transported_base_degree_is_exact
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    {D : RawPacketDegreeData Lift DegreeBase}
    (T : LiftBaseTransportCandidate D) :
    ExactTransportedDegree T (transportedBaseDegree T) := by
  intro u
  rfl

theorem choice_degree_product_transport
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    {D : RawPacketDegreeData Lift DegreeBase}
    (T : LiftBaseTransportCandidate D) (n : Nat)
    (choice : Fin n -> Lift) :
    choiceDegreeProduct n (transportedBaseDegree T) choice =
      choiceDegreeProduct n D.baseDegree
        (choiceReindexEquiv T.placeEquiv n choice) := by
  rfl

theorem choice_degree_mass_transport
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    [Fintype Lift] [Fintype DegreeBase]
    {D : RawPacketDegreeData Lift DegreeBase}
    (T : LiftBaseTransportCandidate D) (n : Nat) :
    choiceDegreeMass n (transportedBaseDegree T) =
      choiceDegreeMass n D.baseDegree := by
  classical
  unfold choiceDegreeMass
  exact Fintype.sum_equiv (choiceReindexEquiv T.placeEquiv n)
    _ _ (fun choice => choice_degree_product_transport T n choice)

theorem normalized_choice_weight_transport
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    [Fintype Lift] [Fintype DegreeBase]
    {D : RawPacketDegreeData Lift DegreeBase}
    (T : LiftBaseTransportCandidate D) (n : Nat)
    (choice : Fin n -> Lift) :
    thm110NormalizedChoiceWeight n (transportedBaseDegree T) choice =
      thm110NormalizedChoiceWeight n D.baseDegree
        (choiceReindexEquiv T.placeEquiv n choice) := by
  unfold thm110NormalizedChoiceWeight
  rw [choice_degree_product_transport T n choice,
    choice_degree_mass_transport T n]

noncomputable def fullChoiceNormalizedMean
    {E : Type uLift} [Fintype E]
    (n : Nat) (degree : E -> Real)
    (profile : (Fin n -> E) -> Real) : Real :=
  (∑ choice : Fin n -> E,
      choiceDegreeProduct n degree choice * profile choice) /
    choiceDegreeMass n degree

def pushChoiceProfileToBase
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    {D : RawPacketDegreeData Lift DegreeBase}
    (T : LiftBaseTransportCandidate D) (n : Nat)
    (profile : (Fin n -> Lift) -> Real) :
    (Fin n -> DegreeBase) -> Real :=
  fun baseChoice => profile ((choiceReindexEquiv T.placeEquiv n).symm baseChoice)

theorem full_choice_normalized_mean_transport
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    [Fintype Lift] [Fintype DegreeBase]
    {D : RawPacketDegreeData Lift DegreeBase}
    (T : LiftBaseTransportCandidate D) (n : Nat)
    (profile : (Fin n -> Lift) -> Real) :
    fullChoiceNormalizedMean n (transportedBaseDegree T) profile =
      fullChoiceNormalizedMean n D.baseDegree
        (pushChoiceProfileToBase T n profile) := by
  classical
  unfold fullChoiceNormalizedMean
  rw [choice_degree_mass_transport T n]
  congr 1
  exact Fintype.sum_equiv (choiceReindexEquiv T.placeEquiv n) _ _
    (fun choice => by
      rw [choice_degree_product_transport T n choice]
      simp [pushChoiceProfileToBase])

noncomputable def sourceSpanBaseIndexedDegreeWeightedMean
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {DegreeBase : Type uDegreeBase}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [Fintype (Above vQ)] [Fintype DegreeBase]
    (D : RawPacketDegreeData (Above vQ) DegreeBase)
    (T : LiftBaseTransportCandidate D)
    (z : SourceSpanTensorPacketQ P j vQ)
    (readout : (choice : SourcePacketChoice Above arity j vQ) ->
      SourceSpanChoiceTensor P j vQ choice -> Real) : Real :=
  fullChoiceNormalizedMean (arity j + 1) D.baseDegree
    (pushChoiceProfileToBase T (arity j + 1)
      (decompositionChoiceProfile P j vQ z readout))

theorem sourceSpan_thm110_mean_reindexes_to_base
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {DegreeBase : Type uDegreeBase}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [Fintype (Above vQ)] [Fintype DegreeBase]
    (D : RawPacketDegreeData (Above vQ) DegreeBase)
    (T : LiftBaseTransportCandidate D)
    (z : SourceSpanTensorPacketQ P j vQ)
    (readout : (choice : SourcePacketChoice Above arity j vQ) ->
      SourceSpanChoiceTensor P j vQ choice -> Real) :
    sourceSpanThm110DegreeWeightedMean P j vQ z
        (transportedBaseDegree T) readout =
      sourceSpanBaseIndexedDegreeWeightedMean P j vQ D T z readout := by
  change fullChoiceNormalizedMean (arity j + 1)
      (transportedBaseDegree T)
      (decompositionChoiceProfile P j vQ z readout) = _
  exact full_choice_normalized_mean_transport T (arity j + 1)
    (decompositionChoiceProfile P j vQ z readout)

def relativeDegreeOnBase
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    {D : RawPacketDegreeData Lift DegreeBase}
    (T : LiftBaseTransportCandidate D) : DegreeBase -> Real :=
  fun v => D.relativeDegree (T.placeEquiv.symm v)

noncomputable def iut3RawBaseChoiceWeight
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    [Fintype DegreeBase]
    {D : RawPacketDegreeData Lift DegreeBase}
    (T : LiftBaseTransportCandidate D) (n : Nat)
    (baseChoice : Fin n -> DegreeBase) : Real :=
  1 / (choiceDegreeProduct n (relativeDegreeOnBase T) baseChoice *
    choiceDegreeMass n D.baseDegree)

theorem iut3_raw_weight_transport
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    [Fintype DegreeBase]
    {D : RawPacketDegreeData Lift DegreeBase}
    (T : LiftBaseTransportCandidate D) (n : Nat)
    (choice : Fin n -> Lift) :
    iut3RawChoiceWeight D n choice =
      iut3RawBaseChoiceWeight T n
        (choiceReindexEquiv T.placeEquiv n choice) := by
  unfold iut3RawChoiceWeight iut3RawBaseChoiceWeight
  congr 3
  ext alpha
  simp [choiceReindexEquiv]

noncomputable def iut3RawBaseChoiceValue
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    [Fintype DegreeBase]
    {D : RawPacketDegreeData Lift DegreeBase}
    (T : LiftBaseTransportCandidate D) (n : Nat)
    (profile : (Fin n -> Lift) -> Real) : Real :=
  ∑ baseChoice : Fin n -> DegreeBase,
    iut3RawBaseChoiceWeight T n baseChoice *
      pushChoiceProfileToBase T n profile baseChoice

theorem iut3_raw_choice_value_transport
    {Lift : Type uLift} {DegreeBase : Type uDegreeBase}
    [Fintype Lift] [Fintype DegreeBase]
    {D : RawPacketDegreeData Lift DegreeBase}
    (T : LiftBaseTransportCandidate D) (n : Nat)
    (profile : (Fin n -> Lift) -> Real) :
    (∑ choice : Fin n -> Lift,
      iut3RawChoiceWeight D n choice * profile choice) =
      iut3RawBaseChoiceValue T n profile := by
  classical
  unfold iut3RawBaseChoiceValue
  exact Fintype.sum_equiv (choiceReindexEquiv T.placeEquiv n) _ _
    (fun choice => by
      rw [iut3_raw_weight_transport T n choice]
      simp [pushChoiceProfileToBase])

theorem sourceSpan_iut3_raw_value_reindexes_to_base
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {DegreeBase : Type uDegreeBase}
    {Label : Type uLabel} {arity : Label -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (P : SourceShapedLocalMonoanalyticQSpanRaw Base Above Label arity K)
    (j : Label) (vQ : Base) [Fintype (Above vQ)] [Fintype DegreeBase]
    (D : RawPacketDegreeData (Above vQ) DegreeBase)
    (T : LiftBaseTransportCandidate D)
    (z : SourceSpanTensorPacketQ P j vQ)
    (readout : (choice : SourcePacketChoice Above arity j vQ) ->
      SourceSpanChoiceTensor P j vQ choice -> Real) :
    sourceSpanIUT3RawDegreeWeightedValue P j vQ D z readout =
      iut3RawBaseChoiceValue T (arity j + 1)
        (decompositionChoiceProfile P j vQ z readout) := by
  exact iut3_raw_choice_value_transport T (arity j + 1)
    (decompositionChoiceProfile P j vQ z readout)

def surjectiveOnlyDegreeData : RawPacketDegreeData Bool Unit where
  toBase := fun _ => ()
  relativeDegree := fun _ => 1
  baseDegree := fun _ => 1

theorem surjective_only_map_is_surjective :
    Function.Surjective surjectiveOnlyDegreeData.toBase := by
  intro v
  exact ⟨false, rfl⟩

theorem surjective_only_map_is_not_injective :
    ¬ Function.Injective surjectiveOnlyDegreeData.toBase := by
  intro h
  have := h (show surjectiveOnlyDegreeData.toBase false =
    surjectiveOnlyDegreeData.toBase true by rfl)
  cases this

theorem surjective_only_choice_mass_is_duplicated :
    choiceDegreeMass 1
        (fun u : Bool => surjectiveOnlyDegreeData.baseDegree
          (surjectiveOnlyDegreeData.toBase u)) = 2 /\
      choiceDegreeMass 1 surjectiveOnlyDegreeData.baseDegree = 1 := by
  constructor <;>
    rw [choice_degree_mass_eq_sum_pow] <;>
    norm_num [Src.CoreLayer.WeightedAvg.lamE, surjectiveOnlyDegreeData]

def injectiveOnlyDegreeData : RawPacketDegreeData Unit Bool where
  toBase := fun _ => false
  relativeDegree := fun _ => 1
  baseDegree := fun _ => 1

theorem injective_only_map_is_injective :
    Function.Injective injectiveOnlyDegreeData.toBase := by
  intro x y _
  cases x
  cases y
  rfl

theorem injective_only_map_is_not_surjective :
    ¬ Function.Surjective injectiveOnlyDegreeData.toBase := by
  intro h
  obtain ⟨u, hu⟩ := h true
  cases u
  cases hu

theorem injective_only_choice_mass_omits_a_base :
    choiceDegreeMass 1
        (fun u : Unit => injectiveOnlyDegreeData.baseDegree
          (injectiveOnlyDegreeData.toBase u)) = 1 /\
      choiceDegreeMass 1 injectiveOnlyDegreeData.baseDegree = 2 := by
  constructor <;>
    rw [choice_degree_mass_eq_sum_pow] <;>
    norm_num [Src.CoreLayer.WeightedAvg.lamE, injectiveOnlyDegreeData]

def conventionIdentityTransport :
    LiftBaseTransportCandidate conventionCheckData where
  placeEquiv := Equiv.refl Bool
  toBase_compat := fun _ => rfl

def wrongTransportedDegree : Bool -> Real
  | false => 1
  | true => 2

theorem wrong_degree_is_not_exact :
    ¬ ExactTransportedDegree conventionIdentityTransport
      wrongTransportedDegree := by
  intro h
  have := h true
  norm_num [wrongTransportedDegree, conventionIdentityTransport,
    conventionCheckData] at this

theorem wrong_degree_mass : choiceDegreeMass 1 wrongTransportedDegree = 3 := by
  rw [choice_degree_mass_eq_sum_pow]
  norm_num [Src.CoreLayer.WeightedAvg.lamE, wrongTransportedDegree]

theorem wrong_degree_changes_true_weight :
    thm110NormalizedChoiceWeight 1 wrongTransportedDegree
        conventionTrueChoice = 2 / 3 /\
      thm110NormalizedChoiceWeight 1 conventionCheckData.baseDegree
        conventionTrueChoice = 3 / 4 := by
  constructor
  · unfold thm110NormalizedChoiceWeight
    rw [wrong_degree_mass]
    norm_num [choiceDegreeProduct, Src.CoreLayer.WeightedAvg.lamProd,
      wrongTransportedDegree, conventionTrueChoice]
  · exact convention_thm110_true_weight

def scaledButInexactDegree : Bool -> Real
  | false => 2
  | true => 6

theorem scaled_degree_is_not_exact :
    ¬ ExactTransportedDegree conventionIdentityTransport
      scaledButInexactDegree := by
  intro h
  have := h false
  norm_num [scaledButInexactDegree, conventionIdentityTransport,
    conventionCheckData] at this

theorem scaled_degree_mass :
    choiceDegreeMass 1 scaledButInexactDegree = 8 := by
  rw [choice_degree_mass_eq_sum_pow]
  norm_num [Src.CoreLayer.WeightedAvg.lamE, scaledButInexactDegree]

theorem scaled_inexact_weights_match_source_weights :
    thm110NormalizedChoiceWeight 1 scaledButInexactDegree
        conventionFalseChoice = 1 / 4 /\
      thm110NormalizedChoiceWeight 1 scaledButInexactDegree
        conventionTrueChoice = 3 / 4 := by
  constructor <;> unfold thm110NormalizedChoiceWeight <;>
    rw [scaled_degree_mass] <;>
    norm_num [choiceDegreeProduct, Src.CoreLayer.WeightedAvg.lamProd,
      scaledButInexactDegree, conventionFalseChoice, conventionTrueChoice]

theorem conditional_true_reweight_differs_from_full :
    (3 : Real) / 3 ≠
      thm110NormalizedChoiceWeight 1 conventionCheckData.baseDegree
        conventionTrueChoice := by
  change (3 : Real) / 3 ≠
    thm110NormalizedChoiceWeight 1 conventionCheckData.baseDegree
      (baseChoiceOfLift conventionCheckData conventionTrueChoice)
  rw [convention_thm110_true_weight]
  norm_num

def factorReindex
    {E : Type uLift} {n : Nat} (sigma : Fin n ≃ Fin n)
    (choice : Fin n -> E) : Fin n -> E :=
  fun alpha => choice (sigma alpha)

theorem choice_degree_product_factor_reindex
    {E : Type uLift} {n : Nat} (sigma : Fin n ≃ Fin n)
    (degree : E -> Real) (choice : Fin n -> E) :
    choiceDegreeProduct n degree (factorReindex sigma choice) =
      choiceDegreeProduct n degree choice := by
  unfold choiceDegreeProduct Src.CoreLayer.WeightedAvg.lamProd factorReindex
  exact sigma.prod_comp (fun alpha => degree (choice alpha))

end CitedLV.Theorem311
