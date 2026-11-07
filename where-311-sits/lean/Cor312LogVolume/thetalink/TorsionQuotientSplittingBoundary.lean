import Cor312LogVolume.thetalink.FormalEvaluationEquivarianceBoundary

namespace CitedLV.ThetaLink

universe uRaw uTF uCore uRay uEnv uGau uEnvTF uGauTF
  uCoreE uRayE uCoreG uRayG

structure TorsionQuotientSplitRaw
    (Raw : Type uRaw) (TF : Type uTF)
    (Core : Type uCore) (Ray : Type uRay) where
  project : Raw → TF
  split : TF → Core × Ray
  unsplit : Core × Ray → TF

def MultiplicativeMapLaws
    {A : Type uRaw} {B : Type uTF} [Monoid A] [Monoid B]
    (f : A → B) : Prop :=
  f 1 = 1 ∧ ∀ x y, f (x * y) = f x * f y

def MultiplicativeEquivalenceLaws
    {A : Type uRaw} {B : Type uTF} [Monoid A] [Monoid B]
    (f : A → B) : Prop :=
  MultiplicativeMapLaws f ∧ Function.Bijective f

def TorsionQuotientProjectionLaws
    {Raw : Type uRaw} {TF : Type uTF}
    {Core : Type uCore} {Ray : Type uRay}
    [Monoid Raw] [Monoid TF]
    (S : TorsionQuotientSplitRaw Raw TF Core Ray) : Prop :=
  MultiplicativeMapLaws S.project ∧ Function.Surjective S.project

def TorsionFreeSplitLaws
    {Raw : Type uRaw} {TF : Type uTF}
    {Core : Type uCore} {Ray : Type uRay}
    [Monoid TF] [Monoid Core] [Monoid Ray]
    (S : TorsionQuotientSplitRaw Raw TF Core Ray) : Prop :=
  MultiplicativeEquivalenceLaws S.split ∧
    Function.LeftInverse S.unsplit S.split ∧
    Function.RightInverse S.unsplit S.split

def multiplicativeMapMonoidHom
    {A : Type uRaw} {B : Type uTF} [Monoid A] [Monoid B]
    (f : A → B) (h : MultiplicativeMapLaws f) : A →* B where
  toFun := f
  map_one' := h.1
  map_mul' := h.2

def torsionFreeSplitMulEquiv
    {Raw : Type uRaw} {TF : Type uTF}
    {Core : Type uCore} {Ray : Type uRay}
    [Monoid TF] [Monoid Core] [Monoid Ray]
    (S : TorsionQuotientSplitRaw Raw TF Core Ray)
    (h : TorsionFreeSplitLaws S) : TF ≃* Core × Ray where
  toFun := S.split
  invFun := S.unsplit
  left_inv := h.2.1
  right_inv := h.2.2
  map_mul' := h.1.1.2

structure FormalEvaluationTFSplitRaw
    (Env : Type uEnv) (Gau : Type uGau)
    (EnvTF : Type uEnvTF) (GauTF : Type uGauTF)
    (CoreEnv : Type uCoreE) (RayEnv : Type uRayE)
    (CoreGau : Type uCoreG) (RayGau : Type uRayG) where
  envView : TorsionQuotientSplitRaw Env EnvTF CoreEnv RayEnv
  gauView : TorsionQuotientSplitRaw Gau GauTF CoreGau RayGau
  evalTF : EnvTF → GauTF
  factorEval : CoreEnv × RayEnv → CoreGau × RayGau

def EvaluationDescendsToTF
    {Env : Type uEnv} {Gau : Type uGau}
    {EnvTF : Type uEnvTF} {GauTF : Type uGauTF}
    {CoreEnv : Type uCoreE} {RayEnv : Type uRayE}
    {CoreGau : Type uCoreG} {RayGau : Type uRayG}
    (evaluate : Env → Gau)
    (S : FormalEvaluationTFSplitRaw Env Gau EnvTF GauTF
      CoreEnv RayEnv CoreGau RayGau) : Prop :=
  ∀ x, S.evalTF (S.envView.project x) = S.gauView.project (evaluate x)

def EvaluationRespectsTFSplitting
    {Env : Type uEnv} {Gau : Type uGau}
    {EnvTF : Type uEnvTF} {GauTF : Type uGauTF}
    {CoreEnv : Type uCoreE} {RayEnv : Type uRayE}
    {CoreGau : Type uCoreG} {RayGau : Type uRayG}
    (S : FormalEvaluationTFSplitRaw Env Gau EnvTF GauTF
      CoreEnv RayEnv CoreGau RayGau) : Prop :=
  ∀ x, S.gauView.split (S.evalTF x) =
    S.factorEval (S.envView.split x)

theorem raw_evaluation_reaches_target_split_coordinates
    {Env : Type uEnv} {Gau : Type uGau}
    {EnvTF : Type uEnvTF} {GauTF : Type uGauTF}
    {CoreEnv : Type uCoreE} {RayEnv : Type uRayE}
    {CoreGau : Type uCoreG} {RayGau : Type uRayG}
    (evaluate : Env → Gau)
    (S : FormalEvaluationTFSplitRaw Env Gau EnvTF GauTF
      CoreEnv RayEnv CoreGau RayGau)
    (hdesc : EvaluationDescendsToTF evaluate S)
    (hsplit : EvaluationRespectsTFSplitting S) (x : Env) :
    S.gauView.split (S.gauView.project (evaluate x)) =
      S.factorEval (S.envView.split (S.envView.project x)) := by
  rw [← hdesc x]
  exact hsplit (S.envView.project x)

noncomputable def evaluationTFMonoidEquiv
    {Env : Type uEnv} {Gau : Type uGau}
    {EnvTF : Type uEnvTF} {GauTF : Type uGauTF}
    {CoreEnv : Type uCoreE} {RayEnv : Type uRayE}
    {CoreGau : Type uCoreG} {RayGau : Type uRayG}
    [Monoid EnvTF] [Monoid GauTF]
    (S : FormalEvaluationTFSplitRaw Env Gau EnvTF GauTF
      CoreEnv RayEnv CoreGau RayGau)
    (h : MultiplicativeEquivalenceLaws S.evalTF) : EnvTF ≃* GauTF :=
  MulEquiv.ofBijective (multiplicativeMapMonoidHom S.evalTF h.1) h.2

def c3PairIdentitySplit :
    TorsionQuotientSplitRaw C3Square C3Square C3 C3 where
  project := id
  split := id
  unsplit := id

def c3PairSwapSplit :
    TorsionQuotientSplitRaw C3Square C3Square C3 C3 where
  project := id
  split := fun x ↦ (x.2, x.1)
  unsplit := fun x ↦ (x.2, x.1)

def c3PairCollapsedSplit :
    TorsionQuotientSplitRaw C3Square C3Square C3 C3 where
  project := id
  split := fun _ ↦ 1
  unsplit := fun _ ↦ 1

def c3PairBadProjection :
    TorsionQuotientSplitRaw C3Square C3Square C3 C3 where
  project := fun _ ↦ c3AxisWitness
  split := id
  unsplit := id

theorem identity_multiplicative_map_laws :
    MultiplicativeMapLaws (id : C3Square → C3Square) :=
  ⟨rfl, fun _ _ ↦ rfl⟩

theorem identity_multiplicative_equivalence_laws :
    MultiplicativeEquivalenceLaws (id : C3Square → C3Square) :=
  ⟨identity_multiplicative_map_laws, Function.bijective_id⟩

theorem c3_identity_projection_laws :
    TorsionQuotientProjectionLaws c3PairIdentitySplit :=
  ⟨identity_multiplicative_map_laws, Function.surjective_id⟩

theorem c3_swap_view_projection_laws :
    TorsionQuotientProjectionLaws c3PairSwapSplit :=
  ⟨identity_multiplicative_map_laws, Function.surjective_id⟩

theorem swap_multiplicative_equivalence_laws :
    MultiplicativeEquivalenceLaws
      (fun x : C3Square ↦ (x.2, x.1)) := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro x y
    rfl
  · exact c3SquareSwap.bijective

theorem c3_identity_split_laws :
    TorsionFreeSplitLaws c3PairIdentitySplit :=
  ⟨identity_multiplicative_equivalence_laws,
    fun _ ↦ rfl, fun _ ↦ rfl⟩

theorem c3_swap_split_laws :
    TorsionFreeSplitLaws c3PairSwapSplit :=
  ⟨swap_multiplicative_equivalence_laws,
    fun x ↦ by cases x; rfl,
    fun x ↦ by cases x; rfl⟩

theorem c3AxisWitness_ne_one : c3AxisWitness ≠ (1 : C3Square) := by
  decide

theorem c3_bad_projection_not_multiplicative :
    ¬ MultiplicativeMapLaws c3PairBadProjection.project := by
  intro h
  exact c3AxisWitness_ne_one h.1

theorem c3_bad_projection_not_surjective :
    ¬ Function.Surjective c3PairBadProjection.project := by
  intro h
  obtain ⟨x, hx⟩ := h (1 : C3Square)
  exact c3AxisWitness_ne_one hx

theorem c3_bad_projection_not_a_quotient_projection :
    ¬ TorsionQuotientProjectionLaws c3PairBadProjection := by
  intro h
  exact c3_bad_projection_not_multiplicative h.1

theorem constant_one_not_multiplicative_equivalence :
    ¬ MultiplicativeEquivalenceLaws
      (fun _ : C3Square ↦ (1 : C3Square)) := by
  intro h
  have heq : (1 : C3Square) = c3AxisWitness :=
    h.2.1 (show (1 : C3Square) = 1 by rfl)
  exact c3AxisWitness_ne_one heq.symm

theorem c3_collapsed_not_split :
    ¬ TorsionFreeSplitLaws c3PairCollapsedSplit := by
  intro h
  exact constant_one_not_multiplicative_equivalence h.1

def c3RawEvaluation : C3Square → C3Square :=
  fun x ↦ (x.2, x.1)

def c3GoodTFComparison :
    FormalEvaluationTFSplitRaw C3Square C3Square C3Square C3Square
      C3 C3 C3 C3 where
  envView := c3PairIdentitySplit
  gauView := c3PairSwapSplit
  evalTF := fun x ↦ (x.2, x.1)
  factorEval := id

def c3BadSplitComparison :
    FormalEvaluationTFSplitRaw C3Square C3Square C3Square C3Square
      C3 C3 C3 C3 where
  envView := c3PairIdentitySplit
  gauView := c3PairIdentitySplit
  evalTF := fun x ↦ (x.2, x.1)
  factorEval := id

def c3BadDescentComparison :
    FormalEvaluationTFSplitRaw C3Square C3Square C3Square C3Square
      C3 C3 C3 C3 where
  envView := c3PairIdentitySplit
  gauView := c3PairSwapSplit
  evalTF := id
  factorEval := fun x ↦ (x.2, x.1)

def c3CollapsedTFComparison :
    FormalEvaluationTFSplitRaw C3Square C3Square C3Square C3Square
      C3 C3 C3 C3 where
  envView := c3PairCollapsedSplit
  gauView := c3PairCollapsedSplit
  evalTF := fun x ↦ (x.2, x.1)
  factorEval := id

theorem c3_good_evaluation_descends :
    EvaluationDescendsToTF c3RawEvaluation
      c3GoodTFComparison := by
  intro x
  rfl

theorem c3_good_evaluation_respects_splitting :
    EvaluationRespectsTFSplitting c3GoodTFComparison := by
  intro x
  rfl

theorem c3_good_tf_interface_passes :
    TorsionQuotientProjectionLaws c3GoodTFComparison.envView ∧
      TorsionQuotientProjectionLaws c3GoodTFComparison.gauView ∧
      TorsionFreeSplitLaws c3GoodTFComparison.envView ∧
      TorsionFreeSplitLaws c3GoodTFComparison.gauView ∧
      MultiplicativeEquivalenceLaws c3GoodTFComparison.evalTF ∧
      MultiplicativeEquivalenceLaws c3GoodTFComparison.factorEval ∧
      EvaluationDescendsToTF c3RawEvaluation c3GoodTFComparison ∧
      EvaluationRespectsTFSplitting c3GoodTFComparison :=
  ⟨c3_identity_projection_laws, c3_swap_view_projection_laws,
    c3_identity_split_laws, c3_swap_split_laws,
    swap_multiplicative_equivalence_laws,
    identity_multiplicative_equivalence_laws,
    c3_good_evaluation_descends,
    c3_good_evaluation_respects_splitting⟩

theorem c3_good_reaches_target_split_coordinates (x : C3Square) :
    c3GoodTFComparison.gauView.split
        (c3GoodTFComparison.gauView.project
          (c3RawEvaluation x)) =
      c3GoodTFComparison.factorEval
        (c3GoodTFComparison.envView.split
          (c3GoodTFComparison.envView.project x)) :=
  raw_evaluation_reaches_target_split_coordinates
    c3RawEvaluation c3GoodTFComparison
    c3_good_evaluation_descends c3_good_evaluation_respects_splitting x

theorem c3_bad_split_still_descends :
    EvaluationDescendsToTF c3RawEvaluation
      c3BadSplitComparison := by
  intro x
  rfl

theorem c3_bad_split_not_compatible :
    ¬ EvaluationRespectsTFSplitting c3BadSplitComparison := by
  intro h
  have hw := h c3AxisWitness
  exact c3SquareSwap_axis_ne_self hw

theorem valid_splits_and_descent_do_not_force_compatibility :
    TorsionQuotientProjectionLaws c3BadSplitComparison.envView ∧
      TorsionQuotientProjectionLaws c3BadSplitComparison.gauView ∧
      TorsionFreeSplitLaws c3BadSplitComparison.envView ∧
      TorsionFreeSplitLaws c3BadSplitComparison.gauView ∧
      MultiplicativeEquivalenceLaws c3BadSplitComparison.evalTF ∧
      MultiplicativeEquivalenceLaws c3BadSplitComparison.factorEval ∧
      EvaluationDescendsToTF c3RawEvaluation
        c3BadSplitComparison ∧
      ¬ EvaluationRespectsTFSplitting c3BadSplitComparison :=
  ⟨c3_identity_projection_laws, c3_identity_projection_laws,
    c3_identity_split_laws, c3_identity_split_laws,
    swap_multiplicative_equivalence_laws,
    identity_multiplicative_equivalence_laws,
    c3_bad_split_still_descends, c3_bad_split_not_compatible⟩

theorem c3_bad_descent_split_compatible :
    EvaluationRespectsTFSplitting c3BadDescentComparison := by
  intro x
  rfl

theorem c3_bad_descent_not_descended :
    ¬ EvaluationDescendsToTF c3RawEvaluation
      c3BadDescentComparison := by
  intro h
  have hw := h c3AxisWitness
  exact c3SquareSwap_axis_ne_self hw.symm

theorem split_compatibility_does_not_force_descent :
    TorsionFreeSplitLaws c3BadDescentComparison.envView ∧
      TorsionFreeSplitLaws c3BadDescentComparison.gauView ∧
      MultiplicativeEquivalenceLaws c3BadDescentComparison.evalTF ∧
      MultiplicativeEquivalenceLaws c3BadDescentComparison.factorEval ∧
      EvaluationRespectsTFSplitting c3BadDescentComparison ∧
      ¬ EvaluationDescendsToTF c3RawEvaluation
        c3BadDescentComparison :=
  ⟨c3_identity_split_laws, c3_swap_split_laws,
    identity_multiplicative_equivalence_laws,
    swap_multiplicative_equivalence_laws,
    c3_bad_descent_split_compatible, c3_bad_descent_not_descended⟩

theorem c3_collapsed_comparison_is_compatible :
    EvaluationRespectsTFSplitting c3CollapsedTFComparison := by
  intro x
  rfl

theorem compatibility_does_not_make_a_split :
    EvaluationRespectsTFSplitting c3CollapsedTFComparison ∧
      ¬ TorsionFreeSplitLaws c3CollapsedTFComparison.envView ∧
      ¬ TorsionFreeSplitLaws c3CollapsedTFComparison.gauView :=
  ⟨c3_collapsed_comparison_is_compatible,
    c3_collapsed_not_split, c3_collapsed_not_split⟩

end CitedLV.ThetaLink
