import Cor312LogVolume.theorem311.CoherentRegularNormalizationDiagram

namespace CitedLV.Theorem311

universe uBase uIndex uComponent uPacket

noncomputable def finiteSplitRegularNormalizationEquiv
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K]
    (split : K ≃ₐ[R] (∀ i, A i)) :
    regularIntegerOrderOfFiniteSplit split ≃ₐ[R] integralClosure R K :=
  Subalgebra.equivOfEq _ _
    (regularIntegerOrderOfFiniteSplit_eq_integralClosure split)

theorem finiteSplitRegularNormalizationEquiv_coe
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K]
    (split : K ≃ₐ[R] (∀ i, A i))
    (x : regularIntegerOrderOfFiniteSplit split) :
    ((finiteSplitRegularNormalizationEquiv split x :
      integralClosure R K) : K) = (x : K) :=
  rfl

noncomputable def canonicalFiniteSplitNormalizationDiagram
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K]
    (split : K ≃ₐ[R] (∀ i, A i)) (B : Subalgebra R K)
    (hB : B ≤ integralClosure R K) :
    RegularNormalizationCarrierRaw R B
      (regularIntegerOrderOfFiniteSplit split) (integralClosure R K) K where
  rawToAmbient := B.val
  regularToAmbient := (regularIntegerOrderOfFiniteSplit split).val
  normalizedToAmbient := (integralClosure R K).val
  rawToNormalized := Subalgebra.inclusion hB
  regularToNormalized := finiteSplitRegularNormalizationEquiv split

theorem canonicalFiniteSplit_regular_triangle_commutes
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K]
    (split : K ≃ₐ[R] (∀ i, A i)) (B : Subalgebra R K)
    (hB : B ≤ integralClosure R K) :
    RegularNormalizedAmbientCommutes
      (canonicalFiniteSplitNormalizationDiagram split B hB) := by
  intro x
  rfl

theorem canonicalFiniteSplit_raw_triangle_commutes
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K]
    (split : K ≃ₐ[R] (∀ i, A i)) (B : Subalgebra R K)
    (hB : B ≤ integralClosure R K) :
    RawNormalizedAmbientCommutes
      (canonicalFiniteSplitNormalizationDiagram split B hB) := by
  intro x
  rfl

theorem canonicalFiniteSplit_maps_injective
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K]
    (split : K ≃ₐ[R] (∀ i, A i)) (B : Subalgebra R K)
    (hB : B ≤ integralClosure R K) :
    NormalizationCarrierMapsInjective
      (canonicalFiniteSplitNormalizationDiagram split B hB) := by
  exact ⟨Subtype.val_injective, Subtype.val_injective,
    Subtype.val_injective, Subalgebra.inclusion_injective hB⟩

theorem canonicalFiniteSplit_raw_is_proper_iff
    {R : Type uBase} {ι : Type uIndex} {A : ι -> Type uComponent}
    {K : Type uPacket}
    [CommRing R] [Fintype ι]
    [∀ i, CommRing (A i)] [CommRing K]
    [∀ i, Algebra R (A i)] [Algebra R K]
    (split : K ≃ₐ[R] (∀ i, A i)) (B : Subalgebra R K)
    (hB : B ≤ integralClosure R K) :
    RawOrderIsProper
        (canonicalFiniteSplitNormalizationDiagram split B hB) ↔
      ∃ z : integralClosure R K, (z : K) ∉ B := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    intro hzB
    apply hz
    refine ⟨⟨z, hzB⟩, ?_⟩
    apply Subtype.ext
    rfl
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rintro ⟨b, hb⟩
    apply hz
    have hval : (b : K) = (z : K) := congrArg Subtype.val hb
    rw [← hval]
    exact b.2

theorem rawSubalgebra_le_integralClosure_of_isIntegral
    {R : Type uBase} {K : Type uPacket}
    [CommRing R] [CommRing K] [Algebra R K]
    (B : Subalgebra R K) [Algebra.IsIntegral R B] :
    B ≤ integralClosure R K := by
  intro x hx
  let y : B := ⟨x, hx⟩
  have hy : IsIntegral R y := Algebra.IsIntegral.isIntegral y
  have hmapped := hy.map B.val
  simpa [y] using hmapped

noncomputable def polynomialBoolFiniteSplit :
    (Bool -> Polynomial ℚ) ≃ₐ[ℚ] (Bool -> Polynomial ℚ) :=
  AlgEquiv.refl

noncomputable def polynomialBoolRegularOrder :
    Subalgebra ℚ (Bool -> Polynomial ℚ) :=
  regularIntegerOrderOfFiniteSplit polynomialBoolFiniteSplit

noncomputable def boolIntegralStepProfile : Bool -> Polynomial ℚ
  | false => 0
  | true => 1

theorem boolIntegralStepProfile_mem_regularOrder :
    boolIntegralStepProfile ∈ polynomialBoolRegularOrder := by
  unfold polynomialBoolRegularOrder
  rw [mem_regularIntegerOrderOfFiniteSplit_iff]
  intro i
  cases i
  · change IsIntegral ℚ (0 : Polynomial ℚ)
    exact isIntegral_zero
  · change IsIntegral ℚ (1 : Polynomial ℚ)
    exact isIntegral_one

theorem boolIntegralStepProfile_mem_integralClosure :
    boolIntegralStepProfile ∈
      integralClosure ℚ (Bool -> Polynomial ℚ) := by
  rw [← regularIntegerOrderOfFiniteSplit_eq_integralClosure
    polynomialBoolFiniteSplit]
  exact boolIntegralStepProfile_mem_regularOrder

theorem boolIntegralStepProfile_not_mem_bot :
    boolIntegralStepProfile ∉
      (⊥ : Subalgebra ℚ (Bool -> Polynomial ℚ)) := by
  rw [Algebra.mem_bot]
  rintro ⟨q, hq⟩
  have hfalse := congrFun hq false
  have htrue := congrFun hq true
  simp [boolIntegralStepProfile] at hfalse htrue
  subst q
  simp at htrue

noncomputable def polynomialBoolCanonicalDiagram :
    RegularNormalizationCarrierRaw ℚ
      (⊥ : Subalgebra ℚ (Bool -> Polynomial ℚ))
      polynomialBoolRegularOrder
      (integralClosure ℚ (Bool -> Polynomial ℚ))
      (Bool -> Polynomial ℚ) :=
  canonicalFiniteSplitNormalizationDiagram polynomialBoolFiniteSplit ⊥ bot_le

theorem polynomialBool_diagram_regular_triangle_commutes :
    RegularNormalizedAmbientCommutes polynomialBoolCanonicalDiagram :=
  canonicalFiniteSplit_regular_triangle_commutes
    polynomialBoolFiniteSplit ⊥ bot_le

theorem polynomialBool_diagram_raw_triangle_commutes :
    RawNormalizedAmbientCommutes polynomialBoolCanonicalDiagram :=
  canonicalFiniteSplit_raw_triangle_commutes
    polynomialBoolFiniteSplit ⊥ bot_le

theorem polynomialBool_diagram_maps_injective :
    NormalizationCarrierMapsInjective polynomialBoolCanonicalDiagram :=
  canonicalFiniteSplit_maps_injective polynomialBoolFiniteSplit ⊥ bot_le

theorem polynomialBool_diagram_raw_is_proper :
    RawOrderIsProper polynomialBoolCanonicalDiagram := by
  refine ⟨⟨boolIntegralStepProfile,
    boolIntegralStepProfile_mem_integralClosure⟩, ?_⟩
  rintro ⟨x, hx⟩
  apply boolIntegralStepProfile_not_mem_bot
  have hval := congrArg Subtype.val hx
  change (x : Bool -> Polynomial ℚ) = boolIntegralStepProfile at hval
  rw [← hval]
  exact x.2

theorem polynomialBool_nonintegral_profile_still_excluded :
    boolPolynomialProfile ∉
      integralClosure ℚ (Bool -> Polynomial ℚ) := by
  rw [← regularIntegerOrderOfFiniteSplit_eq_integralClosure
    polynomialBoolFiniteSplit]
  exact bool_polynomial_profile_not_mem_regular_refl_split

end CitedLV.Theorem311
