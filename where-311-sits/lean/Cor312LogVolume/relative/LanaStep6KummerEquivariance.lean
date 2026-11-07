import Cor312LogVolume.relative.LanaStep6GenericKummerMap
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Tactic.Group

noncomputable section

namespace Src.CoreLayer.LanaStep6.KummerEquivariance

open CategoryTheory CategoryTheory.Limits
open SrcContinuous.ContinuousH1
open Src.Lib.ContinuousH1RestrictionColimit
open Src.CoreLayer.LanaStep6.GenericKummerMap

universe u

variable
    {G M Mgp : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
    [MulDistribMulAction G M] [ContinuousSMul G M]
    [CommGroup Mgp] [TopologicalSpace Mgp] [IsTopologicalGroup Mgp]
    [MulDistribMulAction G Mgp] [ContinuousSMul G Mgp]
    (I : KummerColimitInput G M Mgp)

def conjHom (g : G) : G →* G where
  toFun x := g⁻¹ * x * g
  map_one' := by simp
  map_mul' x y := by group

@[simp] theorem conjHom_apply (g x : G) : conjHom g x = g⁻¹ * x * g := rfl

theorem conjHom_continuous (g : G) : Continuous (conjHom (G := G) g) :=
  (continuous_const.mul continuous_id).mul continuous_const

theorem conjHom_surjective (g : G) : Function.Surjective (conjHom (G := G) g) :=
  fun y => ⟨g * y * g⁻¹, by simp [conjHom]; group⟩

def conjugateFiniteOpen
    (g : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G) :
    Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G := by
  refine ⟨OpenSubgroup.comap (conjHom g) (conjHom_continuous g) J.1, ⟨?_⟩⟩
  have h := Subgroup.index_comap_of_surjective
    (H := J.1.toSubgroup) (conjHom_surjective g)
  rw [OpenSubgroup.toSubgroup_comap, h]
  exact J.2.index_ne_zero

@[simp] theorem mem_conjugateFiniteOpen_iff
    (g : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (x : G) :
    x ∈ (conjugateFiniteOpen g J).1 ↔ g⁻¹ * x * g ∈ J.1 := Iff.rfl

@[simp] theorem mem_restrictedOpen_iff
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (x : G) :
    x ∈ (restrictedOpen J).toSubgroup ↔ x ∈ J.1 := Iff.rfl

theorem conjugateFiniteOpen_mono
    (g : G)
    {J K : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G}
    (h : J ≤ K) :
    conjugateFiniteOpen g J ≤ conjugateFiniteOpen g K := by
  intro x hx
  exact h hx

@[simp] theorem conjugateFiniteOpen_one
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G) :
    conjugateFiniteOpen (1 : G) J = J := by
  apply Subtype.ext
  apply OpenSubgroup.ext
  intro x
  simp

@[simp] theorem conjugateFiniteOpen_mul
    (g h : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G) :
    conjugateFiniteOpen g (conjugateFiniteOpen h J) =
      conjugateFiniteOpen (g * h) J := by
  apply Subtype.ext
  apply OpenSubgroup.ext
  intro x
  simp only [mem_conjugateFiniteOpen_iff]
  congr! 1
  group

def conjugateSubgroupEquiv
    (g : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G) :
    (restrictedOpen J).toSubgroup ≃ₜ*
      (restrictedOpen (conjugateFiniteOpen g J)).toSubgroup where
  toMulEquiv :=
    { toFun := fun h =>
        ⟨g * h.1 * g⁻¹, by
          apply (mem_conjugateFiniteOpen_iff g J _).2
          have hh : h.1 ∈ J.1 :=
            (mem_restrictedOpen_iff J h.1).1 h.2
          simpa [mul_assoc] using hh⟩
      invFun := fun h =>
        ⟨g⁻¹ * h.1 * g, by
          apply (mem_restrictedOpen_iff J _).2
          exact (mem_conjugateFiniteOpen_iff g J h.1).1
            ((mem_restrictedOpen_iff (conjugateFiniteOpen g J) h.1).1 h.2)⟩
      left_inv := by
        intro h
        apply Subtype.ext
        simp [mul_assoc]
      right_inv := by
        intro h
        apply Subtype.ext
        simp [mul_assoc]
      map_mul' := by
        intro h k
        apply Subtype.ext
        simp [mul_assoc] }
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      (IsTopologicalGroup.continuous_conj g).comp
        continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    simpa only [inv_inv] using
      (IsTopologicalGroup.continuous_conj (g⁻¹ : G)).comp
        continuous_subtype_val

@[simp] theorem conjugateSubgroupEquiv_coe
    (g : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (h : (restrictedOpen J).toSubgroup) :
    ((conjugateSubgroupEquiv g J h :
        (restrictedOpen (conjugateFiniteOpen g J)).toSubgroup) : G) =
      g * h.1 * g⁻¹ :=
  rfl

@[simp] theorem conjugateSubgroupEquiv_symm_coe
    (g : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (h : (restrictedOpen (conjugateFiniteOpen g J)).toSubgroup) :
    (((conjugateSubgroupEquiv g J).symm h :
        (restrictedOpen J).toSubgroup) : G) =
      g⁻¹ * h.1 * g :=
  rfl

def conjugateCoefficientEquiv (g : G) :
    Additive I.LambdaCoeff ≃ₜ+ Additive I.LambdaCoeff where
  toAddEquiv := DistribMulAction.toAddEquiv _ g
  continuous_toFun := continuous_const_smul g
  continuous_invFun := continuous_const_smul (g⁻¹ : G)

def conjugationTransportData
    (g : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G) :
    TransportData
      (G := (restrictedOpen J).toSubgroup)
      (A := Additive I.LambdaCoeff)
      (H := (restrictedOpen (conjugateFiniteOpen g J)).toSubgroup)
      (B := Additive I.LambdaCoeff) where
  groupEquiv := conjugateSubgroupEquiv g J
  coeffEquiv := conjugateCoefficientEquiv I g
  equivariant := by
    intro h a
    change
      g • (h.1 • a) =
        (g * h.1 * g⁻¹) • (g • a)
    simp only [mul_smul, inv_smul_smul]

def stageConjugation
    (g : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G) :
    Stage (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G) J →
      Stage (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G) (conjugateFiniteOpen g J) :=
  transportH1 (conjugationTransportData I g J)

theorem stageConjugation_restriction
    (g : G)
    {J K : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G}
    (h : J ≤ K)
    (x :
      Stage (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G) K) :
    stageConjugation I g J
        (stageRestriction
          (A := Additive I.LambdaCoeff)
          (ContinuousMonoidHom.id G) h x) =
      stageRestriction
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen_mono g h)
        (stageConjugation I g K x) := by
  refine Quotient.inductionOn x ?_
  intro c
  apply congrArg (Quotient.mk _)
  apply Cocycle.ext
  intro q
  change
    g • c
        (Subgroup.inclusion (restrictedOpen_le h)
          ((conjugateSubgroupEquiv g J).symm q)) =
      g • c
        ((conjugateSubgroupEquiv g K).symm
          (Subgroup.inclusion
            (restrictedOpen_le (conjugateFiniteOpen_mono g h)) q))
  apply congrArg (fun r : (restrictedOpen K).toSubgroup => g • c r)
  apply Subtype.ext
  rfl

def identityCoefficientEquiv :
    Additive I.LambdaCoeff ≃ₜ+ Additive I.LambdaCoeff where
  toAddEquiv := AddEquiv.refl _
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

def oneStageSubgroupEquiv
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G) :
    (restrictedOpen (conjugateFiniteOpen (1 : G) J)).toSubgroup ≃ₜ*
      (restrictedOpen J).toSubgroup where
  toMulEquiv :=
    { toFun := fun q =>
        ⟨q.1, by
          have hq :
              (1 : G)⁻¹ * q.1 * 1 ∈ J.1 := q.2
          simpa using hq⟩
      invFun := fun q =>
        ⟨q.1, by
          change (1 : G)⁻¹ * q.1 * 1 ∈ J.1
          simpa using q.2⟩
      left_inv := by
        intro q
        apply Subtype.ext
        rfl
      right_inv := by
        intro q
        apply Subtype.ext
        rfl
      map_mul' := by
        intro q r
        apply Subtype.ext
        rfl }
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

def oneStageBackTransportData
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G) :
    TransportData
      (G := (restrictedOpen (conjugateFiniteOpen (1 : G) J)).toSubgroup)
      (A := Additive I.LambdaCoeff)
      (H := (restrictedOpen J).toSubgroup)
      (B := Additive I.LambdaCoeff) where
  groupEquiv := oneStageSubgroupEquiv J
  coeffEquiv := identityCoefficientEquiv I
  equivariant := by
    intro q a
    rfl

theorem stageConjugation_one_aligned
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (x :
      Stage (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G) J) :
    transportH1 (oneStageBackTransportData I J)
        (stageConjugation I 1 J x) =
      x := by
  refine Quotient.inductionOn x ?_
  intro c
  apply congrArg (Quotient.mk _)
  apply Cocycle.ext
  intro q
  change
    (1 : G) •
        c ((conjugateSubgroupEquiv (1 : G) J).symm
          ((oneStageSubgroupEquiv J).symm q)) =
      c q
  rw [one_smul]
  apply congrArg c
  apply Subtype.ext
  change (1 : G)⁻¹ * q.1 * 1 = q.1
  group

def mulStageSubgroupEquiv
    (g h : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G) :
    (restrictedOpen
        (conjugateFiniteOpen g (conjugateFiniteOpen h J))).toSubgroup ≃ₜ*
      (restrictedOpen (conjugateFiniteOpen (g * h) J)).toSubgroup where
  toMulEquiv :=
    { toFun := fun q =>
        ⟨q.1, by
          have hq :
              h⁻¹ * (g⁻¹ * q.1 * g) * h ∈ J.1 := q.2
          change (g * h)⁻¹ * q.1 * (g * h) ∈ J.1
          convert hq using 1 <;> group⟩
      invFun := fun q =>
        ⟨q.1, by
          have hq :
              (g * h)⁻¹ * q.1 * (g * h) ∈ J.1 := q.2
          change h⁻¹ * (g⁻¹ * q.1 * g) * h ∈ J.1
          convert hq using 1 <;> group⟩
      left_inv := by
        intro q
        apply Subtype.ext
        rfl
      right_inv := by
        intro q
        apply Subtype.ext
        rfl
      map_mul' := by
        intro q r
        apply Subtype.ext
        rfl }
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

def mulStageAlignmentTransportData
    (g h : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G) :
    TransportData
      (G :=
        (restrictedOpen
          (conjugateFiniteOpen g (conjugateFiniteOpen h J))).toSubgroup)
      (A := Additive I.LambdaCoeff)
      (H := (restrictedOpen (conjugateFiniteOpen (g * h) J)).toSubgroup)
      (B := Additive I.LambdaCoeff) where
  groupEquiv := mulStageSubgroupEquiv g h J
  coeffEquiv := identityCoefficientEquiv I
  equivariant := by
    intro q a
    rfl

theorem stageConjugation_mul_aligned
    (g h : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (x :
      Stage (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G) J) :
    transportH1 (mulStageAlignmentTransportData I g h J)
        (stageConjugation I g (conjugateFiniteOpen h J)
          (stageConjugation I h J x)) =
      stageConjugation I (g * h) J x := by
  refine Quotient.inductionOn x ?_
  intro c
  apply congrArg (Quotient.mk _)
  apply Cocycle.ext
  intro q
  change
    g •
        (h •
          c ((conjugateSubgroupEquiv h J).symm
            ((conjugateSubgroupEquiv g
              (conjugateFiniteOpen h J)).symm
              ((mulStageSubgroupEquiv g h J).symm q)))) =
      (g * h) •
        c ((conjugateSubgroupEquiv (g * h) J).symm q)
  rw [mul_smul]
  apply congrArg (fun a => g • (h • c a))
  apply Subtype.ext
  change
    h⁻¹ * (g⁻¹ * q.1 * g) * h =
      (g * h)⁻¹ * q.1 * (g * h)
  group

theorem oneFiniteOpen_le
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G) :
    J ≤ conjugateFiniteOpen (1 : G) J := by
  intro x hx
  change (1 : G)⁻¹ * x * 1 ∈ J.1
  simpa using hx

theorem stageRestriction_one_eq_transportBack
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (x :
      Stage (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen (1 : G) J)) :
    stageRestriction
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (oneFiniteOpen_le J) x =
      transportH1 (oneStageBackTransportData I J) x := by
  refine Quotient.inductionOn x ?_
  intro c
  apply congrArg (Quotient.mk _)
  apply Cocycle.ext
  intro q
  change
    c (Subgroup.inclusion (restrictedOpen_le (oneFiniteOpen_le J)) q) =
      c ((oneStageSubgroupEquiv J).symm q)
  apply congrArg c
  apply Subtype.ext
  rfl

theorem stageToInfinityH1_one_alignment
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (x :
      Stage (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen (1 : G) J)) :
    stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen (1 : G) J) x =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G) J
        (transportH1 (oneStageBackTransportData I J) x) := by
  calc
    stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen (1 : G) J) x
        =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G) J
        (stageRestriction
          (A := Additive I.LambdaCoeff)
          (ContinuousMonoidHom.id G)
          (oneFiniteOpen_le J) x) := by
            symm
            exact stageToInfinityH1_restriction
              (A := Additive I.LambdaCoeff)
              (ContinuousMonoidHom.id G)
              (oneFiniteOpen_le J) x
    _ =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G) J
        (transportH1 (oneStageBackTransportData I J) x) := by
          rw [stageRestriction_one_eq_transportBack]
          rfl

theorem mulAlignmentFiniteOpen_le
    (g h : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G) :
    conjugateFiniteOpen (g * h) J ≤
      conjugateFiniteOpen g (conjugateFiniteOpen h J) := by
  intro x hx
  change h⁻¹ * (g⁻¹ * x * g) * h ∈ J.1
  change (g * h)⁻¹ * x * (g * h) ∈ J.1 at hx
  convert hx using 1 <;> group

theorem stageRestriction_mul_eq_alignment
    (g h : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (x :
      Stage (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen g (conjugateFiniteOpen h J))) :
    stageRestriction
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (mulAlignmentFiniteOpen_le g h J) x =
      transportH1 (mulStageAlignmentTransportData I g h J) x := by
  refine Quotient.inductionOn x ?_
  intro c
  apply congrArg (Quotient.mk _)
  apply Cocycle.ext
  intro q
  change
    c (Subgroup.inclusion
        (restrictedOpen_le (mulAlignmentFiniteOpen_le g h J)) q) =
      c ((mulStageSubgroupEquiv g h J).symm q)
  apply congrArg c
  apply Subtype.ext
  rfl

theorem stageToInfinityH1_mul_alignment
    (g h : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (x :
      Stage (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen g (conjugateFiniteOpen h J))) :
    stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen g (conjugateFiniteOpen h J)) x =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen (g * h) J)
        (transportH1
          (mulStageAlignmentTransportData I g h J) x) := by
  calc
    stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen g (conjugateFiniteOpen h J)) x
        =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen (g * h) J)
        (stageRestriction
          (A := Additive I.LambdaCoeff)
          (ContinuousMonoidHom.id G)
          (mulAlignmentFiniteOpen_le g h J) x) := by
            symm
            exact stageToInfinityH1_restriction
              (A := Additive I.LambdaCoeff)
              (ContinuousMonoidHom.id G)
              (mulAlignmentFiniteOpen_le g h J) x
    _ =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen (g * h) J)
        (transportH1
          (mulStageAlignmentTransportData I g h J) x) := by
          rw [stageRestriction_mul_eq_alignment]
          rfl

noncomputable def conjugationCocone (g : G) :
    Cocone
      (restrictionDiagram
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)) where
  pt := I.infinityH1
  ι :=
    { app := fun j =>
        TypeCat.ofHom fun x =>
          stageToInfinityH1
            (A := Additive I.LambdaCoeff)
            (ContinuousMonoidHom.id G)
            (conjugateFiniteOpen g (OrderDual.ofDual j))
            (stageConjugation I g (OrderDual.ofDual j) x)
      naturality := by
        intro j k f
        ext x
        dsimp
        let hkj :
            OrderDual.ofDual k ≤ OrderDual.ofDual j :=
          leOfHom f
        calc
          stageToInfinityH1
              (A := Additive I.LambdaCoeff)
              (ContinuousMonoidHom.id G)
              (conjugateFiniteOpen g (OrderDual.ofDual k))
              (stageConjugation I g (OrderDual.ofDual k)
                (stageRestriction
                  (A := Additive I.LambdaCoeff)
                  (ContinuousMonoidHom.id G) hkj x))
              =
            stageToInfinityH1
              (A := Additive I.LambdaCoeff)
              (ContinuousMonoidHom.id G)
              (conjugateFiniteOpen g (OrderDual.ofDual k))
              (stageRestriction
                (A := Additive I.LambdaCoeff)
                (ContinuousMonoidHom.id G)
                (conjugateFiniteOpen_mono g hkj)
                (stageConjugation I g (OrderDual.ofDual j) x)) := by
                  rw [stageConjugation_restriction]
          _ =
            stageToInfinityH1
              (A := Additive I.LambdaCoeff)
              (ContinuousMonoidHom.id G)
              (conjugateFiniteOpen g (OrderDual.ofDual j))
              (stageConjugation I g (OrderDual.ofDual j) x) :=
            stageToInfinityH1_restriction
              (A := Additive I.LambdaCoeff)
              (ContinuousMonoidHom.id G)
              (conjugateFiniteOpen_mono g hkj)
              (stageConjugation I g (OrderDual.ofDual j) x) }

noncomputable def infinityConjugation
    (g : G) : I.infinityH1 → I.infinityH1 :=
  colimit.desc
    (restrictionDiagram
      (A := Additive I.LambdaCoeff)
      (ContinuousMonoidHom.id G))
    (conjugationCocone I g)

theorem infinityConjugation_stage
    (g : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (x :
      Stage (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G) J) :
    infinityConjugation I g
        (stageToInfinityH1
          (A := Additive I.LambdaCoeff)
          (ContinuousMonoidHom.id G) J x) =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen g J)
        (stageConjugation I g J x) := by
  change
    (colimit.desc
      (restrictionDiagram
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G))
      (conjugationCocone I g))
        (colimit.ι
          (restrictionDiagram
            (A := Additive I.LambdaCoeff)
            (ContinuousMonoidHom.id G))
          (OrderDual.toDual J) x) =
      _
  exact colimit.ι_desc_apply
    (conjugationCocone I g) (OrderDual.toDual J) x

theorem infinityConjugation_one_hom :
    (TypeCat.ofHom (infinityConjugation I 1) :
      I.infinityH1 ⟶ I.infinityH1) =
      𝟙 I.infinityH1 := by
  apply colimit.hom_ext
  intro j
  ext x
  change
    infinityConjugation I 1
        (stageToInfinityH1
          (A := Additive I.LambdaCoeff)
          (ContinuousMonoidHom.id G)
          (OrderDual.ofDual j) x) =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (OrderDual.ofDual j) x
  rw [infinityConjugation_stage]
  calc
    stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen (1 : G) (OrderDual.ofDual j))
        (stageConjugation I 1 (OrderDual.ofDual j) x)
        =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (OrderDual.ofDual j)
        (transportH1
          (oneStageBackTransportData I (OrderDual.ofDual j))
          (stageConjugation I 1 (OrderDual.ofDual j) x)) :=
      stageToInfinityH1_one_alignment
        I (OrderDual.ofDual j)
        (stageConjugation I 1 (OrderDual.ofDual j) x)
    _ =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (OrderDual.ofDual j) x := by
          exact congrArg
            (stageToInfinityH1 (A := Additive I.LambdaCoeff)
              (ContinuousMonoidHom.id G) (OrderDual.ofDual j))
            (stageConjugation_one_aligned I (OrderDual.ofDual j) x)

theorem infinityConjugation_one
    (x : I.infinityH1) :
    infinityConjugation I 1 x = x := by
  exact congrArg (fun f => f x) (infinityConjugation_one_hom I)

theorem infinityConjugation_mul_hom
    (g h : G) :
    (TypeCat.ofHom (infinityConjugation I (g * h)) :
      I.infinityH1 ⟶ I.infinityH1) =
      (TypeCat.ofHom (infinityConjugation I h) :
        I.infinityH1 ⟶ I.infinityH1) ≫
      (TypeCat.ofHom (infinityConjugation I g) :
        I.infinityH1 ⟶ I.infinityH1) := by
  apply colimit.hom_ext
  intro j
  ext x
  change
    infinityConjugation I (g * h)
        (stageToInfinityH1
          (A := Additive I.LambdaCoeff)
          (ContinuousMonoidHom.id G)
          (OrderDual.ofDual j) x) =
      infinityConjugation I g
        (infinityConjugation I h
          (stageToInfinityH1
            (A := Additive I.LambdaCoeff)
            (ContinuousMonoidHom.id G)
            (OrderDual.ofDual j) x))
  rw [infinityConjugation_stage,
    infinityConjugation_stage,
    infinityConjugation_stage]
  symm
  calc
    stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen g
          (conjugateFiniteOpen h (OrderDual.ofDual j)))
        (stageConjugation I g
          (conjugateFiniteOpen h (OrderDual.ofDual j))
          (stageConjugation I h (OrderDual.ofDual j) x))
        =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen (g * h) (OrderDual.ofDual j))
        (transportH1
          (mulStageAlignmentTransportData
            I g h (OrderDual.ofDual j))
          (stageConjugation I g
            (conjugateFiniteOpen h (OrderDual.ofDual j))
            (stageConjugation I h (OrderDual.ofDual j) x))) :=
      stageToInfinityH1_mul_alignment
        I g h (OrderDual.ofDual j)
        (stageConjugation I g
          (conjugateFiniteOpen h (OrderDual.ofDual j))
          (stageConjugation I h (OrderDual.ofDual j) x))
    _ =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen (g * h) (OrderDual.ofDual j))
        (stageConjugation I (g * h) (OrderDual.ofDual j) x) := by
          exact congrArg
            (stageToInfinityH1 (A := Additive I.LambdaCoeff)
              (ContinuousMonoidHom.id G)
              (conjugateFiniteOpen (g * h) (OrderDual.ofDual j)))
            (stageConjugation_mul_aligned I g h (OrderDual.ofDual j) x)

theorem infinityConjugation_mul
    (g h : G)
    (x : I.infinityH1) :
    infinityConjugation I (g * h) x =
      infinityConjugation I g (infinityConjugation I h x) := by
  exact congrArg (fun f => f x) (infinityConjugation_mul_hom I g h)

noncomputable instance infinityH1MulAction :
    MulAction G I.infinityH1 where
  smul := infinityConjugation I
  one_smul := infinityConjugation_one I
  mul_smul := infinityConjugation_mul I

noncomputable def rootConjugationDiscrepancy
    (g : G) (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (x : (I.subgroupInput J).Fixed) :
    I.LambdaCoeff :=
  ⟨fun d =>
      ⟨(I.subgroupInput (conjugateFiniteOpen g J)).rootAtDegree
            (g • x.1) d /
          (g • (I.subgroupInput J).rootAtDegree x.1 d), by
        show
          ((I.subgroupInput (conjugateFiniteOpen g J)).rootAtDegree
                (g • x.1) d /
            (g • (I.subgroupInput J).rootAtDegree x.1 d)) ^ d.val = 1
        rw [div_pow,
          (I.subgroupInput (conjugateFiniteOpen g J)).rootAtDegree_pow,
          ← smul_pow',
          (I.subgroupInput J).rootAtDegree_pow]

        show KummerCoefficientInput.toGp I.toKummerSubgroupInput.coeff (g • x.1)
            / g • KummerCoefficientInput.toGp
                I.toKummerSubgroupInput.coeff x.1 = 1
        rw [I.toKummerSubgroupInput.equivariant_toGp, div_self']⟩,
    by
      intro d e hde
      apply Subtype.ext
      show
        ((I.subgroupInput (conjugateFiniteOpen g J)).rootAtDegree
              (g • x.1) e /
            (g • (I.subgroupInput J).rootAtDegree x.1 e)) ^
            (e.val / d.val)
          =
        (I.subgroupInput (conjugateFiniteOpen g J)).rootAtDegree
              (g • x.1) d /
            (g • (I.subgroupInput J).rootAtDegree x.1 d)
      rw [div_pow,
        (I.subgroupInput
          (conjugateFiniteOpen g J)).rootAtDegree_transition
            (g • x.1) hde,
        ← smul_pow',
        (I.subgroupInput J).rootAtDegree_transition x.1 hde]⟩

def conjugateFixed
    (g : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (x : (I.subgroupInput J).Fixed) :
    (I.subgroupInput (conjugateFiniteOpen g J)).Fixed :=
  ⟨g • x.1, by
    intro q
    have hx :=
      x.2 ((conjugateSubgroupEquiv g J).symm q)
    change
      (g⁻¹ * q.1 * g) • x.1 = x.1 at hx
    calc
      q.1 • (g • x.1)
          = (q.1 * g) • x.1 := by
              rw [mul_smul]
      _ = (g * (g⁻¹ * q.1 * g)) • x.1 := by
              congr 1
              group
      _ = g • ((g⁻¹ * q.1 * g) • x.1) := by
              rw [mul_smul]
      _ = g • x.1 := by
              exact congrArg (fun y => g • y) hx⟩

theorem lambdaRatio_conjugation
    (g : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (x : (I.subgroupInput J).Fixed)
    (q :
      (restrictedOpen (conjugateFiniteOpen g J)).toSubgroup) :
    (I.subgroupInput (conjugateFiniteOpen g J)).lambdaRatio
        (conjugateFixed I g J x) q =
      g •
          (I.subgroupInput J).lambdaRatio x
            ((conjugateSubgroupEquiv g J).symm q) *
        (q • rootConjugationDiscrepancy I g J x /
          rootConjugationDiscrepancy I g J x) := by
  apply Subtype.ext
  funext d
  apply Subtype.ext
  change
    q.1 •
          (I.subgroupInput (conjugateFiniteOpen g J)).rootAtDegree
            (g • x.1) d /
        (I.subgroupInput (conjugateFiniteOpen g J)).rootAtDegree
          (g • x.1) d
      =
    g •
          ((g⁻¹ * q.1 * g) •
              (I.subgroupInput J).rootAtDegree x.1 d /
            (I.subgroupInput J).rootAtDegree x.1 d) *
      (q.1 •
            ((I.subgroupInput
              (conjugateFiniteOpen g J)).rootAtDegree
                (g • x.1) d /
              (g •
                (I.subgroupInput J).rootAtDegree x.1 d)) /
        ((I.subgroupInput
          (conjugateFiniteOpen g J)).rootAtDegree
            (g • x.1) d /
          (g • (I.subgroupInput J).rootAtDegree x.1 d)))
  have hconj :
      g •
          ((g⁻¹ * q.1 * g) •
            (I.subgroupInput J).rootAtDegree x.1 d) =
        q.1 •
          (g • (I.subgroupInput J).rootAtDegree x.1 d) := by
    rw [← mul_smul, ← mul_smul]
    congr 1
    group
  simp only [smul_div']
  rw [hconj]

  have key : ∀ a b p q : Mgp,
      q * b⁻¹ * (p * q⁻¹ * (a * b⁻¹)⁻¹) = p * a⁻¹ := by
    intro a b p q
    simp only [mul_inv_rev, inv_inv]
    have h : ∀ u v w : Mgp, u * (v * (w * u⁻¹)) = (u * u⁻¹) * (v * w) := by
      intro u v w; ac_rfl
    simp [mul_comm, mul_assoc, mul_left_comm, h]
  simp only [div_eq_mul_inv]
  rw [key]

theorem stageKummerCocycle_conjugation_cohomologous
    (g : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (x : (I.subgroupInput J).Fixed) :
    Cohomologous
      (restrictedOpen (conjugateFiniteOpen g J)).toSubgroup
      (Additive I.LambdaCoeff)
      (transportCocycle
        (conjugationTransportData I g J)
        (I.stageKummerCocycle J x))
      (I.stageKummerCocycle
        (conjugateFiniteOpen g J)
        (conjugateFixed I g J x)) := by
  refine
    ⟨Additive.ofMul (rootConjugationDiscrepancy I g J x), ?_⟩
  intro q
  apply Additive.toMul.injective
  change
    (I.subgroupInput (conjugateFiniteOpen g J)).lambdaRatio
        (conjugateFixed I g J x) q =
      g •
          (I.subgroupInput J).lambdaRatio x
            ((conjugateSubgroupEquiv g J).symm q) *
        (q • rootConjugationDiscrepancy I g J x /
          rootConjugationDiscrepancy I g J x)
  exact lambdaRatio_conjugation I g J x q

theorem stageKummerClass_conjugation
    (g : G)
    (J : Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G)
    (x : (I.subgroupInput J).Fixed) :
    stageConjugation I g J (I.stageKummerClass J x) =
      I.stageKummerClass
        (conjugateFiniteOpen g J)
        (conjugateFixed I g J x) := by
  exact Quotient.sound
    (stageKummerCocycle_conjugation_cohomologous I g J x)

theorem genericKummerMap_equivariant
    (g : G)
    (m : M) :
    I.genericKummerMap (g • m) =
      g • I.genericKummerMap m := by
  let J :
      Src.CoreLayer.LanaStep6.GenericKummerMap.FiniteOpen G :=
    I.chosenOpen m
  let x : (I.subgroupInput J).Fixed :=
    I.chosenFixed m
  have hgfix :
      ∀ q :
          (restrictedOpen (conjugateFiniteOpen g J)).toSubgroup,
        q • (g • m) = g • m := by
    intro q
    have h := (conjugateFixed I g J x).2 q
    simpa [x, J] using h
  let xg :
      (I.subgroupInput (conjugateFiniteOpen g J)).Fixed :=
    ⟨g • m, hgfix⟩
  have hxg :
      xg = conjugateFixed I g J x := by
    apply Subtype.ext
    rfl
  calc
    I.genericKummerMap (g • m)
        =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen g J)
        (I.stageKummerClass
          (conjugateFiniteOpen g J) xg) := by
            exact I.genericKummerMap_eq_of_fixed
              (g • m) (conjugateFiniteOpen g J) hgfix
    _ =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen g J)
        (I.stageKummerClass
          (conjugateFiniteOpen g J)
          (conjugateFixed I g J x)) := by
            exact congrArg
              (stageToInfinityH1
                (A := Additive I.LambdaCoeff)
                (ContinuousMonoidHom.id G)
                (conjugateFiniteOpen g J))
              (congrArg
                (I.stageKummerClass (conjugateFiniteOpen g J))
                hxg)
    _ =
      stageToInfinityH1
        (A := Additive I.LambdaCoeff)
        (ContinuousMonoidHom.id G)
        (conjugateFiniteOpen g J)
        (stageConjugation I g J
          (I.stageKummerClass J x)) := by
            exact congrArg
              (stageToInfinityH1
                (A := Additive I.LambdaCoeff)
                (ContinuousMonoidHom.id G)
                (conjugateFiniteOpen g J))
              (stageKummerClass_conjugation I g J x).symm
    _ =
      infinityConjugation I g
        (stageToInfinityH1
          (A := Additive I.LambdaCoeff)
          (ContinuousMonoidHom.id G) J
          (I.stageKummerClass J x)) := by
            exact
              (infinityConjugation_stage
                I g J (I.stageKummerClass J x)).symm
    _ = g • I.genericKummerMap m := by
      rfl

end Src.CoreLayer.LanaStep6.KummerEquivariance

end
