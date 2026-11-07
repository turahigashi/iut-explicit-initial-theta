import Cor312LogVolume.Src.Lib.ContinuousH1
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.Index
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Filtered.Basic

namespace Src.Lib.ContinuousH1RestrictionColimit

open SrcContinuous.ContinuousH1
open CategoryTheory CategoryTheory.Limits

universe u

variable {G P A : Type u} [Group G] [Group P] [AddCommGroup A]
  [TopologicalSpace G] [TopologicalSpace P] [TopologicalSpace A]
  [DistribMulAction G A] [ContinuousSMul G A]

def restrictCocycle {H K : Subgroup G} (h : H ≤ K)
    (c : Cocycle K A) : Cocycle H A where
  toContinuousMap :=
    { toFun := fun g => c (Subgroup.inclusion h g)
      continuous_toFun := c.toContinuousMap.continuous.comp
        (continuous_subtype_val.subtype_mk (fun g => h g.property)) }
  cocycle' g k :=
    c.cocycle' (Subgroup.inclusion h g) (Subgroup.inclusion h k)

omit [ContinuousSMul G A] in

theorem restrict_cohomologous {H K : Subgroup G} (h : H ≤ K)
    {c d : Cocycle K A} (hcd : Cohomologous K A c d) :
    Cohomologous H A (restrictCocycle h c) (restrictCocycle h d) := by
  obtain ⟨a, ha⟩ := hcd
  exact ⟨a, fun g => ha (Subgroup.inclusion h g)⟩

def restrictH1 {H K : Subgroup G} (h : H ≤ K) :
    H1 K A → H1 H A :=
  Quotient.map (restrictCocycle h)
    (fun _ _ hcd => restrict_cohomologous h hcd)

omit [ContinuousSMul G A] in

theorem restrictCocycle_refl {H : Subgroup G} (c : Cocycle H A) :
    restrictCocycle (le_refl H) c = c := by
  rfl

omit [ContinuousSMul G A] in

theorem restrictCocycle_comp {H K L : Subgroup G} (h : H ≤ K) (k : K ≤ L)
    (c : Cocycle L A) :
    restrictCocycle h (restrictCocycle k c) = restrictCocycle (h.trans k) c := by
  rfl

theorem restrictH1_refl {H : Subgroup G} (x : H1 H A) :
    restrictH1 (le_refl H) x = x := by
  refine Quotient.inductionOn x ?_
  intro c
  exact congrArg (Quotient.mk _) (restrictCocycle_refl c)

theorem restrictH1_comp {H K L : Subgroup G} (h : H ≤ K) (k : K ≤ L)
    (x : H1 L A) :
    restrictH1 h (restrictH1 k x) = restrictH1 (h.trans k) x := by
  refine Quotient.inductionOn x ?_
  intro c
  exact congrArg (Quotient.mk _) (restrictCocycle_comp h k c)

abbrev FiniteOpen (P : Type u) [Group P] [TopologicalSpace P] :=
  {J : OpenSubgroup P // J.toSubgroup.FiniteIndex}

instance finiteOpenNonempty : Nonempty (FiniteOpen P) := by
  refine ⟨⟨⊤, ?_⟩⟩
  change (⊤ : Subgroup P).FiniteIndex
  infer_instance

instance finiteOpenCodirected : IsCodirectedOrder (FiniteOpen P) where
  directed J K := by
    letI : J.val.toSubgroup.FiniteIndex := J.property
    letI : K.val.toSubgroup.FiniteIndex := K.property
    refine ⟨⟨J.val ⊓ K.val, ?_⟩, ?_, ?_⟩
    · rw [OpenSubgroup.toSubgroup_inf]
      infer_instance
    · change J.val ⊓ K.val ≤ J.val
      exact inf_le_left
    · change J.val ⊓ K.val ≤ K.val
      exact inf_le_right

theorem reverseIndex_isFiltered :
    CategoryTheory.IsFiltered (OrderDual (FiniteOpen P)) :=
  inferInstance

def restrictedOpen (f : G →ₜ* P) (J : FiniteOpen P) :
    OpenSubgroup G :=
  OpenSubgroup.comap f.toMonoidHom f.continuous J.val

theorem restrictedOpen_le (f : G →ₜ* P)
    {J K : FiniteOpen P} (h : J ≤ K) :
    (restrictedOpen f J).toSubgroup ≤
      (restrictedOpen f K).toSubgroup := by
  intro g hg
  exact h hg

abbrev Stage (f : G →ₜ* P) (J : FiniteOpen P) :=
  H1 (restrictedOpen f J).toSubgroup A

def stageRestriction (f : G →ₜ* P)
    {J K : FiniteOpen P} (h : J ≤ K) :
    Stage (A := A) f K → Stage (A := A) f J :=
  restrictH1 (restrictedOpen_le f h)

theorem stageRestriction_refl (f : G →ₜ* P) {J : FiniteOpen P}
    (x : Stage (A := A) f J) :
    stageRestriction f (le_refl J) x = x :=
  restrictH1_refl x

theorem stageRestriction_comp (f : G →ₜ* P) {J K L : FiniteOpen P}
    (h : J ≤ K) (k : K ≤ L) (x : Stage (A := A) f L) :
    stageRestriction f h (stageRestriction f k x) =
      stageRestriction f (h.trans k) x :=
  restrictH1_comp (restrictedOpen_le f h) (restrictedOpen_le f k) x

def restrictionDiagram (f : G →ₜ* P) : OrderDual (FiniteOpen P) ⥤ Type u where
  obj J := Stage (A := A) f (OrderDual.ofDual J)
  map h := TypeCat.ofHom (stageRestriction f (leOfHom h))
  map_id J := by
    ext x
    exact stageRestriction_refl f x
  map_comp h k := by
    ext x
    exact (stageRestriction_comp f (leOfHom k) (leOfHom h) x).symm

noncomputable def InfinityH1 (f : G →ₜ* P) : Type u :=
  colimit (restrictionDiagram (A := A) f)

noncomputable def stageToInfinityH1 (f : G →ₜ* P) (J : FiniteOpen P) :
    Stage (A := A) f J → InfinityH1 (A := A) f :=
  colimit.ι (restrictionDiagram (A := A) f) (OrderDual.toDual J)

theorem stageToInfinityH1_restriction (f : G →ₜ* P) {J K : FiniteOpen P}
    (h : J ≤ K) (x : Stage (A := A) f K) :
    stageToInfinityH1 f J (stageRestriction f h x) = stageToInfinityH1 f K x := by
  exact congrArg (fun k => k x)
    (colimit.w (restrictionDiagram (A := A) f)
      (homOfLE (show OrderDual.toDual K ≤ OrderDual.toDual J from h)))

end Src.Lib.ContinuousH1RestrictionColimit
