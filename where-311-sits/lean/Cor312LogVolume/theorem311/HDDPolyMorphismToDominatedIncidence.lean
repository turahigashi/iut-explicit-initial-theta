import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.HDDPolyMorphismToDominatedIncidence

universe uS uT uM

structure DirectedDegreeSystem where
  Source : Type uS
  Target : Type uT
  Hom : Source -> Target -> Type uM
  sourceDegree : Source -> Real
  targetDegree : Target -> Real
  degree_mono :
    forall {q : Source} {d : Target},
      Hom q d -> sourceDegree q <= targetDegree d

variable (D : DirectedDegreeSystem.{uS,uT,uM})

structure PolyMorphismOrbit (q : D.Source) (d : D.Target) where
  arrows : Set (D.Hom q d)
  nonempty : arrows.Nonempty

def targetDegreeDownwardHull (d : D.Target) : Set Real :=
  Set.Iic (D.targetDegree d)

theorem PolyMorphismOrbit.sourceDegree_le_targetDegree
    {q : D.Source} {d : D.Target}
    (O : PolyMorphismOrbit D q d) :
    D.sourceDegree q <= D.targetDegree d := by
  obtain ⟨f, hf⟩ := O.nonempty
  exact D.degree_mono f

theorem PolyMorphismOrbit.sourceDegree_mem_downwardHull
    {q : D.Source} {d : D.Target}
    (O : PolyMorphismOrbit D q d) :
    D.sourceDegree q ∈ targetDegreeDownwardHull D d :=
  O.sourceDegree_le_targetDegree

theorem PolyMorphismOrbit.sourceDegree_le_endpoint
    {q : D.Source} {d : D.Target}
    (O : PolyMorphismOrbit D q d)
    (b : Real)
    (hd : D.targetDegree d <= b) :
    D.sourceDegree q <= b :=
  le_trans O.sourceDegree_le_targetDegree hd

def ExactDegreeIncidence (q : D.Source) (d : D.Target) : Prop :=
  D.sourceDegree q = D.targetDegree d

theorem exactDegreeIncidence_implies_bound
    {q : D.Source} {d : D.Target}
    (h : ExactDegreeIncidence D q d) :
    D.sourceDegree q <= D.targetDegree d :=
  le_of_eq h

def strictModel : DirectedDegreeSystem where
  Source := Unit
  Target := Unit
  Hom := fun _ _ => Unit
  sourceDegree := fun _ => 0
  targetDegree := fun _ => 1
  degree_mono := by
    intro q d f
    norm_num

def strictModelOrbit :
    PolyMorphismOrbit strictModel () () where
  arrows := Set.univ
  nonempty := ⟨(), Set.mem_univ ()⟩

theorem directed_route_is_strictly_weaker_than_exact_degree :
    strictModel.sourceDegree () <= strictModel.targetDegree () ∧
      ¬ ExactDegreeIncidence strictModel () () := by
  constructor
  · exact strictModelOrbit.sourceDegree_le_targetDegree
  · change ¬ (0 : Real) = 1
    norm_num

theorem family_of_orbits_gives_pointwise_bounds
    {I : Type*}
    (q : I -> D.Source)
    (d : I -> D.Target)
    (h : forall i : I, Nonempty (PolyMorphismOrbit D (q i) (d i))) :
    forall i : I,
      D.sourceDegree (q i) <= D.targetDegree (d i) := by
  intro i
  obtain ⟨O⟩ := h i
  exact O.sourceDegree_le_targetDegree

end CitedLV.Theorem311.HDDPolyMorphismToDominatedIncidence
end
