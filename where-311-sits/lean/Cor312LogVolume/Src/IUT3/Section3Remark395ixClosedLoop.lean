import Cor312LogVolume.Src.IUT3.Section3Remark3111InputPrimeStripLink

namespace Src.IUT3.Remark395ix

open CategoryTheory Src.IUT3.Remark3111

inductive Stage where
  | thetaLink
  | lowerSecondHorizontalInv
  | lowerFirstHorizontalInv
  | firstVerticalKummer
  | upperFirstHorizontal
  | upperSecondHorizontal
  | upperThirdHorizontal
  | sq3HullDeterminant
  | sq4LogKummerAdjustment
  | sq5RealifiedSemisimplification
  deriving DecidableEq

def iplStages : List Stage :=
  [.lowerSecondHorizontalInv, .lowerFirstHorizontalInv, .firstVerticalKummer,
    .upperFirstHorizontal, .upperSecondHorizontal, .upperThirdHorizontal]

def iplPath : List Stage :=
  .thetaLink :: iplStages

def completedBeforeSQ5 : List Stage :=
  iplPath ++ [.sq3HullDeterminant, .sq4LogKummerAdjustment]

def completedThroughSQ5 : List Stage :=
  completedBeforeSQ5 ++ [.sq5RealifiedSemisimplification]

structure LoopData (S : AlgorithmSetting) where

  hullTarget : S.Strip

  sq3 : S.diagram.Elgp ⟶ hullTarget

  sq4 : hullTarget ⟶ S.qStrip

  sq3Twist : Set (hullTarget ⟶ hullTarget)

  sq4Twist : Set (S.qStrip ⟶ S.qStrip)

namespace LoopData

variable {S : AlgorithmSetting} (L : LoopData S)

def src : Stage → Option S.Strip
  | .thetaLink => some S.qStrip
  | .lowerSecondHorizontalInv => some S.diagram.FLGP
  | .lowerFirstHorizontalInv => some S.diagram.Fgau
  | .firstVerticalKummer => some S.diagram.Fenv
  | .upperFirstHorizontal => some S.diagram.Eenv
  | .upperSecondHorizontal => some S.diagram.Egau
  | .upperThirdHorizontal => some S.diagram.ELGP
  | .sq3HullDeterminant => some S.diagram.Elgp
  | .sq4LogKummerAdjustment => some L.hullTarget
  | .sq5RealifiedSemisimplification => none

def tgt : Stage → Option S.Strip
  | .thetaLink => some S.diagram.FLGP
  | .lowerSecondHorizontalInv => some S.diagram.Fgau
  | .lowerFirstHorizontalInv => some S.diagram.Fenv
  | .firstVerticalKummer => some S.diagram.Eenv
  | .upperFirstHorizontal => some S.diagram.Egau
  | .upperSecondHorizontal => some S.diagram.ELGP
  | .upperThirdHorizontal => some S.diagram.Elgp
  | .sq3HullDeterminant => some L.hullTarget
  | .sq4LogKummerAdjustment => some S.qStrip
  | .sq5RealifiedSemisimplification => none

theorem hasArrow (s : Stage) (hs : s ≠ .sq5RealifiedSemisimplification) :
    ∃ a b, L.src s = some a ∧ L.tgt s = some b ∧ Nonempty (a ⟶ b) := by
  cases s with
  | thetaLink => exact ⟨_, _, rfl, rfl, ⟨inv S.thetaLink⟩⟩
  | lowerSecondHorizontalInv => exact ⟨_, _, rfl, rfl, ⟨inv S.diagram.l2⟩⟩
  | lowerFirstHorizontalInv => exact ⟨_, _, rfl, rfl, ⟨inv S.diagram.l1⟩⟩
  | firstVerticalKummer => exact ⟨_, _, rfl, rfl, ⟨S.diagram.kEnv⟩⟩
  | upperFirstHorizontal => exact ⟨_, _, rfl, rfl, ⟨S.diagram.u1⟩⟩
  | upperSecondHorizontal => exact ⟨_, _, rfl, rfl, ⟨S.diagram.u2⟩⟩
  | upperThirdHorizontal => exact ⟨_, _, rfl, rfl, ⟨S.diagram.u3⟩⟩
  | sq3HullDeterminant => exact ⟨_, _, rfl, rfl, ⟨L.sq3⟩⟩
  | sq4LogKummerAdjustment => exact ⟨_, _, rfl, rfl, ⟨L.sq4⟩⟩
  | sq5RealifiedSemisimplification => exact absurd rfl hs

def IsWalk : List Stage → S.Strip → S.Strip → Prop
  | [], a, b => a = b
  | s :: rest, a, b => L.src s = some a ∧ ∃ c, L.tgt s = some c ∧ IsWalk rest c b

def StartsAt (path : List Stage) (a : S.Strip) : Prop :=
  ∃ b, L.IsWalk path a b

def ClosedUpToFormalQuotient (path : List Stage) : Prop :=
  L.IsWalk path S.qStrip S.qStrip ∧ Stage.sq5RealifiedSemisimplification ∉ path

def EndpointHullsComparable (path : List Stage) : Prop :=
  ∃ pre post, path = pre ++ post ∧ pre.getLast? = some .sq3HullDeterminant ∧ L.IsWalk pre S.qStrip L.hullTarget

def VerticalMismatchAdjusted (path : List Stage) : Prop :=
  ∃ pre post, path = pre ++ post ∧ pre.getLast? = some .sq4LogKummerAdjustment ∧ L.IsWalk pre S.qStrip S.qStrip

def InScope (path : List Stage) : Prop :=
  L.ClosedUpToFormalQuotient path ∧ L.EndpointHullsComparable path ∧ L.VerticalMismatchAdjusted path

theorem walk_iplPath : L.IsWalk iplPath S.qStrip S.diagram.Elgp := by
  simp [IsWalk, iplPath, iplStages, src, tgt]

theorem walk_to_hull : L.IsWalk (iplPath ++ [.sq3HullDeterminant]) S.qStrip L.hullTarget := by
  simp [IsWalk, iplPath, iplStages, src, tgt]

theorem walk_completed : L.IsWalk completedBeforeSQ5 S.qStrip S.qStrip := by
  simp [IsWalk, completedBeforeSQ5, iplPath, iplStages, src, tgt]

theorem closed_before_sq5 : L.ClosedUpToFormalQuotient completedBeforeSQ5 :=
  ⟨L.walk_completed, by decide⟩

theorem comparable_before_sq5 : L.EndpointHullsComparable completedBeforeSQ5 :=
  ⟨iplPath ++ [.sq3HullDeterminant], [.sq4LogKummerAdjustment], by simp [completedBeforeSQ5], by simp,
    L.walk_to_hull⟩

theorem adjusted_before_sq5 : L.VerticalMismatchAdjusted completedBeforeSQ5 :=
  ⟨completedBeforeSQ5, [], by simp, by simp [completedBeforeSQ5], L.walk_completed⟩

theorem inScope_before_sq5 : L.InScope completedBeforeSQ5 :=
  ⟨L.closed_before_sq5, L.comparable_before_sq5, L.adjusted_before_sq5⟩

theorem startsAt_before_sq5 : L.StartsAt completedBeforeSQ5 S.qStrip :=
  ⟨_, L.walk_completed⟩

theorem scoped_path_nonempty :
    ∃ path, L.StartsAt path S.qStrip ∧ L.ClosedUpToFormalQuotient path ∧
      L.EndpointHullsComparable path ∧ L.VerticalMismatchAdjusted path :=
  ⟨completedBeforeSQ5, L.startsAt_before_sq5, L.closed_before_sq5, L.comparable_before_sq5,
    L.adjusted_before_sq5⟩

theorem no_walk_through_sq5 (path : List Stage) (h : Stage.sq5RealifiedSemisimplification ∈ path) :
    ∀ a b, ¬ L.IsWalk path a b := by
  induction path with
  | nil => simp at h
  | cons s rest ih =>
    intro a b hw
    rcases List.mem_cons.1 h with h | h
    · subst h
      exact absurd hw.1 (by simp [src])
    · obtain ⟨_, c, _, hrest⟩ := hw
      exact ih h c b hrest

theorem not_closed_through_sq5 : ¬ L.ClosedUpToFormalQuotient completedThroughSQ5 :=
  fun h => h.2 (by decide)

theorem actual_path_endpoints : ∀ x ∈ S.possible, L.IsWalk iplPath S.qStrip (S.stripOf x) := by
  intro x hx
  rw [S.possible_strip hx]
  exact L.walk_iplPath

noncomputable def loopArrow (t : L.hullTarget ⟶ L.hullTarget) (u : S.qStrip ⟶ S.qStrip) : S.qStrip ⟶ S.qStrip :=
  inv S.thetaLink ≫ S.diagram.iplComposite ≫ L.sq3 ≫ t ≫ L.sq4 ≫ u

noncomputable def loopPoly : Set (S.qStrip ⟶ S.qStrip) :=
  {f | ∃ t ∈ insert (𝟙 _) L.sq3Twist, ∃ u ∈ insert (𝟙 _) L.sq4Twist, f = L.loopArrow t u}

theorem loopPoly_nonempty : L.loopPoly.Nonempty :=
  ⟨L.loopArrow (𝟙 _) (𝟙 _), 𝟙 _, Set.mem_insert _ _, 𝟙 _, Set.mem_insert _ _, rfl⟩

theorem loopArrow_route (t : L.hullTarget ⟶ L.hullTarget) (u : S.qStrip ⟶ S.qStrip) :
    L.loopArrow t u = inv S.thetaLink ≫ S.diagram.l3 ≫ S.diagram.kLgp ≫ L.sq3 ≫ t ≫ L.sq4 ≫ u := by
  unfold loopArrow
  rw [S.diagram.iplComposite_eq_lower, Category.assoc]

end LoopData

section Model

def modelLoop : LoopData modelAlgorithm where
  hullTarget := obj 9
  sq3 := idHom 8 9
  sq4 := idHom 9 0
  sq3Twist := {swapHom 9 9}
  sq4Twist := ∅

def skipSq3 : List Stage := iplPath ++ [.sq4LogKummerAdjustment]

def skipSq4 : List Stage := iplPath ++ [.sq3HullDeterminant]

def sq3ThenSq5 : List Stage := iplPath ++ [.sq3HullDeterminant, .sq5RealifiedSemisimplification]

theorem model_skipSq3_not_walk : ∀ a b, ¬ modelLoop.IsWalk skipSq3 a b := by
  intro a b hw
  simp [LoopData.IsWalk, skipSq3, iplPath, iplStages, LoopData.src, LoopData.tgt, modelLoop, modelAlgorithm,
    modelDiagram, obj] at hw

theorem model_skipSq4_not_closed : ¬ modelLoop.ClosedUpToFormalQuotient skipSq4 := by
  intro h
  have hw := h.1
  simp [LoopData.IsWalk, skipSq4, iplPath, iplStages, LoopData.src, LoopData.tgt, modelLoop, modelAlgorithm,
    modelDiagram, obj, strip2] at hw

theorem model_sq3ThenSq5_not_walk : ∀ a b, ¬ modelLoop.IsWalk sq3ThenSq5 a b :=
  modelLoop.no_walk_through_sq5 _ (by decide)

theorem model_iplPath_not_comparable : ¬ modelLoop.EndpointHullsComparable iplPath := by
  rintro ⟨pre, post, hpath, hlast, hw⟩
  have hpre : pre <+: iplPath := ⟨post, hpath.symm⟩
  have hmem : Stage.sq3HullDeterminant ∈ pre := List.mem_of_getLast? hlast
  have : Stage.sq3HullDeterminant ∈ iplPath := hpre.subset hmem
  exact absurd this (by decide)

theorem model_twist_moves :
    modelLoop.loopArrow (swapHom 9 9) (𝟙 _) ≠ modelLoop.loopArrow (𝟙 _) (𝟙 _) := by
  intro h
  simp only [LoopData.loopArrow, cancel_epi, Category.comp_id] at h
  have h' : (swapHom 9 9 : modelLoop.hullTarget ⟶ modelLoop.hullTarget) = 𝟙 modelLoop.hullTarget :=
    (cancel_mono modelLoop.sq4).1 h
  have h0 := congrArg (fun g : obj 9 ⟶ obj 9 => ((g true : Fin 2 ≃ Fin 2) (0 : Fin 2) : Fin 2)) h'
  change (Equiv.swap (0 : Fin 2) 1) 0 = (Equiv.refl (Fin 2)) 0 at h0
  simp at h0

theorem model_nondegenerate :
    (∀ a b, ¬ modelLoop.IsWalk skipSq3 a b) ∧
      ¬ modelLoop.ClosedUpToFormalQuotient skipSq4 ∧
      (∀ a b, ¬ modelLoop.IsWalk sq3ThenSq5 a b) ∧
      ¬ modelLoop.EndpointHullsComparable iplPath ∧
      modelLoop.loopArrow (swapHom 9 9) (𝟙 _) ≠ modelLoop.loopArrow (𝟙 _) (𝟙 _) :=
  ⟨model_skipSq3_not_walk, model_skipSq4_not_closed, model_sq3ThenSq5_not_walk, model_iplPath_not_comparable,
    model_twist_moves⟩

end Model

end Src.IUT3.Remark395ix

section Check
open Src.IUT3.Remark395ix
end Check
