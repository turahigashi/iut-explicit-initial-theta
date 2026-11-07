import Mathlib
import Cor312LogVolume.Src.IUT3.Section3Theorem311Indeterminacies

namespace Src.IUT3.Remark3111

open CategoryTheory

universe v u

section Diagram

variable (C : Type u) [Groupoid.{v} C]

structure KummerDiagram where
  Eenv : C
  Egau : C
  ELGP : C
  Elgp : C
  Fenv : C
  Fgau : C
  FLGP : C
  Flgp : C
  u1 : Eenv ⟶ Egau
  u2 : Egau ⟶ ELGP
  u3 : ELGP ⟶ Elgp
  l1 : Fenv ⟶ Fgau
  l2 : Fgau ⟶ FLGP
  l3 : FLGP ⟶ Flgp
  kEnv : Fenv ⟶ Eenv
  kGau : Fgau ⟶ Egau
  kLGP : FLGP ⟶ ELGP
  kLgp : Flgp ⟶ Elgp
  sq1 : l1 ≫ kGau = kEnv ≫ u1
  sq2 : l2 ≫ kLGP = kGau ≫ u2
  sq3 : l3 ≫ kLgp = kLGP ≫ u3

end Diagram

section FullPoly

variable {C : Type u} [Groupoid.{v} C]

def FullPoly (A B : C) : Set (A ⟶ B) :=
  Set.univ

def polyComp {A B E : C} (P : Set (A ⟶ B)) (Q : Set (B ⟶ E)) : Set (A ⟶ E) :=
  {h | ∃ f ∈ P, ∃ g ∈ Q, h = f ≫ g}

theorem polyComp_fullPoly {A B E : C} (f : A ⟶ B) :
    polyComp (FullPoly A B) (FullPoly B E) = FullPoly A E := by
  ext h
  simp only [polyComp, FullPoly, Set.mem_univ, true_and, Set.mem_setOf_eq, iff_true]
  exact ⟨f, inv f ≫ h, by simp⟩

theorem fullPoly_conj {A B : C} (α : A ⟶ A) (β : B ⟶ B) :
    (fun f => α ≫ f ≫ β) '' FullPoly A B = FullPoly A B := by
  ext h
  simp only [FullPoly, Set.image_univ, Set.mem_range, Set.mem_univ, iff_true]
  exact ⟨inv α ≫ h ≫ inv β, by simp⟩

theorem chosen_not_conj_stable {A B : C} (f : A ⟶ B) (α : A ⟶ A) (hα : α ≫ f ≠ f) :
    (fun g => α ≫ g ≫ 𝟙 B) '' {f} ≠ {f} := by
  intro h
  have : α ≫ f ≫ 𝟙 B ∈ (fun g => α ≫ g ≫ 𝟙 B) '' ({f} : Set (A ⟶ B)) := ⟨f, rfl, rfl⟩
  rw [h] at this
  exact hα (by simpa using this)

end FullPoly

namespace KummerDiagram

variable {C : Type u} [Groupoid.{v} C] (D : KummerDiagram C)

noncomputable def iplComposite : D.FLGP ⟶ D.Elgp :=
  inv D.l2 ≫ inv D.l1 ≫ D.kEnv ≫ D.u1 ≫ D.u2 ≫ D.u3

theorem iplComposite_eq_kummer : D.iplComposite = D.kLGP ≫ D.u3 := by
  have e1 : D.kEnv ≫ D.u1 ≫ D.u2 ≫ D.u3 = D.l1 ≫ D.kGau ≫ D.u2 ≫ D.u3 := by
    rw [← Category.assoc, ← D.sq1, Category.assoc]
  have e2 : D.kGau ≫ D.u2 ≫ D.u3 = D.l2 ≫ D.kLGP ≫ D.u3 := by
    rw [← Category.assoc, ← D.sq2, Category.assoc]
  unfold iplComposite
  rw [e1, IsIso.inv_hom_id_assoc, e2, IsIso.inv_hom_id_assoc]

theorem iplComposite_eq_lower : D.iplComposite = D.l3 ≫ D.kLgp := by
  rw [iplComposite_eq_kummer, D.sq3]

end KummerDiagram

structure AlgorithmSetting : Type 1 where

  Strip : Type
  [grpd : Groupoid.{0} Strip]

  diagram : KummerDiagram Strip

  qStrip : Strip

  thetaLink : diagram.FLGP ⟶ qStrip

  Output : Type

  stripOf : Output → Strip

  actual : Output
  actual_strip : stripOf actual = diagram.Elgp

  indStep : Output → Output → Prop
  indStep_strip : ∀ x y, indStep x y → stripOf y = stripOf x

  hull : Set Output → Output
  hull_strip : ∀ (T : Set Output) (s : Strip), T.Nonempty → (∀ x ∈ T, stripOf x = s) → stripOf (hull T) = s

attribute [instance] AlgorithmSetting.grpd

namespace AlgorithmSetting

variable (S : AlgorithmSetting)

inductive Possible : S.Output → Prop
  | actual : Possible S.actual
  | ind {x y : S.Output} : Possible x → S.indStep x y → Possible y
  | hull (T : Set S.Output) : T.Nonempty → (∀ x ∈ T, Possible x) → Possible (S.hull T)

def possible : Set S.Output :=
  {x | S.Possible x}

def Linked (x : S.Output) : Prop :=
  (FullPoly (S.stripOf x) S.qStrip).Nonempty

theorem actual_mem_possible : S.actual ∈ S.possible :=
  Possible.actual

theorem possible_nonempty : S.possible.Nonempty :=
  ⟨S.actual, S.actual_mem_possible⟩

theorem possible_strip {x : S.Output} (hx : x ∈ S.possible) : S.stripOf x = S.diagram.Elgp := by
  induction hx with
  | actual => exact S.actual_strip
  | ind _ hstep ih => rw [S.indStep_strip _ _ hstep, ih]
  | hull T hT _ ih => exact S.hull_strip T _ hT ih

noncomputable def iplLink {x : S.Output} (hx : x ∈ S.possible) : S.stripOf x ⟶ S.qStrip :=
  eqToHom (S.possible_strip hx) ≫ inv S.diagram.iplComposite ≫ S.thetaLink

theorem iplLink_route {x : S.Output} (hx : x ∈ S.possible) :
    S.iplLink hx = eqToHom (S.possible_strip hx) ≫ inv S.diagram.kLgp ≫ inv S.diagram.l3 ≫ S.thetaLink := by
  unfold iplLink
  simp only [S.diagram.iplComposite_eq_lower, IsIso.inv_comp, Category.assoc]

theorem ipl : ∀ x ∈ S.possible, S.Linked x :=
  fun _ hx => ⟨S.iplLink hx, Set.mem_univ _⟩

theorem ipl_link_coric {x : S.Output} (α : S.stripOf x ⟶ S.stripOf x) (β : S.qStrip ⟶ S.qStrip) :
    (fun f => α ≫ f ≫ β) '' FullPoly (S.stripOf x) S.qStrip = FullPoly (S.stripOf x) S.qStrip :=
  fullPoly_conj α β

def possibleScalarValues (readout : S.Output → ℝ) : Set ℝ :=
  readout '' S.possible

def ScalarProduction (readout : S.Output → ℝ) (qValue : ℝ) : Prop :=
  qValue ∈ S.possibleScalarValues readout

theorem scalarProduction_iff_exists_possible_equal_value
    (readout : S.Output → ℝ) (qValue : ℝ) :
    S.ScalarProduction readout qValue ↔
      ∃ x : S.Output, x ∈ S.possible ∧ readout x = qValue := by
  rfl

theorem scalarProduction_iff_exists_possible_linked_equal_value
    (readout : S.Output → ℝ) (qValue : ℝ) :
    S.ScalarProduction readout qValue ↔
      ∃ x : S.Output,
        x ∈ S.possible ∧ S.Linked x ∧ readout x = qValue := by
  constructor
  · rintro ⟨x, hx, hvalue⟩
    exact ⟨x, hx, S.ipl x hx, hvalue⟩
  · rintro ⟨x, hx, _hlinked, hvalue⟩
    exact ⟨x, hx, hvalue⟩

theorem actual_scalarProduction (readout : S.Output → ℝ) :
    S.ScalarProduction readout (readout S.actual) := by
  exact ⟨S.actual, S.actual_mem_possible, rfl⟩

theorem scalarProduction_of_actual_readout_eq
    (readout : S.Output → ℝ) (qValue : ℝ)
    (h : readout S.actual = qValue) :
    S.ScalarProduction readout qValue := by
  exact ⟨S.actual, S.actual_mem_possible, h⟩

end AlgorithmSetting

section Model

open Src.IUT3.Theorem311

structure ModelStrip where
  tag : ℕ
  size : Bool → ℕ

instance : Groupoid.{0} ModelStrip where
  Hom A B := ∀ b, Fin (A.size b) ≃ Fin (B.size b)
  id A := fun b => Equiv.refl _
  comp f g := fun b => (f b).trans (g b)
  id_comp f := by funext b; rfl
  comp_id f := by funext b; rfl
  assoc f g h := by funext b; rfl
  inv f := fun b => (f b).symm
  inv_comp f := by funext b; exact Equiv.symm_trans_self _
  comp_inv f := by funext b; exact Equiv.self_trans_symm _

def obj (k : ℕ) : ModelStrip := ⟨k, fun _ => 2⟩

def strip2 : ModelStrip := obj 0

def strip3 : ModelStrip := ⟨100, fun _ => 3⟩

def swapHom (k l : ℕ) : obj k ⟶ obj l :=
  fun _ => (Equiv.swap (0 : Fin 2) 1 : Fin 2 ≃ Fin 2)

def idHom (k l : ℕ) : obj k ⟶ obj l :=
  fun _ => Equiv.refl (Fin 2)

def swapStrip : strip2 ⟶ strip2 :=
  swapHom 0 0

theorem swap_id_square (a b c d : ℕ) : swapHom a b ≫ idHom b d = idHom a c ≫ swapHom c d := by
  funext x
  exact Equiv.ext fun _ => rfl

def modelDiagram : KummerDiagram ModelStrip where
  Fenv := obj 1
  Fgau := obj 2
  FLGP := obj 3
  Flgp := obj 4
  Eenv := obj 5
  Egau := obj 6
  ELGP := obj 7
  Elgp := obj 8
  u1 := swapHom 5 6
  u2 := swapHom 6 7
  u3 := swapHom 7 8
  l1 := swapHom 1 2
  l2 := swapHom 2 3
  l3 := swapHom 3 4
  kEnv := idHom 1 5
  kGau := idHom 2 6
  kLGP := idHom 3 7
  kLgp := idHom 4 8
  sq1 := swap_id_square 1 2 5 6
  sq2 := swap_id_square 2 3 6 7
  sq3 := swap_id_square 3 4 7 8

noncomputable def modelHull (T : Set (ModelStrip × modelSystem.Regions)) : ModelStrip × modelSystem.Regions := by
  classical
  exact if h : T.Nonempty then ((Classical.choose h).1, fun vQ j => ⋃ x ∈ T, x.2 vQ j)
    else (strip2, fun vQ j => ∅)

theorem modelHull_strip (T : Set (ModelStrip × modelSystem.Regions)) (s : ModelStrip) (hT : T.Nonempty)
    (hs : ∀ x ∈ T, x.1 = s) : (modelHull T).1 = s := by
  unfold modelHull
  rw [dif_pos hT]
  exact hs (Classical.choose hT) (Classical.choose_spec hT)

noncomputable def modelAlgorithm : AlgorithmSetting where
  Strip := ModelStrip
  diagram := modelDiagram
  qStrip := strip2
  thetaLink := idHom 3 0
  Output := ModelStrip × modelSystem.Regions
  stripOf := Prod.fst
  actual := (obj 8, halfRegions)
  actual_strip := rfl
  indStep x y := y.1 = x.1 ∧ modelSystem.IndRel x.2 y.2
  indStep_strip _ _ h := h.1
  hull := modelHull
  hull_strip := modelHull_strip

theorem no_iso_strip3_strip2 : ¬ Nonempty (strip3 ⟶ strip2) := by
  rintro ⟨f⟩
  have h : Nonempty (Fin 3 ≃ Fin 2) := ⟨f true⟩
  have := Fin.equiv_iff_eq.mp h
  omega

theorem swapStrip_ne : swapStrip ≫ 𝟙 strip2 ≠ 𝟙 strip2 := by
  intro h
  have h0 := congrArg (fun g : strip2 ⟶ strip2 => ((g true : Fin 2 ≃ Fin 2) (0 : Fin 2) : Fin 2)) h
  change ((Equiv.swap (0 : Fin 2) 1).trans (Equiv.refl (Fin 2))) 0 = (Equiv.refl (Fin 2)) 0 at h0
  simp at h0

def rotAut : modelSystem.ProcessionAut :=
  ⟨fun j => finRotate (j.val + 1), fun _ _ _ _ => ()⟩

theorem rotAut_moves : halfRegions ≠ rotAut.act halfRegions := by
  intro hxy
  have h1 := congrFun (congrFun hxy ()) 1
  let w : Fin 2 → ℝ := fun α => if α = 0 then 1 else -1
  have hx : w ∈ halfRegions () 1 := by
    change (0 : ℝ) ≤ w 0
    simp [w]
  rw [h1] at hx
  obtain ⟨z, hz, hzw⟩ := hx
  have hw1 : w 1 = z ((finRotate 2).symm 1) := (congrFun hzw 1).symm
  have hwv : w 1 = -1 := by simp [w]
  have hz' : (0 : ℝ) ≤ z ((finRotate 2).symm 1) := by
    have hrot : (finRotate 2).symm 1 = 0 := by decide
    rw [hrot]
    exact hz
  linarith

theorem model_nondegenerate :
    (∃ x y, x ∈ modelAlgorithm.possible ∧ y ∈ modelAlgorithm.possible ∧ x ≠ y) ∧
      (∃ x, x ∉ modelAlgorithm.possible) ∧
      (∃ x, ¬ modelAlgorithm.Linked x) ∧
      (fun g => swapStrip ≫ g ≫ 𝟙 strip2) '' ({𝟙 strip2} : Set (strip2 ⟶ strip2)) ≠ {𝟙 strip2} := by
  refine ⟨?_, ?_, ?_, chosen_not_conj_stable _ _ swapStrip_ne⟩
  · refine ⟨(obj 8, halfRegions), (obj 8, rotAut.act halfRegions), AlgorithmSetting.Possible.actual,
      AlgorithmSetting.Possible.ind AlgorithmSetting.Possible.actual ⟨rfl, Or.inl ⟨rotAut, rfl⟩⟩, ?_⟩
    intro heq
    exact rotAut_moves (congrArg Prod.snd heq)
  · refine ⟨(strip3, halfRegions), fun hx => ?_⟩
    have h1 : strip3 = obj 8 := modelAlgorithm.possible_strip hx
    have h2 := congrFun (congrArg ModelStrip.size h1) true
    simp [obj, strip3] at h2
  · refine ⟨(strip3, halfRegions), fun ⟨f, _⟩ => no_iso_strip3_strip2 ⟨f⟩⟩

theorem model_ipl_without_arbitrary_scalarProduction :
    (∀ x ∈ modelAlgorithm.possible, modelAlgorithm.Linked x) ∧
      ¬ modelAlgorithm.ScalarProduction (fun _ => (0 : ℝ)) 1 := by
  constructor
  · exact modelAlgorithm.ipl
  · intro h
    rcases h with ⟨x, hx, hvalue⟩
    norm_num at hvalue

end Model

end Src.IUT3.Remark3111

section Check
open Src.IUT3.Remark3111
end Check
