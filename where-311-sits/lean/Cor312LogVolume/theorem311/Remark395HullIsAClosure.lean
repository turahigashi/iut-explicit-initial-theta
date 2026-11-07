import Mathlib.Data.Set.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Src.CoreLayer.Theorem311.Remark395

variable {α : Type*}

structure HullOperator (α : Type*) where

  isDomain : Set α → Prop

  isHull   : Set α → Prop

  hull_sub_domain : ∀ {H}, isHull H → isDomain H

  φ : Set α → Set α

  φ_isHull : ∀ {P}, isDomain P → isHull (φ P)

  P1 : ∀ {H}, isHull H → φ H = H

  P2 : ∀ {P}, isDomain P → P ⊆ φ P

  P3 : ∀ {P₁ P₂}, isDomain P₁ → isDomain P₂ → P₁ ⊆ P₂ → φ P₁ ⊆ φ P₂

namespace HullOperator

variable (Ω : HullOperator α)

theorem hull_eq_iInter {P : Set α} (hP : Ω.isDomain P) :
    Ω.φ P = ⋂ (H : Set α) (_ : Ω.isHull H ∧ P ⊆ H), H := by
  apply Set.Subset.antisymm
  ·
    simp only [Set.subset_iInter_iff]
    rintro H ⟨hH, hPH⟩
    calc Ω.φ P ⊆ Ω.φ H := Ω.P3 hP (Ω.hull_sub_domain hH) hPH
    _ = H := Ω.P1 hH
  ·
    have hmem : Ω.isHull (Ω.φ P) ∧ P ⊆ Ω.φ P := ⟨Ω.φ_isHull hP, Ω.P2 hP⟩
    intro x hx
    exact Set.mem_iInter₂.mp hx (Ω.φ P) hmem

theorem hull_unique (Ω' : HullOperator α)
    (hdom : Ω.isDomain = Ω'.isDomain) (hhull : Ω.isHull = Ω'.isHull)
    {P : Set α} (hP : Ω.isDomain P) :
    Ω.φ P = Ω'.φ P := by
  have hP' : Ω'.isDomain P := hdom ▸ hP
  rw [Ω.hull_eq_iInter hP, Ω'.hull_eq_iInter hP', hhull]

theorem hull_idempotent {P : Set α} (hP : Ω.isDomain P) :
    Ω.φ (Ω.φ P) = Ω.φ P :=
  Ω.P1 (Ω.φ_isHull hP)

theorem domain_subset_hull {P : Set α} (hP : Ω.isDomain P) : P ⊆ Ω.φ P := Ω.P2 hP

def Phi (μ : Set α → ℝ) (P : Set α) : Set (Set α) :=
  { H | Ω.isHull H ∧ H ⊆ Ω.φ P ∧ μ H ≥ μ P }

theorem indeterminacy_is_bounded (μ : Set α → ℝ) (P : Set α) :
    ⋃ H ∈ Ω.Phi μ P, H ⊆ Ω.φ P := by
  simp only [Set.iUnion_subset_iff]
  rintro H ⟨-, hsub, -⟩
  exact hsub

def PhiWithoutCondition (μ : Set α → ℝ) (P : Set α) : Set (Set α) :=
  { H | Ω.isHull H ∧ μ H ≥ μ P }

end HullOperator

def trivialHull : HullOperator ℝ where
  isDomain := fun _ => True
  isHull   := fun _ => True
  hull_sub_domain := fun _ => trivial
  φ := id
  φ_isHull := fun _ => trivial
  P1 := fun _ => rfl
  P2 := fun _ => subset_rfl
  P3 := fun _ _ h => h

theorem without_the_condition_unbounded :
    (⋃ H ∈ trivialHull.Phi (fun _ => (0:ℝ)) {0}, H) ⊆ trivialHull.φ {0} ∧
    ¬ ((⋃ H ∈ trivialHull.PhiWithoutCondition (fun _ => (0:ℝ)) {0}, H)
        ⊆ trivialHull.φ {0}) := by
  constructor
  · exact HullOperator.indeterminacy_is_bounded _ _ _
  · intro h
    have h1 : (1 : ℝ) ∈ ⋃ H ∈ trivialHull.PhiWithoutCondition (fun _ => (0:ℝ)) {0}, H :=
      Set.mem_iUnion₂.mpr ⟨{1}, ⟨trivial, le_refl 0⟩, rfl⟩
    have h2 := h h1
    simp [trivialHull] at h2

theorem quantifier_choice_dissolved_by_uniqueness
    (Ω Ω' : HullOperator α)
    (hdom : Ω.isDomain = Ω'.isDomain) (hhull : Ω.isHull = Ω'.isHull)
    (μ : Set α → ℝ) {P : Set α} (hP : Ω.isDomain P) :

    μ (Ω.φ P) = μ (Ω'.φ P) := by
  rw [Ω.hull_unique Ω' hdom hhull hP]

end Src.CoreLayer.Theorem311.Remark395
