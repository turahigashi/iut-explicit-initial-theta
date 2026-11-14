-- IUT-STATEMENT: IUT-III Remark 3.9.5
/-
# Uniqueness of the hull of Remark 3.9.5(ii): a conditional set-level theory

[S] Mochizuki, IUT III, May 2020, Remark 3.9.5(ii)–(iii), pp. 126–128.

[P] `HullOperator` takes as input the domain and the family of hulls, the
operator, and (P1)–(P3).  From these conditions we prove the intersection
formula, uniqueness and idempotence, and that the union of `Phi` lies in the
hull.  `quantifier_choice_dissolved_by_uniqueness` is the equality of the
values of two hulls that land in the same family.  It does not state that the
designated q lies in that hull, nor the comparison inequality of the source.

There is no topology in this type.  `indeterminacy_is_bounded` is an inclusion
of sets, not a proof of compactness.  `without_the_condition_unbounded` proves
non-inclusion in a degenerate set model; it does not state topological
unboundedness.  The actual λ-O hull, finite log-volume, compactness, and the
connection to the full family of possible images of the source are needed
separately.  Not independently re-checked.
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace IUTFormal.M3.Theorem311.Remark395

variable {α : Type*}

/-- The source's `ℙ` (all product regions) and `ℍ` (all hulls, `ℍ ⊆ ℙ`), with
the hull-forming operation `φ : ℙ → ℍ`, axiomatized only by (P1)(P2)(P3) of
(ii) in the source. -/
structure HullOperator (α : Type*) where
  /-- `ℙ`: all regions to which log-volume applies. -/
  isDomain : Set α → Prop
  /-- `ℍ`: all hulls. -/
  isHull   : Set α → Prop
  /-- `ℍ ⊆ ℙ`. -/
  hull_sub_domain : ∀ {H}, isHull H → isDomain H
  /-- The hull-forming operation. -/
  φ : Set α → Set α
  /-- `φ` lands in `ℍ`. -/
  φ_isHull : ∀ {P}, isDomain P → isHull (φ P)
  /-- **(P1)** Identity on hulls. -/
  P1 : ∀ {H}, isHull H → φ H = H
  /-- **(P2)** Extensive. -/
  P2 : ∀ {P}, isDomain P → P ⊆ φ P
  /-- **(P3)** Monotone. -/
  P3 : ∀ {P₁ P₂}, isDomain P₁ → isDomain P₂ → P₁ ⊆ P₂ → φ P₁ ⊆ φ P₂

namespace HullOperator

variable (Ω : HullOperator α)

/-- The source says this follows *formally* from (P1)–(P3); here it is proved:
`φ(P) = ⋂ {H ∈ ℍ | P ⊆ H}`. -/
theorem hull_eq_iInter {P : Set α} (hP : Ω.isDomain P) :
    Ω.φ P = ⋂ (H : Set α) (_ : Ω.isHull H ∧ P ⊆ H), H := by
  apply Set.Subset.antisymm
  · -- φ P is contained in each H on the right
    simp only [Set.subset_iInter_iff]
    rintro H ⟨hH, hPH⟩
    calc Ω.φ P ⊆ Ω.φ H := Ω.P3 hP (Ω.hull_sub_domain hH) hPH
    _ = H := Ω.P1 hH
  · -- φ P itself is one of the terms of the intersection on the right
    have hmem : Ω.isHull (Ω.φ P) ∧ P ⊆ Ω.φ P := ⟨Ω.φ_isHull hP, Ω.P2 hP⟩
    intro x hx
    exact Set.mem_iInter₂.mp hx (Ω.φ P) hmem

/-- An operator satisfying (P1)–(P3) is **unique** (the source: "uniquely characterized"). -/
theorem hull_unique (Ω' : HullOperator α)
    (hdom : Ω.isDomain = Ω'.isDomain) (hhull : Ω.isHull = Ω'.isHull)
    {P : Set α} (hP : Ω.isDomain P) :
    Ω.φ P = Ω'.φ P := by
  have hP' : Ω'.isDomain P := hdom ▸ hP
  rw [Ω.hull_eq_iInter hP, Ω'.hull_eq_iInter hP', hhull]

/-- It is a closure operator (idempotent). -/
theorem hull_idempotent {P : Set α} (hP : Ω.isDomain P) :
    Ω.φ (Ω.φ P) = Ω.φ P :=
  Ω.P1 (Ω.φ_isHull hP)

/-- The hull contains the original region (a restatement of (P2); the basis of monotonicity of log-volume). -/
theorem domain_subset_hull {P : Set α} (hP : Ω.isDomain P) : P ⊆ Ω.φ P := Ω.P2 hP

/-! ## §2 The union of Phi lies in the hull (compactness is a separate obligation) -/

/-- The source's `Φ(P)`: hulls *contained in* `φ(P)` whose log-volume is at
least that of `P`.  The condition `H ⊆ φ(P)` is the point. -/
def Phi (μ : Set α → ℝ) (P : Set α) : Set (Set α) :=
  { H | Ω.isHull H ∧ H ⊆ Ω.φ P ∧ μ H ≥ μ P }

/-- By the inclusion imposed on Phi in its definition, the whole union lies in the hull.  Not a topological statement. -/
theorem indeterminacy_is_bounded (μ : Set α → ℝ) (P : Set α) :
    ⋃ H ∈ Ω.Phi μ P, H ⊆ Ω.φ P := by
  simp only [Set.iUnion_subset_iff]
  rintro H ⟨-, hsub, -⟩
  exact hsub

/-- The version *without* the condition `H ⊆ φ(P)`. -/
def PhiWithoutCondition (μ : Set α → ℝ) (P : Set α) : Set (Set α) :=
  { H | Ω.isHull H ∧ μ H ≥ μ P }

end HullOperator

/-! ## §3 A set model without the inclusion condition -/

/-- The degenerate hull operator used for the counterexample: `ℍ = ℙ = all subsets`, `φ = id`. -/
def trivialHull : HullOperator ℝ where
  isDomain := fun _ => True
  isHull   := fun _ => True
  hull_sub_domain := fun _ => trivial
  φ := id
  φ_isHull := fun _ => trivial
  P1 := fun _ => rfl
  P2 := fun _ => subset_rfl
  P3 := fun _ _ h => h

/-- In the degenerate set model, dropping the inclusion condition lets the union leave the original hull. -/
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

/-! ## §4 Two constructions with the same family of hulls give the same value -/

/-- Hulls obtained from the same domain, family of hulls and (P1)–(P3) coincide, so any real-valued function takes the same value on them.  No comparison with the designated q is included. -/
theorem quantifier_choice_dissolved_by_uniqueness
    (Ω Ω' : HullOperator α)
    (hdom : Ω.isDomain = Ω'.isDomain) (hhull : Ω.isHull = Ω'.isHull)
    (μ : Set α → ℝ) {P : Set α} (hP : Ω.isDomain P) :
    -- whichever standard construction is taken: the same set, hence the same volume
    μ (Ω.φ P) = μ (Ω'.φ P) := by
  rw [Ω.hull_unique Ω' hdom hhull hP]

#print axioms HullOperator.hull_eq_iInter
#print axioms HullOperator.hull_unique
#print axioms HullOperator.hull_idempotent
#print axioms HullOperator.indeterminacy_is_bounded
#print axioms without_the_condition_unbounded
#print axioms quantifier_choice_dissolved_by_uniqueness

end IUTFormal.M3.Theorem311.Remark395
