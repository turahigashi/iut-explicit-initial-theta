import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Ideal.Defs

namespace SrcLib.Hull

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

def hull (P : Set M) : Submodule R M := Submodule.span R P

theorem hull_smul_mem (P : Set M) (r : R) {x : M} (hx : x ∈ hull (R := R) P) :
    r • x ∈ hull (R := R) P :=
  Submodule.smul_mem _ r hx

theorem hull_units_stable (P : Set M) (u : Rˣ) {x : M} (hx : x ∈ hull (R := R) P) :
    (u : R) • x ∈ hull (R := R) P :=
  hull_smul_mem P (u : R) hx

theorem hull_units_stable_iff (P : Set M) (u : Rˣ) {x : M} :
    (u : R) • x ∈ hull (R := R) P ↔ x ∈ hull (R := R) P := by
  constructor
  · intro h
    have := hull_smul_mem (R := R) P ((u⁻¹ : Rˣ) : R) h
    simpa [smul_smul, ← Units.val_mul] using this
  · intro h; exact hull_units_stable P u h

theorem subset_hull (P : Set M) : P ⊆ (hull (R := R) P : Set M) :=
  Submodule.subset_span

theorem hull_le_of_le (P : Set M) (N : Submodule R M) (h : P ⊆ (N : Set M)) :
    hull (R := R) P ≤ N :=
  Submodule.span_le.mpr h

theorem hull_is_least_stable (P : Set M) :
    P ⊆ (hull (R := R) P : Set M) ∧
    (∀ r : R, ∀ x ∈ hull (R := R) P, r • x ∈ hull (R := R) P) ∧
    (∀ N : Submodule R M, P ⊆ (N : Set M) → hull (R := R) P ≤ N) :=
  ⟨subset_hull P, fun r _ hx => hull_smul_mem P r hx, fun N h => hull_le_of_le P N h⟩

theorem hull_of_submodule (N : Submodule R M) :
    hull (R := R) (N : Set M) = N :=
  Submodule.span_eq N

theorem hull_mono {P Q : Set M} (h : P ⊆ Q) :
    hull (R := R) P ≤ hull (R := R) Q :=
  Submodule.span_mono h

theorem summary_Ob2 (P : Set M) (N : Submodule R M) :
    (P ⊆ (hull (R := R) P : Set M)) ∧
    (∀ u : Rˣ, ∀ x ∈ hull (R := R) P, (u : R) • x ∈ hull (R := R) P) ∧
    (P ⊆ (N : Set M) → hull (R := R) P ≤ N) ∧
    (hull (R := R) (N : Set M) = N) :=
  ⟨subset_hull P,
   fun u _ hx => hull_units_stable P u hx,
   fun h => hull_le_of_le P N h,
   hull_of_submodule N⟩

def unitOrbit (x : M) : Set M := {y | ∃ u : Rˣ, y = (u : R) • x}

theorem self_mem_unitOrbit (x : M) : x ∈ unitOrbit (R := R) x :=
  ⟨1, by simp⟩

theorem hull_unitOrbit_eq_span_singleton (x : M) :
    hull (R := R) (unitOrbit (R := R) x) = Submodule.span R {x} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨u, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span (self_mem_unitOrbit x)

theorem hull_indep_of_representative (x : M) (u : Rˣ) :
    hull (R := R) (unitOrbit (R := R) ((u : R) • x))
      = hull (R := R) (unitOrbit (R := R) x) := by
  rw [hull_unitOrbit_eq_span_singleton, hull_unitOrbit_eq_span_singleton]
  apply le_antisymm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨((u⁻¹ : Rˣ) : R), ?_⟩
    simp [smul_smul, ← Units.val_mul]

theorem summary_Ob1_to_Ob2 (x : M) (u : Rˣ) :
    (x ∈ unitOrbit (R := R) x) ∧
    (hull (R := R) (unitOrbit (R := R) x) = Submodule.span R {x}) ∧
    (hull (R := R) (unitOrbit (R := R) ((u : R) • x))
       = hull (R := R) (unitOrbit (R := R) x)) :=
  ⟨self_mem_unitOrbit x,
   hull_unitOrbit_eq_span_singleton x,
   hull_indep_of_representative x u⟩

end SrcLib.Hull
