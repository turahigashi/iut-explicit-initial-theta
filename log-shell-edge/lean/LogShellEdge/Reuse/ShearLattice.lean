import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel

/-!
# The span of an orbit under shears

`span_orbit_eq`: if `x = α a + u b + w₀` with `u` a unit and `w₀` in the span of `S`, then the span of
`x`, `x + u a` and the elements `x + u w + c(w) a` (`w ∈ S`) equals the span of `a`, `b` and `S`.
Used in the proof of Lemma 5.2 (`EvenSmall.lemma52`).

Adapted from an earlier, unpublished Lean development of the author: the comments were
rewritten, the namespace was renamed and a few unused summary statements were removed; the
remaining definitions and proofs are unchanged.
-/

set_option autoImplicit false

namespace LogShellEdge.ShearLattice

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem span_orbit_eq (a b : V) (S : Set V) (α u : R) (hu : IsUnit u) (w₀ : V)
    (hw₀ : w₀ ∈ Submodule.span R S) (c : V → R) (x : V) (hx : x = α • a + u • b + w₀) :
    Submodule.span R (({x, x + u • a} : Set V) ∪ (fun w => x + u • w + c w • a) '' S) =
      Submodule.span R (({a, b} : Set V) ∪ S) := by
  obtain ⟨u', rfl⟩ := hu
  apply le_antisymm
  ·
    set T := Submodule.span R (({a, b} : Set V) ∪ S) with hT
    have ha : a ∈ T := Submodule.subset_span (Or.inl (Or.inl rfl))
    have hb : b ∈ T := Submodule.subset_span (Or.inl (Or.inr rfl))
    have hS : ∀ w ∈ S, w ∈ T := fun w hw => Submodule.subset_span (Or.inr hw)
    have hw : w₀ ∈ T := Submodule.span_mono Set.subset_union_right hw₀
    have hxT : x ∈ T := by
      rw [hx]
      exact T.add_mem (T.add_mem (T.smul_mem _ ha) (T.smul_mem _ hb)) hw
    apply Submodule.span_le.2
    rintro y (hy | ⟨w, hwS, rfl⟩)
    · rcases hy with rfl | rfl
      · exact hxT
      · exact T.add_mem hxT (T.smul_mem _ ha)
    · exact T.add_mem (T.add_mem hxT (T.smul_mem _ (hS w hwS))) (T.smul_mem _ ha)
  ·
    set N := Submodule.span R (({x, x + (u' : R) • a} : Set V) ∪
      (fun w => x + (u' : R) • w + c w • a) '' S) with hN
    have hxN : x ∈ N := Submodule.subset_span (Or.inl (Or.inl rfl))
    have hxa : x + (u' : R) • a ∈ N := Submodule.subset_span (Or.inl (Or.inr rfl))
    have hua : (u' : R) • a ∈ N := by
      have h := N.sub_mem hxa hxN
      rwa [add_sub_cancel_left] at h
    have ha : a ∈ N := by
      have h := N.smul_mem ((u'⁻¹ : Rˣ) : R) hua
      rwa [smul_smul, Units.inv_mul, one_smul] at h
    have hS : ∀ w ∈ S, w ∈ N := by
      intro w hwS
      have h1 : x + (u' : R) • w + c w • a ∈ N := Submodule.subset_span (Or.inr ⟨w, hwS, rfl⟩)
      have h2 : (u' : R) • w ∈ N := by
        have h := N.sub_mem (N.sub_mem h1 hxN) (N.smul_mem (c w) ha)
        have e : x + (u' : R) • w + c w • a - x - c w • a = (u' : R) • w := by abel
        rwa [e] at h
      have h := N.smul_mem ((u'⁻¹ : Rˣ) : R) h2
      rwa [smul_smul, Units.inv_mul, one_smul] at h
    have hw : w₀ ∈ N := (Submodule.span_le.2 hS) hw₀
    have hub : (u' : R) • b ∈ N := by
      have h := N.sub_mem (N.sub_mem hxN (N.smul_mem α ha)) hw
      have e : x - α • a - w₀ = (u' : R) • b := by rw [hx]; abel
      rwa [e] at h
    have hb : b ∈ N := by
      have h := N.smul_mem ((u'⁻¹ : Rˣ) : R) hub
      rwa [smul_smul, Units.inv_mul, one_smul] at h
    apply Submodule.span_le.2
    rintro y (hy | hy)
    · rcases hy with rfl | rfl
      · exact ha
      · exact hb
    · exact hS y hy

end LogShellEdge.ShearLattice
