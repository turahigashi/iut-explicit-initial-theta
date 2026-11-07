import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

namespace CitedLV.Theorem311.Assembly

structure Assembly (V W : Type*) [Preorder W] where

  thetaSet : Set V

  qValue : V

  unitAction : V → V

  readout : V → W

  readout_invariant : ∀ v : V, readout (unitAction v) = readout v

  thetaSet_stable : ∀ v ∈ thetaSet, unitAction v ∈ thetaSet

  bound : W

  thetaSet_bounded : ∀ v ∈ thetaSet, readout v ≤ bound

variable {V W : Type*} [Preorder W]

theorem readout_survives_iteration (A : Assembly V W) (v : V) :
    ∀ n : ℕ, A.readout (A.unitAction^[n] v) = A.readout v := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', A.readout_invariant]
      exact ih

theorem thetaSet_survives_iteration (A : Assembly V W) {v : V} (hv : v ∈ A.thetaSet) :
    ∀ n : ℕ, A.unitAction^[n] v ∈ A.thetaSet := by
  intro n
  induction n with
  | zero => exact hv
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact A.thetaSet_stable _ ih

theorem comparison_is_well_posed (A : Assembly V W) {v : V} (hv : v ∈ A.thetaSet) (n : ℕ) :
    A.unitAction^[n] v ∈ A.thetaSet ∧ A.readout (A.unitAction^[n] v) ≤ A.bound :=
  ⟨thetaSet_survives_iteration A hv n,
   by rw [readout_survives_iteration A v n]; exact A.thetaSet_bounded v hv⟩

def counterexample : Assembly ℕ ℕ where
  thetaSet := {0}
  qValue := 5
  unitAction := id
  readout := id
  readout_invariant := fun _ => rfl
  thetaSet_stable := fun _ hv => hv
  bound := 0
  thetaSet_bounded := by
    intro v hv
    simp only [Set.mem_singleton_iff] at hv
    subst hv
    exact le_refl 0

theorem conditions_do_not_give_membership :
    counterexample.qValue ∉ counterexample.thetaSet
    ∧ ¬ (counterexample.readout counterexample.qValue ≤ counterexample.bound) := by
  constructor
  · intro h
    have h0 : (5 : ℕ) = 0 := Set.mem_singleton_iff.mp h
    exact absurd h0 (by decide)
  · intro h
    have h5 : (5 : ℕ) ≤ 0 := h
    exact absurd h5 (by decide)

def satisfyingExample : Assembly ℕ ℕ where
  thetaSet := {0}
  qValue := 0
  unitAction := id
  readout := id
  readout_invariant := fun _ => rfl
  thetaSet_stable := fun _ hv => hv
  bound := 0
  thetaSet_bounded := by
    intro v hv
    simp only [Set.mem_singleton_iff] at hv
    subst hv
    exact le_refl 0

theorem satisfying_example_has_membership :
    satisfyingExample.qValue ∈ satisfyingExample.thetaSet := rfl

theorem inequality_from_membership (A : Assembly V W)
    (hmem : A.qValue ∈ A.thetaSet) :
    A.readout A.qValue ≤ A.bound :=
  A.thetaSet_bounded A.qValue hmem

theorem inequality_survives_iteration (A : Assembly V W)
    (hmem : A.qValue ∈ A.thetaSet) (n : ℕ) :
    A.readout (A.unitAction^[n] A.qValue) ≤ A.bound := by
  rw [readout_survives_iteration A A.qValue n]
  exact inequality_from_membership A hmem

theorem phaseG0_summary (A : Assembly V W) (v : V) (hv : v ∈ A.thetaSet) (n : ℕ) :
    (A.readout (A.unitAction^[n] v) = A.readout v)
    ∧ (A.unitAction^[n] v ∈ A.thetaSet)
    ∧ ((A.qValue ∈ A.thetaSet) → A.readout A.qValue ≤ A.bound)
    ∧ (counterexample.qValue ∉ counterexample.thetaSet
       ∧ ¬ (counterexample.readout counterexample.qValue ≤ counterexample.bound)) :=
  ⟨readout_survives_iteration A v n,
   thetaSet_survives_iteration A hv n,
   inequality_from_membership A,
   conditions_do_not_give_membership⟩

end CitedLV.Theorem311.Assembly
