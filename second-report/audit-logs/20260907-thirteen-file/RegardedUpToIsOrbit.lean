import Init

/-!
# A finite distinction between invariance and closure

This is the finite model in Appendix B.  It proves statements about four-bit
subsets only, not statements about the possible images in IUT or hypothesis SA.
`act` interchanges 0 with 1 and 2 with 3; `hull` fills the interval spanned by a
subset.  `VolInvariant` and `UpToAct` are distinct predicates.  Invariance alone
does not imply closure.  For the orbit predicate both hold, yet the hull of the
union has strictly larger cardinality than the hull of either orbit member.
-/

namespace RegardedUpTo

def mem (n i : Nat) : Bool := (n / 2 ^ i) % 2 == 1

def card (n : Nat) : Nat :=
  (if mem n 0 then 1 else 0) + (if mem n 1 then 1 else 0)
  + (if mem n 2 then 1 else 0) + (if mem n 3 then 1 else 0)

def act (n : Nat) : Nat :=
  (if mem n 0 then 2 else 0) + (if mem n 1 then 1 else 0)
  + (if mem n 2 then 8 else 0) + (if mem n 3 then 4 else 0)

def hull (n : Nat) : Nat :=
  if n == 0 then 0 else
  let lo := if mem n 0 then 0 else if mem n 1 then 1 else if mem n 2 then 2 else 3
  let hi := if mem n 3 then 3 else if mem n 2 then 2 else if mem n 1 then 1 else 0
  (if 0 ≥ lo && 0 ≤ hi then 1 else 0) + (if 1 ≥ lo && 1 ≤ hi then 2 else 0)
  + (if 2 ≥ lo && 2 ≤ hi then 4 else 0) + (if 3 ≥ lo && 3 ≤ hi then 8 else 0)

def cup (m n : Nat) : Nat :=
  (if mem m 0 || mem n 0 then 1 else 0) + (if mem m 1 || mem n 1 then 2 else 0)
  + (if mem m 2 || mem n 2 then 4 else 0) + (if mem m 3 || mem n 3 then 8 else 0)

def A : Nat := 5

def sA : Nat := 10

theorem act_A : act A = sA := by decide

theorem act_is_nontrivial : A ≠ act A := by decide

theorem hull_card_invariant : card (hull A) = card (hull (act A)) := by decide

theorem union_hull_exceeds_every_member :
    card (hull A) < card (hull (cup A (act A)))
    ∧ card (hull (act A)) < card (hull (cup A (act A))) := by decide

abbrev VolInvariant (Output : Nat → Prop) : Prop :=
  ∀ r, Output r → card (hull (act r)) = card (hull r)

abbrev UpToAct (Output : Nat → Prop) : Prop :=
  ∀ r, Output r → Output (act r)

abbrev Single (r : Nat) : Prop := r = A

theorem orbit_not_forced_by_invariance :
    VolInvariant Single ∧ ¬ UpToAct Single := by
  constructor
  · intro r hr; subst hr; decide
  · intro h
    have h2 : act A = A := h A rfl
    exact absurd h2 (by decide)

abbrev Orbit (r : Nat) : Prop := r = A ∨ r = sA

theorem act_sA : act sA = A := by decide

theorem orbit_is_up_to_act : UpToAct Orbit := by
  intro r hr
  rcases hr with h | h
  · exact Or.inr (by rw [h, act_A])
  · exact Or.inl (by rw [h, act_sA])

theorem orbit_vol_invariant : VolInvariant Orbit := by
  intro r hr
  rcases hr with h | h <;> subst h <;> decide

theorem the_point :
    UpToAct Orbit
    ∧ VolInvariant Orbit
    ∧ card (hull A) < card (hull (cup A (act A)))
    ∧ card (hull (act A)) < card (hull (cup A (act A))) :=
  ⟨orbit_is_up_to_act, orbit_vol_invariant, by decide, by decide⟩

/-! ## Axiom check

The per-declaration axiom dependencies of this file are reported by
`scripts/lean_audit.py`, which runs Lean's print-axioms command on EVERY
declaration the file adds to the environment, not only on the named theorems.
The explicit print-axioms lines that used to stand here covered a self-selected
subset; an axiom report not attributable to a declaration the auditor is
tracking is exactly what the auditor refuses to accept, so they are removed.
-/

end RegardedUpTo
