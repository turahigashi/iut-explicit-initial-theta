/-
Elementary cores of the readings (a)-(e) of the central question
(Section 1.6) of "Questions on the remaining value-group profile switch
from Theorem 3.11 to Corollary 3.12", version 2.0.0.

Standalone: it depends only on Mathlib.  Compiled with Lean 4.30.0 against
Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f; the axioms printed at the
end are among propext, Classical.choice and Quot.sound.

What is checked are the logical and arithmetic forms that the readings use.
  * Section 1, readings (a) and (b): an upper bound for the hull of the
    maximal family is an upper bound for every smaller family; the hull of a
    family that contains the container and lies in it is the hull of the
    container; an excess bounded independently of N fails, from some N on, a
    requirement that grows linearly in N.
  * Section 2, readings (c) and (d): a statement about data that do not
    contain the value of the q-pilot also holds in the configuration that
    changes only that value, and there (S) at the level of values fails; so
    such a statement does not imply (S).
  * Section 3, reading (e) with Q0, Q1, Q2 and Q6: a scaling of the local
    degrees that keeps the families of total degree zero is one scalar common
    to all places; one scalar acting on all labels alike does not carry the
    profile {a}_j to {j^2 a}_j, nor back, once two labels are present; a
    transport that keeps every degree readout keeps the profile.

What is not checked: that the constructions of IUT have the forms assumed
here, that is, the readings themselves; the models cited in the note; and
anything about mono-theta environments, Frobenioids or Hodge theatres.
-/
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

set_option autoImplicit false

namespace CentralQuestionReadings

/-! ## 1. Readings (a) and (b): the family of possible images and the hull -/

section Hull

variable {α : Type*}

/-- The hull of a family of regions: the hull of their union. -/
def familyHull (hull : Set α → Set α) (F : Set (Set α)) : Set α :=
  hull (⋃₀ F)

/-- A larger family has a larger hull, for a monotone hull operator. -/
theorem familyHull_mono {hull : Set α → Set α} (hmono : Monotone hull)
    {F G : Set (Set α)} (hFG : F ⊆ G) : familyHull hull F ⊆ familyHull hull G :=
  hmono (Set.sUnion_subset_sUnion hFG)

/-- Reading (b): if the family contains the container and every member of
the family lies in the container, its hull is the hull of the container. -/
theorem familyHull_eq_hull_container (hull : Set α → Set α)
    {F : Set (Set α)} {C : Set α} (hC : C ∈ F) (hle : ∀ R ∈ F, R ⊆ C) :
    familyHull hull F = hull C := by
  unfold familyHull
  rw [show ⋃₀ F = C from
    subset_antisymm (Set.sUnion_subset hle) (Set.subset_sUnion_of_mem hC)]

/-- Readings (a) and (b): an upper bound for the excess of the hull of the
maximal family over the log-volume `θ` of the Θ-pilot is an upper bound for
every smaller family, for a monotone hull and a monotone log-volume. -/
theorem excess_le_of_subfamily {hull : Set α → Set α} (hmono : Monotone hull)
    {μ : Set α → ℝ} (hμ : Monotone μ) {F G : Set (Set α)} (hFG : F ⊆ G)
    {θ E : ℝ} (hG : μ (familyHull hull G) - θ ≤ E) :
    μ (familyHull hull F) - θ ≤ E := by
  have := hμ (familyHull_mono hmono hFG)
  linarith

/-- Reading (b): an excess bounded independently of `N` fails, from some `N`
on, a requirement `s * N + t` with `s > 0`. -/
theorem bounded_fails_linear (excess : ℕ → ℝ) {E s t : ℝ} (hs : 0 < s)
    (hbd : ∀ N, excess N ≤ E) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ¬ (s * N + t ≤ excess N) := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((E - t) / s)
  refine ⟨N₀, fun N hN h => ?_⟩
  have h1 : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
  have h2 : E - t < N₀ * s := (div_lt_iff₀ hs).1 hN₀
  have h3 : (N₀ : ℝ) * s ≤ N * s := mul_le_mul_of_nonneg_right h1 hs.le
  have h4 := hbd N
  linarith

/-- Readings (a) and (b) together.  Along configurations indexed by `N` (for
instance theta data whose Tate parameter is raised to the power `N`), suppose
that the actual family lies in the maximal family, that the maximal family
contains the container and lies in it, and that the excess of the hull of
the container over the Θ-pilot is bounded by `E` independently of `N`.  Then,
from some `N` on, the hull of the actual family fails every requirement that
grows linearly in `N`. -/
theorem actual_family_fails_linear_requirement {hull : Set α → Set α}
    (hmono : Monotone hull) {μ : Set α → ℝ} (hμ : Monotone μ)
    (Fact Fmax : ℕ → Set (Set α)) (C : ℕ → Set α) (θ : ℕ → ℝ) {E s t : ℝ}
    (hs : 0 < s) (hsub : ∀ N, Fact N ⊆ Fmax N) (hC : ∀ N, C N ∈ Fmax N)
    (hle : ∀ N, ∀ R ∈ Fmax N, R ⊆ C N) (hE : ∀ N, μ (hull (C N)) - θ N ≤ E) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ¬ (s * N + t ≤ μ (familyHull hull (Fact N)) - θ N) := by
  apply bounded_fails_linear _ hs
  intro N
  apply excess_le_of_subfamily hmono hμ (hsub N)
  rw [familyHull_eq_hull_container hull (hC N) (hle N)]
  exact hE N

/-- The hypotheses of `actual_family_fails_linear_requirement` can all be met
together, with a nonempty actual family. -/
theorem actual_family_hypotheses_satisfiable :
    ∃ (hull : Set ℕ → Set ℕ) (μ : Set ℕ → ℝ) (Fact Fmax : ℕ → Set (Set ℕ))
      (C : ℕ → Set ℕ) (θ : ℕ → ℝ) (E : ℝ),
      Monotone hull ∧ Monotone μ ∧ (∀ N, Fact N ⊆ Fmax N) ∧ (∀ N, C N ∈ Fmax N) ∧
      (∀ N, ∀ R ∈ Fmax N, R ⊆ C N) ∧ (∀ N, μ (hull (C N)) - θ N ≤ E) ∧
      (∀ N, (Fact N).Nonempty) :=
  ⟨id, fun _ => 0, fun _ => {∅}, fun _ => {∅, Set.univ}, fun _ => Set.univ,
    fun _ => 0, 0, monotone_id, fun _ _ _ => le_rfl, fun _ => by simp,
    fun _ => by simp, fun _ _ _ => Set.subset_univ _, fun _ => by norm_num,
    fun _ => Set.singleton_nonempty _⟩

end Hull

/-! ## 2. Readings (c) and (d): statements whose data omit the q-pilot -/

section QValue

/-- A configuration: data that do not contain the value of the q-pilot, and
that value, the log-volume of the image of the q-pilot. -/
structure Config (D : Type*) where
  data : D
  qVal : ℝ

/-- (S) at the level of values: the log-volume of the q-pilot does not exceed
the log-volume of the hull, which is computed from the data. -/
def ValueS {D : Type*} (hullVol : D → ℝ) (c : Config D) : Prop :=
  c.qVal ≤ hullVol c.data

/-- Readings (c) and (d): a statement about the data also holds in the
configuration that changes only the value of the q-pilot, and in that
configuration (S) at the level of values fails. -/
theorem data_statement_holds_where_S_fails {D : Type*} (hullVol : D → ℝ)
    (P : D → Prop) (c : Config D) (hP : P c.data) :
    ∃ c' : Config D, c'.data = c.data ∧ P c'.data ∧ ¬ ValueS hullVol c' := by
  refine ⟨⟨c.data, hullVol c.data + 1⟩, rfl, hP, ?_⟩
  intro h
  simp only [ValueS] at h
  linarith

/-- Hence a statement about the data that holds in some configuration does not
imply (S) at the level of values. -/
theorem data_statement_does_not_imply_S {D : Type*} (hullVol : D → ℝ)
    (P : D → Prop) (c : Config D) (hP : P c.data) :
    ¬ ∀ c' : Config D, P c'.data → ValueS hullVol c' := by
  intro h
  obtain ⟨c', -, hP', hS⟩ := data_statement_holds_where_S_fails hullVol P c hP
  exact hS (h c' hP')

end QValue

/-! ## 3. Reading (e), with Q0, Q1, Q2 and Q6: scalars, places and labels -/

section Scalars

open Finset

/-- Reading (e), with Q1: a scaling of the local degrees, place by place,
that sends every family of local degrees of total zero to one of total zero
is one scalar common to all places.  The families of total zero stand for the
principal divisors of the product formula. -/
theorem scaling_keeping_total_zero_is_common {V : Type*} [Fintype V]
    [DecidableEq V] (c : V → ℝ)
    (h : ∀ x : V → ℝ, ∑ v, x v = 0 → ∑ v, c v * x v = 0) (v w : V) :
    c v = c w := by
  let x : V → ℝ := fun u => (if u = v then 1 else 0) - (if u = w then 1 else 0)
  have h0 : ∑ u, x u = 0 := by
    simp [x, Finset.sum_sub_distrib]
  have h1 := h x h0
  simp [x, mul_sub, Finset.sum_sub_distrib] at h1
  linarith

/-- In particular a scaling supported at one place `v₀`, by a factor `t ≠ 1`,
sends some family of total zero to one of nonzero total, as soon as there is a
second place. -/
theorem one_place_scaling_moves_total {V : Type*} [Fintype V] [DecidableEq V]
    {v₀ w : V} (hw : w ≠ v₀) {t : ℝ} (ht : t ≠ 1) :
    ∃ x : V → ℝ, ∑ v, x v = 0 ∧ ∑ v, (if v = v₀ then t else 1) * x v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have := scaling_keeping_total_zero_is_common (fun v => if v = v₀ then t else 1)
    hcon v₀ w
  simp [hw] at this
  exact ht this

/-- Conversely, one scalar common to all places keeps the families of total
zero. -/
theorem common_scaling_keeps_total_zero {V : Type*} [Fintype V] (k : ℝ)
    (x : V → ℝ) (hx : ∑ v, x v = 0) : ∑ v, k * x v = 0 := by
  rw [← Finset.mul_sum, hx, mul_zero]

/-- The value-group profile of the Θ-pilot at the label `j`, in units of the
log-volume `a` of the q-pilot. -/
def thetaProfile (a : ℝ) (j : ℕ) : ℝ := (j : ℝ) ^ 2 * a

/-- The value-group profile of the q-pilot: the same value at every label. -/
def qProfile (a : ℝ) (_j : ℕ) : ℝ := a

private theorem nat_eq_of_sq_eq {j₁ j₂ : ℕ} (h : (j₁ : ℝ) ^ 2 = (j₂ : ℝ) ^ 2) :
    j₁ = j₂ := by
  have h' : ((j₁ ^ 2 : ℕ) : ℝ) = ((j₂ ^ 2 : ℕ) : ℝ) := by
    push_cast
    exact h
  have h'' : j₁ ^ 2 = j₂ ^ 2 := by exact_mod_cast h'
  exact Nat.pow_left_injective (by norm_num) h''

/-- Reading (e), with Q0: one scalar acting on all labels alike does not carry
the profile of the q-pilot to that of the Θ-pilot, as soon as two distinct
labels are present and `a ≠ 0`. -/
theorem common_scalar_does_not_carry_q_to_theta {S : Finset ℕ} {j₁ j₂ : ℕ}
    (h₁ : j₁ ∈ S) (h₂ : j₂ ∈ S) (hne : j₁ ≠ j₂) {a : ℝ} (ha : a ≠ 0) (c : ℝ) :
    ¬ ∀ j ∈ S, c * qProfile a j = thetaProfile a j := by
  intro h
  have e1 := h j₁ h₁
  have e2 := h j₂ h₂
  simp only [qProfile, thetaProfile] at e1 e2
  have e3 : ((j₁ : ℝ) ^ 2 - (j₂ : ℝ) ^ 2) * a = 0 := by
    linear_combination e2 - e1
  rcases mul_eq_zero.1 e3 with h0 | h0
  · exact hne (nat_eq_of_sq_eq (by linarith))
  · exact ha h0

/-- Reading (e), with Q0, in the other direction: one scalar acting on all
labels alike does not carry the profile of the Θ-pilot to that of the
q-pilot either. -/
theorem common_scalar_does_not_carry_theta_to_q {S : Finset ℕ} {j₁ j₂ : ℕ}
    (h₁ : j₁ ∈ S) (h₂ : j₂ ∈ S) (hne : j₁ ≠ j₂) {a : ℝ} (ha : a ≠ 0) (c : ℝ) :
    ¬ ∀ j ∈ S, c * thetaProfile a j = qProfile a j := by
  intro h
  have e1 := h j₁ h₁
  have e2 := h j₂ h₂
  simp only [qProfile, thetaProfile] at e1 e2
  have hca : c * a ≠ 0 := by
    intro h0
    apply ha
    have : c * ((j₁ : ℝ) ^ 2 * a) = (j₁ : ℝ) ^ 2 * (c * a) := by ring
    rw [this, h0, mul_zero] at e1
    exact e1.symm
  have e3 : ((j₁ : ℝ) ^ 2 - (j₂ : ℝ) ^ 2) * (c * a) = 0 := by
    linear_combination e1 - e2
  rcases mul_eq_zero.1 e3 with h0 | h0
  · exact hne (nat_eq_of_sq_eq (by linarith))
  · exact hca h0

/-- Q2 and Q6: a transport that keeps the degree readout of every element does
not carry a pilot with the profile `{j^2 a}_j` to the profile `{a}_j`, as soon
as two distinct labels are present and `a ≠ 0`.  This is the case `c = 1` of
`common_scalar_does_not_carry_theta_to_q`. -/
theorem degree_preserving_transport_does_not_switch {X : Type*} (deg : X → ℝ)
    (T : X → X) (hT : ∀ x, deg (T x) = deg x) (pilot : ℕ → X) {a : ℝ}
    (ha : a ≠ 0) (hθ : ∀ j, deg (pilot j) = thetaProfile a j) {S : Finset ℕ}
    {j₁ j₂ : ℕ} (h₁ : j₁ ∈ S) (h₂ : j₂ ∈ S) (hne : j₁ ≠ j₂) :
    ¬ ∀ j ∈ S, deg (T (pilot j)) = qProfile a j := by
  intro h
  apply common_scalar_does_not_carry_theta_to_q h₁ h₂ hne ha 1
  intro j hj
  rw [one_mul, ← hθ j, ← hT (pilot j)]
  exact h j hj

/-- The hypotheses of the three statements above can be met: the labels `1`
and `2`, with `a = -1`. -/
theorem labels_witness : (1 : ℕ) ∈ ({1, 2} : Finset ℕ) ∧ (2 : ℕ) ∈ ({1, 2} : Finset ℕ) ∧
    (1 : ℕ) ≠ 2 ∧ (-1 : ℝ) ≠ 0 := by
  refine ⟨by simp, by simp, by norm_num, by norm_num⟩

end Scalars

/-! ## 4. The hypotheses are needed -/

section Needed

/-- Without `s > 0` the conclusion of `bounded_fails_linear` can fail. -/
theorem bounded_fails_linear_needs_positive_slope :
    ¬ ∀ (excess : ℕ → ℝ) (E s t : ℝ), (∀ N, excess N ≤ E) →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ¬ (s * N + t ≤ excess N) := by
  intro h
  obtain ⟨N₀, hN₀⟩ := h (fun _ => 0) 0 0 0 (fun _ => le_rfl)
  exact hN₀ N₀ le_rfl (by simp)

/-- Without the condition that every member lies in the container, the hull
of the family need not be the hull of the container. -/
theorem familyHull_needs_members_in_container :
    familyHull id ({∅, Set.univ} : Set (Set ℕ)) ≠ id (∅ : Set ℕ) := by
  intro h
  have h1 : (0 : ℕ) ∈ familyHull id ({∅, Set.univ} : Set (Set ℕ)) := by
    simp [familyHull]
  rw [h] at h1
  simp at h1

/-- With one label only, a common scalar does carry the profile of the
q-pilot to that of the Θ-pilot: two distinct labels are needed. -/
theorem one_label_profiles_agree (a : ℝ) :
    ∀ j ∈ ({1} : Finset ℕ), (1 : ℝ) * qProfile a j = thetaProfile a j := by
  intro j hj
  simp only [Finset.mem_singleton] at hj
  subst hj
  simp [qProfile, thetaProfile]

/-- With a single place, every scaling keeps the families of total zero, so a
second place is needed in `one_place_scaling_moves_total`. -/
theorem single_place_any_scaling_keeps_total_zero (t : ℝ) (x : Unit → ℝ)
    (hx : ∑ v, x v = 0) : ∑ v, t * x v = 0 :=
  common_scaling_keeps_total_zero t x hx

end Needed

end CentralQuestionReadings

#print axioms CentralQuestionReadings.familyHull_mono
#print axioms CentralQuestionReadings.familyHull_eq_hull_container
#print axioms CentralQuestionReadings.excess_le_of_subfamily
#print axioms CentralQuestionReadings.bounded_fails_linear
#print axioms CentralQuestionReadings.actual_family_fails_linear_requirement
#print axioms CentralQuestionReadings.actual_family_hypotheses_satisfiable
#print axioms CentralQuestionReadings.data_statement_holds_where_S_fails
#print axioms CentralQuestionReadings.data_statement_does_not_imply_S
#print axioms CentralQuestionReadings.scaling_keeping_total_zero_is_common
#print axioms CentralQuestionReadings.one_place_scaling_moves_total
#print axioms CentralQuestionReadings.common_scalar_does_not_carry_q_to_theta
#print axioms CentralQuestionReadings.common_scalar_does_not_carry_theta_to_q
#print axioms CentralQuestionReadings.degree_preserving_transport_does_not_switch
#print axioms CentralQuestionReadings.labels_witness
#print axioms CentralQuestionReadings.common_scaling_keeps_total_zero
#print axioms CentralQuestionReadings.bounded_fails_linear_needs_positive_slope
#print axioms CentralQuestionReadings.familyHull_needs_members_in_container
#print axioms CentralQuestionReadings.one_label_profiles_agree
#print axioms CentralQuestionReadings.single_place_any_scaling_keeps_total_zero
