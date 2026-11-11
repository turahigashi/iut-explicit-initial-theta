import Mathlib

/-!
# The forgetting / completeness frame: standalone core

Standalone core of the frame used in

  T. Urahigashi, *Forgetting and completeness: the centre of the
  passage from Theorem 3.11 to Corollary 3.12 in inter-universal
  Teichmüller theory*, version 1.0.0 (2026).

This file depends only on Mathlib.  It contains:

* `CompleteFor`: an abstraction `α` is complete for a query `Q` if
  `Q` factors through `α` (Definition 3.1 of the paper);
* the fibre criterion (`CompleteFor.fiber`, `CompleteFor.of_fiber`);
* restoration by a tracked invariant (`complete_on_normalized`);
* the examples of §2: sign abstraction (complete for products,
  incomplete for sums) and the interval dependency problem with its
  labelled restoration;
* the scale-defect reduction theorem (Proposition 3.4):
  sufficiency of a nonpositive defect, equivalence with slack,
  preservation as vanishing defect, and the sign translation for
  negative log-volumes;
* the hull-bound parameterization lemmas used in the sign-convention
  table.

The instantiation of the frame on the value-part classes of the
sideways formalization (`completeFor_thetaRootClass_readout`,
`completeFor_thetaValueClass_readout`) is not part of this file; it
lives in the full development file
`ActualValuePartCompletenessFrame.lean`, reproduced next to this
file for reference.  Independent review has not been received.
-/

noncomputable section
set_option autoImplicit false

namespace CompletenessFrameCore

variable {X A C Y : Type*}

/-- An abstraction `α` is complete for a query `Q` when `Q`
factors through `α`: the abstract data determines the answer. -/
def CompleteFor (α : X → A) (Q : X → Y) : Prop :=
  ∃ Qhat : A → Y, Q = Qhat ∘ α

/-- Completeness implies constancy on fibres. -/
theorem CompleteFor.fiber {α : X → A} {Q : X → Y}
    (h : CompleteFor α Q) {x₁ x₂ : X} (hx : α x₁ = α x₂) :
    Q x₁ = Q x₂ := by
  obtain ⟨Qhat, rfl⟩ := h
  exact congrArg Qhat hx

/-- Constancy on fibres gives completeness. -/
theorem CompleteFor.of_fiber {α : X → A} {Q : X → Y} [Nonempty Y]
    (h : ∀ x₁ x₂ : X, α x₁ = α x₂ → Q x₁ = Q x₂) :
    CompleteFor α Q := by
  classical
  refine ⟨fun a => if h' : ∃ x, α x = a then Q h'.choose
    else Classical.arbitrary Y, ?_⟩
  funext x
  simp only [Function.comp_apply]
  rw [dif_pos ⟨x, rfl⟩]
  exact h x _ (Classical.choose_spec (⟨x, rfl⟩ : ∃ y, α y = α x)).symm

/-- Restoration by a tracked invariant: if the query factors
through abstract data together with a tracked invariant `c`, and
`c` is normalized to a constant `c₀` on the relevant states, then
on those states the query is already determined by the abstract
data alone. -/
theorem complete_on_normalized {α : X → A} {c : X → C} {Q : X → Y}
    {P : X → Prop} {c₀ : C}
    (hQ : CompleteFor (fun x => (α x, c x)) Q)
    (hc : ∀ x, P x → c x = c₀) :
    ∀ x₁ x₂ : X, P x₁ → P x₂ → α x₁ = α x₂ → Q x₁ = Q x₂ := by
  intro x₁ x₂ h₁ h₂ hx
  apply hQ.fiber
  exact Prod.ext hx (by rw [hc x₁ h₁, hc x₂ h₂])

/-- The interval summary of an integer known only to lie in
`[0, 1]`. -/
def intervalAbs : ℤ → Set ℤ := fun _ => Set.Icc 0 1

/-- The dependency problem in miniature: componentwise intervals
are incomplete for the end-to-end query `a - b`. -/
theorem not_completeFor_sub :
    ¬ CompleteFor
      (fun p : ℤ × ℤ => (intervalAbs p.1, intervalAbs p.2))
      (fun p : ℤ × ℤ => p.1 - p.2) := by
  intro h
  have h01 := h.fiber (x₁ := (0, 0)) (x₂ := (0, 1)) rfl
  norm_num at h01

/-- Carrying the shared label (equality of the two copies)
restores exactness for the zero-query. -/
theorem completeFor_sub_eq_zero_labelled :
    CompleteFor
      (fun p : ℤ × ℤ =>
        (intervalAbs p.1, intervalAbs p.2, decide (p.1 = p.2)))
      (fun p : ℤ × ℤ => decide (p.1 - p.2 = 0)) := by
  refine ⟨fun a => a.2.2, ?_⟩
  funext p
  simp only [Function.comp_apply, sub_eq_zero]

/-- Sign abstraction is complete for the multiplicative sign
query. -/
theorem completeFor_sign_mul :
    CompleteFor (fun p : ℤ × ℤ => (Int.sign p.1, Int.sign p.2))
      (fun p : ℤ × ℤ => Int.sign (p.1 * p.2)) := by
  refine ⟨fun q => q.1 * q.2, ?_⟩
  funext p
  simp only [Function.comp_apply]
  rw [Int.sign_mul]

/-- Sign abstraction is incomplete for the additive sign query:
`(1, -1)` and `(2, -1)` have the same abstract image and
different answers. -/
theorem not_completeFor_sign_add :
    ¬ CompleteFor (fun p : ℤ × ℤ => (Int.sign p.1, Int.sign p.2))
      (fun p : ℤ × ℤ => Int.sign (p.1 + p.2)) := by
  intro h
  have h01 := h.fiber (x₁ := (1, -1)) (x₂ := (2, -1)) (by decide)
  norm_num [Int.sign] at h01

/-- Hull-bound parameterization: from a scaled conclusion and
`s ≤ 1` against a nonnegative hull bound, the unscaled conclusion
follows. -/
theorem conclusion_of_scaled_and_scale_le_one {qvol hvol s : ℝ}
    (hscaled : qvol ≤ s * hvol) (hs : s ≤ 1) (h0 : 0 ≤ hvol) :
    qvol ≤ hvol :=
  le_trans hscaled (by
    have h := mul_le_mul_of_nonneg_right hs h0
    simpa using h)

/-- Sharpness on extremal (no-slack) data in the hull-bound
parameterization. -/
theorem scale_le_one_iff_of_extremal {s a b : ℝ} (ha : 0 < a)
    (hab : a = b) : s * a ≤ b ↔ s ≤ 1 := by
  subst hab
  constructor
  · intro h
    have h' : s * a ≤ 1 * a := by simpa using h
    exact le_of_mul_le_mul_right h' ha
  · intro h
    have h' := mul_le_mul_of_nonneg_right h ha.le
    simpa using h'

/-- Reduction theorem, sufficiency: a nonpositive scale defect
`Δ = (s - 1) * vol θ` gives the conclusion. -/
theorem conclusion_of_nonpositive_scale_defect
    {vTheta vQ vH s : ℝ}
    (hrel : vQ = s * vTheta) (hθH : vTheta ≤ vH)
    (hΔ : (s - 1) * vTheta ≤ 0) : vQ ≤ vH := by
  have hvq : vQ = vTheta + (s - 1) * vTheta := by rw [hrel]; ring
  rw [hvq]
  linarith

/-- Reduction theorem, equivalence with slack: the conclusion
holds if and only if the defect is covered by the slack
`vol H - vol θ`. -/
theorem conclusion_iff_defect_le_slack
    {vTheta vQ vH s : ℝ}
    (hrel : vQ = s * vTheta) :
    vQ ≤ vH ↔ (s - 1) * vTheta ≤ vH - vTheta := by
  have hvq : vQ = vTheta + (s - 1) * vTheta := by rw [hrel]; ring
  rw [hvq]
  constructor <;> intro h <;> linarith

/-- Preservation itself: for nonzero `vol θ`, the defect vanishes
if and only if `s = 1`. -/
theorem scale_defect_eq_zero_iff_scale_eq_one
    {s vTheta : ℝ} (hv : vTheta ≠ 0) :
    (s - 1) * vTheta = 0 ↔ s = 1 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · exact absurd h hv
  · intro h
    rw [h]
    simp

/-- Sign translation for negative log-volumes: nonpositivity of
the defect is the one-sided condition `1 ≤ s`. -/
theorem nonpositive_defect_iff_one_le_of_neg
    {s vTheta : ℝ} (hv : vTheta < 0) :
    (s - 1) * vTheta ≤ 0 ↔ 1 ≤ s := by
  constructor
  · intro h
    by_contra hnot
    have hlt : s < 1 := lt_of_not_ge hnot
    have hpos : 0 < (s - 1) * vTheta :=
      mul_pos_of_neg_of_neg (by linarith) hv
    linarith
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hv.le

#print axioms CompleteFor.fiber
#print axioms CompleteFor.of_fiber
#print axioms complete_on_normalized
#print axioms not_completeFor_sub
#print axioms completeFor_sub_eq_zero_labelled
#print axioms completeFor_sign_mul
#print axioms not_completeFor_sign_add
#print axioms conclusion_of_scaled_and_scale_le_one
#print axioms scale_le_one_iff_of_extremal
#print axioms conclusion_of_nonpositive_scale_defect
#print axioms conclusion_iff_defect_le_slack
#print axioms scale_defect_eq_zero_iff_scale_eq_one
#print axioms nonpositive_defect_iff_one_le_of_neg

end CompletenessFrameCore
