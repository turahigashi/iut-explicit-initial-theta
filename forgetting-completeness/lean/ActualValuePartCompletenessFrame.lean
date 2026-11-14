-- IUT-STATEMENT: NON-IUT abstract-interpretation completeness frame, instantiated on value-part classes
import M3.relative.ActualValuePartThetaClass

/-!
# The forgetting / completeness frame, as Lean scaffolding

Companion Lean file to the note *Forgetting and completeness*.
This file formalizes only the abstract logic of the frame and
instantiates it on existing value-part assets.  It contains no new
arithmetic.

## The frame

An interface is a forgetful map `α : X → A`.  It is *complete*
for a query `Q : X → Y` if `Q` factors through `α`
(`CompleteFor`).  Three formal facts carry the whole discussion:

1. `CompleteFor.fiber` / `CompleteFor.of_fiber`: completeness is
   constancy of `Q` on fibers of `α` (the countermodel criterion:
   incompleteness = two states with equal abstract image and
   different query values).
2. `complete_on_normalized`: if `Q` factors through the pair
   `(α, c)` (abstract data plus a tracked invariant `c`, the
   scale), and `c` is constant on the relevant states (scale
   normalized), then `Q` is already determined by `α` there.
   This is the abstract shape of the scale-restoration step
   (paper Prop. 26; calibration packages).
3. `not_completeFor_sub` with `completeFor_sub_eq_zero_labelled`:
   the dependency problem in miniature.  Componentwise (product)
   abstraction forgets the correlation between two uses of the
   same datum, so the end-to-end query `a - b` is not determined
   even though each component abstraction is exact for its local
   range query; carrying the shared label (equality of the two
   copies) restores exactness.  This is *not* a model of IUT; it
   is the shared logical skeleton: local exactness at every
   interface is compatible with end-to-end incompleteness for a
   cross-interface correlation query, and label-tracking is the
   cure.

## Instantiation on value-part assets

`completeFor_thetaRootClass_readout` and
`completeFor_thetaValueClass_readout`: the value-part quotient
interface (forgetting = quotient by integral units, angular part)
is complete for the readout queries `‖t‖` and `‖t‖^(j*j)`,
with completing map the spectral readout.  These are restatements
of `valueReadout_thetaRootClass` / `valueReadout_thetaValueClass`
in frame language; the content is that the quotient interface was
chosen so that the radial query factors through it, while the
scale across copies (`linkScale`) is precisely the invariant
that must additionally be tracked, as in item 2:
`calibrated_pilot_degree_eq` (in `ActualValuePartLocalGlobal`)
is the Prop-26 instance, and its hypothesis (calibration) is
the outstanding supply.

## [H] Non-claims

* The frame classifies the logic of the Thm 3.11 → Cor. 3.12
  wall; it proves nothing about the construction, supplies no
  calibration, and does not touch hull families or Cor. 3.12.
* The toy in item 3 is an abstract finite/interval skeleton.
  Identification of IUT interfaces with the toy's components is
  a matter of interpretation, not a theorem here.
  Not independently re-checked.
-/

noncomputable section
set_option autoImplicit false

namespace IUTFormal.M3.ActualValuePartCompletenessFrame

open IUTFormal.Theorem311
open IUTFormal.Theorem311.NumberFieldRealDivisor
open IUTFormal.Theorem311.NumberFieldRealLocalization
open IUTFormal.IUT1.Corollary37
open IUTFormal.IUT2.Definition49viii
open IUTFormal.IUT3.Theorem311
open IUTFormal.M3.ActualStrictBelyiFieldReconstruction
open IUTFormal.M3.ActualValuePartQuotient
open IUTFormal.M3.ActualValuePartLocalGlobal
open IUTFormal.M3.ActualValuePartRealification
open IUTFormal.M3.ActualValuePartThetaClass
open IUTFormal.M3.ActualFinitePlaceArithmeticCurve
open Dispute.Prop310FinitePrimeFiberPacket
open IUTFormal.ThetaLink.SourceArithmeticThetaKummer
open IUTFormal.ThetaLink.GaussianMonoidFromThetaValues

section Frame

variable {X A C Y : Type*}

/-- An abstraction `α` is complete for a query `Q` when `Q`
factors through `α`: the abstract data determines the answer. -/
def CompleteFor (α : X → A) (Q : X → Y) : Prop :=
  ∃ Qhat : A → Y, Q = Qhat ∘ α

/-- Completeness implies constancy on fibers: abstractly
indistinguishable states give the same answer.  Incompleteness is
therefore always witnessed by a pair of states with equal
abstract image and different answers (the countermodel shape). -/
theorem CompleteFor.fiber {α : X → A} {Q : X → Y}
    (h : CompleteFor α Q) {x₁ x₂ : X} (hx : α x₁ = α x₂) :
    Q x₁ = Q x₂ := by
  obtain ⟨Qhat, rfl⟩ := h
  exact congrArg Qhat hx

/-- Constancy on fibers also gives completeness (choice of a
representative per fiber). -/
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

/-- ★ Scale restoration, abstract Prop-26 shape: if the query
factors through abstract data together with a tracked invariant
`c` (the scale), and `c` is constant on the relevant states
(scale normalized to `c₀`), then on those states the query is
already determined by the abstract data alone. -/
theorem complete_on_normalized {α : X → A} {c : X → C} {Q : X → Y}
    {P : X → Prop} {c₀ : C}
    (hQ : CompleteFor (fun x => (α x, c x)) Q)
    (hc : ∀ x, P x → c x = c₀) :
    ∀ x₁ x₂ : X, P x₁ → P x₂ → α x₁ = α x₂ → Q x₁ = Q x₂ := by
  intro x₁ x₂ h₁ h₂ hx
  apply hQ.fiber
  exact Prod.ext hx (by rw [hc x₁ h₁, hc x₂ h₂])

/-- The interval summary of an integer known only to lie in
`[0, 1]`: componentwise range abstraction. -/
def intervalAbs : ℤ → Set ℤ := fun _ => Set.Icc 0 1

/-- The dependency problem in miniature: the product abstraction
(componentwise intervals) is incomplete for the end-to-end query
`a - b`, even on runs where the two components are the same
datum.  The two states `(0, 0)` and `(0, 1)` are abstractly
indistinguishable with different answers. -/
theorem not_completeFor_sub :
    ¬ CompleteFor
      (fun p : ℤ × ℤ => (intervalAbs p.1, intervalAbs p.2))
      (fun p : ℤ × ℤ => p.1 - p.2) := by
  intro h
  have h01 := h.fiber (x₁ := (0, 0)) (x₂ := (0, 1)) rfl
  norm_num at h01

/-- Carrying the shared label (equality of the two copies — the
affine-arithmetic noise symbol, the shared marking/history)
restores exactness for the zero-query. -/
theorem completeFor_sub_eq_zero_labelled :
    CompleteFor
      (fun p : ℤ × ℤ =>
        (intervalAbs p.1, intervalAbs p.2, decide (p.1 = p.2)))
      (fun p : ℤ × ℤ => decide (p.1 - p.2 = 0)) := by
  refine ⟨fun a => a.2.2, ?_⟩
  funext p
  simp only [Function.comp_apply, sub_eq_zero]

/-- Sign abstraction, preserving case: the sign of a product is
determined by the signs of the factors.  The forgetful map
`Int.sign` is complete for the multiplicative sign query. -/
theorem completeFor_sign_mul :
    CompleteFor (fun p : ℤ × ℤ => (Int.sign p.1, Int.sign p.2))
      (fun p : ℤ × ℤ => Int.sign (p.1 * p.2)) := by
  refine ⟨fun q => q.1 * q.2, ?_⟩
  funext p
  simp only [Function.comp_apply]
  rw [Int.sign_mul]

/-- Sign abstraction, breaking case: the sign of a sum is not
determined by the signs of the summands.  The states `(1, -1)`
and `(2, -1)` have the same abstract image and different
answers.  One and the same forgetful map is complete for one
query and incomplete for another: completeness is a relation
between an abstraction and a query, not a property of the
abstraction alone. -/
theorem not_completeFor_sign_add :
    ¬ CompleteFor (fun p : ℤ × ℤ => (Int.sign p.1, Int.sign p.2))
      (fun p : ℤ × ℤ => Int.sign (p.1 + p.2)) := by
  intro h
  have h01 := h.fiber (x₁ := (1, -1)) (x₂ := (2, -1)) (by decide)
  norm_num [Int.sign] at h01

/-- From a scaled conclusion and a scale bound, the unscaled
conclusion follows.  This is the hull-bound parameterisation:
`s` multiplies a nonnegative hull bound, so the favourable
one-sided condition is `s ≤ 1`.  It is *not* the same parameter
as the degree scale of the published paper, whose log-volumes
are negative; the defect formulation below is the
convention-independent core. -/
theorem conclusion_of_scaled_and_scale_le_one {qvol hvol s : ℝ}
    (hscaled : qvol ≤ s * hvol) (hs : s ≤ 1) (h0 : 0 ≤ hvol) :
    qvol ≤ hvol :=
  le_trans hscaled (by
    have h := mul_le_mul_of_nonneg_right hs h0
    simpa using h)

/-- Sharpness on extremal data: when the two sides of the scaled
conclusion coincide at scale `1` (no slack), the conclusion holds
if and only if the scale is at most `1`.  Hence, uniformly over a
class of data closed under extremal examples, a scale bound is
not merely sufficient but necessary; pointwise, with slack, the
conclusion can hold for other reasons and no equivalence is
claimed. -/
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

/-! ## The reduction theorem in defect form

Write the signed log-volume relation as in the published paper,
`vol q = s * vol θ`, and put `Δ = (s - 1) * vol θ` (the scale
defect).  Then the desired inequality against the hull `H` is
controlled solely by `Δ` and the slack `vol H - vol θ`: no sign
convention for a one-sided bound on `s` is built into these
statements.  Exact preservation is `Δ = 0`, i.e. `s = 1` when
`vol θ ≠ 0`. -/

/-- Nonpositive defect is sufficient: if `θ` itself lies below
the hull bound and the scaling does not push the value upward,
then `q` lies below the hull bound. -/
theorem conclusion_of_nonpositive_scale_defect
    {vTheta vQ vH s : ℝ}
    (hrel : vQ = s * vTheta) (hθH : vTheta ≤ vH)
    (hΔ : (s - 1) * vTheta ≤ 0) : vQ ≤ vH := by
  have hvq : vQ = vTheta + (s - 1) * vTheta := by rw [hrel]; ring
  rw [hvq]
  linarith

/-- The conclusion is equivalent to the defect being covered by
the slack between the hull and `θ`.  With no slack
(`vH = vTheta`), it is equivalent to `Δ ≤ 0`; with slack, it can
hold for other reasons, so no unconditional equivalence between
the conclusion and preservation is claimed. -/
theorem conclusion_iff_defect_le_slack
    {vTheta vQ vH s : ℝ}
    (hrel : vQ = s * vTheta) :
    vQ ≤ vH ↔ (s - 1) * vTheta ≤ vH - vTheta := by
  have hvq : vQ = vTheta + (s - 1) * vTheta := by rw [hrel]; ring
  rw [hvq]
  constructor <;> intro h <;> linarith

/-- Exact scale preservation, in defect form: for nonzero
`vol θ`, the defect vanishes if and only if `s = 1`. -/
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

/-- Sign translation for the published convention, where the
relevant log-volumes are negative: nonpositivity of the defect
is the one-sided condition `1 ≤ s` there (the countermodel scale
is `3/14 < 1`).  Under the nonnegative hull-bound
parameterisation above the favourable side reads `s ≤ 1`
instead; the invariant content shared by both is `Δ ≤ 0`, and
preservation proper is `Δ = 0`. -/
theorem nonpositive_defect_iff_one_le_of_neg
    {s vTheta : ℝ} (hv : vTheta < 0) :
    (s - 1) * vTheta ≤ 0 ↔ 1 ≤ s := by
  constructor
  · intro h
    by_contra hnot
    push_neg at hnot
    have hpos : 0 < (s - 1) * vTheta :=
      mul_pos_of_neg_of_neg (by linarith) hv
    linarith
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hv.le

end Frame

section Instantiate

variable (E : ArithmeticCurve.{0})

/-- ★ The value-part quotient interface is complete for the root
readout query: the norm of a bounded local unit factors through
its theta root class, via the spectral readout. -/
theorem completeFor_thetaRootClass_readout :
    CompleteFor
      (fun t : {t : E.Kˣ // ‖(t : E.K)‖ ≤ 1} =>
        thetaRootClass E t.1 t.2)
      (fun t : {t : E.Kˣ // ‖(t : E.K)‖ ≤ 1} => ‖(t.1 : E.K)‖) := by
  refine ⟨fun v => valueReadout E v, ?_⟩
  funext t
  exact (valueReadout_thetaRootClass E t.1 t.2).symm

/-- ★ The value-part quotient interface is complete for every
label readout query, via the same spectral readout. -/
theorem completeFor_thetaValueClass_readout (j : ℕ) :
    CompleteFor
      (fun t : {t : E.Kˣ // ‖(t : E.K)‖ ≤ 1} =>
        thetaValueClass E t.1 t.2 j)
      (fun t : {t : E.Kˣ // ‖(t : E.K)‖ ≤ 1} =>
        ‖(t.1 : E.K)‖ ^ (j * j)) := by
  refine ⟨fun v => valueReadout E v, ?_⟩
  funext t
  exact (valueReadout_thetaValueClass E t.1 t.2 j).symm

end Instantiate

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
#print axioms completeFor_thetaRootClass_readout
#print axioms completeFor_thetaValueClass_readout

end IUTFormal.M3.ActualValuePartCompletenessFrame
