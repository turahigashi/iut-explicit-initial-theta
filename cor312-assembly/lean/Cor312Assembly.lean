-- Cor. 3.12 assembly capstone: abstract transport/scaling core plus
-- the final assembly over the existing two-sentence capstone.
import M3.relative.ActualValuePartCompletenessFrame
import M3.relative.ActualValuePartHullIdentification

/-!
# Cor. 3.12 assembly: from place-wise data to the hull conclusion

This module is the Lean counterpart of the assembly layer of the
working draft [W] of the paper (Lemma 3.4 = discharge of hinge H1,
Lemma 13.2 = discharge of hinge H2, §22 supplement for
Prop. 3.9(ii)(iv)).  It proves, with no new axioms:

* **Zero-shift recalibration** (§22.1–22.3 core): log-volume
  differences are invariant under a common additive shift;
  place-wise correction constants commute with weighted sums
  (hence with packet weights and procession averages); corrected
  place-wise equality descends to global equality.
* **Uniform scaling** (§13 / (Ob4) core): comparison on the
  tensor-power side, where all degrees are multiplied by a
  common `M > 0`, preserves inequalities and ratios.
* **The monoanalytic correction constant** of [AbsTopIII]
  Prop. 5.8(iii), `c = -(f + m) log p + e f log p*`, and its
  vanishing in the unramified case and for `ℚ₂` (classical
  spot-checks, cf. [W] §22.1).
* **Capstones** `cor312_of_assembly` and
  `cor312_of_assembly_scaled`: given the volume decompositions
  of `μ T` and `vQ` as the *same* weighted sum of place-wise
  volumes, place-wise corrected equality, and membership of the
  θ region in the possible-image family, the
  Corollary-3.12-shaped conclusion `vQ ≤ μ (hull)` follows, via
  the existing `conclusion_of_two_realization_sentences`.
  `scale_eq_one_of_assembly` derives exact scale preservation
  `s = 1` from the same data.

## What remains as hypotheses (by design)

The capstone hypotheses are exactly the obligations left open
in the paper draft, stated as data, not axioms:

* `hvolTheta` / `hvolQ`: the global volumes really are the
  weighted sums of the place-wise volumes (transport / frame
  fidelity: this is where a faithful formalisation of the
  actual IUT construction must discharge its part).
* `hlocal`: corrected place-wise equality.  Within the model
  frame this is supplied at pilot-degree level by
  `ActualValuePartLocalCancellationTate.pilot_degree_thetaTateStrip_eq`;
  identifying that model pair with the actual construction is
  not done here.
* `hmem`: the output-side membership sentence.

No new axioms.  Not independently re-checked.
-/

noncomputable section
set_option autoImplicit false

namespace IUTFormal.M3.Cor312Assembly

open IUTFormal.M3.Theorem311.Remark395
open IUTFormal.M3.ActualValuePartCompletenessFrame
open IUTFormal.M3.ActualValuePartHullIdentification

variable {α ι : Type*}

/-! ## Zero-shift recalibration (H1 / §22 core) -/

/-- Log-volume *differences* are invariant under a common
additive shift of the zero-point.  This is the abstract content
of changing the reference integral structure: only differences
(and hence ratios of the underlying volumes) are intrinsic. -/
theorem volume_diff_invariant_under_shift {μ ν : α → ℝ} {c : ℝ}
    (h : ∀ x, ν x = μ x + c) (a b : α) :
    ν a - ν b = μ a - μ b := by
  rw [h a, h b]
  ring

/-- Subtracting the same correction constant on both sides does
not create or destroy equality: corrected equality is raw
equality, once the correction is genuinely common. -/
theorem corrected_eq_iff_raw_eq {x y c : ℝ} :
    x - c = y - c ↔ x = y :=
  ⟨fun h => by linarith, fun h => by rw [h]⟩

/-- Place-wise equality descends to any common weighted sum.
This covers packet weights (Remark 3.1.1(ii)) and the
procession average (constant weights) simultaneously. -/
theorem weighted_sum_eq_of_pointwise (s : Finset ι) (w x y : ι → ℝ)
    (h : ∀ i ∈ s, x i = y i) :
    (∑ i ∈ s, w i * x i) = ∑ i ∈ s, w i * y i :=
  Finset.sum_congr rfl fun i hi => by rw [h i hi]

/-- Place-wise correction constants commute with weighted sums:
correcting before summing equals correcting after, with the
explicit total correction `∑ wᵢ cᵢ`. -/
theorem weighted_sum_sub_correction (s : Finset ι) (w x c : ι → ℝ) :
    (∑ i ∈ s, w i * (x i - c i))
      = (∑ i ∈ s, w i * x i) - ∑ i ∈ s, w i * c i := by
  have hfun : (fun i => w i * (x i - c i))
      = fun i => w i * x i - w i * c i :=
    funext fun i => by ring
  rw [hfun, Finset.sum_sub_distrib]

/-! ## Uniform scaling (H2 / (Ob4) core) -/

/-- Comparison on the tensor-power side: multiplying both
sides by a common `M > 0` (the effect of the naive Frobenius
functor on degrees, [FrdI] Prop. 2.1(ii)) preserves the
inequality, so the tensor-power twist never enters the
numerical comparison. -/
theorem le_iff_mul_le_mul_of_pos {M a b : ℝ} (hM : 0 < M) :
    a ≤ b ↔ M * a ≤ M * b :=
  ⟨fun h => mul_le_mul_of_nonneg_left h hM.le,
    fun h => le_of_mul_le_mul_left h hM⟩

/-- Ratios are unchanged by a common nonzero scaling. -/
theorem ratio_invariant_under_scaling {M a b : ℝ} (hM : M ≠ 0) :
    (M * a) / (M * b) = a / b := mul_div_mul_left a b hM

/-! ## The monoanalytic correction constant ([AbsTopIII] 5.8(iii)) -/

/-- The correction constant of [W] §22.1: for a local
field of absolute ramification index `e`, residue degree `f`,
with `p^m` the number of `p`-power roots of unity and
`p* = p` (odd `p`) or `p²` (`p = 2`), the log-volume of the
monoanalytic integral structure in the local-regular
normalisation is `-(f + m) log p + e f log p*`. -/
def monoCorrection (e f m : ℕ) (p pstar : ℝ) : ℝ :=
  -((f : ℝ) + m) * Real.log p + e * f * Real.log pstar

/-- Unramified case (`e = 1`, `m = 0`, `p* = p`): the
correction vanishes, matching `ℐ_k = 𝒪_k`. -/
theorem monoCorrection_unramified (f : ℕ) (p : ℝ) :
    monoCorrection 1 f 0 p p = 0 := by
  unfold monoCorrection
  push_cast
  ring

/-- `ℚ₂` case (`e = f = 1`, `m = 1`, `p* = 4`): the correction
vanishes, matching `log (ℤ₂ˣ) = 4ℤ₂`, `ℐ = ℤ₂`. -/
theorem monoCorrection_Q2 : monoCorrection 1 1 1 2 4 = 0 := by
  have h : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  unfold monoCorrection
  rw [h]
  push_cast
  ring

/-! ## Capstones -/

/-- ★ Capstone.  Suppose the θ-volume and the q-volume are the
*same* weighted sum of place-wise volumes (`hvolTheta`,
`hvolQ`: the transport output of Lemma 3.4), the corrected
place-wise volumes agree (`hlocal`: local cancellation after
the §22 correction), and the θ region belongs to the
possible-image family (`hmem`: the output sentence).  Then the
Corollary-3.12-shaped conclusion against the hull follows.

This is exactly `conclusion_of_two_realization_sentences` with
its input sentence `s = 1` *derived* from place-wise data
instead of assumed. -/
theorem cor312_of_assembly (Ω : HullOperator α)
    {Fam : Set (Set α)} {T : Set α} {μ : Set α → ℝ} {vQ : ℝ}
    (places : Finset ι) (w thetaV qV : ι → ℝ)
    (hμ : Monotone μ) (hunion : Ω.isDomain (⋃₀ Fam))
    (hmem : T ∈ Fam)
    (hvolTheta : μ T = ∑ i ∈ places, w i * thetaV i)
    (hvolQ : vQ = ∑ i ∈ places, w i * qV i)
    (hlocal : ∀ i ∈ places, qV i = thetaV i) :
    vQ ≤ μ (Ω.φ (⋃₀ Fam)) := by
  have hsum : (∑ i ∈ places, w i * qV i)
      = ∑ i ∈ places, w i * thetaV i :=
    weighted_sum_eq_of_pointwise places w qV thetaV hlocal
  have hrel : vQ = 1 * μ T := by
    rw [hvolQ, hsum, ← hvolTheta, one_mul]
  exact conclusion_of_two_realization_sentences Ω hμ hunion hmem
    hrel rfl

/-- ★ Capstone, tensor-power variant.  The volume
decompositions are only known after the common tensor power
`M > 0` (the (Ob3)/(Ob4) comparison side).  The conclusion is
unchanged: the common factor cancels before the hull
comparison. -/
theorem cor312_of_assembly_scaled (Ω : HullOperator α)
    {Fam : Set (Set α)} {T : Set α} {μ : Set α → ℝ} {vQ M : ℝ}
    (places : Finset ι) (w thetaV qV : ι → ℝ)
    (hμ : Monotone μ) (hunion : Ω.isDomain (⋃₀ Fam))
    (hmem : T ∈ Fam) (hM : 0 < M)
    (hvolTheta : M * μ T = ∑ i ∈ places, w i * thetaV i)
    (hvolQ : M * vQ = ∑ i ∈ places, w i * qV i)
    (hlocal : ∀ i ∈ places, qV i = thetaV i) :
    vQ ≤ μ (Ω.φ (⋃₀ Fam)) := by
  have hsum : (∑ i ∈ places, w i * qV i)
      = ∑ i ∈ places, w i * thetaV i :=
    weighted_sum_eq_of_pointwise places w qV thetaV hlocal
  have heq : vQ = μ T := by
    have hMeq : M * vQ = M * μ T := by rw [hvolQ, hsum, ← hvolTheta]
    exact mul_left_cancel₀ (ne_of_gt hM) hMeq
  have hrel : vQ = 1 * μ T := by rw [heq, one_mul]
  exact conclusion_of_two_realization_sentences Ω hμ hunion hmem
    hrel rfl

/-- Exact scale preservation from assembly data: if the
q-volume is related to the θ-volume by *some* scale `s`, and
the place-wise assembly data hold, then `s = 1` — equivalently
(by `scale_defect_eq_zero_iff_scale_eq_one`) the scale defect
`Δ = (s - 1) * vol θ` vanishes. -/
theorem scale_eq_one_of_assembly
    {s vQ vTheta : ℝ} (places : Finset ι) (w thetaV qV : ι → ℝ)
    (hvolTheta : vTheta = ∑ i ∈ places, w i * thetaV i)
    (hvolQ : vQ = ∑ i ∈ places, w i * qV i)
    (hlocal : ∀ i ∈ places, qV i = thetaV i)
    (hrel : vQ = s * vTheta) (hne : vTheta ≠ 0) : s = 1 := by
  have hsum : (∑ i ∈ places, w i * qV i)
      = ∑ i ∈ places, w i * thetaV i :=
    weighted_sum_eq_of_pointwise places w qV thetaV hlocal
  have heq : vQ = vTheta := by rw [hvolQ, hsum, ← hvolTheta]
  have hdef : (s - 1) * vTheta = 0 := by
    have : s * vTheta = 1 * vTheta := by rw [← hrel, heq]; ring
    have h' : (s - 1) * vTheta = s * vTheta - 1 * vTheta := by ring
    rw [h', this, sub_self]
  exact (scale_defect_eq_zero_iff_scale_eq_one hne).mp hdef

end IUTFormal.M3.Cor312Assembly

end

#print axioms
  IUTFormal.M3.Cor312Assembly.volume_diff_invariant_under_shift
#print axioms
  IUTFormal.M3.Cor312Assembly.weighted_sum_sub_correction
#print axioms
  IUTFormal.M3.Cor312Assembly.monoCorrection_unramified
#print axioms IUTFormal.M3.Cor312Assembly.monoCorrection_Q2
#print axioms IUTFormal.M3.Cor312Assembly.cor312_of_assembly
#print axioms
  IUTFormal.M3.Cor312Assembly.cor312_of_assembly_scaled
#print axioms
  IUTFormal.M3.Cor312Assembly.scale_eq_one_of_assembly

