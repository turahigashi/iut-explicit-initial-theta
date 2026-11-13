-- Formal implication checks for the question note ronbun9810.
import M3.relative.ActualValuePartProfileIndependence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Formal cores behind the implication claims in the question note

This file does **not** formalize [EtTh], mono-theta environments,
global synchronization, Statement P', bridge (a), bridge (b), or
any IUT construction.  It checks only the finite and formal
implications used when auditing the logical relations in the
question note:

* two splittings of one group surjection agree after passage to
  the quotient, and their pointwise difference lies in the
  kernel (with the usual cocycle identity);
* a permutation-invariant normalized linear readout is the mean;
* the mean-square profile formula and the common-ratio global
  total (no cancellation when the same ratio occurs at every
  place);
* object membership plus equality of readouts gives the volume
  inequality (the abstract (α) -> (β) step);
* a bare numerical equality for an otherwise unconstrained
  transported readout does not supply that inequality in the
  profile countermodel;
* total degree alone does not determine a label profile.

The countermodel itself is imported from
`ActualValuePartProfileIndependence`.
-/

noncomputable section
set_option autoImplicit false

namespace Kouchiku.M3.ActualValuePartQuestionImplications

open Kouchiku.M3.Theorem311.Remark395
open Kouchiku.M3.ActualValuePartProfileIndependence
open Classical

/-! ## Splittings of one surjection -/

section Splittings

variable {E Q : Type*} [Group E] [Group Q]
variable {p : E →* Q} {s t : Q →* E}

/-- The pointwise difference of two splittings. -/
def sectionDiff (s t : Q →* E) (q : Q) : E :=
  t q * (s q)⁻¹

theorem section_apply (hs : p.comp s = MonoidHom.id Q) (q : Q) :
    p (s q) = q := by
  have h := DFunLike.congr_fun hs q
  simpa using h

theorem sectionDiff_mem_ker
    (hs : p.comp s = MonoidHom.id Q)
    (ht : p.comp t = MonoidHom.id Q) (q : Q) :
    sectionDiff s t q ∈ p.ker := by
  rw [MonoidHom.mem_ker]
  unfold sectionDiff
  rw [map_mul, map_inv, section_apply hs, section_apply ht,
    mul_inv_cancel]

theorem quotient_readout_eq
    (hs : p.comp s = MonoidHom.id Q)
    (ht : p.comp t = MonoidHom.id Q)
    {α : Type*} (F : Q → α) (q : Q) :
    F (p (s q)) = F (p (t q)) := by
  rw [section_apply hs, section_apply ht]

theorem sectionDiff_mul (q r : Q) :
    sectionDiff s t (q * r)
      = sectionDiff s t q
        * (s q * sectionDiff s t r * (s q)⁻¹) := by
  unfold sectionDiff
  simp [map_mul, mul_assoc]

end Splittings

/-! ## Permutation-invariant linear readouts are means -/

theorem weights_apply_eq_of_perm_invariant {ι : Type*}
    (w : ι → ℝ)
    (hinv : ∀ σ : Equiv.Perm ι, w ∘ σ = w) (i j : ι) :
    w i = w j := by
  by_cases h : i = j
  · subst h
    rfl
  · have hfun := congrFun (hinv (Equiv.swap i j)) i
    simp [Function.comp_apply, Equiv.swap_apply_left] at hfun
    exact hfun.symm

theorem weighted_readout_eq_average {ι : Type*} [Fintype ι]
    [Nonempty ι] {w x : ι → ℝ}
    (hinv : ∀ σ : Equiv.Perm ι, w ∘ σ = w)
    (hnorm : ∑ i, w i * (1 : ℝ) = 1) :
    ∑ i, w i * x i
      = (∑ i, x i) / (Fintype.card ι : ℝ) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hall : ∀ i, w i = w i₀ :=
    fun i => weights_apply_eq_of_perm_invariant w hinv i i₀
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have hsumw : ∑ i, w i = 1 := by
    simpa using hnorm
  have hsum_const : ∑ i, w i = (Fintype.card ι : ℝ) * w i₀ := by
    rw [Finset.sum_congr rfl (fun i _ => hall i)]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : w i₀ = 1 / (Fintype.card ι : ℝ) := by
    rw [hsum_const] at hsumw
    field_simp
    linarith
  calc
    ∑ i, w i * x i
        = ∑ i, w i₀ * x i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hall i]
    _ = w i₀ * ∑ i, x i := by
          rw [Finset.mul_sum]
    _ = (∑ i, x i) / (Fintype.card ι : ℝ) := by
          rw [hc]
          field_simp

/-! ## Mean-square profile and common-ratio totals -/

theorem sum_range_succ_sq (n : ℕ) :
    ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℚ)) ^ 2
      = (n : ℚ) * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring

theorem mean_sq_range {n : ℕ} (hn : n ≠ 0) :
    (∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℚ)) ^ 2) / (n : ℚ)
      = ((n : ℚ) + 1) * (2 * (n : ℚ) + 1) / 6 := by
  rw [sum_range_succ_sq]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  field_simp

theorem weighted_total_scaling {ι : Type*} (S : Finset ι)
    (w q theta : ι → ℝ) (r : ℝ)
    (h : ∀ i ∈ S, theta i = r * q i) :
    ∑ i ∈ S, w i * theta i
      = r * ∑ i ∈ S, w i * q i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i hi]
  ring

theorem weighted_total_ne_of_scaling {ι : Type*} (S : Finset ι)
    (w q theta : ι → ℝ) (r : ℝ)
    (h : ∀ i ∈ S, theta i = r * q i)
    (hq : ∑ i ∈ S, w i * q i ≠ 0) (hr : r ≠ 1) :
    ∑ i ∈ S, w i * theta i ≠ ∑ i ∈ S, w i * q i := by
  intro heq
  have hscale := weighted_total_scaling S w q theta r h
  have hratio : r * (∑ i ∈ S, w i * q i)
      = ∑ i ∈ S, w i * q i := hscale.symm.trans heq
  have hzero : (r - 1) * (∑ i ∈ S, w i * q i) = 0 := by
    rw [sub_mul, hratio, one_mul, sub_self]
  rcases mul_eq_zero.mp hzero with hr' | hq'
  · exact hr (by linarith)
  · exact hq hq'

/-! ## Membership plus readout equality gives the volume bound -/

theorem volume_le_of_membership_of_eq {α : Type*}
    (Ω : HullOperator α) {μ : Set α → ℝ} (hμ : Monotone μ)
    {Fam : Set (Set α)} {T : Set α} {vQ : ℝ}
    (hdom : Ω.isDomain (⋃₀ Fam))
    (hmem : T ∈ Fam)
    (hrel : vQ = μ T) :
    vQ ≤ μ (Ω.φ (⋃₀ Fam)) := by
  have hsub : T ⊆ Ω.φ (⋃₀ Fam) :=
    (Set.subset_sUnion_of_mem hmem).trans (Ω.P2 hdom)
  calc
    vQ = μ T := hrel
    _ ≤ μ (Ω.φ (⋃₀ Fam)) := hμ hsub

/-! ## A bare transported numerical equality has no force by itself -/

/-- An unconstrained transported number in the profile model. -/
def transportedQProf : ℝ := -1

theorem no_derivation_from_transported_equality_alone :
    ¬ ∀ (Ω : HullOperator ℝ) (Fam : Set (Set ℝ)) (T : Set ℝ)
      (μ : Set ℝ → ℝ) (vQ transported : ℝ)
      (places : Finset ℕ) (w thetaV qV : ℕ → ℝ),
      Monotone μ →
      Ω.isDomain (⋃₀ Fam) →
      T ∈ Fam →
      μ (Ω.φ (⋃₀ Fam)) = ∑ j ∈ places, w j * thetaV j →
      vQ = ∑ j ∈ places, w j * qV j →
      transported = vQ →
      vQ ≤ μ (Ω.φ (⋃₀ Fam)) := by
  intro h
  obtain ⟨hμ, hdom, hmem, htheta, hq, -, -, -, -, hcon⟩ :=
    profile_countermodel
  have htheta' :
      muProf (trivialHull.φ (⋃₀ FamProf))
        = ∑ j ∈ placesProf, wProf j * thetaVProf j := by
    have hU : ⋃₀ FamProf = TProf := Set.sUnion_singleton TProf
    rw [hU]
    show muProf TProf
      = ∑ j ∈ placesProf, wProf j * thetaVProf j
    exact htheta
  exact hcon
    (h trivialHull FamProf TProf muProf vQProf transportedQProf
      placesProf wProf thetaVProf qVProf
      hμ hdom hmem htheta' hq rfl)

/-- A different label profile with the same weighted total. -/
def altThetaVProf : ℕ → ℝ := fun j =>
  if j = 1 then -2 else if j = 2 then -3 else thetaVProf j

theorem same_weighted_total_of_distinct_profile :
    (∑ j ∈ placesProf, wProf j * altThetaVProf j
      = ∑ j ∈ placesProf, wProf j * thetaVProf j)
    ∧ altThetaVProf ≠ thetaVProf := by
  constructor
  · norm_num [placesProf, wProf, thetaVProf, altThetaVProf,
      Finset.sum_insert, Finset.sum_singleton]
  · intro h
    have h1 := congrFun h 1
    norm_num [thetaVProf, altThetaVProf] at h1

#print axioms sectionDiff_mem_ker
#print axioms quotient_readout_eq
#print axioms sectionDiff_mul
#print axioms weights_apply_eq_of_perm_invariant
#print axioms weighted_readout_eq_average
#print axioms sum_range_succ_sq
#print axioms mean_sq_range
#print axioms weighted_total_scaling
#print axioms weighted_total_ne_of_scaling
#print axioms volume_le_of_membership_of_eq
#print axioms no_derivation_from_transported_equality_alone
#print axioms same_weighted_total_of_distinct_profile

end Kouchiku.M3.ActualValuePartQuestionImplications

