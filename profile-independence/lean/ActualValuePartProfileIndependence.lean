-- Profile independence countermodel for
-- the Cor. 3.12 assembly capstone.
-- Import is deliberately light: the independence statement below
-- replicates the hypothesis shape of
-- `IUTFormal.M3.Cor312Assembly.cor312_of_assembly`
-- (M3/relative/Cor312Assembly.lean) minus `hlocal`, over the
-- same `HullOperator` type; it does not need the assembly module.
import M3.theorem311.Remark395HullIsAClosure
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Profile independence: the assembly inputs minus the profile switch
do not imply the Corollary-3.12-shaped conclusion

This module exhibits one concrete profile-valued datum (at
`ℓ = 7`, labels `j ∈ {1, 2, 3}`, one bad place, normalized
`u = 1`) which satisfies every hypothesis of
`IUTFormal.M3.Cor312Assembly.cor312_of_assembly` **except**
label-wise `hlocal`, together with the extra supplied-layer
inputs of the assembly, and in which the conclusion
`vQ ≤ μ (hull)` is **false**.

Readouts are those read off the source:

* Θ-pilot label-`j` readout `-(j^2) * u`  (theta values
  `q̲^{j^2}`; IUT IV Thm. 1.10 proof (v), `λ = ord(q̲_{v_j}^{j^2})`),
* q-pilot readout `-1 * u`  (triangle label;
  `|log(q̲)| = (1/(2ℓ)) * log(q)`, IUT IV Thm. 1.10),
* procession weights equal, `w = 1/3` (IUT III Prop. 3.9(i),
  Remark 3.9.3: weighted averages are excluded).

Supplied layers that *hold* in the model:

* chart/generator layer: the normalized generator (`j = 1`)
  readouts agree, `thetaV 1 = qV 1` (the Tate pilot-degree
  cancellation input);
* unit layer: unit readouts are label-wise equal;
* membership: `T ∈ Fam` holds; monotonicity and hull domain hold
  (the degenerate identity hull `trivialHull`).

What fails, and only this: label-wise corrected equality
`hlocal` (`j = 2`: `-1 ≠ -4`), equivalently the aggregate scale
is forced to `s = 3/14 = 12/(ℓ(ℓ+1)) ≠ 1`.  Hence no derivation
of the capstone conclusion exists from the remaining inputs;
the profile part of H*val (preprint R2V), namely `hlocal`, is
logically independent of them; the membership part `hmem` holds
in the model.  This is an independence statement about
the listed assembly inputs, not a statement about the actual
IUT construction.

No new axioms.  Not independently re-checked.
-/

noncomputable section
set_option autoImplicit false

namespace IUTFormal.M3.ActualValuePartProfileIndependence

open IUTFormal.M3.Theorem311.Remark395
open Classical

/-! ## The ℓ = 7 profile datum (one bad place, `u = 1`) -/

/-- Labels `j ∈ {1, 2, 3} = {1, ..., ℓ^⋊}` for `ℓ = 7`. -/
def placesProf : Finset ℕ := {1, 2, 3}

/-- Procession equal weights (Prop. 3.9(i); Remark 3.9.3). -/
def wProf : ℕ → ℝ := fun _ => 1 / 3

/-- Θ-pilot label readouts `-(j^2) * u` with `u = 1`. -/
def thetaVProf : ℕ → ℝ := fun j => -((j : ℝ) ^ 2)

/-- q-pilot readouts `-1 * u` (constant profile). -/
def qVProf : ℕ → ℝ := fun _ => -1

/-- Unit-side readouts, identical on both sides by construction
(the supplied unit layer). -/
def unitThetaProf : ℕ → ℝ := fun _ => 0
def unitQProf : ℕ → ℝ := fun _ => 0

/-- The θ region: the singleton containing the aggregate
Θ readout. -/
def TProf : Set ℝ := {(-14 / 3 : ℝ)}

/-- The possible-image family: just the θ region, so membership
`hmem` holds in the model. -/
def FamProf : Set (Set ℝ) := {TProf}

/-- The aggregate q readout. -/
def vQProf : ℝ := -1

/-- A monotone volume readout with `μ TProf = -14/3`. -/
def muProf : Set ℝ → ℝ :=
  fun S => if (-14 / 3 : ℝ) ∈ S then -14 / 3 else -100

theorem muProf_mono : Monotone muProf := by
  intro a b hab
  unfold muProf
  by_cases ha : (-14 / 3 : ℝ) ∈ a
  · rw [if_pos ha, if_pos (hab ha)]
  · rw [if_neg ha]
    split_ifs <;> norm_num

theorem theta_sum :
    (∑ j ∈ placesProf, wProf j * thetaVProf j) = -14 / 3 := by
  norm_num [placesProf, wProf, thetaVProf,
    Finset.sum_insert, Finset.sum_singleton]

theorem q_sum :
    (∑ j ∈ placesProf, wProf j * qVProf j) = -1 := by
  norm_num [placesProf, wProf, qVProf,
    Finset.sum_insert, Finset.sum_singleton]

theorem muProf_TProf : muProf TProf = -14 / 3 := by
  unfold muProf TProf
  rw [if_pos (Set.mem_singleton_iff.mpr rfl)]

/-! ## The countermodel bundle -/

/-- ★ The profile countermodel: every capstone hypothesis
except label-wise `hlocal` holds, the supplied chart/generator
and unit layers hold, the aggregate scale is `3/14`, and the
Corollary-3.12-shaped conclusion is false. -/
theorem profile_countermodel :
    Monotone muProf ∧
    trivialHull.isDomain (⋃₀ FamProf) ∧
    TProf ∈ FamProf ∧
    muProf TProf
      = ∑ j ∈ placesProf, wProf j * thetaVProf j ∧
    vQProf = ∑ j ∈ placesProf, wProf j * qVProf j ∧
    thetaVProf 1 = qVProf 1 ∧
    (∀ j, unitThetaProf j = unitQProf j) ∧
    vQProf = (3 / 14) * muProf TProf ∧
    ¬ (∀ j ∈ placesProf, qVProf j = thetaVProf j) ∧
    ¬ (vQProf ≤ muProf (trivialHull.φ (⋃₀ FamProf))) := by
  refine ⟨muProf_mono, trivial, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [muProf_TProf, theta_sum]
  · rw [show vQProf = (-1 : ℝ) from rfl, q_sum]
  · norm_num [thetaVProf, qVProf]
  · intro j
    rfl
  · rw [muProf_TProf]
    norm_num [vQProf]
  · intro h
    have h2 := h 2 (by simp [placesProf])
    norm_num [qVProf, thetaVProf] at h2
  · have hU : ⋃₀ FamProf = TProf := Set.sUnion_singleton TProf
    rw [hU]
    show ¬ (vQProf ≤ muProf TProf)
    rw [muProf_TProf]
    norm_num [vQProf]

/-- The aggregate scale of the model is forced to be
`3/14 = 12/(ℓ(ℓ+1))` at `ℓ = 7`, in particular `≠ 1`:
the certified profile readout is incompatible with exact
scale preservation. -/
theorem aggregate_scale_eq {s : ℝ}
    (hs : vQProf = s * muProf TProf) : s = 3 / 14 := by
  rw [muProf_TProf] at hs
  have h : (-1 : ℝ) = s * (-14 / 3) := hs
  linarith

theorem aggregate_scale_ne_one {s : ℝ}
    (hs : vQProf = s * muProf TProf) : s ≠ 1 := by
  rw [aggregate_scale_eq hs]
  norm_num

/-! ## Independence corollary -/

/-- ★ No derivation of the capstone conclusion exists from
the hypotheses of `cor312_of_assembly` with label-wise
`hlocal` removed — even though membership, the volume
decompositions with the certified profile readout, generator
cancellation and unit compatibility can all hold
simultaneously (`profile_countermodel`).  The profile part of
H*val (`hlocal`; the membership part `hmem` holds in the model)
is therefore independent of the remaining assembly inputs. -/
theorem no_cor312_derivation_without_hlocal :
    ¬ ∀ (Ω : HullOperator ℝ) (Fam : Set (Set ℝ)) (T : Set ℝ)
        (μ : Set ℝ → ℝ) (vQ : ℝ)
        (places : Finset ℕ) (w thetaV qV : ℕ → ℝ),
        Monotone μ → Ω.isDomain (⋃₀ Fam) → T ∈ Fam →
        μ T = ∑ i ∈ places, w i * thetaV i →
        vQ = ∑ i ∈ places, w i * qV i →
        vQ ≤ μ (Ω.φ (⋃₀ Fam)) := by
  intro h
  obtain ⟨hμ, hdom, hmem, hvθ, hvq, -, -, -, -, hcon⟩ :=
    profile_countermodel
  exact hcon (h trivialHull FamProf TProf muProf vQProf
    placesProf wProf thetaVProf qVProf hμ hdom hmem hvθ hvq)

end IUTFormal.M3.ActualValuePartProfileIndependence

end

#print axioms
  IUTFormal.M3.ActualValuePartProfileIndependence.profile_countermodel
#print axioms
  IUTFormal.M3.ActualValuePartProfileIndependence.aggregate_scale_ne_one
#print axioms
  IUTFormal.M3.ActualValuePartProfileIndependence.no_cor312_derivation_without_hlocal
