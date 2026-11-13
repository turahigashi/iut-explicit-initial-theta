-- Lean check of the relations drawn for the region B in Figure 1 of
-- "A conditional assembly from Theorem 3.11 to Corollary 3.12" (v1.0.2).
--
-- Frame: the hypotheses of `Kouchiku.M3.Cor312Assembly.cor312_of_assembly`,
-- replicated here in the same shape (as in
-- `ActualValuePartProfileIndependence`), together with the chart/generator
-- layer (Proposition A, `s_chart = 1`) and the unit layer (Lemma 8.2).
-- B = the inputs of Theorem 9.1 other than H*val.  Since the published texts
-- name the Lean counterpart of H*val as `hmem`, as `hlocal`, or (in the proof
-- of Theorem 9.1) use it for both, every statement below is proved for each
-- of the three readings.
--
-- This is a statement about the abstract assembly frame, not about the actual
-- IUT construction.  Not standalone: it imports two modules of the author's
-- larger Lean development (the hull operator and the profile countermodel).
-- Compiled with Lean 4.30.0 against Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f;
-- the axioms printed at the end are propext, Classical.choice, Quot.sound.
import M3.theorem311.Remark395HullIsAClosure
import M3.relative.ActualValuePartProfileIndependence

noncomputable section
set_option autoImplicit false

namespace VennRegionB

open Kouchiku.M3.Theorem311.Remark395
open Kouchiku.M3.ActualValuePartProfileIndependence
open Classical

/-- One "structure" of the figure, at the level of the assembly capstone. -/
structure Str (α : Type) where
  Ω : HullOperator α
  Fam : Set (Set α)
  T : Set α
  μ : Set α → ℝ
  vQ : ℝ
  places : Finset ℕ
  w : ℕ → ℝ
  thetaV : ℕ → ℝ
  qV : ℕ → ℝ
  uTheta : ℕ → ℝ
  uQ : ℕ → ℝ

variable {α : Type}

/-- Frame inputs of Theorem 9.1 (monotone volume, hull domain, and the two
volume decompositions = transport output). -/
def Frame (x : Str α) : Prop :=
  Monotone x.μ ∧ x.Ω.isDomain (⋃₀ x.Fam) ∧
  x.μ x.T = ∑ i ∈ x.places, x.w i * x.thetaV i ∧
  x.vQ = ∑ i ∈ x.places, x.w i * x.qV i

/-- Chart / generator layer, Proposition A: `s_chart = 1`
(the normalized generator `j = 1` reads the same on both sides). -/
def Chart (x : Str α) : Prop := 1 ∈ x.places ∧ x.thetaV 1 = x.qV 1

/-- Unit layer, Lemma 8.2. -/
def Unit (x : Str α) : Prop := ∀ j, x.uTheta j = x.uQ j

/-- `hmem`: the θ region is a possible image. -/
def Mem (x : Str α) : Prop := x.T ∈ x.Fam

/-- `hlocal`: label-wise equality of the value-group profiles. -/
def Prof (x : Str α) : Prop := ∀ j ∈ x.places, x.qV j = x.thetaV j

/-- `K`: the Corollary-3.12-shaped conclusion. -/
def K (x : Str α) : Prop := x.vQ ≤ x.μ (x.Ω.φ (⋃₀ x.Fam))

/-- `(9-1)` in the reading of [U26], Definition (fourth item), without the
nonzero-measure clause: some possible image has the volume of the q-pilot. -/
def N91 (x : Str α) : Prop := ∃ X ∈ x.Fam, x.μ X = x.vQ

/-- The three readings of H*val found in the published texts:
`prof` = `hlocal` (profile-independence paper), `mem` = `hmem`
(Table in §1 of the assembly paper), `both` = both
(the proof of Theorem 9.1 uses H*val for membership and for the profile). -/
inductive Reading | prof | mem | both

/-- H*val under a reading. -/
def Hval : Reading → Str α → Prop
  | .prof, x => Prof x
  | .mem,  x => Mem x
  | .both, x => Mem x ∧ Prof x

/-- `B`: the inputs of Theorem 9.1 other than H*val. -/
def B : Reading → Str α → Prop
  | .prof, x => Frame x ∧ Chart x ∧ Unit x ∧ Mem x
  | .mem,  x => Frame x ∧ Chart x ∧ Unit x ∧ Prof x
  | .both, x => Frame x ∧ Chart x ∧ Unit x

/-! ## Relations (c), (d) of the caption, for every reading -/

/-- (c) `s_chart = 1` throughout `B`. -/
theorem chart_of_B (r : Reading) (x : Str α) (h : B r x) : Chart x := by
  cases r <;> exact h.2.1

/-- `B` together with H*val gives back all the hypotheses of the capstone. -/
theorem capstone_inputs_of_B (r : Reading) (x : Str α) (hB : B r x)
    (hH : Hval r x) : Frame x ∧ Mem x ∧ Prof x := by
  cases r
  · exact ⟨hB.1, hB.2.2.2, hH⟩
  · exact ⟨hB.1, hH, hB.2.2.2⟩
  · exact ⟨hB.1, hH.1, hH.2⟩

/-- The capstone `cor312_of_assembly`, re-proved in the same shape. -/
theorem K_of_capstone (x : Str α) (hF : Frame x) (hM : Mem x) (hP : Prof x) :
    K x := by
  obtain ⟨hμ, hdom, hθ, hq⟩ := hF
  have hsum : (∑ i ∈ x.places, x.w i * x.qV i)
      = ∑ i ∈ x.places, x.w i * x.thetaV i :=
    Finset.sum_congr rfl fun i hi => by rw [hP i hi]
  have hv : x.vQ = x.μ x.T := by rw [hq, hsum, ← hθ]
  have hsub : x.T ⊆ x.Ω.φ (⋃₀ x.Fam) :=
    (Set.subset_sUnion_of_mem hM).trans (x.Ω.P2 hdom)
  unfold K
  rw [hv]
  exact hμ hsub

/-- (d) `B ∩ H*val ⊆ K` (Theorem 9.1). -/
theorem K_of_B_Hval (r : Reading) (x : Str α) (hB : B r x) (hH : Hval r x) :
    K x := by
  obtain ⟨hF, hM, hP⟩ := capstone_inputs_of_B r x hB hH
  exact K_of_capstone x hF hM hP

/-- (d) `B ∩ H*val ⊆ (9-1)` (§10). -/
theorem N91_of_B_Hval (r : Reading) (x : Str α) (hB : B r x) (hH : Hval r x) :
    N91 x := by
  obtain ⟨⟨_, _, hθ, hq⟩, hM, hP⟩ := capstone_inputs_of_B r x hB hH
  have hsum : (∑ i ∈ x.places, x.w i * x.qV i)
      = ∑ i ∈ x.places, x.w i * x.thetaV i :=
    Finset.sum_congr rfl fun i hi => by rw [hP i hi]
  exact ⟨x.T, hM, by rw [hq, hsum, ← hθ]⟩

/-- (b) of [U26], checked in this frame: `(9-1) ⊆ K` wherever the volume is
monotone and the union is a hull domain (in particular on `B`). -/
theorem K_of_N91 (x : Str α) (hμ : Monotone x.μ)
    (hdom : x.Ω.isDomain (⋃₀ x.Fam)) (h : N91 x) : K x := by
  obtain ⟨X, hX, hvol⟩ := h
  unfold K
  rw [← hvol]
  exact hμ ((Set.subset_sUnion_of_mem hX).trans (x.Ω.P2 hdom))

/-! ## The drawing: `B` crosses the wall (both sides are inhabited) -/

/-- The published profile countermodel, as a structure. -/
def profStr : Str ℝ where
  Ω := trivialHull
  Fam := FamProf
  T := TProf
  μ := muProf
  vQ := vQProf
  places := placesProf
  w := wProf
  thetaV := thetaVProf
  qV := qVProf
  uTheta := unitThetaProf
  uQ := unitQProf

/-- A monotone volume readout: `-1` on sets containing `0`, else `-100`. -/
def muInd : Set ℝ → ℝ := fun S => if (0 : ℝ) ∈ S then -1 else -100

theorem muInd_of_mem {S : Set ℝ} (h : (0 : ℝ) ∈ S) : muInd S = -1 := by
  unfold muInd; rw [if_pos h]

theorem muInd_of_not_mem {S : Set ℝ} (h : (0 : ℝ) ∉ S) : muInd S = -100 := by
  unfold muInd; rw [if_neg h]

theorem mono_indicator : Monotone muInd := by
  intro a b hab
  by_cases ha : (0 : ℝ) ∈ a
  · rw [muInd_of_mem ha, muInd_of_mem (hab ha)]
  · rw [muInd_of_not_mem ha]
    by_cases hb : (0 : ℝ) ∈ b
    · rw [muInd_of_mem hb]; norm_num
    · rw [muInd_of_not_mem hb]

/-- A structure with profiles equal but the θ region outside the family. -/
def memFailStr : Str ℝ where
  Ω := trivialHull
  Fam := {∅}
  T := {0}
  μ := muInd
  vQ := -1
  places := {1}
  w := fun _ => 1
  thetaV := fun _ => -1
  qV := fun _ => -1
  uTheta := fun _ => 0
  uQ := fun _ => 0

/-- A structure satisfying every input, H*val included. -/
def goodStr : Str ℝ where
  Ω := trivialHull
  Fam := {{0}}
  T := {0}
  μ := muInd
  vQ := -1
  places := {1}
  w := fun _ => 1
  thetaV := fun _ => -1
  qV := fun _ => -1
  uTheta := fun _ => 0
  uQ := fun _ => 0

theorem profStr_frame : Frame profStr := by
  obtain ⟨hμ, hdom, _, hθ, hq, -⟩ := profile_countermodel
  exact ⟨hμ, hdom, hθ, hq⟩

theorem profStr_chart : Chart profStr := by
  obtain ⟨-, -, -, -, -, h1, -⟩ := profile_countermodel
  exact ⟨by simp [profStr, placesProf], h1⟩

theorem profStr_unit : Unit profStr := by
  obtain ⟨-, -, -, -, -, -, hu, -⟩ := profile_countermodel
  exact hu

theorem profStr_mem : Mem profStr := by
  obtain ⟨-, -, hm, -⟩ := profile_countermodel
  exact hm

theorem profStr_not_K : ¬ K profStr := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hc⟩ := profile_countermodel
  exact hc

theorem memFailStr_B : B .mem memFailStr := by
  refine ⟨⟨mono_indicator, trivial, ?_, ?_⟩, ⟨by simp [memFailStr], rfl⟩,
    fun _ => rfl, ?_⟩
  · show muInd {0} = ∑ i ∈ ({1} : Finset ℕ), (fun _ => (1:ℝ)) i * (fun _ => (-1:ℝ)) i
    rw [muInd_of_mem (Set.mem_singleton 0)]; simp
  · show (-1 : ℝ) = ∑ i ∈ ({1} : Finset ℕ), (fun _ => (1:ℝ)) i * (fun _ => (-1:ℝ)) i
    simp
  · intro j _; rfl

theorem memFailStr_not_K : ¬ K memFailStr := by
  show ¬ ((-1 : ℝ) ≤ muInd (id (⋃₀ ({∅} : Set (Set ℝ)))))
  rw [Set.sUnion_singleton, id, muInd_of_not_mem (Set.notMem_empty 0)]
  norm_num

theorem goodStr_B (r : Reading) : B r goodStr ∧ Hval r goodStr := by
  have hF : Frame goodStr := by
    refine ⟨mono_indicator, trivial, ?_, ?_⟩
    · show muInd {0} = ∑ i ∈ ({1} : Finset ℕ), (fun _ => (1:ℝ)) i * (fun _ => (-1:ℝ)) i
      rw [muInd_of_mem (Set.mem_singleton 0)]; simp
    · show (-1 : ℝ) = ∑ i ∈ ({1} : Finset ℕ), (fun _ => (1:ℝ)) i * (fun _ => (-1:ℝ)) i
      simp
  have hC : Chart goodStr := ⟨by simp [goodStr], rfl⟩
  have hU : Unit goodStr := fun _ => rfl
  have hM : Mem goodStr := by simp [goodStr, Mem]
  have hP : Prof goodStr := fun _ _ => rfl
  cases r
  · exact ⟨⟨hF, hC, hU, hM⟩, hP⟩
  · exact ⟨⟨hF, hC, hU, hP⟩, hM⟩
  · exact ⟨⟨hF, hC, hU⟩, hM, hP⟩

/-- ★ For every reading of H*val: `B` meets `K` (inside the wall, together
with H*val) and is not contained in `K` (outside the wall).  So drawing `B`
across the wall is accurate in this frame, and "`B ⊆ K` is not claimed" is
the right wording (it is in fact false in the frame). -/
theorem B_crosses_wall (r : Reading) :
    (∃ x : Str ℝ, B r x ∧ Hval r x ∧ K x) ∧ (∃ x : Str ℝ, B r x ∧ ¬ K x) := by
  refine ⟨⟨goodStr, (goodStr_B r).1, (goodStr_B r).2,
    K_of_B_Hval r _ (goodStr_B r).1 (goodStr_B r).2⟩, ?_⟩
  cases r
  · exact ⟨profStr, ⟨profStr_frame, profStr_chart, profStr_unit, profStr_mem⟩,
      profStr_not_K⟩
  · exact ⟨memFailStr, memFailStr_B, memFailStr_not_K⟩
  · exact ⟨profStr, ⟨profStr_frame, profStr_chart, profStr_unit⟩, profStr_not_K⟩

/-- `B ⊆ K` fails for every reading. -/
theorem not_B_subset_K (r : Reading) : ¬ ∀ x : Str ℝ, B r x → K x := by
  intro h
  obtain ⟨x, hB, hK⟩ := (B_crosses_wall r).2
  exact hK (h x hB)

end VennRegionB

end

#print axioms VennRegionB.chart_of_B
#print axioms VennRegionB.K_of_B_Hval
#print axioms VennRegionB.N91_of_B_Hval
#print axioms VennRegionB.K_of_N91
#print axioms VennRegionB.B_crosses_wall
#print axioms VennRegionB.not_B_subset_K
