import LogShellEdge.FreeGroupMoves
import LogShellEdge.Even

/-!
# From Lemma 4.1 to the maps in `Γ` (Proposition 4.4)

`RealizesOdd Γ y` (resp. `RealizesEven Γ y`) is the conclusion of Lemma 4.1 (with Theorem 3.1 and the
definition of `α₊` in Section 2.2): every automorphism `ψ` of the free group on `z_1, …, z_d` that fixes
`z_1` and the boundary word is realized in `Γ` by the linear map whose matrix in the basis `y` is the
abelianization of `ψ`. The group-theoretic core of Lemma 4.1 is `lemma41_descends`.

From this one input, together with the free-group automorphisms of `LogShellEdge.FG` (Lemmas 4.2, 4.3),
we derive every map that the structures of Sections 5, 6 and 8 put into `Γ`:
* `oddMoves_of_realizes`: the fields `moveU`, `moveV`, `swap` of `OddSmall` (Proposition 4.4(b));
* `evenMoves_of_realizes`: the fields `moveT`, `moveU` of `EvenSmall` (Proposition 4.4(a));
* `cycloM_of_realizes` (in `RealizeCyclo`): the map `M` used in Lemma 8.8 (`CycloData.moveM`), from the
  mixing word `M` of Lemma 4.3, written in the basis `z, y_2, …` of Lemma 8.6.
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge

variable {p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]

/-- the linear combination of the basis with integer coefficients `c` -/
def combo {n : ℕ} (y : Module.Basis (Fin n) ℚ_[p] V) (c : Fin n → ℤ) : V :=
  ∑ j, ((c j : ℤ) : ℚ_[p]) • y j

theorem combo_add {n : ℕ} (y : Module.Basis (Fin n) ℚ_[p] V) (c c' : Fin n → ℤ) :
    combo y (c + c') = combo y c + combo y c' := by
  simp only [combo, Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]

theorem combo_single {n : ℕ} (y : Module.Basis (Fin n) ℚ_[p] V) (i : Fin n) :
    combo y (Pi.single i 1) = y i := by
  simp only [combo]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem combo_zero {n : ℕ} (y : Module.Basis (Fin n) ℚ_[p] V) : combo y 0 = 0 := by
  simp [combo]

theorem combo_smul {n : ℕ} (y : Module.Basis (Fin n) ℚ_[p] V) (a : ℤ) (c : Fin n → ℤ) :
    combo y (a • c) = ((a : ℤ) : ℚ_[p]) • combo y c := by
  simp only [combo, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.smul_sum, smul_smul]

/-- Lemma 4.1 (odd degree), as an input: realization by the abelianization. -/
def RealizesOdd {g : ℕ} (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (y : Module.Basis (Fin (2 * g + 1)) ℚ_[p] V) :
    Prop :=
  ∀ ψ : FreeGroup (Fin (2 * g + 1)) ≃* FreeGroup (Fin (2 * g + 1)),
    ψ (FreeGroup.of ⟨0, by omega⟩) = FreeGroup.of ⟨0, by omega⟩ → ψ (FG.oddBoundary g) = FG.oddBoundary g →
    ∃ γ ∈ Γ, ∀ i, γ (y i) = combo y (FG.vecN (ψ (FreeGroup.of i)))

/-- Lemma 4.1 (even degree), as an input. -/
def RealizesEven {g : ℕ} (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (y : Module.Basis (Fin (2 * g)) ℚ_[p] V)
    (hg : 1 ≤ g) : Prop :=
  ∀ ψ : FreeGroup (Fin (2 * g)) ≃* FreeGroup (Fin (2 * g)),
    ψ (FreeGroup.of ⟨0, by omega⟩) = FreeGroup.of ⟨0, by omega⟩ → ψ (FG.evenBoundary g) = FG.evenBoundary g →
    ∃ γ ∈ Γ, ∀ i, γ (y i) = combo y (FG.vecN (ψ (FreeGroup.of i)))

/-- the two descriptions of the swap of adjacent pairs agree -/
theorem swapIdx_eq {g : ℕ} (k : ℕ) (hk : k + 1 < g) (i : Fin (2 * g + 1)) :
    FG.swapIdx (2 * k + 1) (by omega) i = swapIdx k hk i := by
  apply Fin.ext
  rw [FG.swapIdx_val']
  simp only [swapIdx]
  split_ifs <;> simp_all <;> omega

/-- Proposition 4.4(b) from Lemma 4.1: the fields `moveU`, `moveV`, `swap` of `OddSmall`. -/
theorem oddMoves_of_realizes {g : ℕ} (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V))
    (y : Module.Basis (Fin (2 * g + 1)) ℚ_[p] V) (hR : RealizesOdd Γ y) :
    (∀ k : Fin g, ∃ γ ∈ Γ, ∀ i, γ (y i) = if i = uIdx k then y (uIdx k) + y (vIdx k) else y i) ∧
    (∀ k : Fin g, ∃ γ ∈ Γ, ∀ i, γ (y i) = if i = vIdx k then y (vIdx k) + y (uIdx k) else y i) ∧
    (∀ (k : ℕ) (hk : k + 1 < g), ∃ γ ∈ Γ, ∀ i, γ (y i) = y (swapIdx k hk i)) := by
  refine ⟨fun k => ?_, fun k => ?_, fun k hk => ?_⟩
  · obtain ⟨γ, hγ, h⟩ := hR (FG.oddPairU g k) (FG.oddPairU_fix0 g k) (FG.oddPairU_boundary g k)
    refine ⟨γ, hγ, fun i => ?_⟩
    rw [h i, FG.oddPairU_vec, combo_add, combo_single]
    by_cases hi : i = uIdx k
    · subst hi
      rw [if_pos (by simp [uIdx]), if_pos rfl, combo_single]; rfl
    · rw [if_neg (fun h => hi (Fin.ext (by simp [uIdx, h]))), if_neg hi, combo_zero, add_zero]
  · obtain ⟨γ, hγ, h⟩ := hR (FG.oddPairV g k) (FG.oddPairV_fix0 g k) (FG.oddPairV_boundary g k)
    refine ⟨γ, hγ, fun i => ?_⟩
    rw [h i, FG.oddPairV_vec, combo_add, combo_single]
    by_cases hi : i = vIdx k
    · subst hi
      rw [if_pos (by simp [vIdx]), if_pos rfl, combo_single]; rfl
    · rw [if_neg (fun h => hi (Fin.ext (by simp [vIdx, h]))), if_neg hi, combo_zero, add_zero]
  · obtain ⟨γ, hγ, h⟩ := hR (FG.oddSwap g k hk) (FG.oddSwap_fix0 g k hk) (FG.oddSwap_boundary g k hk)
    refine ⟨γ, hγ, fun i => ?_⟩
    rw [h i, FG.oddSwap_vec, combo_single, swapIdx_eq k hk i]

theorem formE_eq_formQ {g : ℕ} (i j : Fin (2 * g)) :
    FG.formE g (Pi.single i 1) (Pi.single j 1) = formQ i j := by
  rw [FG.formE_single_eq]; rfl

/-- Proposition 4.4(a) from Lemma 4.1: the fields `moveT`, `moveU` of `EvenSmall`. -/
theorem evenMoves_of_realizes {g : ℕ} (hg : 1 ≤ g) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V))
    (y : Module.Basis (Fin (2 * g)) ℚ_[p] V) (hR : RealizesEven Γ y hg) :
    (∃ γ ∈ Γ, ∀ i, γ (y i) = if i = ⟨1, by omega⟩ then y ⟨1, by omega⟩ + y ⟨0, by omega⟩ else y i) ∧
    (∀ j : Fin (2 * g), 2 ≤ j.val → ∃ γ ∈ Γ, ∀ i,
      γ (y i) = y i + ((formQ i ⟨0, by omega⟩ : ℤ) : ℚ_[p]) • y j +
        ((formQ i j : ℤ) : ℚ_[p]) • y ⟨0, by omega⟩) := by
  refine ⟨?_, fun j hj => ?_⟩
  · obtain ⟨γ, hγ, h⟩ := hR (FG.evenTa g hg) (FG.evenTa_fix0 g hg) (FG.evenTa_boundary g hg)
    refine ⟨γ, hγ, fun i => ?_⟩
    rw [h i, FG.evenTa_vec, combo_add, combo_single]
    by_cases hi : i = ⟨1, by omega⟩
    · subst hi; rw [if_pos rfl, if_pos rfl, combo_single]
    · rw [if_neg (fun h => hi (Fin.ext h)), if_neg hi, combo_zero, add_zero]
  · obtain ⟨γ, hγ, h⟩ := hR (FG.evenU g j hj) (FG.evenU_fix0 g j hj) (FG.evenU_boundary g j hj)
    refine ⟨γ, hγ, fun i => ?_⟩
    rw [h i, FG.evenU_vec, combo_add, combo_add, combo_single, combo_smul, combo_smul, combo_single,
      combo_single, formE_eq_formQ, formE_eq_formQ]

end LogShellEdge
