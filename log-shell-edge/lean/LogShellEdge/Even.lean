import LogShellEdge.OddMain
import LogShellEdge.Reuse.ShearLattice

/-!
# Even degree (Section 5.1 of the note)

Indices are 0-based: `a = y 0`, `b = y 1` (the paper's `y_1, y_2`), pairs `(y (2k), y (2k+1))`.
The alternating form is `⟨e_{2k}, e_{2k+1}⟩ = -1`, `⟨e_{2k+1}, e_{2k}⟩ = 1` (Section 4.3).

* `EvenSmall`: a small field of even degree with Kondo's description of `ker Tr` and the maps
  `T_a` and `U_{y_j}` (`j ≥ 2`) of Proposition 4.4(a).
* `lemma52`: if `Tr(x)` generates `p ℤ_p` then the images of `x` span `Λ` (Lemma 5.2). The linear
  algebra is the reused lemma `SourceShearLattice.span_orbit_eq`.
* `thm51_even`: Theorem 5.1(a).
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge

open LogShellEdge.ShearLattice

variable {p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]

/-- the alternating form on the indices `Fin (2g)` (pairs `(2k, 2k+1)`) -/
def formQ {n : ℕ} (i j : Fin n) : ℤ :=
  if i.val % 2 = 0 ∧ j.val = i.val + 1 then -1
  else if i.val % 2 = 1 ∧ i.val = j.val + 1 then 1 else 0

theorem norm_formQ_le {n : ℕ} (i j : Fin n) : ‖((formQ i j : ℤ) : ℚ_[p])‖ ≤ 1 :=
  Padic.norm_int_le_one _

/-- A small field of even degree `d = 2g` with the inputs of Sections 3-5. -/
structure EvenSmall (p : ℕ) [Fact p.Prime] (V : Type*) [AddCommGroup V] [Module ℚ_[p] V]
    [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V] (g : ℕ)
    extends SmallField p V (Fin (2 * g)) where
  hg : 1 ≤ g
  /-- [Kondo, Theorem 1.3] (even degree): `ker Tr = ⟨y_1, y_3, …, y_d⟩` -/
  hker : ∀ i : Fin (2 * g), i.val ≠ 1 → τ (y i) = 0
  /-- Lemma 3.4: `Tr(y_2)` generates `p ℤ_p` -/
  hτ1 : ‖τ (y ⟨1, by omega⟩)‖ = 1
  /-- Proposition 4.4(a): `T_a`, from `x_2 ↦ x_2 x_1` -/
  moveT : ∃ γ ∈ Γ, ∀ i, γ (y i) = if i = ⟨1, by omega⟩ then y ⟨1, by omega⟩ + y ⟨0, by omega⟩ else y i
  /-- Proposition 4.4(a): `U_w(x) = x + ⟨x,a⟩ w + ⟨x,w⟩ a` for `w = y_j`, `j ≥ 2` (Lemma 4.3) -/
  moveU : ∀ j : Fin (2 * g), 2 ≤ j.val → ∃ γ ∈ Γ, ∀ i,
    γ (y i) = y i + ((formQ i ⟨0, by omega⟩ : ℤ) : ℚ_[p]) • y j + ((formQ i j : ℤ) : ℚ_[p]) • y ⟨0, by omega⟩

namespace EvenSmall

variable {g : ℕ} (K : EvenSmall p V g)

/-- index `0` -/
def i0 : Fin (2 * g) := ⟨0, by have := K.hg; omega⟩
/-- index `1` -/
def i1 : Fin (2 * g) := ⟨1, by have := K.hg; omega⟩

theorem tau_eq (x : V) : K.τ x = K.y.repr x K.i1 * K.τ (K.y K.i1) := by
  conv_lhs => rw [← K.y.sum_repr x]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single K.i1]
  · intro i _ hi
    rw [K.hker i (fun h => hi (Fin.ext (by simp [i1, h]))), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem norm_tau_eq (x : V) : ‖K.τ x‖ = ‖K.y.repr x K.i1‖ := by
  rw [K.tau_eq, norm_mul]
  have : ‖K.τ (K.y K.i1)‖ = 1 := K.hτ1
  rw [this, mul_one]

/-- `U_{y_j}(x) = x + x_1 y_j + (∑ᵢ xᵢ ⟨eᵢ, e_j⟩) y_0`. -/
theorem apply_U (γ : V ≃ₗ[ℚ_[p]] V) (j : Fin (2 * g))
    (hγ : ∀ i, γ (K.y i) = K.y i + ((formQ i K.i0 : ℤ) : ℚ_[p]) • K.y j +
      ((formQ i j : ℤ) : ℚ_[p]) • K.y K.i0) (x : V) :
    γ x = x + K.y.repr x K.i1 • K.y j +
      (∑ i, K.y.repr x i * ((formQ i j : ℤ) : ℚ_[p])) • K.y K.i0 := by
  rw [show γ x = (γ : V →ₗ[ℚ_[p]] V) x from rfl, apply_eq_sum K.y (γ : V →ₗ[ℚ_[p]] V) x]
  have hsum : ∀ i, K.y.repr x i • (γ : V →ₗ[ℚ_[p]] V) (K.y i) =
      K.y.repr x i • K.y i + (K.y.repr x i * ((formQ i K.i0 : ℤ) : ℚ_[p])) • K.y j +
        (K.y.repr x i * ((formQ i j : ℤ) : ℚ_[p])) • K.y K.i0 := by
    intro i
    rw [show (γ : V →ₗ[ℚ_[p]] V) (K.y i) = γ (K.y i) from rfl, hγ i, smul_add, smul_add, smul_smul, smul_smul]
  rw [Finset.sum_congr rfl (fun i _ => hsum i), Finset.sum_add_distrib, Finset.sum_add_distrib,
    K.y.sum_repr, ← Finset.sum_smul, ← Finset.sum_smul]
  congr 2
  rw [Finset.sum_eq_single K.i1]
  · simp [formQ, i0, i1]
  · intro i _ hi
    have : formQ i K.i0 = 0 := by
      have hne : i.val ≠ 1 := fun h => hi (Fin.ext (by simp [i1, h]))
      unfold formQ
      have e0 : (K.i0).val = 0 := rfl
      rw [e0, if_neg (by omega), if_neg (by omega)]
    rw [this]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Lemma 5.2: if `x ∈ Λ` and `Tr(x)` generates `p ℤ_p`, then the images of `x` span `Λ`. -/
theorem lemma52 (x : V) (hx : x ∈ K.F.L 1) (hτ : ‖K.τ x‖ = 1) : K.F.L 1 ≤ spanImg K.Γ x := by
  set c := K.y.repr x with hc
  have hc1 : ‖c K.i1‖ = 1 := by rw [hc, ← K.norm_tau_eq]; exact hτ
  have hcle : ∀ i, ‖c i‖ ≤ 1 := fun i => K.toSmallField.coeff_le_one hx i
  set a := K.y K.i0
  set b := K.y K.i1
  set S : Set V := {z | ∃ j : Fin (2 * g), 2 ≤ j.val ∧ z = K.y j} with hS
  set α : ℤ_[p] := zp (c K.i0) (hcle _)
  set u : ℤ_[p] := zp (c K.i1) (hcle _)
  have hu : IsUnit u := PadicInt.isUnit_iff.mpr hc1
  set w₀ : V := x - α • a - u • b with hw₀
  have hw₀S : w₀ ∈ Submodule.span ℤ_[p] S := by
    have hrepr : ∀ i, K.y.repr w₀ i = if 2 ≤ i.val then c i else 0 := by
      intro i
      rw [hw₀, zp_smul, zp_smul]
      simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
        Module.Basis.repr_self, Finsupp.single_apply, a, b]
      by_cases h0 : i = K.i0
      · subst h0; simp [i0, i1, hc]
      · by_cases h1 : i = K.i1
        · subst h1; simp [i0, i1, hc]
        · have h2 : 2 ≤ i.val := by
            by_contra hlt
            have : i.val = 0 ∨ i.val = 1 := by omega
            rcases this with h | h
            · exact h0 (Fin.ext (by simp [i0, h]))
            · exact h1 (Fin.ext (by simp [i1, h]))
          rw [if_pos h2, if_neg (Ne.symm h0), if_neg (Ne.symm h1)]; simp [hc]
    rw [K.toSmallField.sum_repr w₀]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [hrepr i]
    split_ifs with h2
    · rw [← zp_smul _ (hcle i)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, h2, rfl⟩)
    · rw [zero_smul]; exact Submodule.zero_mem _
  -- the coefficient `⟨x, w⟩` for `w ∈ S`
  let ctr : V → ℚ_[p] := fun w =>
    ∑ i, c i * ∑ k, K.y.repr w k * ((formQ i k : ℤ) : ℚ_[p])
  have hctr_le : ∀ w ∈ S, ‖ctr w‖ ≤ 1 := by
    rintro w ⟨j, -, rfl⟩
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
    rw [norm_mul]
    refine mul_le_one₀ (hcle i) (norm_nonneg _) ?_
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun k _ => ?_)
    rw [norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) (norm_formQ_le i k)
    rw [Module.Basis.repr_self, Finsupp.single_apply]; split_ifs <;> simp
  let cfun : V → ℤ_[p] := fun w => if h : ‖ctr w‖ ≤ 1 then zp (ctr w) h else 0
  have hx_eq : x = α • a + u • b + w₀ := by rw [hw₀]; abel
  have key := span_orbit_eq a b S α u hu w₀ hw₀S cfun x hx_eq
  -- the left side lies in the span of the orbit
  have hle : Submodule.span ℤ_[p] (({x, x + u • a} : Set V) ∪ (fun w => x + u • w + cfun w • a) '' S) ≤
      spanImg K.Γ x := by
    refine Submodule.span_le.mpr ?_
    rintro z (hz | ⟨w, hwS, rfl⟩)
    · rcases hz with rfl | rfl
      · exact mem_spanImg_self _ _
      · obtain ⟨γ, hγ, hT⟩ := K.moveT
        have := apply_of_move K.y (γ : V →ₗ[ℚ_[p]] V) K.i1 K.i0 (fun i => hT i) x
        have e : x + u • a = γ x := by
          rw [show γ x = (γ : V →ₗ[ℚ_[p]] V) x from rfl, this, zp_smul]
        rw [e]; exact mem_spanImg_of_mem _ _ hγ
    · obtain ⟨j, hj, rfl⟩ := hwS
      obtain ⟨γ, hγ, hU⟩ := K.moveU j hj
      have happ := K.apply_U γ j (fun i => hU i) x
      have hcf : cfun (K.y j) = zp (ctr (K.y j)) (hctr_le _ ⟨j, hj, rfl⟩) := by
        simp only [cfun, dif_pos (hctr_le _ ⟨j, hj, rfl⟩)]
      have hctrj : ctr (K.y j) = ∑ i, c i * ((formQ i j : ℤ) : ℚ_[p]) := by
        simp only [ctr]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        congr 1
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk; simp [Finsupp.single_apply, Ne.symm hk]
        · intro h; exact absurd (Finset.mem_univ _) h
      have e : x + u • K.y j + cfun (K.y j) • a = γ x := by
        rw [happ, hcf, zp_smul, zp_smul, hctrj]
      show x + u • K.y j + cfun (K.y j) • a ∈ spanImg K.Γ x
      rw [e]; exact mem_spanImg_of_mem _ _ hγ
  refine le_trans ?_ (key ▸ hle)
  refine K.toSmallField.L1_le_of_basis _ (fun i => ?_)
  by_cases h0 : i = K.i0
  · subst h0; exact Submodule.subset_span (Or.inl (Or.inl rfl))
  · by_cases h1 : i = K.i1
    · subst h1; exact Submodule.subset_span (Or.inl (Or.inr rfl))
    · have h2 : 2 ≤ i.val := by
        by_contra hlt
        have : i.val = 0 ∨ i.val = 1 := by omega
        rcases this with h | h
        · exact h0 (Fin.ext (by simp [i0, h]))
        · exact h1 (Fin.ext (by simp [i1, h]))
      exact Submodule.subset_span (Or.inr ⟨i, h2, rfl⟩)

/-- Theorem 5.1(a): in even degree, `S_K(m) = 𝔪^(lo m)` for every `m`, and `a_K(m) = (m-1) mod e`
is attained. -/
theorem thm51_even (m : ℤ) :
    S K.Γ (K.F.L m) = K.F.L (lo K.F.e m) ∧ Reaches K.F K.Γ (K.F.L m) (lo K.F.e m) := by
  have h : ∀ r : ℤ, 1 ≤ r → r ≤ K.F.e → K.F.L 1 ≤ S K.Γ (K.F.L r) := by
    intro r hr1 hre
    have hpcLr : K.pc ∈ K.F.L r := K.F.anti_le hre K.hpc
    have hpcL1 : K.pc ∈ K.F.L 1 := K.F.anti_le hr1 hpcLr
    exact (K.lemma52 K.pc hpcL1 K.hpcτ).trans (spanImg_le_S K.Γ hpcLr)
  exact ⟨S_eq_of_period K.F K.Γ K.hΓ1 h m, reaches_of_period K.F K.Γ K.hΓ1 h m⟩

end EvenSmall

end LogShellEdge
