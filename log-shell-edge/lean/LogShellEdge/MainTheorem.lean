import LogShellEdge.Even

/-!
# Theorem 6.7 (main theorem), Corollary 7.2, Corollary 6.8 and Remark 6.9

* `main_even`, `main_odd_f2`, `main_odd_tr`: Theorem 6.7 in the three cases of a small field
  (even degree; odd degree with `f ≥ 2`; odd degree, totally ramified, with Theorem 6.5 for `s = 1`).
* `cor72_*`: Corollary 7.2: condition (U) of [Tiers], i.e. `a_K(0) = e - 1`: some image of `𝒪_K`
  reaches valuation `1 - e`.
* `OddLattice`, `cor68`: Corollary 6.8 for an odd-degree field (not necessarily small) with `s = 1`:
  some `α ∈ Γ` moves the line `(ℚ_p)_+`. `rem69`: the automorphism of Theorem 6.5 moves `y_1`.
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge

variable {p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]

theorem lo_zero (e : ℕ) (he : 0 < e) : lo e 0 = 1 - e := by
  have := lo_add_mul e he e (-1) (by omega) le_rfl
  rw [show (-1 : ℤ) * e + e = 0 by ring] at this
  rw [this]; ring

/-- Theorem 6.7, even degree. -/
theorem main_even {g : ℕ} (K : EvenSmall p V g) (m : ℤ) :
    S K.Γ (K.F.L m) = K.F.L (lo K.F.e m) ∧ Reaches K.F K.Γ (K.F.L m) (lo K.F.e m) :=
  K.thm51_even m

/-- Theorem 6.7, odd degree with `f ≥ 2`. -/
theorem main_odd_f2 {g : ℕ} (K : OddSmall p V g) (hf : 2 ≤ K.f) (m : ℤ) :
    S K.Γ (K.F.L m) = K.F.L (lo K.F.e m) ∧ Reaches K.F K.Γ (K.F.L m) (lo K.F.e m) :=
  K.thm51_odd m (Or.inl hf)

/-- Theorem 6.7, odd degree, totally ramified (`d = e ≥ 3`). -/
theorem main_odd_tr {g : ℕ} (K : OddTR p V g) (hg : 1 ≤ g) (m : ℤ) :
    S K.Γ (K.F.L m) = K.F.L (lo K.F.e m) ∧ Reaches K.F K.Γ (K.F.L m) (lo K.F.e m) :=
  K.main hg m

/-- Corollary 7.2 (even degree): some image of `𝒪_K = 𝔪^0` has valuation exactly `1 - e`. -/
theorem cor72_even {g : ℕ} (K : EvenSmall p V g) : Reaches K.F K.Γ (K.F.L 0) (1 - K.F.e) := by
  have := (main_even K 0).2; rwa [lo_zero _ K.F.e_pos] at this

/-- Corollary 7.2 (odd degree, `f ≥ 2`). -/
theorem cor72_odd_f2 {g : ℕ} (K : OddSmall p V g) (hf : 2 ≤ K.f) :
    Reaches K.F K.Γ (K.F.L 0) (1 - K.F.e) := by
  have := (main_odd_f2 K hf 0).2; rwa [lo_zero _ K.F.e_pos] at this

/-- Corollary 7.2 (odd degree, totally ramified). -/
theorem cor72_odd_tr {g : ℕ} (K : OddTR p V g) (hg : 1 ≤ g) :
    Reaches K.F K.Γ (K.F.L 0) (1 - K.F.e) := by
  have := (main_odd_tr K hg 0).2; rwa [lo_zero _ K.F.e_pos] at this

/-- The lattice data of an odd-degree field `k` (not necessarily small) used in Corollary 6.8:
`Λ = log U¹_k` with the `ℤ_p`-basis `y` (Lemma 3.2, valid since `μ_p ⊄ k`), the trace, the maps of
Proposition 4.4(b) inside the pairs, and Theorem 6.5 for `s = 1`. -/
structure OddLattice (p : ℕ) [Fact p.Prime] (V : Type*) [AddCommGroup V] [Module ℚ_[p] V]
    [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V] (g : ℕ) where
  Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)
  /-- `y_i = log rec⁻¹(x_i)`; `Λ = ⊕ ℤ_p y_i` -/
  y : Module.Basis (Fin (2 * g + 1)) ℚ_[p] V
  /-- `Tr / p` -/
  τ : V →ₗ[ℚ_[p]] ℚ_[p]
  /-- (Γ2) -/
  hΓ2 : ∀ γ ∈ Γ, ∀ x, τ (γ x) = τ x
  /-- [Kondo, Theorem 1.3] (odd degree) -/
  hker : ∀ i : Fin (2 * g + 1), i ≠ 0 → τ (y i) = 0
  hτ0 : τ (y 0) ≠ 0
  /-- Proposition 4.4(b) -/
  moveU : ∀ k : Fin g, ∃ γ ∈ Γ, ∀ i, γ (y i) = if i = uIdx k then y (uIdx k) + y (vIdx k) else y i
  moveV : ∀ k : Fin g, ∃ γ ∈ Γ, ∀ i, γ (y i) = if i = vIdx k then y (vIdx k) + y (uIdx k) else y i
  /-- the integer `s` of the Jannsen-Wingberg presentation -/
  s : ℕ
  /-- Theorem 6.5 (proved for `s = 1`), stated modulo `pΛ` in coordinates -/
  lift : s = 1 → ∀ hg : 1 ≤ g, ∃ φ ∈ Γ, ∀ i j : Fin (2 * g + 1),
    ‖y.repr (φ (y i) - (if i = 0 then y 0 + y ⟨1, by omega⟩ else y i)) j‖ ≤ ‖(p : ℚ_[p])‖

namespace OddLattice

variable {g : ℕ} (K : OddLattice p V g)

theorem tau_eq (x : V) : K.τ x = K.y.repr x 0 * K.τ (K.y 0) := by
  conv_lhs => rw [← K.y.sum_repr x]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single (0 : Fin (2 * g + 1))]
  · intro i _ hi; rw [K.hker i hi, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- If `γ` preserves the trace and `τ u ≠ 0`, then `γ u ∈ ℚ_p u` forces `γ u = u`. -/
theorem eq_of_mem_line {γ : V ≃ₗ[ℚ_[p]] V} (hγ : γ ∈ K.Γ) {u : V} (hu : K.τ u ≠ 0) {t : ℚ_[p]}
    (ht : γ u = t • u) : γ u = u := by
  have h1 := K.hΓ2 γ hγ u
  rw [ht, map_smul, smul_eq_mul] at h1
  have : t = 1 := by
    have := mul_right_cancel₀ hu (h1.trans (one_mul _).symm)
    exact this
  rw [ht, this, one_smul]

/-- Corollary 6.8: for an odd-degree field with `s = 1` and `d ≥ 3`, if `u ∈ Λ` is primitive (some
coordinate has norm `1`) with `Tr(u) ≠ 0` (e.g. a generator of `(ℚ_p)_+ ∩ Λ`), some `α ∈ Γ` satisfies
`α u ∉ ℚ_p u`; hence `α((ℚ_p)_+) ∩ (ℚ_p)_+ = 0`. -/
theorem cor68 (hs : K.s = 1) (hg : 1 ≤ g) (u : V) (hu1 : ∀ i, ‖K.y.repr u i‖ ≤ 1)
    (hprim : ∃ i, ‖K.y.repr u i‖ = 1) (hτu : K.τ u ≠ 0) :
    ∃ α ∈ K.Γ, ∀ t : ℚ_[p], α u ≠ t • u := by
  set c := K.y.repr u with hc
  have hc0 : c 0 ≠ 0 := by
    intro h; apply hτu; rw [K.tau_eq, ← hc, h, zero_mul]
  by_cases hc0n : ‖c 0‖ = 1
  · -- case (a): use the automorphism of Theorem 6.5
    obtain ⟨φ, hφ, hφy⟩ := K.lift hs hg
    refine ⟨φ, hφ, fun t ht => ?_⟩
    have hφu := K.eq_of_mem_line hφ hτu ht
    set i1 : Fin (2 * g + 1) := ⟨1, by omega⟩
    have hi10 : i1 ≠ 0 := by intro h; have := congrArg Fin.val h; simp [i1] at this
    -- `φ u - u - c₀ y₁ = Σ cᵢ (φ yᵢ - (yᵢ + [i = 0] y₁))`, all coordinates `≤ ‖p‖`
    have hsum : φ u - (u + c 0 • K.y i1) =
        ∑ i, c i • (φ (K.y i) - (if i = 0 then K.y 0 + K.y i1 else K.y i)) := by
      have e1 : φ u = ∑ i, c i • φ (K.y i) := by
        rw [hc]; exact apply_eq_sum K.y (φ : V →ₗ[ℚ_[p]] V) u
      have e2 : u + c 0 • K.y i1 = ∑ i, c i • (if i = 0 then K.y 0 + K.y i1 else K.y i) := by
        conv_lhs => rw [← K.y.sum_repr u]
        rw [← hc]
        have : ∀ i, c i • (if i = 0 then K.y 0 + K.y i1 else K.y i) =
            c i • K.y i + (if i = 0 then c 0 • K.y i1 else 0) := by
          intro i; split_ifs with h
          · subst h; rw [smul_add]
          · rw [add_zero]
        rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, Finset.sum_ite_eq',
          if_pos (Finset.mem_univ _)]
      rw [e1, e2, ← Finset.sum_sub_distrib]
      simp only [smul_sub]
    have hcoord : ‖K.y.repr (φ u - (u + c 0 • K.y i1)) i1‖ ≤ ‖(p : ℚ_[p])‖ := by
      rw [hsum, map_sum, Finsupp.finset_sum_apply]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun i _ => ?_)
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hu1 i)).trans (hφy i i1)
    rw [hφu] at hcoord
    rw [show u - (u + c 0 • K.y i1) = -(c 0 • K.y i1) by abel] at hcoord
    simp only [map_neg, map_smul, Finsupp.neg_apply, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, smul_eq_mul, mul_one, norm_neg] at hcoord
    rw [hc0n] at hcoord
    exact absurd hcoord (not_le.mpr norm_p_lt_one')
  · -- case (b): a coordinate on some pair is a unit; use a move inside that pair
    obtain ⟨i₀, hi₀⟩ := hprim
    have hi₀0 : i₀ ≠ 0 := by intro h; subst h; exact hc0n hi₀
    obtain ⟨k, hk⟩ := idx_cases i₀ hi₀0
    rcases hk with h | h <;> subst h
    · obtain ⟨γ, hγ, hU⟩ := K.moveU k
      refine ⟨γ, hγ, fun t ht => ?_⟩
      have h1 := K.eq_of_mem_line hγ hτu ht
      have happ := apply_of_move K.y (γ : V →ₗ[ℚ_[p]] V) (uIdx k) (vIdx k) (fun i => hU i) u
      change γ u = _ at happ
      rw [h1] at happ
      have : c (uIdx k) • K.y (vIdx k) = 0 := by
        have := congrArg (fun z => z - u) happ; simpa [hc] using this.symm
      rw [smul_eq_zero] at this
      rcases this with h0 | h0
      · rw [h0, norm_zero] at hi₀; exact zero_ne_one hi₀
      · exact K.y.ne_zero _ h0
    · obtain ⟨γ, hγ, hV⟩ := K.moveV k
      refine ⟨γ, hγ, fun t ht => ?_⟩
      have h1 := K.eq_of_mem_line hγ hτu ht
      have happ := apply_of_move K.y (γ : V →ₗ[ℚ_[p]] V) (vIdx k) (uIdx k) (fun i => hV i) u
      change γ u = _ at happ
      rw [h1] at happ
      have : c (vIdx k) • K.y (uIdx k) = 0 := by
        have := congrArg (fun z => z - u) happ; simpa [hc] using this.symm
      rw [smul_eq_zero] at this
      rcases this with h0 | h0
      · rw [h0, norm_zero] at hi₀; exact zero_ne_one hi₀
      · exact K.y.ne_zero _ h0

/-- Remark 6.9: the automorphism of Theorem 6.5 satisfies `φ₊(y₁) ≠ y₁` (the element asked for in
[Kondo, Remark 1.10]), for `s = 1`. -/
theorem rem69 (hs : K.s = 1) (hg : 1 ≤ g) : ∃ φ ∈ K.Γ, φ (K.y 0) ≠ K.y 0 := by
  obtain ⟨φ, hφ, hφy⟩ := K.lift hs hg
  refine ⟨φ, hφ, fun h => ?_⟩
  have := hφy 0 ⟨1, by omega⟩
  rw [if_pos rfl, h, show K.y 0 - (K.y 0 + K.y ⟨1, by omega⟩) = -K.y ⟨1, by omega⟩ by abel] at this
  simp only [map_neg, Module.Basis.repr_self, Finsupp.neg_apply, Finsupp.single_eq_same, norm_neg,
    norm_one] at this
  exact absurd this (not_le.mpr norm_p_lt_one')

end OddLattice

end LogShellEdge
