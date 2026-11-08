import LogShellEdge.Coord

/-!
# Odd degree (Sections 5.2 and 6 of the note)

Indices are 0-based: `y 0` is the paper's `y_1`, and the pairs are `(y (2k+1), y (2k+2))`, `k < g`
(the paper's `(y_{2k+2}, y_{2k+3})`), `d = 2g + 1`.

* `OddSmall`: a small field of odd degree with Kondo's description of `ker Tr` and the maps of
  Proposition 4.4(b) (both moves inside each pair and the swaps of adjacent pairs).
* `lemma53`: `w ∈ W ∖ pW ⇒ span Γ w ⊇ W` (Lemma 5.3).
* `lemma54`: if `f (e + 1 - r) ≥ 2` then `Λ ⊆ S_K(r)` (Lemma 5.4).
* `thm51_odd`: Theorem 5.1(b)(c).
* `OddTR`: the totally ramified case `f = 1`, with the element `p ∈ K` and, for `s = 1`, the
  automorphism of Theorem 6.5 (as a hypothesis; its algebraic core is `GroupRing`).
* `thm61_i`, `thm61_ii`: Theorem 6.1; `cor66`: Corollary 6.6; `main_odd`: Theorem 6.7 in odd degree.
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge

variable {p : ℕ} [Fact p.Prime]

/-- index of the first member of pair `k` -/
def uIdx {g : ℕ} (k : Fin g) : Fin (2 * g + 1) := ⟨2 * k.val + 1, by omega⟩

/-- index of the second member of pair `k` -/
def vIdx {g : ℕ} (k : Fin g) : Fin (2 * g + 1) := ⟨2 * k.val + 2, by omega⟩

/-- the permutation of indices exchanging pair `k` and pair `k + 1` -/
def swapIdx {g : ℕ} (k : ℕ) (hk : k + 1 < g) (i : Fin (2 * g + 1)) : Fin (2 * g + 1) :=
  if i.val = 2 * k + 1 then ⟨2 * k + 3, by omega⟩
  else if i.val = 2 * k + 2 then ⟨2 * k + 4, by omega⟩
  else if i.val = 2 * k + 3 then ⟨2 * k + 1, by omega⟩
  else if i.val = 2 * k + 4 then ⟨2 * k + 2, by omega⟩
  else i

theorem idx_cases {g : ℕ} (i : Fin (2 * g + 1)) (hi : i ≠ 0) : ∃ k : Fin g, i = uIdx k ∨ i = vIdx k := by
  have hi' : i.val ≠ 0 := fun h => hi (Fin.ext h)
  rcases Nat.even_or_odd i.val with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine ⟨⟨m - 1, by omega⟩, Or.inr (Fin.ext ?_)⟩
    simp only [vIdx]; omega
  · refine ⟨⟨m, by omega⟩, Or.inl (Fin.ext ?_)⟩
    simp only [uIdx]; omega

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]

/-- A small field of odd degree `d = 2g+1` with the inputs of Sections 3-5. -/
structure OddSmall (p : ℕ) [Fact p.Prime] (V : Type*) [AddCommGroup V] [Module ℚ_[p] V]
    [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V] (g : ℕ)
    extends SmallField p V (Fin (2 * g + 1)) where
  /-- [Kondo, Theorem 1.3] (odd degree): `ker Tr = ⟨y_2, …, y_d⟩` -/
  hker : ∀ i : Fin (2 * g + 1), i ≠ 0 → τ (y i) = 0
  /-- Lemma 3.4: `Tr(y_1)` generates `p ℤ_p` -/
  hτ0 : ‖τ (y 0)‖ = 1
  /-- Proposition 4.4(b): `u ↦ u + v` on pair `k` (Lemma 4.1, Lemma 4.2(i)) -/
  moveU : ∀ k : Fin g, ∃ γ ∈ Γ, ∀ i, γ (y i) = if i = uIdx k then y (uIdx k) + y (vIdx k) else y i
  /-- Proposition 4.4(b): `v ↦ v + u` on pair `k` -/
  moveV : ∀ k : Fin g, ∃ γ ∈ Γ, ∀ i, γ (y i) = if i = vIdx k then y (vIdx k) + y (uIdx k) else y i
  /-- Proposition 4.4(b): the swap of adjacent pairs (Lemma 4.1, Lemma 4.2(ii)) -/
  swap : ∀ (k : ℕ) (hk : k + 1 < g), ∃ γ ∈ Γ, ∀ i, γ (y i) = y (swapIdx k hk i)

namespace OddSmall

variable {g : ℕ} (K : OddSmall p V g)

theorem tau_eq (x : V) : K.τ x = K.y.repr x 0 * K.τ (K.y 0) := by
  conv_lhs => rw [← K.y.sum_repr x]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single (0 : Fin (2 * g + 1))]
  · intro i _ hi
    rw [K.hker i hi, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem tau_y0_ne : K.τ (K.y 0) ≠ 0 := by
  intro h; have := K.hτ0; rw [h, norm_zero] at this; exact zero_ne_one this

theorem coeff0_eq_zero_of_tau {x : V} (hx : K.τ x = 0) : K.y.repr x 0 = 0 := by
  rw [K.tau_eq] at hx
  exact (mul_eq_zero.mp hx).resolve_right K.tau_y0_ne

theorem norm_tau_eq (x : V) : ‖K.τ x‖ = ‖K.y.repr x 0‖ := by
  rw [K.tau_eq, norm_mul, K.hτ0, mul_one]

theorem norm_tau_le {x : V} (hx : x ∈ K.F.L 1) : ‖K.τ x‖ ≤ 1 := by
  rw [K.norm_tau_eq]; exact K.toSmallField.coeff_le_one hx 0

/-- The span of the orbit of `w` contains pair `k` if a coordinate of `w` on pair `k` is a unit. -/
theorem pair_mem_of_unit (w : V) (k : Fin g)
    (h : ‖K.y.repr w (uIdx k)‖ = 1 ∨ ‖K.y.repr w (vIdx k)‖ = 1) :
    K.y (uIdx k) ∈ spanImg K.Γ w ∧ K.y (vIdx k) ∈ spanImg K.Γ w := by
  obtain ⟨γU, hγU, hU⟩ := K.moveU k
  obtain ⟨γV, hγV, hV⟩ := K.moveV k
  have hU' := apply_of_move K.y (γU : V →ₗ[ℚ_[p]] V) (uIdx k) (vIdx k) (fun i => hU i)
  have hV' := apply_of_move K.y (γV : V →ₗ[ℚ_[p]] V) (vIdx k) (uIdx k) (fun i => hV i)
  have huv : uIdx k ≠ vIdx k := by
    intro h; have := congrArg Fin.val h; simp [uIdx, vIdx] at this
  -- if `c • y j ∈ N` with `‖c‖ = 1` then `y j ∈ N`
  have unit_div : ∀ (c : ℚ_[p]) (z : V), ‖c‖ = 1 → c • z ∈ spanImg K.Γ w → z ∈ spanImg K.Γ w := by
    intro c z hc hz
    have hc0 : c ≠ 0 := by intro h0; rw [h0, norm_zero] at hc; exact zero_ne_one hc
    have hci : ‖c⁻¹‖ ≤ 1 := by rw [norm_inv, hc, inv_one]
    have := (spanImg K.Γ w).smul_mem (zp c⁻¹ hci) hz
    rwa [zp_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  rcases h with hu | hv
  · have h1 : K.y.repr w (uIdx k) • K.y (vIdx k) ∈ spanImg K.Γ w := by
      have : K.y.repr w (uIdx k) • K.y (vIdx k) = γU w - w := by
        rw [show γU w = (γU : V →ₗ[ℚ_[p]] V) w from rfl, hU']; abel
      rw [this]
      exact sub_mem (mem_spanImg_of_mem _ _ hγU) (mem_spanImg_self _ _)
    have hv' : K.y (vIdx k) ∈ spanImg K.Γ w := unit_div _ _ hu h1
    refine ⟨?_, hv'⟩
    have : K.y (uIdx k) = γV (K.y (vIdx k)) - K.y (vIdx k) := by
      rw [hV (vIdx k), if_pos rfl]; abel
    rw [this]
    exact sub_mem (spanImg_stable _ _ hγV hv') hv'
  · have h1 : K.y.repr w (vIdx k) • K.y (uIdx k) ∈ spanImg K.Γ w := by
      have : K.y.repr w (vIdx k) • K.y (uIdx k) = γV w - w := by
        rw [show γV w = (γV : V →ₗ[ℚ_[p]] V) w from rfl, hV']; abel
      rw [this]
      exact sub_mem (mem_spanImg_of_mem _ _ hγV) (mem_spanImg_self _ _)
    have hu' : K.y (uIdx k) ∈ spanImg K.Γ w := unit_div _ _ hv h1
    refine ⟨hu', ?_⟩
    have : K.y (vIdx k) = γU (K.y (uIdx k)) - K.y (uIdx k) := by
      rw [hU (uIdx k), if_pos rfl]; abel
    rw [this]
    exact sub_mem (spanImg_stable _ _ hγU hu') hu'

/-- If one pair lies in the span of the orbit, all pairs do (swaps of adjacent pairs). -/
theorem all_pairs_mem (w : V) (k₀ : Fin g)
    (h₀ : K.y (uIdx k₀) ∈ spanImg K.Γ w ∧ K.y (vIdx k₀) ∈ spanImg K.Γ w) :
    ∀ k : Fin g, K.y (uIdx k) ∈ spanImg K.Γ w ∧ K.y (vIdx k) ∈ spanImg K.Γ w := by
  -- moving up
  have up : ∀ (k : ℕ) (hk : k + 1 < g),
      (K.y (uIdx ⟨k, by omega⟩) ∈ spanImg K.Γ w ∧ K.y (vIdx ⟨k, by omega⟩) ∈ spanImg K.Γ w) →
      (K.y (uIdx ⟨k + 1, hk⟩) ∈ spanImg K.Γ w ∧ K.y (vIdx ⟨k + 1, hk⟩) ∈ spanImg K.Γ w) := by
    intro k hk ⟨hu, hv⟩
    obtain ⟨γ, hγ, hs⟩ := K.swap k hk
    have e1 : swapIdx k hk (uIdx ⟨k, by omega⟩) = uIdx ⟨k + 1, hk⟩ := by
      apply Fin.ext; simp only [swapIdx, uIdx]; split_ifs <;> simp only [Fin.val_mk] at * <;> omega
    have e2 : swapIdx k hk (vIdx ⟨k, by omega⟩) = vIdx ⟨k + 1, hk⟩ := by
      apply Fin.ext; simp only [swapIdx, vIdx]; split_ifs <;> simp only [Fin.val_mk] at * <;> omega
    refine ⟨?_, ?_⟩
    · rw [← e1, ← hs]; exact spanImg_stable _ _ hγ hu
    · rw [← e2, ← hs]; exact spanImg_stable _ _ hγ hv
  have down : ∀ (k : ℕ) (hk : k + 1 < g),
      (K.y (uIdx ⟨k + 1, hk⟩) ∈ spanImg K.Γ w ∧ K.y (vIdx ⟨k + 1, hk⟩) ∈ spanImg K.Γ w) →
      (K.y (uIdx ⟨k, by omega⟩) ∈ spanImg K.Γ w ∧ K.y (vIdx ⟨k, by omega⟩) ∈ spanImg K.Γ w) := by
    intro k hk ⟨hu, hv⟩
    obtain ⟨γ, hγ, hs⟩ := K.swap k hk
    have e1 : swapIdx k hk (uIdx ⟨k + 1, hk⟩) = uIdx ⟨k, by omega⟩ := by
      apply Fin.ext; simp only [swapIdx, uIdx]; split_ifs <;> simp only [Fin.val_mk] at * <;> omega
    have e2 : swapIdx k hk (vIdx ⟨k + 1, hk⟩) = vIdx ⟨k, by omega⟩ := by
      apply Fin.ext; simp only [swapIdx, vIdx]; split_ifs <;> simp only [Fin.val_mk] at * <;> omega
    refine ⟨?_, ?_⟩
    · rw [← e1, ← hs]; exact spanImg_stable _ _ hγ hu
    · rw [← e2, ← hs]; exact spanImg_stable _ _ hγ hv
  have upN : ∀ n : ℕ, (hn : k₀.val + n < g) →
      K.y (uIdx ⟨k₀.val + n, hn⟩) ∈ spanImg K.Γ w ∧ K.y (vIdx ⟨k₀.val + n, hn⟩) ∈ spanImg K.Γ w := by
    intro n
    induction n with
    | zero => intro _; exact h₀
    | succ n ih => intro hn; exact up (k₀.val + n) hn (ih (by omega))
  have downN : ∀ n : ℕ, (hn : n ≤ k₀.val) →
      K.y (uIdx ⟨k₀.val - n, by omega⟩) ∈ spanImg K.Γ w ∧
        K.y (vIdx ⟨k₀.val - n, by omega⟩) ∈ spanImg K.Γ w := by
    intro n
    induction n with
    | zero => intro _; exact h₀
    | succ n ih =>
      intro hn
      have := down (k₀.val - (n + 1)) (by omega)
      have e : k₀.val - (n + 1) + 1 = k₀.val - n := by omega
      simp only [e] at this
      exact this (ih (by omega))
  intro k
  by_cases hk : k₀.val ≤ k.val
  · have := upN (k.val - k₀.val) (by omega)
    have e : k₀.val + (k.val - k₀.val) = k.val := by omega
    simp only [e] at this
    exact this
  · have := downN (k₀.val - k.val) (by omega)
    have e : k₀.val - (k₀.val - k.val) = k.val := by omega
    simp only [e] at this
    exact this

/-- If the span `N` contains `y_i` for all `i ≠ 0`, it contains every element of `Λ ∩ ker Tr`. -/
theorem ker_le_of_basis (N : Submodule ℤ_[p] V) (h : ∀ i : Fin (2 * g + 1), i ≠ 0 → K.y i ∈ N) :
    ∀ x ∈ K.F.L 1, K.τ x = 0 → x ∈ N := by
  intro x hx hτ
  rw [K.toSmallField.sum_repr x]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  by_cases hi : i = 0
  · subst hi; rw [K.coeff0_eq_zero_of_tau hτ, zero_smul]; exact N.zero_mem
  · rw [← zp_smul _ (K.toSmallField.coeff_le_one hx i)]
    exact N.smul_mem _ (h i hi)

/-- Lemma 5.3: if `w ∈ W ∖ pW` then the span of the orbit of `w` contains `W = Λ ∩ ker Tr`. -/
theorem lemma53 (w : V) (hw : w ∈ K.F.L 1) (hτw : K.τ w = 0) (hw' : w ∉ K.F.L (1 + K.F.e)) :
    ∀ x ∈ K.F.L 1, K.τ x = 0 → x ∈ spanImg K.Γ w := by
  obtain ⟨i₀, hi₀⟩ := K.toSmallField.exists_coeff_unit hw hw'
  have hi₀0 : i₀ ≠ 0 := by
    intro h; subst h; rw [K.coeff0_eq_zero_of_tau hτw, norm_zero] at hi₀; exact zero_ne_one hi₀
  obtain ⟨k₀, hk₀⟩ := idx_cases i₀ hi₀0
  have h₀ := K.pair_mem_of_unit w k₀ (by rcases hk₀ with h | h <;> subst h <;> simp [hi₀])
  have hall := K.all_pairs_mem w k₀ h₀
  refine K.ker_le_of_basis _ (fun i hi => ?_)
  obtain ⟨k, hk⟩ := idx_cases i hi
  rcases hk with h | h <;> subst h
  · exact (hall k).1
  · exact (hall k).2

/-- If `N` contains `Λ ∩ ker Tr` and an element of `Λ ∩ N` whose trace generates `p ℤ_p`, then `Λ ⊆ N`. -/
theorem L1_le_of_ker (N : Submodule ℤ_[p] V) (hW : ∀ x ∈ K.F.L 1, K.τ x = 0 → x ∈ N)
    (x₀ : V) (hx₀ : x₀ ∈ K.F.L 1) (hx₀N : x₀ ∈ N) (hτ : ‖K.τ x₀‖ = 1) : K.F.L 1 ≤ N := by
  set c := K.y.repr x₀ 0 with hc
  have hc1 : ‖c‖ = 1 := by rw [hc, ← K.norm_tau_eq]; exact hτ
  have hc0 : c ≠ 0 := by intro h0; rw [h0, norm_zero] at hc1; exact zero_ne_one hc1
  -- `x₀ - c y_0` has trace `0`
  have hrest : x₀ - c • K.y 0 ∈ N := by
    apply hW
    · refine sub_mem hx₀ ?_
      rw [← zp_smul _ hc1.le]
      exact (K.F.L 1).smul_mem _ (K.toSmallField.y_mem 0)
    · rw [map_sub, map_smul, K.tau_eq x₀, smul_eq_mul, ← hc, sub_self]
  have hy0 : K.y 0 ∈ N := by
    have h1 : c • K.y 0 ∈ N := by
      have := sub_mem hx₀N hrest
      rwa [sub_sub_cancel] at this
    have hci : ‖c⁻¹‖ ≤ 1 := by rw [norm_inv, hc1, inv_one]
    have := N.smul_mem (zp c⁻¹ hci) h1
    rwa [zp_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  refine K.toSmallField.L1_le_of_basis N (fun i => ?_)
  by_cases hi : i = 0
  · subst hi; exact hy0
  · refine hW _ (K.toSmallField.y_mem i) (K.hker i hi)

/-- `pΛ` maps to traces of norm `≤ ‖p‖`. -/
theorem norm_tau_le_p {z : V} (hz : z ∈ K.F.L (1 + K.F.e)) : ‖K.τ z‖ ≤ ‖(p : ℚ_[p])‖ := by
  rw [K.norm_tau_eq]; exact (K.toSmallField.mem_pL1_iff z).1 hz 0

/-- `t • x ∈ pΛ` if `x ∈ Λ` and `‖t‖ ≤ ‖p‖`. -/
theorem smul_mem_pL1 {x : V} (hx : x ∈ K.F.L 1) {t : ℚ_[p]} (ht : ‖t‖ ≤ ‖(p : ℚ_[p])‖) :
    t • x ∈ K.F.L (1 + K.F.e) := by
  rw [K.toSmallField.mem_pL1_iff]
  intro i
  rw [repr_smul, norm_mul]
  calc ‖t‖ * ‖K.y.repr x i‖ ≤ ‖(p : ℚ_[p])‖ * 1 :=
        mul_le_mul ht (K.toSmallField.coeff_le_one hx i) (norm_nonneg _) (norm_nonneg _)
    _ = ‖(p : ℚ_[p])‖ := mul_one _

end OddSmall

end LogShellEdge
