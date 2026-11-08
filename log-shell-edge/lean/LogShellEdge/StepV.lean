import LogShellEdge.Basic

/-!
# Theorem 7.1: the arithmetic of the orders and the lower bound for the holomorphic hull

The proof of Theorem 7.1 takes, at each factor `i ≠ j`, an element of `R_i` whose image has
valuation `lo_{e_i}(0) = 1 - e_i`, and at the factor `j` an element of `𝔪^m` (`m = e_j λ`) whose image
has valuation `lo_{e_j}(m)` (Theorem 6.7). The pure tensor of these images is a unit of `T` whose
order in every field component is (`ord_identity`)
  `∑_{i≠j} (1 - e_i)/e_i + lo_{e_j}(m)/e_j = ⌈λ⌉ - 𝔡_I`,   `𝔡_I = ∑_i (e_i - 1)/e_i`,
and a unit `u` in a set `X` forces `u · R̃ ⊆ hull(X)` (`unit_smul_subset_hull`; the hull is the
intersection of the `c · R̃` containing `X`, [IUT3, Remark 3.9.5(i)]). That a unit of `T` with these
orders generates `p^(⌈λ⌉-𝔡_I) R̃` ([Tiers, §2.1]) and the reverse inclusion ([Tiers, Theorem 4.2])
are cited inputs.
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge

open scoped Pointwise

/-- `⌊(m-1)/e⌋ = ⌈m/e⌉ - 1` for `e > 0` (integer division on the left). -/
theorem ediv_pred_eq_ceil_sub_one (e : ℕ) (he : 0 < e) (m : ℤ) :
    (m - 1) / (e : ℤ) = ⌈(m : ℚ) / e⌉ - 1 := by
  have hep : (0 : ℚ) < e := by exact_mod_cast he
  have h1 := Int.mul_ediv_add_emod (m - 1) (e : ℤ)
  have h2 := Int.emod_nonneg (m - 1) (show (e : ℤ) ≠ 0 by exact_mod_cast he.ne')
  have h3 := Int.emod_lt_of_pos (m - 1) (show (0 : ℤ) < e by exact_mod_cast he)
  set q := (m - 1) / (e : ℤ)
  set r := (m - 1) % (e : ℤ)
  have key : ⌈(m : ℚ) / e⌉ = q + 1 := by
    rw [Int.ceil_eq_iff]
    have hm : (m : ℚ) = (e : ℚ) * q + r + 1 := by
      have : (m : ℤ) = e * q + r + 1 := by omega
      exact_mod_cast this
    rw [hm]
    constructor
    · rw [lt_div_iff₀ hep]
      push_cast
      have : (0 : ℚ) ≤ r := by exact_mod_cast h2
      nlinarith
    · rw [div_le_iff₀ hep]
      push_cast
      have : (r : ℚ) + 1 ≤ e := by exact_mod_cast (show r + 1 ≤ (e : ℤ) by omega)
      nlinarith
  rw [key]; ring

/-- `lo_e(m)/e = ⌈m/e⌉ - (e - 1)/e`. -/
theorem lo_div (e : ℕ) (he : 0 < e) (m : ℤ) :
    ((lo e m : ℤ) : ℚ) / e = ⌈(m : ℚ) / e⌉ - ((e : ℚ) - 1) / e := by
  have hep : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  unfold lo
  rw [ediv_pred_eq_ceil_sub_one e he m]
  push_cast
  field_simp
  ring

/-- Theorem 7.1, the orders: `∑_{i ≠ j} (1 - e_i)/e_i + lo_{e_j}(m)/e_j = ⌈m/e_j⌉ - 𝔡_I`. -/
theorem ord_identity {ι : Type*} [DecidableEq ι] (I : Finset ι) (e : ι → ℕ) (he : ∀ i, 0 < e i)
    (j : ι) (hj : j ∈ I) (m : ℤ) :
    (∑ i ∈ I.erase j, ((1 : ℚ) - e i) / e i) + ((lo (e j) m : ℤ) : ℚ) / e j =
      ⌈(m : ℚ) / e j⌉ - ∑ i ∈ I, ((e i : ℚ) - 1) / e i := by
  rw [lo_div (e j) (he j) m, ← Finset.sum_erase_add I _ hj]
  have : ∀ i, ((1 : ℚ) - e i) / e i = -(((e i : ℚ) - 1) / e i) := by intro i; ring
  simp only [this, Finset.sum_neg_distrib]
  ring

/-- the holomorphic hull: the intersection of all `c · R̃` (`c` a unit of `T`) containing `X` -/
def hull {T : Type*} [CommRing T] (R : Subring T) (X : Set T) : Set T :=
  ⋂ c ∈ {c : Tˣ | X ⊆ (c : T) • (R : Set T)}, (c : T) • (R : Set T)

/-- A unit `u ∈ X` gives `u · R̃ ⊆ hull(X)` ("a unit contained in `c R̃` has `u R̃ ⊆ c R̃`"). -/
theorem unit_smul_subset_hull {T : Type*} [CommRing T] (R : Subring T) {X : Set T} {u : Tˣ}
    (hu : (u : T) ∈ X) : (u : T) • (R : Set T) ⊆ hull R X := by
  intro z hz
  simp only [hull, Set.mem_iInter, Set.mem_setOf_eq]
  intro c hc
  obtain ⟨r, hr, hru⟩ := hc hu
  obtain ⟨s, hs, rfl⟩ := hz
  refine ⟨r * s, R.mul_mem hr hs, ?_⟩
  simp only [smul_eq_mul] at hru ⊢
  rw [← hru]
  ring

end LogShellEdge
