import Mathlib

/-!
# Lattices `𝔪^j`, the spans `S_K(m)`, and the trivial upper bound (Section 2.3 of the note)

The field `K` is modelled by a `ℚ_[p]`-vector space `V` carrying a decreasing family of `ℤ_[p]`-lattices
`L j` (`j : ℤ`, the powers `𝔪^j` of the maximal ideal) with `L (j + e) = p · L j`.
The group `Γ_K` of induced maps is a subgroup `Γ` of the `ℚ_[p]`-linear automorphisms of `V`.

* `lo e m = e ⌊(m-1)/e⌋ + 1` (Definition 2.4).
* `S Γ N` is the `ℤ_[p]`-span of all images `γ x` (`γ ∈ Γ`, `x ∈ N`); `S_K(m) = S Γ (L m)` (Definition 2.4).
* `Reaches F Γ N k`: all images of `N` lie in `L k` and some image does not lie in `L (k+1)`.
  For `N = L m` this says `a_K(m) = m - k` (Definition 2.4, without naming the valuation).
* `upper`: if `Γ` preserves `Λ = L 1` then every image of `L m` lies in `L (lo e m)` (Proposition 2.5).
* `S_eq_of_period`: if `L 1 ≤ S_K(r)` for `1 ≤ r ≤ e`, then `S_K(m) = L (lo e m)` for every integer `m`,
  and the minimal valuation `lo e m` is attained (`reaches_of_period`).
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge

/-! ## The function `lo` -/

/-- `lo e m = e * ⌊(m - 1) / e⌋ + 1`: the largest integer `≤ m` that is `≡ 1 (mod e)` (Definition 2.4). -/
def lo (e : ℕ) (m : ℤ) : ℤ := (e : ℤ) * ((m - 1) / (e : ℤ)) + 1

theorem lo_spec (e : ℕ) (m : ℤ) : m - lo e m = (m - 1) % (e : ℤ) := by
  have h := Int.mul_ediv_add_emod (m - 1) (e : ℤ)
  unfold lo
  omega

theorem lo_le (e : ℕ) (he : 0 < e) (m : ℤ) : lo e m ≤ m := by
  have h1 := lo_spec e m
  have h2 : 0 ≤ (m - 1) % (e : ℤ) := Int.emod_nonneg _ (by exact_mod_cast he.ne')
  omega

theorem lo_add_mul (e : ℕ) (he : 0 < e) (r q : ℤ) (hr1 : 1 ≤ r) (hre : r ≤ e) :
    lo e (q * e + r) = q * e + 1 := by
  unfold lo
  have hep : (0 : ℤ) < e := by exact_mod_cast he
  have : (q * (e : ℤ) + r - 1) / (e : ℤ) = q := by
    rw [show q * (e : ℤ) + r - 1 = (r - 1) + (e : ℤ) * q by ring, Int.add_mul_ediv_left _ _ hep.ne']
    rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    ring
  rw [this]
  ring

/-! ## Filtrations -/

variable (p : ℕ) [Fact p.Prime]

/-- A decreasing family of `ℤ_[p]`-lattices `L j = 𝔪^j` in a `ℚ_[p]`-vector space with `L (j+e) = p L j`. -/
structure Filtration (V : Type*) [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] where
  /-- the ramification index -/
  e : ℕ
  e_pos : 0 < e
  /-- `L j = 𝔪^j` -/
  L : ℤ → Submodule ℤ_[p] V
  anti : ∀ j, L (j + 1) ≤ L j
  /-- `𝔪^(j+e) = p 𝔪^j` -/
  shift : ∀ (j : ℤ) (x : V), x ∈ L (j + e) ↔ ((p : ℚ_[p])⁻¹ • x) ∈ L j
  /-- the inclusions are strict -/
  strict : ∀ j, ¬ L j ≤ L (j + 1)

variable {p}
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]

theorem padic_p_ne_zero : (p : ℚ_[p]) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

namespace Filtration

variable (F : Filtration p V)

theorem anti_le {j k : ℤ} (h : j ≤ k) : F.L k ≤ F.L j := by
  obtain ⟨n, rfl⟩ := Int.le.dest h
  induction n with
  | zero => simp
  | succ n ih =>
    have := F.anti (j + n)
    push_cast at *
    rw [← add_assoc]
    exact this.trans (ih (by omega))

theorem mem_shift_nat (n : ℕ) (j : ℤ) (x : V) :
    x ∈ F.L (j + n * F.e) ↔ ((p : ℚ_[p]) ^ (-(n : ℤ))) • x ∈ F.L j := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have h1 : j + ((n + 1 : ℕ) : ℤ) * F.e = (j + n * F.e) + F.e := by push_cast; ring
    rw [h1, F.shift, ih, smul_smul]
    congr 2
    rw [show -(((n + 1 : ℕ) : ℤ)) = -(n : ℤ) + (-1) by push_cast; ring, zpow_add₀ padic_p_ne_zero,
      zpow_neg_one]

/-- `x ∈ 𝔪^(j + q e)` iff `p^(-q) x ∈ 𝔪^j`, for every integer `q`. -/
theorem mem_shift_zpow (q j : ℤ) (x : V) :
    x ∈ F.L (j + q * F.e) ↔ ((p : ℚ_[p]) ^ (-q)) • x ∈ F.L j := by
  rcases Int.eq_nat_or_neg q with ⟨n, rfl | rfl⟩
  · exact F.mem_shift_nat n j x
  · have key := F.mem_shift_nat n (j + -(n : ℤ) * F.e) (((p : ℚ_[p]) ^ (n : ℤ)) • x)
    rw [show j + -(n : ℤ) * F.e + n * F.e = j by ring, smul_smul, ← zpow_add₀ padic_p_ne_zero,
      neg_add_cancel, zpow_zero, one_smul] at key
    rw [neg_neg]
    exact key.symm

/-- `x ∈ 𝔪^(j + q e)` iff `x = p^q z` with `z ∈ 𝔪^j`. -/
theorem mem_shift_iff_exists (q j : ℤ) (x : V) :
    x ∈ F.L (j + q * F.e) ↔ ∃ z ∈ F.L j, x = ((p : ℚ_[p]) ^ q) • z := by
  rw [F.mem_shift_zpow]
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    rw [smul_smul, ← zpow_add₀ padic_p_ne_zero, add_neg_cancel, zpow_zero, one_smul]
  · rintro ⟨z, hz, rfl⟩
    rwa [smul_smul, ← zpow_add₀ padic_p_ne_zero, neg_add_cancel, zpow_zero, one_smul]

end Filtration

/-! ## Images and spans -/

/-- the set of images `γ x` with `γ ∈ Γ`, `x ∈ N` -/
def imgSet (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (N : Submodule ℤ_[p] V) : Set V :=
  {y | ∃ γ ∈ Γ, ∃ x ∈ N, γ x = y}

/-- `S Γ N`: the `ℤ_[p]`-span of all images of `N` (no closure is taken), Definition 2.4. -/
def S (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (N : Submodule ℤ_[p] V) : Submodule ℤ_[p] V :=
  Submodule.span ℤ_[p] (imgSet Γ N)

/-- All images of `N` lie in `L k` and some image does not lie in `L (k+1)`: the largest drop of the
valuation on `N = 𝔪^m` is `m - k` (Definition 2.4). -/
def Reaches (F : Filtration p V) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (N : Submodule ℤ_[p] V) (k : ℤ) : Prop :=
  (∀ γ ∈ Γ, ∀ x ∈ N, γ x ∈ F.L k) ∧ ∃ γ ∈ Γ, ∃ x ∈ N, γ x ∉ F.L (k + 1)


/-! ## Scalar multiplication as a `ℤ_[p]`-linear map -/

/-- `x ↦ c • x` for `c : ℚ_[p]`, as a `ℤ_[p]`-linear map. -/
def smulL (c : ℚ_[p]) : V →ₗ[ℤ_[p]] V where
  toFun x := c • x
  map_add' x y := smul_add c x y
  map_smul' t x := by
    simp only [RingHom.id_apply]
    rw [← algebraMap_smul ℚ_[p] t x, ← algebraMap_smul ℚ_[p] t (c • x), smul_smul, smul_smul, mul_comm]

@[simp] theorem smulL_apply (c : ℚ_[p]) (x : V) : smulL c x = c • x := rfl

/-! ## Proposition 2.5: the trivial upper bound and the periodicity -/

/-- (Γ1) restricted to what is used: every `γ ∈ Γ` maps `Λ = L 1` into itself. -/
def PreservesL1 (F : Filtration p V) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) : Prop :=
  ∀ γ ∈ Γ, ∀ x ∈ F.L 1, γ x ∈ F.L 1

theorem lo_eq_one_add (e : ℕ) (m : ℤ) : lo e m = 1 + ((m - 1) / (e : ℤ)) * e := by
  unfold lo; ring

/-- Proposition 2.5: every image of `𝔪^m` lies in `𝔪^(lo m)`. -/
theorem upper (F : Filtration p V) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (hΓ : PreservesL1 F Γ) (m : ℤ) :
    ∀ γ ∈ Γ, ∀ x ∈ F.L m, γ x ∈ F.L (lo F.e m) := by
  intro γ hγ x hx
  have hx' : x ∈ F.L (lo F.e m) := F.anti_le (lo_le F.e F.e_pos m) hx
  rw [lo_eq_one_add, F.mem_shift_zpow] at hx' ⊢
  have := hΓ γ hγ _ hx'
  rwa [map_smul] at this

theorem S_le_lo (F : Filtration p V) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (hΓ : PreservesL1 F Γ) (m : ℤ) :
    S Γ (F.L m) ≤ F.L (lo F.e m) := by
  refine Submodule.span_le.mpr ?_
  rintro y ⟨γ, hγ, x, hx, rfl⟩
  exact upper F Γ hΓ m γ hγ x hx

/-- Proposition 2.5, periodicity: `S_K(r + q e) = p^q S_K(r)`. -/
theorem S_shift (F : Filtration p V) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (r q : ℤ) :
    S Γ (F.L (r + q * F.e)) = (S Γ (F.L r)).map (smulL ((p : ℚ_[p]) ^ q)) := by
  unfold S
  rw [← Submodule.span_image]
  congr 1
  ext y
  simp only [imgSet, Set.mem_setOf_eq, Set.mem_image, smulL_apply]
  constructor
  · rintro ⟨γ, hγ, x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (F.mem_shift_iff_exists q r x).1 hx
    exact ⟨γ z, ⟨γ, hγ, z, hz, rfl⟩, (map_smul γ _ z).symm⟩
  · rintro ⟨_, ⟨γ, hγ, z, hz, rfl⟩, rfl⟩
    exact ⟨γ, hγ, _, (F.mem_shift_iff_exists q r _).2 ⟨z, hz, rfl⟩, map_smul γ _ z⟩

/-- Proposition 2.5, `a_K(m + q e) = a_K(m)`: the largest drop of the valuation on `𝔪^m` is periodic in
`m` (the drop on `𝔪^m` is `m - k` exactly when `Reaches F Γ (F.L m) k`). -/
theorem reaches_shift (F : Filtration p V) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (m k q : ℤ) :
    Reaches F Γ (F.L (m + q * F.e)) (k + q * F.e) ↔ Reaches F Γ (F.L m) k := by
  have hp : (p : ℚ_[p]) ≠ 0 := padic_p_ne_zero
  have hc : ((p : ℚ_[p]) ^ (-q)) * (p : ℚ_[p]) ^ q = 1 := by
    rw [← zpow_add₀ hp, neg_add_cancel, zpow_zero]
  have e1 : ∀ x : V, x ∈ F.L m ↔ ((p : ℚ_[p]) ^ q) • x ∈ F.L (m + q * F.e) := by
    intro x; rw [F.mem_shift_zpow, smul_smul, hc, one_smul]
  have e2 : ∀ (j : ℤ) (y : V), y ∈ F.L (j + q * F.e) ↔ ((p : ℚ_[p]) ^ (-q)) • y ∈ F.L j :=
    fun j y => F.mem_shift_zpow q j y
  have hk1 : k + q * F.e + 1 = (k + 1) + q * F.e := by ring
  constructor
  · rintro ⟨hall, γ, hγ, x, hx, hnot⟩
    refine ⟨fun γ' hγ' x' hx' => ?_, γ, hγ, ((p : ℚ_[p]) ^ (-q)) • x, (e2 m x).1 hx, ?_⟩
    · have h := hall γ' hγ' _ ((e1 x').1 hx')
      rw [e2, map_smul, smul_smul, hc, one_smul] at h
      exact h
    · intro h
      rw [map_smul] at h
      apply hnot
      rw [hk1]
      exact (e2 (k + 1) _).2 h
  · rintro ⟨hall, γ, hγ, x, hx, hnot⟩
    refine ⟨fun γ' hγ' x' hx' => ?_, γ, hγ, ((p : ℚ_[p]) ^ q) • x, (e1 x).1 hx, ?_⟩
    · have h := hall γ' hγ' _ ((e2 m x').1 hx')
      rw [map_smul] at h
      exact (e2 k _).2 h
    · intro h
      rw [hk1, e2, map_smul, smul_smul, hc, one_smul] at h
      exact hnot h

/-- If some image of `N` lies outside `L (k+1)` whenever `S Γ N = L k`: the minimum is attained. -/
theorem reaches_of_S_eq (F : Filtration p V) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (N : Submodule ℤ_[p] V)
    (k : ℤ) (hup : ∀ γ ∈ Γ, ∀ x ∈ N, γ x ∈ F.L k) (hS : S Γ N = F.L k) : Reaches F Γ N k := by
  refine ⟨hup, ?_⟩
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  apply F.strict k
  rw [← hS]
  refine Submodule.span_le.mpr ?_
  rintro y ⟨γ, hγ, x, hx, rfl⟩
  exact hcon γ hγ x hx

/-- Write `m = q e + r` with `1 ≤ r ≤ e`. -/
theorem decomp (e : ℕ) (he : 0 < e) (m : ℤ) :
    ∃ q r : ℤ, 1 ≤ r ∧ r ≤ e ∧ m = r + q * e ∧ lo e m = 1 + q * e := by
  refine ⟨(m - 1) / e, (m - 1) % e + 1, ?_, ?_, ?_, lo_eq_one_add e m⟩
  · have := Int.emod_nonneg (m - 1) (show (e : ℤ) ≠ 0 by exact_mod_cast he.ne'); omega
  · have := Int.emod_lt_of_pos (m - 1) (show (0 : ℤ) < e by exact_mod_cast he); omega
  · have := Int.mul_ediv_add_emod (m - 1) (e : ℤ); linarith [mul_comm ((m - 1) / (e : ℤ)) (e : ℤ)]

/-- The exact value from one period: if `L 1 ≤ S_K(r)` for `1 ≤ r ≤ e`, then `S_K(m) = 𝔪^(lo m)`
for every integer `m`, and `a_K(m) = m - lo m = (m - 1) mod e` is attained. -/
theorem S_eq_of_period (F : Filtration p V) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (hΓ : PreservesL1 F Γ)
    (h : ∀ r : ℤ, 1 ≤ r → r ≤ F.e → F.L 1 ≤ S Γ (F.L r)) (m : ℤ) :
    S Γ (F.L m) = F.L (lo F.e m) := by
  refine le_antisymm (S_le_lo F Γ hΓ m) ?_
  obtain ⟨q, r, hr1, hre, rfl, hlo⟩ := decomp F.e F.e_pos m
  rw [hlo, S_shift]
  intro y hy
  obtain ⟨z, hz, rfl⟩ := (F.mem_shift_iff_exists q 1 y).1 hy
  exact ⟨z, h r hr1 hre hz, rfl⟩

theorem reaches_of_period (F : Filtration p V) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (hΓ : PreservesL1 F Γ)
    (h : ∀ r : ℤ, 1 ≤ r → r ≤ F.e → F.L 1 ≤ S Γ (F.L r)) (m : ℤ) :
    Reaches F Γ (F.L m) (lo F.e m) :=
  reaches_of_S_eq F Γ _ _ (upper F Γ hΓ m) (S_eq_of_period F Γ hΓ h m)

end LogShellEdge
