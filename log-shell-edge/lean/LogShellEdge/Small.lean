import LogShellEdge.Basic

/-!
# The data of a small p-adic field (Sections 2-3 of the note)

`SmallField p V ι` collects what Sections 2-6 use about a finite extension `K/ℚ_p` with `e ≤ p - 2`:
the filtration `𝔪^j`, the group `Γ_K`, the basis `y_i = log rec⁻¹(x_i)` of `Λ = 𝔪`, and the trace.
Every field is an input whose source is given in its docstring; nothing here is proved about a
concrete field.  The lemmas below are elementary consequences used later.
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge

variable {p : ℕ} [Fact p.Prime]

/-- The data of a small field used in Sections 2-6. -/
structure SmallField (p : ℕ) [Fact p.Prime] (V : Type*) [AddCommGroup V] [Module ℚ_[p] V]
    [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V] (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- `L j = 𝔪^j`, with `e` the ramification index -/
  F : Filtration p V
  /-- the group `Γ_K` of maps induced by automorphisms of `G_K` (Section 2.2, [Hoshi]) -/
  Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)
  /-- the residue degree -/
  f : ℕ
  hdeg : Fintype.card ι = F.e * f
  /-- `y_i = log rec_K⁻¹(x_i)`: a `ℚ_p`-basis of `K` ([HN, Lemma 1.3], [Kondo, §1]) -/
  y : Module.Basis ι ℚ_[p] V
  /-- `Λ = log U¹ = 𝔪` (Lemma 2.2(b)) and `y` is a `ℤ_p`-basis of `Λ` (Lemma 3.2) -/
  hΛ : ∀ x, x ∈ F.L 1 ↔ ∀ i, ‖y.repr x i‖ ≤ 1
  /-- `τ = Tr_{K/ℚ_p} / p` -/
  τ : V →ₗ[ℚ_[p]] ℚ_[p]
  /-- (Γ1): `γ(Λ) ⊆ Λ` ([Hoshi], Proposition 2.3) -/
  hΓ1 : PreservesL1 F Γ
  /-- (Γ2): `Tr ∘ γ = Tr` ([HN, Lemma 2.3(ii)], Proposition 2.3) -/
  hΓ2 : ∀ γ ∈ Γ, ∀ x, τ (γ x) = τ x
  /-- `dim_{F_p} 𝔪^r / p𝔪 = f (e + 1 - r)` for `1 ≤ r ≤ e + 1` (structure of `𝔪^j/𝔪^{j+1}`) -/
  hcard : ∀ r : ℕ, 1 ≤ r → r ≤ F.e + 1 →
    Nat.card (↥(F.L r) ⧸ (F.L (F.e + 1 : ℕ)).comap (F.L r).subtype) = p ^ (f * (F.e + 1 - r))
  /-- the element `p c` of Lemma 2.2(d) -/
  pc : V
  /-- `p c ∈ 𝔪^e` (Lemma 2.2(d)) -/
  hpc : pc ∈ F.L F.e
  /-- `Tr(p c) ∈ p ℤ_p^×` (Lemma 2.2(d)) -/
  hpcτ : ‖τ pc‖ = 1

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## `ℤ_p`-scalars from elements of `ℚ_p` of norm `≤ 1` -/

/-- an element of `ℚ_p` of norm `≤ 1`, as an element of `ℤ_p` -/
def zp (c : ℚ_[p]) (h : ‖c‖ ≤ 1) : ℤ_[p] := ⟨c, h⟩

theorem zp_smul (c : ℚ_[p]) (h : ‖c‖ ≤ 1) (x : V) : zp c h • x = c • x := by
  rw [← algebraMap_smul ℚ_[p] (zp c h) x]
  rfl

theorem zpS_smul (t : ℤ_[p]) (x : V) : t • x = (t : ℚ_[p]) • x := by
  rw [← algebraMap_smul ℚ_[p] t x]
  rfl

/-! ## Spans of orbits -/

/-- the `ℤ_p`-span of the `Γ`-orbit of `w` -/
def spanImg (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (w : V) : Submodule ℤ_[p] V :=
  Submodule.span ℤ_[p] {z | ∃ γ ∈ Γ, γ w = z}

theorem mem_spanImg_self (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (w : V) : w ∈ spanImg Γ w :=
  Submodule.subset_span ⟨1, Γ.one_mem, rfl⟩

theorem mem_spanImg_of_mem (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (w : V) {γ : V ≃ₗ[ℚ_[p]] V} (hγ : γ ∈ Γ) :
    γ w ∈ spanImg Γ w :=
  Submodule.subset_span ⟨γ, hγ, rfl⟩

/-- the span of an orbit is stable under `Γ` -/
theorem spanImg_stable (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (w : V) {γ : V ≃ₗ[ℚ_[p]] V} (hγ : γ ∈ Γ)
    {z : V} (hz : z ∈ spanImg Γ w) : γ z ∈ spanImg Γ w := by
  have key : spanImg Γ w ≤ (spanImg Γ w).comap ((γ : V →ₗ[ℚ_[p]] V).restrictScalars ℤ_[p]) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨δ, hδ, rfl⟩
    show γ (δ w) ∈ spanImg Γ w
    exact Submodule.subset_span ⟨γ * δ, Γ.mul_mem hγ hδ, rfl⟩
  exact key hz

theorem spanImg_le_S (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) {N : Submodule ℤ_[p] V} {w : V} (hw : w ∈ N) :
    spanImg Γ w ≤ S Γ N := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨γ, hγ, rfl⟩
  exact Submodule.subset_span ⟨γ, hγ, w, hw, rfl⟩

/-- `S Γ N` is stable under `Γ` -/
theorem S_stable (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (N : Submodule ℤ_[p] V) {γ : V ≃ₗ[ℚ_[p]] V}
    (hγ : γ ∈ Γ) {z : V} (hz : z ∈ S Γ N) : γ z ∈ S Γ N := by
  have key : S Γ N ≤ (S Γ N).comap ((γ : V →ₗ[ℚ_[p]] V).restrictScalars ℤ_[p]) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨δ, hδ, x, hx, rfl⟩
    show γ (δ x) ∈ S Γ N
    exact Submodule.subset_span ⟨γ * δ, Γ.mul_mem hγ hδ, x, hx, rfl⟩
  exact key hz

namespace SmallField

variable (K : SmallField p V ι)

/-- coordinates in the basis `y` -/
theorem sum_repr (x : V) : x = ∑ i, K.y.repr x i • K.y i := (K.y.sum_repr x).symm

theorem y_mem (i : ι) : K.y i ∈ K.F.L 1 := by
  rw [K.hΛ]
  intro j
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

/-- a `ℤ_p`-combination of the basis vectors lies in `Λ` -/
theorem mem_L1_of_coeff (x : V) (hx : ∀ i, ‖K.y.repr x i‖ ≤ 1) : x ∈ K.F.L 1 := (K.hΛ x).2 hx

/-- `x ∈ pΛ = 𝔪^(e+1)` iff all coordinates have norm `≤ ‖p‖`. -/
theorem mem_pL1_iff (x : V) : x ∈ K.F.L (1 + K.F.e) ↔ ∀ i, ‖K.y.repr x i‖ ≤ ‖(p : ℚ_[p])‖ := by
  rw [K.F.shift, K.hΛ]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_inv]
  have hp : 0 < ‖(p : ℚ_[p])‖ := norm_pos_iff.mpr padic_p_ne_zero
  constructor
  · intro h i
    have := h i
    rw [inv_mul_le_iff₀ hp, mul_one] at this
    exact this
  · intro h i
    rw [inv_mul_le_iff₀ hp, mul_one]
    exact h i

/-- If the `ℤ_p`-span `N` contains every basis vector, it contains `Λ`. -/
theorem L1_le_of_basis (N : Submodule ℤ_[p] V) (h : ∀ i, K.y i ∈ N) : K.F.L 1 ≤ N := by
  intro x hx
  rw [K.hΛ] at hx
  rw [K.sum_repr x]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  rw [← zp_smul _ (hx i)]
  exact N.smul_mem _ (h i)

end SmallField

end LogShellEdge
