import LogShellEdge.Small

/-!
# Coordinates in the basis `y`, norms, and maps given on the basis

Elementary facts about `ℚ_p`, `ℤ_p` and the coordinates of elements of `Λ` that the arguments of
Sections 5, 6 and 8 use repeatedly.
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge

variable {p : ℕ} [Fact p.Prime]

/-- In `ℚ_p`, a norm `< 1` of an element of norm `≤ 1` is at most `‖p‖`. -/
theorem norm_le_p_of_lt_one {c : ℚ_[p]} (h : ‖c‖ ≤ 1) (h2 : ‖c‖ < 1) : ‖c‖ ≤ ‖(p : ℚ_[p])‖ := by
  set z : ℤ_[p] := ⟨c, h⟩
  have hz : ‖z‖ < 1 := h2
  obtain ⟨w, hw⟩ := (PadicInt.norm_lt_one_iff_dvd z).1 hz
  have h1 : ‖z‖ = ‖(p : ℤ_[p])‖ * ‖w‖ := by rw [hw, norm_mul]
  have h3 : ‖z‖ = ‖c‖ := rfl
  have h4 : ‖(p : ℤ_[p])‖ = ‖(p : ℚ_[p])‖ := by simp
  rw [← h3, h1, h4]
  exact mul_le_of_le_one_right (norm_nonneg _) w.norm_le_one

theorem norm_p_lt_one' : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one

theorem norm_p_pos : 0 < ‖(p : ℚ_[p])‖ := norm_pos_iff.mpr padic_p_ne_zero

/-- `‖a + b‖ = 1` if `‖a‖ = 1` and `‖b‖ ≤ ‖p‖`. -/
theorem norm_add_eq_one_of {a b : ℚ_[p]} (ha : ‖a‖ = 1) (hb : ‖b‖ ≤ ‖(p : ℚ_[p])‖) : ‖a + b‖ = 1 := by
  have hb1 : ‖b‖ < ‖a‖ := by rw [ha]; exact lt_of_le_of_lt hb norm_p_lt_one'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hb1), max_eq_left hb1.le, ha]

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A linear map is determined by the images of the basis vectors. -/
theorem apply_eq_sum (y : Module.Basis ι ℚ_[p] V) (γ : V →ₗ[ℚ_[p]] V) (x : V) :
    γ x = ∑ i, y.repr x i • γ (y i) := by
  conv_lhs => rw [← y.sum_repr x]
  rw [map_sum]
  simp only [map_smul]

/-- A map acting on the basis by `y j ↦ y j + y k` (other basis vectors fixed) sends `x` to
`x + x_j y_k`. -/
theorem apply_of_move (y : Module.Basis ι ℚ_[p] V) (γ : V →ₗ[ℚ_[p]] V) (j k : ι)
    (hγ : ∀ i, γ (y i) = if i = j then y j + y k else y i) (x : V) :
    γ x = x + y.repr x j • y k := by
  rw [apply_eq_sum y γ x]
  have : ∀ i, y.repr x i • γ (y i) = y.repr x i • y i + (if i = j then y.repr x j • y k else 0) := by
    intro i
    rw [hγ i]
    split_ifs with h
    · subst h; rw [smul_add]
    · rw [add_zero]
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), y.sum_repr]

theorem repr_add_smul (y : Module.Basis ι ℚ_[p] V) (x : V) (c : ℚ_[p]) (k i : ι) :
    y.repr (x + c • y k) i = y.repr x i + (if i = k then c else 0) := by
  simp [Finsupp.single_apply, eq_comm]

theorem repr_sub (y : Module.Basis ι ℚ_[p] V) (x z : V) (i : ι) :
    y.repr (x - z) i = y.repr x i - y.repr z i := by simp

theorem repr_smul (y : Module.Basis ι ℚ_[p] V) (c : ℚ_[p]) (x : V) (i : ι) :
    y.repr (c • x) i = c * y.repr x i := by simp

namespace SmallField

variable (K : SmallField p V ι)

theorem coeff_le_one {x : V} (hx : x ∈ K.F.L 1) (i : ι) : ‖K.y.repr x i‖ ≤ 1 := (K.hΛ x).1 hx i

/-- an element of `Λ` not in `pΛ` has a coordinate of norm `1` -/
theorem exists_coeff_unit {x : V} (hx : x ∈ K.F.L 1) (hx' : x ∉ K.F.L (1 + K.F.e)) :
    ∃ i, ‖K.y.repr x i‖ = 1 := by
  rw [K.mem_pL1_iff] at hx'
  push_neg at hx'
  obtain ⟨i, hi⟩ := hx'
  refine ⟨i, le_antisymm (K.coeff_le_one hx i) ?_⟩
  by_contra hlt
  push_neg at hlt
  exact absurd (norm_le_p_of_lt_one (K.coeff_le_one hx i) hlt) (not_le.mpr hi)

/-- `pΛ ⊆ Λ` -/
theorem pL1_le_L1 : K.F.L (1 + K.F.e) ≤ K.F.L 1 :=
  K.F.anti_le (by have := K.F.e_pos; omega)

end SmallField

end LogShellEdge
