import LogShellEdge.Cyclo

/-!
# Section 8.4: unions of images (Proposition 8.13)

`A_K(m) = ⋃_{γ ∈ Γ} γ(𝔪^m)` is `imgSet Γ (L m)`.

* `prop813a_*`: small fields of odd degree (Proposition 8.13(a)), with Kondo's `Sp` on `W` and the
  automorphism of Theorem 6.5 (`s = 1`).
* `prop813b`: the cyclotomic boundary (Proposition 8.13(b)).
* `prop813c_*`: the unions of (a) for `m = n e`, `f = 1`, and of (b) for `f = 1`, `r = e`, `d ≥ 4`, are not
  additive groups; their relative measures are `1 - 1/p + p^(-d)` and `1 - 1/p + p^(1-d)`, i.e. their
  images in `Λ/pΛ ≅ F_p^d` have `(p-1) p^(d-1) + 1` and `(p-1) p^(d-1) + p` elements.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LogShellEdge

variable {p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]

/-- the alternating form on `W = ⟨y 1, …, y (2g)⟩` in odd degree (pairs `(2k+1, 2k+2)`,
`⟨y (2k+1), y (2k+2)⟩ = -1`), in coordinates -/
def oddForm {g : ℕ} (y : Module.Basis (Fin (2 * g + 1)) ℚ_[p] V) (x v : V) : ℚ_[p] :=
  ∑ k : Fin g, (y.repr x (vIdx k) * y.repr v (uIdx k) - y.repr x (uIdx k) * y.repr v (vIdx k))

/-! ## The odd block, reduced modulo `p` -/

/-- the coordinates `c 1, …, c (2g)`, as a vector of `F_p^(2g)` -/
def blkO {g : ℕ} (c : Fin (2 * g + 1) → ZMod p) : Fin (2 * g) → ZMod p :=
  fun j => c ⟨j.val + 1, by omega⟩

/-- a block vector, extended by `0` on the index `0` -/
def unblkO {g : ℕ} (u : Fin (2 * g) → ZMod p) : Fin (2 * g + 1) → ZMod p :=
  fun i => if h : 1 ≤ i.val then u ⟨i.val - 1, by omega⟩ else 0

theorem blkO_unblkO {g : ℕ} (u : Fin (2 * g) → ZMod p) : blkO (unblkO u) = u := by
  funext j
  simp only [blkO, unblkO]
  rw [dif_pos (by simp)]
  congr 1

theorem blkO_add {g : ℕ} (c c' : Fin (2 * g + 1) → ZMod p) : blkO (c + c') = blkO c + blkO c' := rfl

theorem blkO_sub {g : ℕ} (c c' : Fin (2 * g + 1) → ZMod p) : blkO (c - c') = blkO c - blkO c' := rfl

theorem blkO_smul {g : ℕ} (a : ZMod p) (c : Fin (2 * g + 1) → ZMod p) :
    blkO (a • c) = a • blkO c := rfl

theorem blkO_single {g : ℕ} (i : Fin (2 * g + 1)) (hi : 1 ≤ i.val) (a : ZMod p) :
    blkO (Pi.single i a) = Pi.single ⟨i.val - 1, by omega⟩ a := by
  funext j
  simp only [blkO, Pi.single_apply, Fin.ext_iff]
  by_cases h : j.val = i.val - 1
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- a vector of `F_p^(2g+1)` is determined by its coordinate `0` and its block -/
theorem eq_of_blkO {g : ℕ} {c c' : Fin (2 * g + 1) → ZMod p} (h0 : c 0 = c' 0)
    (hb : blkO c = blkO c') : c = c' := by
  funext i
  by_cases hi : i.val = 0
  · have : i = 0 := Fin.ext hi
    rw [this]
    exact h0
  · have := congrFun hb ⟨i.val - 1, by omega⟩
    simp only [blkO] at this
    have e : (⟨i.val - 1 + 1, by omega⟩ : Fin (2 * g + 1)) = i := Fin.ext (by simp; omega)
    rwa [e] at this

theorem norm_oddForm_le {g : ℕ} (y : Module.Basis (Fin (2 * g + 1)) ℚ_[p] V) {x v : V}
    (hx : Integ y x) (hv : Integ y v) : ‖oddForm y x v‖ ≤ 1 := by
  unfold oddForm
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun k _ =>
    norm_sub_le_one (norm_mul_le_one (hx _) (hv _)) (norm_mul_le_one (hx _) (hv _)))

/-- `oddForm` reduces to the standard symplectic form on the block -/
theorem red_oddForm {g : ℕ} (y : Module.Basis (Fin (2 * g + 1)) ℚ_[p] V) {x v : V}
    (hx : Integ y x) (hv : Integ y v) :
    red (oddForm y x v) = Symp.omega (blkO (rd y x)) (blkO (rd y v)) := by
  unfold oddForm Symp.omega
  rw [red_sum _ _ (fun k _ =>
    norm_sub_le_one (norm_mul_le_one (hx _) (hv _)) (norm_mul_le_one (hx _) (hv _)))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [red_sub (norm_mul_le_one (hx _) (hv _)) (norm_mul_le_one (hx _) (hv _)),
    red_mul (hx _) (hv _), red_mul (hx _) (hv _)]
  rfl

/-- An odd-degree small field with [Kondo26, Lemma 3.3] (`Sp(W)` fixing `y_1`, here its transvections)
and Theorem 6.5 (for `s = 1`). -/
structure OddKondo (p : ℕ) [Fact p.Prime] (V : Type*) [AddCommGroup V] [Module ℚ_[p] V]
    [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V] (g : ℕ) extends OddSmall p V g where
  hg : 1 ≤ g
  /-- [Kondo26, Lemma 3.3]: transvections of `W`, fixing `y_1` -/
  kondoT : ∀ v : V, y.repr v 0 = 0 → (∀ i, ‖y.repr v i‖ ≤ 1) →
    ∀ a : ℤ_[p], ∃ γ ∈ Γ, ∀ x, γ x = x + ((a : ℚ_[p]) * oddForm y x v) • v
  /-- the integer `s` of the Jannsen-Wingberg presentation -/
  s : ℕ
  /-- `s = 1` since `p ∤ e` -/
  hs : s = 1
  /-- Theorem 6.5 (proved for `s = 1`) -/
  lift : s = 1 → ∃ φ ∈ Γ, ∀ i : Fin (2 * g + 1),
    φ (y i) - (if i = 0 then y 0 + y ⟨1, by omega⟩ else y i) ∈ F.L (1 + F.e)

namespace OddKondo

variable {g : ℕ} (K : OddKondo p V g)

theorem integ_iff (x : V) : x ∈ K.F.L 1 ↔ Integ K.y x := K.hΛ x

theorem mem_pL1_iff_rd {x : V} (hx : Integ K.y x) : x ∈ K.F.L (1 + K.F.e) ↔ rd K.y x = 0 := by
  rw [K.toSmallField.mem_pL1_iff, rd_eq_zero_iff K.y hx]

theorem hΓinteg : ∀ γ ∈ K.Γ, ∀ x, Integ K.y x → Integ K.y (γ x) := fun γ hγ x hx =>
  (K.integ_iff _).1 (K.hΓ1 γ hγ x ((K.integ_iff x).2 hx))

/-- `Γ` preserves `pΛ = 𝔪^(1+e)` -/
theorem hΓpL1 : ∀ γ ∈ K.Γ, ∀ x ∈ K.F.L (1 + K.F.e), γ x ∈ K.F.L (1 + K.F.e) := by
  intro γ hγ x hx
  rw [K.F.shift] at hx ⊢
  have := K.hΓ1 γ hγ _ hx
  rwa [map_smul] at this

/-- `Γ` fixes the coordinate of `y_1` (since it preserves the trace) -/
theorem coord0_inv {γ : V ≃ₗ[ℚ_[p]] V} (hγ : γ ∈ K.Γ) (x : V) :
    K.y.repr (γ x) 0 = K.y.repr x 0 := by
  have h := K.hΓ2 γ hγ x
  rw [K.toOddSmall.tau_eq, K.toOddSmall.tau_eq x] at h
  exact mul_right_cancel₀ K.toOddSmall.tau_y0_ne h

/-- elements with the same reduced coordinates are congruent modulo `pΛ` -/
theorem sub_mem_of_rd {x x' : V} (hx : Integ K.y x) (hx' : Integ K.y x')
    (h : rd K.y x = rd K.y x') : x - x' ∈ K.F.L (1 + K.F.e) :=
  (K.toSmallField.mem_pL1_iff _).2 ((rd_eq_iff K.y hx hx').1 h)

/-- the transvections of `W`, reduced modulo `p` -/
theorem transv_liftO (v : Fin (2 * g) → ZMod p) (a : ZMod p) :
    ∃ γ ∈ K.Γ, ∀ x, Integ K.y x → blkO (rd K.y (γ x)) = Symp.transv v a (blkO (rd K.y x)) := by
  set w := liftV K.y (unblkO v) with hw
  have hw0 : K.y.repr w 0 = 0 := repr_liftV_eq_zero K.y (by simp [unblkO])
  have hwI : Integ K.y w := integ_liftV K.y _
  obtain ⟨γ, hγ, hγx⟩ := K.kondoT w hw0 hwI ((a.val : ℕ) : ℤ_[p])
  refine ⟨γ, hγ, fun x hx => ?_⟩
  have ha : ‖((((a.val : ℕ) : ℤ_[p])) : ℚ_[p])‖ ≤ 1 := (((a.val : ℕ) : ℤ_[p])).2
  have hc : ‖((((a.val : ℕ) : ℤ_[p])) : ℚ_[p]) * oddForm K.y x w‖ ≤ 1 :=
    norm_mul_le_one ha (norm_oddForm_le K.y hx hwI)
  rw [hγx x, rd_add K.y hx (integ_smul K.y hc hwI), rd_smul K.y hc hwI, rd_liftV,
    red_mul ha (norm_oddForm_le K.y hx hwI), red_coe, toZMod_natCast_val,
    red_oddForm K.y hx hwI, rd_liftV, blkO_add, blkO_smul, blkO_unblkO]
  rfl

/-- the automorphism of Theorem 6.5, reduced modulo `p`: `ȳ₀ ↦ ȳ₀ + ȳ₁` -/
theorem exists_phi : ∃ φ ∈ K.Γ, ∀ x, Integ K.y x →
    rd K.y (φ x) = rd K.y x + rd K.y x 0 •
      Pi.single (⟨1, by have := K.hg; omega⟩ : Fin (2 * g + 1)) 1 := by
  obtain ⟨φ, hφ, hφy⟩ := K.lift K.hs
  refine ⟨φ, hφ, fun x hx => ?_⟩
  set i1 : Fin (2 * g + 1) := ⟨1, by have := K.hg; omega⟩ with hi1
  have hD : φ x - (x + K.y.repr x 0 • K.y i1) ∈ K.F.L (1 + K.F.e) := by
    have hsum : φ x = ∑ i, K.y.repr x i • φ (K.y i) :=
      apply_eq_sum K.y (φ : V →ₗ[ℚ_[p]] V) x
    have hxsum : x + K.y.repr x 0 • K.y i1 =
        ∑ i, K.y.repr x i • (if i = 0 then K.y 0 + K.y i1 else K.y i) := by
      have : ∀ i, K.y.repr x i • (if i = 0 then K.y 0 + K.y i1 else K.y i) =
          K.y.repr x i • K.y i + (if i = 0 then K.y.repr x 0 • K.y i1 else 0) := by
        intro i
        split_ifs with h
        · subst h; rw [smul_add]
        · rw [add_zero]
      rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), K.y.sum_repr]
    rw [hsum, hxsum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [← smul_sub]
    exact smul_mem_of_norm_le _ (hx i) (hφy i)
  have hφI : Integ K.y (φ x) := K.hΓinteg φ hφ x hx
  have hsI : Integ K.y (K.y.repr x 0 • K.y i1) := integ_smul K.y (hx 0) (integ_basis K.y i1)
  have h := (rd_eq_iff K.y hφI (integ_add K.y hx hsI)).2 ((K.toSmallField.mem_pL1_iff _).1 hD)
  rw [h, rd_add K.y hx hsI, rd_smul K.y (hx 0) (integ_basis K.y i1), rd_basis]
  rfl

/-- the translations `x̄ ↦ x̄ + x̄₀ w` of `W̄` (conjugates of the automorphism of Theorem 6.5) -/
theorem exists_translateO (w : Fin (2 * g) → ZMod p) :
    ∃ γ ∈ K.Γ, ∀ x, Integ K.y x → blkO (rd K.y (γ x)) = blkO (rd K.y x) + rd K.y x 0 • w := by
  have hg := K.hg
  set e : Fin (2 * g) → ZMod p := Pi.single ⟨0, by omega⟩ 1 with he
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    rw [he, Pi.single_eq_same, Pi.zero_apply] at this
    exact one_ne_zero this
  refine exists_translate K.y blkO K.hΓinteg K.transv_liftO (fun x => rd K.y x 0)
    (fun γ hγ x => by simp only [rd_apply, K.coord0_inv hγ]) he0 ?_ w
  obtain ⟨φ, hφ, hφx⟩ := K.exists_phi
  refine ⟨φ, hφ, fun x hx => ?_⟩
  rw [hφx x hx, blkO_add, blkO_smul, blkO_single _ (by simp)]
  rfl

/-- the orbit of an element with `x̄₀ ≠ 0` is the fibre of `τ̄` -/
theorem exists_hit_unit {x z : V} (hx : Integ K.y x) (hz : Integ K.y z) (hx0 : rd K.y x 0 ≠ 0)
    (hz0 : rd K.y z 0 ≠ 0) : ∃ γ ∈ K.Γ, ∃ t : ℤ_[p], x - γ (t • z) ∈ K.F.L (1 + K.F.e) := by
  set s : ZMod p := rd K.y x 0 * (rd K.y z 0)⁻¹ with hs
  set t : ℤ_[p] := ((s.val : ℕ) : ℤ_[p]) with ht
  have htI : Integ K.y (t • z) := integ_zsmul K.y t hz
  have h0 : rd K.y (t • z) 0 = rd K.y x 0 := by
    rw [rd_zsmul K.y t hz, ht, toZMod_natCast_val, Pi.smul_apply, smul_eq_mul, hs, mul_assoc,
      inv_mul_cancel₀ hz0, mul_one]
  obtain ⟨γ, hγ, hγx⟩ :=
    K.exists_translateO ((rd K.y x 0)⁻¹ • (blkO (rd K.y x) - blkO (rd K.y (t • z))))
  refine ⟨γ, hγ, t, K.sub_mem_of_rd hx (K.hΓinteg γ hγ _ htI) ?_⟩
  apply eq_of_blkO
  · show rd K.y x 0 = red (K.y.repr (γ (t • z)) 0)
    rw [K.coord0_inv hγ]
    exact h0.symm
  · rw [hγx _ htI, h0, smul_smul, mul_inv_cancel₀ hx0, one_smul]
    abel

/-- the transvections are transitive on `W̄ ∖ {0}` -/
theorem exists_hit_ker {x w : V} (hx : Integ K.y x) (hw : Integ K.y w) (hx0 : rd K.y x 0 = 0)
    (hw0 : rd K.y w 0 = 0) (hxb : blkO (rd K.y x) ≠ 0) (hwb : blkO (rd K.y w) ≠ 0) :
    ∃ γ ∈ K.Γ, x - γ w ∈ K.F.L (1 + K.F.e) := by
  obtain ⟨γ, hγ, hγx⟩ := exists_move K.y blkO K.hΓinteg K.transv_liftO hwb hxb
  refine ⟨γ, hγ, K.sub_mem_of_rd hx (K.hΓinteg γ hγ _ hw) ?_⟩
  apply eq_of_blkO
  · show rd K.y x 0 = red (K.y.repr (γ w) 0)
    rw [K.coord0_inv hγ]
    exact hx0.trans hw0.symm
  · rw [hγx w hw rfl]

/-- `A_K(r) = Λ` if `f (e + 1 - r) ≥ 2` -/
theorem imgSet_eq_L1 (r : ℕ) (hr1 : 1 ≤ r) (hre : r ≤ K.F.e) (hf : 2 ≤ K.f * (K.F.e + 1 - r)) :
    imgSet K.Γ (K.F.L r) = K.F.L 1 := by
  have hLr1 : K.F.L r ≤ K.F.L 1 := K.F.anti_le (by exact_mod_cast hr1)
  have hpLr : K.F.L (1 + K.F.e) ≤ K.F.L r := K.F.anti_le (by have := hre; omega)
  ext x
  constructor
  · rintro ⟨γ, hγ, z, hz, rfl⟩
    exact K.hΓ1 γ hγ z (hLr1 hz)
  · intro hx
    have hxI := (K.integ_iff x).1 hx
    by_cases h0 : rd K.y x 0 = 0
    · by_cases hb : blkO (rd K.y x) = 0
      · have : x ∈ K.F.L (1 + K.F.e) :=
          (K.mem_pL1_iff_rd hxI).2 (eq_of_blkO (by rw [h0]; rfl) (by rw [hb]; rfl))
        exact ⟨1, K.Γ.one_mem, x, hpLr this, rfl⟩
      · obtain ⟨w, hw, hw', hτw⟩ := K.toOddSmall.exists_kernel_elt r hr1 hre hf
        have hwI := (K.integ_iff w).1 (hLr1 hw)
        have hw0 : rd K.y w 0 = 0 := by
          rw [rd_apply, red_eq_zero_iff (hwI 0), ← K.toOddSmall.norm_tau_eq]
          exact hτw
        have hwb : blkO (rd K.y w) ≠ 0 := by
          intro hwb
          exact hw' ((K.mem_pL1_iff_rd hwI).2 (eq_of_blkO (by rw [hw0]; rfl) (by rw [hwb]; rfl)))
        obtain ⟨γ, hγ, hγx⟩ := K.exists_hit_ker hxI hwI h0 hw0 hb hwb
        exact mem_imgSet_of_sub_mem hpLr K.hΓpL1 hγ hw hγx
    · have hpcr : K.pc ∈ K.F.L r := K.F.anti_le (by exact_mod_cast hre) K.hpc
      have hpcI := (K.integ_iff _).1 (hLr1 hpcr)
      have hpc0 : rd K.y K.pc 0 ≠ 0 :=
        red_ne_zero_of_norm_eq_one (by rw [← K.toOddSmall.norm_tau_eq]; exact K.hpcτ)
      obtain ⟨γ, hγ, t, ht⟩ := K.exists_hit_unit hxI hpcI h0 hpc0
      exact mem_imgSet_of_sub_mem hpLr K.hΓpL1 hγ ((K.F.L r).smul_mem t hpcr) ht

/-- `A_K(e) = {x ∈ Λ : Tr x ∉ p² ℤ_p} ∪ pΛ` when `𝔪^e / pΛ = F_p p̄` -/
theorem imgSet_e_eq (pv : V) (hpv : pv ∈ K.F.L K.F.e) (hpvτ : ‖K.τ pv‖ = 1)
    (hLe : ∀ z ∈ K.F.L K.F.e, ∃ a : ℤ_[p], z - a • pv ∈ K.F.L (1 + K.F.e)) :
    imgSet K.Γ (K.F.L K.F.e) = {x | x ∈ K.F.L 1 ∧ (‖K.τ x‖ = 1 ∨ x ∈ K.F.L (1 + K.F.e))} := by
  have he1 : (1 : ℤ) ≤ K.F.e := by exact_mod_cast K.F.e_pos
  have hLe1 : K.F.L K.F.e ≤ K.F.L 1 := K.F.anti_le he1
  have hpLe : K.F.L (1 + K.F.e) ≤ K.F.L K.F.e := K.F.anti_le (by omega)
  have hpvL1 : pv ∈ K.F.L 1 := hLe1 hpv
  ext x
  constructor
  · rintro ⟨γ, hγ, z, hz, rfl⟩
    refine ⟨K.hΓ1 γ hγ z (hLe1 hz), ?_⟩
    obtain ⟨a, ha⟩ := hLe z hz
    by_cases hau : ‖(a : ℚ_[p])‖ = 1
    · left
      rw [K.hΓ2 γ hγ]
      have : K.τ z = (a : ℚ_[p]) * K.τ pv + K.τ (z - a • pv) := by
        rw [map_sub, zpS_smul, map_smul, smul_eq_mul]
        ring
      rw [this]
      exact norm_add_eq_one_of (by rw [norm_mul, hau, hpvτ, mul_one])
        (K.toOddSmall.norm_tau_le_p ha)
    · right
      have hale : ‖(a : ℚ_[p])‖ ≤ ‖(p : ℚ_[p])‖ := norm_le_p_of_lt_one a.2 (lt_of_le_of_ne a.2 hau)
      have hapv : a • pv ∈ K.F.L (1 + K.F.e) := by
        rw [zpS_smul]
        exact K.toOddSmall.smul_mem_pL1 hpvL1 hale
      have hz' : z ∈ K.F.L (1 + K.F.e) := by
        have := add_mem ha hapv
        rwa [sub_add_cancel] at this
      exact K.hΓpL1 γ hγ z hz'
  · rintro ⟨hx, hx'⟩
    rcases hx' with hτ | hp
    · have hxI := (K.integ_iff x).1 hx
      have hx0 : rd K.y x 0 ≠ 0 :=
        red_ne_zero_of_norm_eq_one (by rw [← K.toOddSmall.norm_tau_eq]; exact hτ)
      have hpvI := (K.integ_iff _).1 hpvL1
      have hpv0 : rd K.y pv 0 ≠ 0 :=
        red_ne_zero_of_norm_eq_one (by rw [← K.toOddSmall.norm_tau_eq]; exact hpvτ)
      obtain ⟨γ, hγ, t, ht⟩ := K.exists_hit_unit hxI hpvI hx0 hpv0
      exact mem_imgSet_of_sub_mem hpLe K.hΓpL1 hγ ((K.F.L K.F.e).smul_mem t hpv) ht
    · exact ⟨1, K.Γ.one_mem, x, hpLe hp, rfl⟩

/-- Proposition 8.13(a), first part: if `f ≥ 2`, or `f = 1` and `e ∤ m`, the union of the images of
`𝔪^m` is all of `𝔪^(lo m)`. -/
theorem prop813a_full (m : ℤ) (hcase : 2 ≤ K.f ∨ ¬ ((K.F.e : ℤ) ∣ m)) :
    imgSet K.Γ (K.F.L m) = K.F.L (lo K.F.e m) := by
  obtain ⟨q, r, hr1, hre, rfl, hlo⟩ := decomp K.F.e K.F.e_pos m
  rw [hlo]
  lift r to ℕ using (by omega)
  have hf : 2 ≤ K.f * (K.F.e + 1 - r) := by
    rcases hcase with hf | hdvd
    · calc 2 ≤ K.f := hf
        _ = K.f * 1 := (mul_one _).symm
        _ ≤ K.f * (K.F.e + 1 - r) := Nat.mul_le_mul_left _ (by omega)
    · have hre' : r ≠ K.F.e := by
        intro h; apply hdvd; subst h; exact ⟨q + 1, by ring⟩
      have hr' : r < K.F.e := lt_of_le_of_ne (by exact_mod_cast hre) hre'
      calc 2 ≤ K.F.e + 1 - r := by omega
        _ = 1 * (K.F.e + 1 - r) := (one_mul _).symm
        _ ≤ K.f * (K.F.e + 1 - r) := Nat.mul_le_mul_right _ K.toOddSmall.f_pos
  rw [imgSet_shift, K.imgSet_eq_L1 r (by exact_mod_cast hr1) (by exact_mod_cast hre) hf,
    L_shift_set]

/-- Proposition 8.13(a), second part: if `f = 1` (so `d = e`), with `p ∈ 𝔪^e` generating `𝔪^e/pΛ` and
`Tr(p) ∈ p ℤ_p^×`, then `A_K(n e) = p^(n-1) ({x ∈ Λ : Tr x ∉ p² ℤ_p} ∪ pΛ)`. -/
theorem prop813a_tr (hf : K.f = 1) (pv : V) (hpv : pv ∈ K.F.L K.F.e) (hpvτ : ‖K.τ pv‖ = 1)
    (hLe : ∀ z ∈ K.F.L K.F.e, ∃ a : ℤ_[p], z - a • pv ∈ K.F.L (1 + K.F.e)) (n : ℤ) :
    imgSet K.Γ (K.F.L (n * K.F.e)) =
      (smulL ((p : ℚ_[p]) ^ (n - 1))) '' {x | x ∈ K.F.L 1 ∧ (‖K.τ x‖ = 1 ∨ x ∈ K.F.L (1 + K.F.e))} := by
  -- `hf` is not needed: `hLe` already says `𝔪^e / pΛ = F_p p̄`
  have _hf := hf
  rw [show n * (K.F.e : ℤ) = K.F.e + (n - 1) * K.F.e by ring, imgSet_shift,
    K.imgSet_e_eq pv hpv hpvτ hLe]

/-- Proposition 8.13(c) for (a): the union for `m = e` (`f = 1`, `d = e ≥ 3`) is not an additive group. -/
theorem prop813c_a_not_add (hf : K.f = 1) (pv : V) (hpv : pv ∈ K.F.L K.F.e) (hpvτ : ‖K.τ pv‖ = 1)
    (hLe : ∀ z ∈ K.F.L K.F.e, ∃ a : ℤ_[p], z - a • pv ∈ K.F.L (1 + K.F.e)) :
    ∃ x ∈ imgSet K.Γ (K.F.L K.F.e), ∃ x' ∈ imgSet K.Γ (K.F.L K.F.e), x + x' ∉ imgSet K.Γ (K.F.L K.F.e) := by
  -- `hf` is not needed: `hLe` already says `𝔪^e / pΛ = F_p p̄`
  have _hf := hf
  rw [K.imgSet_e_eq pv hpv hpvτ hLe]
  have hg := K.hg
  set i1 : Fin (2 * g + 1) := ⟨1, by omega⟩ with hi1
  have hi10 : i1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [hi1] at this
  have hτ1 : K.τ (K.y i1) = 0 := K.hker i1 hi10
  refine ⟨K.y 0, ⟨K.toSmallField.y_mem 0, Or.inl K.hτ0⟩, -K.y 0 + K.y i1,
    ⟨add_mem (neg_mem (K.toSmallField.y_mem 0)) (K.toSmallField.y_mem i1), Or.inl ?_⟩, ?_⟩
  · rw [map_add, map_neg, hτ1, add_zero, norm_neg]
    exact K.hτ0
  · rintro ⟨-, h⟩
    rw [add_neg_cancel_left] at h
    rcases h with h | h
    · rw [hτ1, norm_zero] at h
      exact zero_ne_one h
    · have := (K.toSmallField.mem_pL1_iff _).1 h i1
      rw [Module.Basis.repr_self, Finsupp.single_eq_same, norm_one] at this
      exact absurd this (not_le.mpr norm_p_lt_one')

end OddKondo

namespace CycloData

variable {g : ℕ} (K : CycloData p V g)

/-- the translations `(t, u) ↦ (t, u + t w)` modulo `R` (from `M` and the transvections) -/
theorem exists_translateC (w : Fin (2 * (g - 1)) → ZMod p) :
    ∃ γ ∈ K.Γ, ∀ x, Integ K.b x → blkC (rd K.b (γ x)) = blkC (rd K.b x) + rd K.b x K.i1 • w := by
  by_cases hg2 : 2 ≤ g
  · set e : Fin (2 * (g - 1)) → ZMod p := Pi.single ⟨1, by omega⟩ 1 with he
    have he0 : e ≠ 0 := by
      intro h
      have := congrFun h ⟨1, by omega⟩
      rw [he, Pi.single_eq_same, Pi.zero_apply] at this
      exact one_ne_zero this
    have he' : e = Pi.single (Symp.od (⟨0, by omega⟩ : Fin (g - 1))) 1 := rfl
    refine exists_translate K.b blkC K.hΓinteg K.transv_lift (fun x => rd K.b x K.i1)
      (fun γ hγ x => by simp only [rd_apply, K.coord1_inv hγ]) he0 ?_ w
    obtain ⟨M, hM, hMx⟩ := K.exists_M hg2
    obtain ⟨T, hT, hTx⟩ := K.transv_lift e (-1)
    have hMrd : ∀ x, Integ K.b x → blkC (rd K.b (M x)) =
        blkC (rd K.b x) + (rd K.b x K.i1 - rd K.b x ⟨2, by omega⟩) • e := by
      intro x hx
      have hzI : Integ K.b ((K.α : ℚ_[p]) • K.b K.iz) := integ_smul K.b K.α.2 (integ_basis K.b _)
      have hw₀I : Integ K.b ((K.α : ℚ_[p]) • K.b K.iz + K.b ⟨3, by omega⟩) :=
        integ_add K.b hzI (integ_basis K.b _)
      have hc : ‖K.b.repr x K.i1 - K.b.repr x ⟨2, by omega⟩‖ ≤ 1 := norm_sub_le_one (hx _) (hx _)
      rw [hMx x, rd_add K.b hx (integ_smul K.b hc hw₀I), rd_smul K.b hc hw₀I,
        red_sub (hx _) (hx _), rd_add K.b hzI (integ_basis K.b _),
        rd_smul K.b K.α.2 (integ_basis K.b _), rd_basis, rd_basis, blkC_add, blkC_smul, blkC_add,
        blkC_smul, blkC_single_lt _ (by simp [iz]), blkC_single _ (by simp), smul_zero, zero_add]
      rfl
    refine ⟨T * M, K.Γ.mul_mem hT hM, fun x hx => ?_⟩
    have hom : Symp.omega (blkC (rd K.b x) + (rd K.b x K.i1 - rd K.b x ⟨2, by omega⟩) • e) e =
        -rd K.b x ⟨2, by omega⟩ := by
      rw [he', Symp.omega_single_od]
      congr 1
      rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne (Symp.ev_ne_od _ _), smul_zero, add_zero]
      rfl
    rw [LinearEquiv.mul_apply, hTx _ (K.hΓinteg M hM x hx), hMrd x hx, Symp.transv_apply, hom,
      neg_one_mul, neg_neg, add_assoc, ← add_smul, sub_add_cancel]
  · exact ⟨1, K.Γ.one_mem, fun x _ => funext (fun j => absurd j.2 (by omega))⟩

/-- the orbit of an element with `x̄₁ ≠ 0`, modulo `R`, is the fibre of `τ̄` -/
theorem exists_hit_unitC {x z : V} (hx : Integ K.b x) (hz : Integ K.b z)
    (hx1 : rd K.b x K.i1 ≠ 0) (hz1 : rd K.b z K.i1 ≠ 0) :
    ∃ γ ∈ K.Γ, ∃ t : ℤ_[p], x - γ (t • z) ∈ K.F.L p := by
  set s : ZMod p := rd K.b x K.i1 * (rd K.b z K.i1)⁻¹ with hs
  set t : ℤ_[p] := ((s.val : ℕ) : ℤ_[p]) with ht
  have htI : Integ K.b (t • z) := integ_zsmul K.b t hz
  have h1 : rd K.b (t • z) K.i1 = rd K.b x K.i1 := by
    rw [rd_zsmul K.b t hz, ht, toZMod_natCast_val, Pi.smul_apply, smul_eq_mul, hs, mul_assoc,
      inv_mul_cancel₀ hz1, mul_one]
  obtain ⟨γ, hγ, hγx⟩ :=
    K.exists_translateC ((rd K.b x K.i1)⁻¹ • (blkC (rd K.b x) - blkC (rd K.b (t • z))))
  refine ⟨γ, hγ, t, K.sub_mem_Lp_of_rd hx (K.hΓinteg γ hγ _ htI) ?_ ?_⟩
  · show rd K.b x K.i1 = red (K.b.repr (γ (t • z)) K.i1)
    rw [K.coord1_inv hγ]
    exact h1.symm
  · rw [hγx _ htI, h1, smul_smul, mul_inv_cancel₀ hx1, one_smul]
    abel

/-- the transvections are transitive on `Ū ∖ {0}` -/
theorem exists_hit_kerC {x w : V} (hx : Integ K.b x) (hw : Integ K.b w)
    (hx1 : rd K.b x K.i1 = 0) (hw1 : rd K.b w K.i1 = 0) (hxb : blkC (rd K.b x) ≠ 0)
    (hwb : blkC (rd K.b w) ≠ 0) : ∃ γ ∈ K.Γ, x - γ w ∈ K.F.L p := by
  obtain ⟨γ, hγ, hγx⟩ := exists_move K.b blkC K.hΓinteg K.transv_lift hwb hxb
  refine ⟨γ, hγ, K.sub_mem_Lp_of_rd hx (K.hΓinteg γ hγ _ hw) ?_ ?_⟩
  · show rd K.b x K.i1 = red (K.b.repr (γ w) K.i1)
    rw [K.coord1_inv hγ]
    exact hx1.trans hw1.symm
  · rw [hγx w hw rfl]

/-- the counting step: if `dim (𝔪^r / pΛ) ≥ 3` then `𝔪^r` contains `w` with `τ̄ w = 0` and a
nonzero block -/
theorem exists_ker_block (r : ℕ) (hr2 : 2 ≤ r) (hre : r ≤ K.F.e)
    (hdim : 2 ≤ K.f * (K.F.e + 1 - r)) : ∃ w ∈ K.F.L r, rd K.b w K.i1 = 0 ∧ blkC (rd K.b w) ≠ 0 := by
  have hLrΛ : K.F.L r ≤ K.Λ := K.L_le_Λ (by exact_mod_cast hr2)
  by_contra H
  push Not at H
  have hle := card_quot_le (A := K.F.L r) (P := pMul K.Λ) (T := ZMod p × ZMod p)
    (fun x => (rd K.b x K.iz, rd K.b x K.i1)) (by
      intro x hx x' hx' hxx'
      simp only [Prod.mk.injEq] at hxx'
      have hxI := (K.integ_iff _).1 (hLrΛ hx)
      have hx'I := (K.integ_iff _).1 (hLrΛ hx')
      have hdI : Integ K.b (x - x') := integ_sub K.b hxI hx'I
      have h1 : rd K.b (x - x') K.i1 = 0 := by
        rw [rd_sub K.b hxI hx'I, Pi.sub_apply, hxx'.2, sub_self]
      have hb := H _ (sub_mem hx hx') h1
      rw [K.mem_pMul_iff_rd hdI]
      apply eq_of_blkC
      · intro i hi
        rcases K.fin_lt_two i hi with rfl | rfl
        · rw [rd_sub K.b hxI hx'I, Pi.sub_apply, hxx'.1, sub_self]
          rfl
        · rw [h1]
          rfl
      · rw [hb]
        rfl)
  rw [K.hcard r hr2 hre, Nat.card_prod, Nat.card_zmod] at hle
  have hp2 := (Fact.out : p.Prime).two_le
  have h3 : p ^ 3 ≤ p ^ (K.f * (K.F.e + 1 - r) + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : p * p < p ^ 3 := by
    rw [pow_succ, pow_two]
    exact lt_mul_of_one_lt_right (by positivity) (by omega)
  omega

/-- for `f = 1`, the elements of `𝔪^e` with `τ̄ = 0` lie in `𝔪^p` (`𝔪^e / pΛ = F_p z̄ ⊕ F_p x̄₁`) -/
theorem Le_ker (hf : K.f = 1) : ∀ z ∈ K.F.L K.F.e, rd K.b z K.i1 = 0 → z ∈ K.F.L p := by
  have he2 : 2 ≤ K.F.e := by
    have h := K.hdeg
    have := K.hg
    have := K.he
    rw [hf, mul_one] at h
    omega
  obtain ⟨x₁, hx₁, hτx₁⟩ := K.htr K.F.e (by omega) le_rfl
  have hLeΛ : K.F.L K.F.e ≤ K.Λ := K.L_le_Λ (by exact_mod_cast he2)
  have hLpLe : K.F.L p ≤ K.F.L K.F.e := K.Lp_le (by exact_mod_cast K.e_lt_p.le)
  have hx₁I := (K.integ_iff _).1 (hLeΛ hx₁)
  have hx₁1 : rd K.b x₁ K.i1 ≠ 0 :=
    red_ne_zero_of_norm_eq_one (by rw [← K.norm_tau_eq]; exact hτx₁)
  set ψ : ZMod p × ZMod p → V :=
    fun q => ((q.1.val : ℕ) : ℤ_[p]) • K.b K.iz + ((q.2.val : ℕ) : ℤ_[p]) • x₁ with hψ
  have hψI : ∀ q, Integ K.b (ψ q) := fun q =>
    integ_add K.b (integ_zsmul K.b _ (integ_basis K.b _)) (integ_zsmul K.b _ hx₁I)
  have hψrd : ∀ q, rd K.b (ψ q) = q.1 • Pi.single K.iz 1 + q.2 • rd K.b x₁ := by
    intro q
    rw [hψ, rd_add K.b (integ_zsmul K.b _ (integ_basis K.b _)) (integ_zsmul K.b _ hx₁I),
      rd_zsmul K.b _ (integ_basis K.b _), rd_zsmul K.b _ hx₁I, toZMod_natCast_val,
      toZMod_natCast_val, rd_basis]
  have hψA : ∀ q, ψ q ∈ K.F.L K.F.e := fun q =>
    add_mem ((K.F.L K.F.e).smul_mem _ (hLpLe K.lemma87.1)) ((K.F.L K.F.e).smul_mem _ hx₁)
  have hinj : ∀ q q', ψ q - ψ q' ∈ pMul K.Λ → q = q' := by
    intro q q' h
    rw [K.mem_pMul_iff_rd (integ_sub K.b (hψI q) (hψI q')), rd_sub K.b (hψI q) (hψI q'), hψrd,
      hψrd, sub_eq_zero] at h
    have h1 := congrFun h K.i1
    have h0 := congrFun h K.iz
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (Ne.symm K.iz_ne_i1),
      Pi.single_eq_same, mul_zero, zero_add, mul_one] at h1 h0
    have hq2 : q.2 = q'.2 := mul_right_cancel₀ hx₁1 h1
    rw [hq2] at h0
    exact Prod.ext (add_right_cancel h0) hq2
  haveI : Finite (↥(K.F.L K.F.e) ⧸ (pMul K.Λ).comap (K.F.L K.F.e).subtype) :=
    Nat.finite_of_card_ne_zero (by
      rw [K.hcard K.F.e he2 le_rfl]
      exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hcardle : Nat.card (↥(K.F.L K.F.e) ⧸ (pMul K.Λ).comap (K.F.L K.F.e).subtype) ≤
      Nat.card (ZMod p × ZMod p) := by
    rw [K.hcard K.F.e he2 le_rfl, Nat.card_prod, Nat.card_zmod, hf,
      show K.F.e + 1 - K.F.e = 1 by omega]
    exact le_of_eq (by ring)
  have key := exists_sub_mem_of_card ψ hψA hinj hcardle
  intro z hz hz1
  obtain ⟨q, hq⟩ := key z hz
  have hzI := (K.integ_iff _).1 (hLeΛ hz)
  have hrdz : rd K.b z = rd K.b (ψ q) := by
    rw [← sub_eq_zero, ← rd_sub K.b hzI (hψI q), ← K.mem_pMul_iff_rd (integ_sub K.b hzI (hψI q))]
    exact hq
  have hq2 : q.2 = 0 := by
    have := congrFun hrdz K.i1
    rw [hψrd, hz1, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      Pi.single_eq_of_ne (Ne.symm K.iz_ne_i1), smul_zero, zero_add, smul_eq_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hx₁1
  have hψq : ψ q ∈ K.F.L p := by
    rw [hψ]
    simp only
    rw [hq2, ZMod.val_zero, Nat.cast_zero, zero_smul, add_zero]
    exact (K.F.L p).smul_mem _ K.lemma87.1
  have := add_mem (K.pMul_le_Lp hq) hψq
  rwa [sub_add_cancel] at this

/-- `A_K(r) = Λ` for `2 ≤ r ≤ e` unless `f = 1` and `r = e` -/
theorem imgSet_eq_Λ (r : ℕ) (hr2 : 2 ≤ r) (hre : r ≤ K.F.e) (hnot : ¬ (K.f = 1 ∧ r = K.F.e)) :
    imgSet K.Γ (K.F.L r) = K.Λ := by
  have hLrΛ : K.F.L r ≤ K.Λ := K.L_le_Λ (by exact_mod_cast hr2)
  have hLpLr : K.F.L p ≤ K.F.L r :=
    K.Lp_le (by exact_mod_cast (le_of_lt (lt_of_le_of_lt hre K.e_lt_p)))
  ext x
  constructor
  · rintro ⟨γ, hγ, z, hz, rfl⟩
    exact K.hΓΛ γ hγ z (hLrΛ hz)
  · intro hx
    have hxI := (K.integ_iff x).1 hx
    by_cases h1 : rd K.b x K.i1 = 0
    · by_cases hb : blkC (rd K.b x) = 0
      · have h := K.sub_mem_Lp_of_rd hxI (integ_zero K.b) (by rw [h1, rd_zero]; rfl)
          (by rw [hb, rd_zero]; rfl)
        rw [sub_zero] at h
        exact ⟨1, K.Γ.one_mem, x, hLpLr h, rfl⟩
      · have hdim : 2 ≤ K.f * (K.F.e + 1 - r) := by
          by_cases hf : K.f = 1
          · have : r ≠ K.F.e := fun h => hnot ⟨hf, h⟩
            rw [hf, one_mul]
            omega
          · have := K.f_pos
            calc 2 ≤ K.f := by omega
              _ = K.f * 1 := (mul_one _).symm
              _ ≤ K.f * (K.F.e + 1 - r) := Nat.mul_le_mul_left _ (by omega)
        obtain ⟨w, hw, hw1, hwb⟩ := K.exists_ker_block r hr2 hre hdim
        have hwI := (K.integ_iff _).1 (hLrΛ hw)
        obtain ⟨γ, hγ, hγx⟩ := K.exists_hit_kerC hxI hwI h1 hw1 hb hwb
        exact mem_imgSet_of_sub_mem hLpLr K.hΓp hγ hw hγx
    · obtain ⟨x₁, hx₁, hτx₁⟩ := K.htr r (by omega) hre
      have hx₁I := (K.integ_iff _).1 (hLrΛ hx₁)
      have hx₁1 : rd K.b x₁ K.i1 ≠ 0 :=
        red_ne_zero_of_norm_eq_one (by rw [← K.norm_tau_eq]; exact hτx₁)
      obtain ⟨γ, hγ, t, ht⟩ := K.exists_hit_unitC hxI hx₁I h1 hx₁1
      exact mem_imgSet_of_sub_mem hLpLr K.hΓp hγ ((K.F.L r).smul_mem t hx₁) ht

/-- for `f = 1`: `A_K(e) = {x ∈ Λ : Tr x ∉ p² ℤ_p} ∪ 𝔪^p` -/
theorem imgSet_e_eqC (hf : K.f = 1) :
    imgSet K.Γ (K.F.L K.F.e) = {x | x ∈ K.Λ ∧ (‖K.τ x‖ = 1 ∨ x ∈ K.F.L p)} := by
  have he2 : 2 ≤ K.F.e := by
    have h := K.hdeg
    have := K.hg
    have := K.he
    rw [hf, mul_one] at h
    omega
  have hLeΛ : K.F.L K.F.e ≤ K.Λ := K.L_le_Λ (by exact_mod_cast he2)
  have hLpLe : K.F.L p ≤ K.F.L K.F.e := K.Lp_le (by exact_mod_cast K.e_lt_p.le)
  ext x
  constructor
  · rintro ⟨γ, hγ, z, hz, rfl⟩
    refine ⟨K.hΓΛ γ hγ z (hLeΛ hz), ?_⟩
    by_cases hτz : ‖K.τ z‖ = 1
    · left
      rw [K.hΓ2 γ hγ]
      exact hτz
    · right
      have hzI := (K.integ_iff _).1 (hLeΛ hz)
      have hz1 : rd K.b z K.i1 = 0 := by
        rw [rd_apply, red_eq_zero_iff (hzI _), ← K.norm_tau_eq]
        exact lt_of_le_of_ne (by rw [K.norm_tau_eq]; exact hzI _) hτz
      exact K.hΓp γ hγ z (K.Le_ker hf z hz hz1)
  · rintro ⟨hx, hx'⟩
    rcases hx' with hτ | hp
    · have hxI := (K.integ_iff x).1 hx
      have hx1 : rd K.b x K.i1 ≠ 0 :=
        red_ne_zero_of_norm_eq_one (by rw [← K.norm_tau_eq]; exact hτ)
      obtain ⟨x₁, hx₁, hτx₁⟩ := K.htr K.F.e (by omega) le_rfl
      have hx₁I := (K.integ_iff _).1 (hLeΛ hx₁)
      have hx₁1 : rd K.b x₁ K.i1 ≠ 0 :=
        red_ne_zero_of_norm_eq_one (by rw [← K.norm_tau_eq]; exact hτx₁)
      obtain ⟨γ, hγ, t, ht⟩ := K.exists_hit_unitC hxI hx₁I hx1 hx₁1
      exact mem_imgSet_of_sub_mem hLpLe K.hΓp hγ ((K.F.L K.F.e).smul_mem t hx₁) ht
    · exact ⟨1, K.Γ.one_mem, x, hLpLe hp, rfl⟩

/-- Proposition 8.13(b). Write `m = r + n e` with `1 ≤ r ≤ e`. -/
theorem prop813b (r n : ℤ) (hr1 : 1 ≤ r) (hre : r ≤ K.F.e) :
    (r = 1 → imgSet K.Γ (K.F.L (r + n * K.F.e)) = K.F.L (r + n * K.F.e)) ∧
    (2 ≤ r → ¬ (K.f = 1 ∧ r = K.F.e) → imgSet K.Γ (K.F.L (r + n * K.F.e)) = pPow n K.Λ) ∧
    (K.f = 1 → r = K.F.e → imgSet K.Γ (K.F.L (r + n * K.F.e)) =
      (smulL ((p : ℚ_[p]) ^ n)) '' {x | x ∈ K.Λ ∧ (‖K.τ x‖ = 1 ∨ x ∈ K.F.L p)}) := by
  refine ⟨fun hr => ?_, fun hr hnot => ?_, fun hf hr => ?_⟩
  · subst hr
    ext x
    constructor
    · rintro ⟨γ, hγ, z, hz, rfl⟩
      exact K.hΓ1n n γ hγ z hz
    · intro hx
      exact ⟨1, K.Γ.one_mem, x, hx, rfl⟩
  · lift r to ℕ using (by omega)
    rw [imgSet_shift, K.imgSet_eq_Λ r (by exact_mod_cast hr) (by exact_mod_cast hre)
      (fun h => hnot ⟨h.1, by exact_mod_cast h.2⟩), pPow, Submodule.map_coe]
  · subst hr
    rw [imgSet_shift, K.imgSet_e_eqC hf]

/-- Proposition 8.13(c) for (b): for `f = 1`, `r = e` and `d ≥ 4` the union is not an additive group. -/
theorem prop813c_b_not_add (hf : K.f = 1) (hg2 : 2 ≤ g) :
    ∃ x ∈ imgSet K.Γ (K.F.L K.F.e), ∃ x' ∈ imgSet K.Γ (K.F.L K.F.e), x + x' ∉ imgSet K.Γ (K.F.L K.F.e) := by
  rw [K.imgSet_e_eqC hf]
  set i2 : Fin (2 * g) := ⟨2, by omega⟩ with hi2
  have hb1Λ : K.b K.i1 ∈ K.Λ := (K.integ_iff _).2 (integ_basis K.b _)
  have hb2Λ : K.b i2 ∈ K.Λ := (K.integ_iff _).2 (integ_basis K.b _)
  have hτ2 : K.τ (K.b i2) = 0 := K.hker i2 (by simp [hi2])
  refine ⟨K.b K.i1, ⟨hb1Λ, Or.inl K.norm_tau_b1⟩, -K.b K.i1 + K.b i2,
    ⟨add_mem (neg_mem hb1Λ) hb2Λ, Or.inl ?_⟩, ?_⟩
  · rw [map_add, map_neg, hτ2, add_zero, norm_neg]
    exact K.norm_tau_b1
  · rintro ⟨-, h⟩
    rw [add_neg_cancel_left] at h
    rcases h with h | h
    · rw [hτ2, norm_zero] at h
      exact zero_ne_one h
    · obtain ⟨t, ht⟩ := K.lemma87.2 _ h
      have hne : K.iz ≠ i2 := by
        intro h'
        have := congrArg Fin.val h'
        simp [iz, hi2] at this
      have := (K.mem_pMul_iff _).1 ht i2
      rw [zpS_smul, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
        Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.single_eq_same,
        Finsupp.single_apply, if_neg hne, smul_zero, sub_zero, norm_one] at this
      exact absurd this (not_le.mpr norm_p_lt_one')

end CycloData

/-- `#{v ∈ F_p^(d'+1) : v j ≠ 0} = (p - 1) p^d'` -/
theorem card_coord_ne_zero (d' : ℕ) (j : Fin (d' + 1)) :
    Fintype.card {v : Fin (d' + 1) → ZMod p // v j ≠ 0} = (p - 1) * p ^ d' := by
  let e : {v : Fin (d' + 1) → ZMod p // v j ≠ 0} ≃ {a : ZMod p // a ≠ 0} × (Fin d' → ZMod p) :=
    { toFun := fun v => (⟨v.1 j, v.2⟩, fun i => v.1 (j.succAbove i))
      invFun := fun q => ⟨j.insertNth q.1.1 q.2, by rw [Fin.insertNth_apply_same]; exact q.1.2⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext i
        refine Fin.succAboveCases j ?_ (fun k => ?_) i
        · simp [Fin.insertNth_apply_same]
        · simp [Fin.insertNth_apply_succAbove]
      right_inv := fun q => by
        ext
        · simp [Fin.insertNth_apply_same]
        · simp [Fin.insertNth_apply_succAbove] }
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    Fintype.card_subtype_compl, ZMod.card, Fintype.card_subtype_eq]

/-- Proposition 8.13(c), the counts in `F_p^d`: the image in `Λ/pΛ` of the union of (a) is
`{v | v 0 ≠ 0} ∪ {0}`, of size `(p-1) p^(d-1) + 1`; the image of the union of (b) is
`{v | v 1 ≠ 0} ∪ F_p z̄`, of size `(p-1) p^(d-1) + p`. -/
theorem card_union_a (d : ℕ) (hd : 1 ≤ d) :
    Fintype.card {v : Fin d → ZMod p // v ⟨0, by omega⟩ ≠ 0 ∨ v = 0} = (p - 1) * p ^ (d - 1) + 1 := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hdisj : Disjoint (fun v : Fin (d' + 1) → ZMod p => v ⟨0, by omega⟩ ≠ 0) (fun v => v = 0) := by
    intro r hrp hrq v hv
    exact (hrp v hv) (by rw [hrq v hv]; rfl)
  rw [Fintype.card_subtype_or_disjoint _ _ hdisj, card_coord_ne_zero, Fintype.card_subtype_eq,
    Nat.add_sub_cancel]

theorem card_union_b (d : ℕ) (hd : 2 ≤ d) :
    Fintype.card {v : Fin d → ZMod p // v ⟨1, by omega⟩ ≠ 0 ∨ ∀ i : Fin d, i.val ≠ 0 → v i = 0} =
      (p - 1) * p ^ (d - 1) + p := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hdisj : Disjoint (fun v : Fin (d' + 1) → ZMod p => v ⟨1, by omega⟩ ≠ 0)
      (fun v => ∀ i : Fin (d' + 1), i.val ≠ 0 → v i = 0) := by
    intro r hrp hrq v hv
    exact (hrp v hv) (hrq v hv ⟨1, by omega⟩ (by simp))
  have e : {v : Fin (d' + 1) → ZMod p // ∀ i : Fin (d' + 1), i.val ≠ 0 → v i = 0} ≃ ZMod p :=
    { toFun := fun v => v.1 0
      invFun := fun a => ⟨Pi.single 0 a, fun i hi => by
        rw [Pi.single_apply, if_neg (fun h => hi (by rw [h]; rfl))]⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext i
        show (Pi.single 0 (v.1 0) : Fin (d' + 1) → ZMod p) i = v.1 i
        by_cases hi : i = 0
        · subst hi; simp
        · rw [Pi.single_apply, if_neg hi, v.2 i (fun h => hi (Fin.ext h))]
      right_inv := fun a => by simp }
  rw [Fintype.card_subtype_or_disjoint _ _ hdisj, card_coord_ne_zero, Fintype.card_congr e,
    ZMod.card, Nat.add_sub_cancel]

end LogShellEdge
