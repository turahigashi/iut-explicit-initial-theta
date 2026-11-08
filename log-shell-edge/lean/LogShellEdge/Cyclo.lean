import LogShellEdge.Radical
import LogShellEdge.MainTheorem
import LogShellEdge.Symplectic
import LogShellEdge.Residue
import LogShellEdge.RealizeCyclo

/-!
# Section 8.2: the cyclotomic boundary (`p` odd, `e = p - 1`, `μ_p ⊂ K`)

`CycloData` collects the inputs. Indices are 0-based in the basis `b` of Lemma 8.6:
`b 0 = z`, `b 1 = y_2`, `b j = y_{j+1}` (`j ≥ 2`); the pairs are `(b (2k), b (2k+1))`, and the block
`U = ⟨b 2, …, b (2g-1)⟩` carries the alternating form `blockForm` (`⟨b (2k), b (2k+1)⟩ = -1`).

* `lemma87`: `R = 𝔪^p / pΛ` is the line spanned by `z` (Lemma 8.7).
* `lemma88`: `S_K(r) = Λ` for `2 ≤ r ≤ e` (Lemma 8.8).
* `thm89`: Theorem 8.9.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LogShellEdge

variable {p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]

/-- the alternating form on the block `⟨b 2, …, b (2g-1)⟩`, in coordinates:
`∑_{k ≥ 1} (x_{2k+1} v_{2k} - x_{2k} v_{2k+1})` -/
def blockForm {g : ℕ} (b : Module.Basis (Fin (2 * g)) ℚ_[p] V) (x v : V) : ℚ_[p] :=
  ∑ k : Fin g, if 1 ≤ k.val then
    b.repr x ⟨2 * k.val + 1, by omega⟩ * b.repr v ⟨2 * k.val, by omega⟩ -
      b.repr x ⟨2 * k.val, by omega⟩ * b.repr v ⟨2 * k.val + 1, by omega⟩
  else 0

/-- `p^n N` for an integer `n` -/
def pPow (n : ℤ) (N : Submodule ℤ_[p] V) : Submodule ℤ_[p] V := N.map (smulL ((p : ℚ_[p]) ^ n))

/-! ## The block, reduced modulo `p` -/

/-- the block coordinates `c 2, …, c (2g-1)`, as a vector of `F_p^(2(g-1))` -/
def blkC {g : ℕ} (c : Fin (2 * g) → ZMod p) : Fin (2 * (g - 1)) → ZMod p :=
  fun j => c ⟨j.val + 2, by omega⟩

/-- a block vector, extended by `0` on the indices `0, 1` -/
def unblkC {g : ℕ} (u : Fin (2 * (g - 1)) → ZMod p) : Fin (2 * g) → ZMod p :=
  fun i => if h : 2 ≤ i.val then u ⟨i.val - 2, by omega⟩ else 0

theorem blkC_unblkC {g : ℕ} (u : Fin (2 * (g - 1)) → ZMod p) : blkC (unblkC u) = u := by
  funext j
  simp only [blkC, unblkC]
  rw [dif_pos (by simp)]
  congr 1

theorem blkC_add {g : ℕ} (c c' : Fin (2 * g) → ZMod p) : blkC (c + c') = blkC c + blkC c' := rfl

theorem blkC_sub {g : ℕ} (c c' : Fin (2 * g) → ZMod p) : blkC (c - c') = blkC c - blkC c' := rfl

theorem blkC_smul {g : ℕ} (a : ZMod p) (c : Fin (2 * g) → ZMod p) : blkC (a • c) = a • blkC c := rfl

theorem blkC_single_lt {g : ℕ} (i : Fin (2 * g)) (hi : i.val < 2) (a : ZMod p) :
    blkC (Pi.single i a) = 0 := by
  funext j
  simp only [blkC, Pi.zero_apply]
  rw [Pi.single_apply, if_neg]
  intro h
  have := congrArg Fin.val h
  simp only at this
  omega

theorem blkC_single {g : ℕ} (i : Fin (2 * g)) (hi : 2 ≤ i.val) (a : ZMod p) :
    blkC (Pi.single i a) = Pi.single ⟨i.val - 2, by omega⟩ a := by
  funext j
  simp only [blkC, Pi.single_apply, Fin.ext_iff]
  by_cases h : j.val = i.val - 2
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- a vector of `F_p^(2g)` is determined by its coordinates `0, 1` and its block -/
theorem eq_of_blkC {g : ℕ} {c c' : Fin (2 * g) → ZMod p}
    (h0 : ∀ i : Fin (2 * g), i.val < 2 → c i = c' i) (hb : blkC c = blkC c') : c = c' := by
  funext i
  by_cases hi : i.val < 2
  · exact h0 i hi
  · have := congrFun hb ⟨i.val - 2, by omega⟩
    simp only [blkC] at this
    have e : (⟨i.val - 2 + 2, by omega⟩ : Fin (2 * g)) = i := Fin.ext (by simp; omega)
    rwa [e] at this

theorem sum_shift {M : Type*} [AddCommMonoid M] : ∀ (g : ℕ) (G : Fin g → M),
    ∑ k : Fin g, (if 1 ≤ k.val then G k else 0) = ∑ i : Fin (g - 1), G ⟨i.val + 1, by omega⟩
  | 0, G => by simp
  | g' + 1, G => by
    rw [Fin.sum_univ_succ, Fin.val_zero, if_neg (by omega), zero_add]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.val_succ, if_pos (by omega)]
    rfl

theorem norm_blockForm_le {g : ℕ} (b : Module.Basis (Fin (2 * g)) ℚ_[p] V) {x v : V}
    (hx : Integ b x) (hv : Integ b v) : ‖blockForm b x v‖ ≤ 1 := by
  unfold blockForm
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun k _ => ?_)
  split_ifs
  · exact norm_sub_le_one (norm_mul_le_one (hx _) (hv _)) (norm_mul_le_one (hx _) (hv _))
  · simp

/-- `blockForm` reduces to the standard symplectic form on the block -/
theorem red_blockForm {g : ℕ} (b : Module.Basis (Fin (2 * g)) ℚ_[p] V) {x v : V}
    (hx : Integ b x) (hv : Integ b v) :
    red (blockForm b x v) = Symp.omega (blkC (rd b x)) (blkC (rd b v)) := by
  unfold blockForm
  rw [red_sum _ _ (fun k _ => by
    split_ifs
    · exact norm_sub_le_one (norm_mul_le_one (hx _) (hv _)) (norm_mul_le_one (hx _) (hv _))
    · simp)]
  have h1 : ∀ k : Fin g, red (if 1 ≤ k.val then
      b.repr x ⟨2 * k.val + 1, by omega⟩ * b.repr v ⟨2 * k.val, by omega⟩ -
        b.repr x ⟨2 * k.val, by omega⟩ * b.repr v ⟨2 * k.val + 1, by omega⟩ else 0) =
      if 1 ≤ k.val then (rd b x ⟨2 * k.val + 1, by omega⟩ * rd b v ⟨2 * k.val, by omega⟩ -
        rd b x ⟨2 * k.val, by omega⟩ * rd b v ⟨2 * k.val + 1, by omega⟩) else 0 := by
    intro k
    split_ifs
    · rw [red_sub (norm_mul_le_one (hx _) (hv _)) (norm_mul_le_one (hx _) (hv _)),
        red_mul (hx _) (hv _), red_mul (hx _) (hv _)]
      rfl
    · exact red_zero
  rw [Finset.sum_congr rfl (fun k _ => h1 k)]
  rw [sum_shift g (fun k : Fin g => rd b x ⟨2 * k.val + 1, by omega⟩ * rd b v ⟨2 * k.val, by omega⟩ -
        rd b x ⟨2 * k.val, by omega⟩ * rd b v ⟨2 * k.val + 1, by omega⟩)]
  unfold Symp.omega
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [blkC, Symp.od, Symp.ev]
  have e1 : (⟨2 * (i.val + 1) + 1, by omega⟩ : Fin (2 * g)) = ⟨2 * i.val + 1 + 2, by omega⟩ :=
    Fin.ext (by simp; ring)
  have e2 : (⟨2 * (i.val + 1), by omega⟩ : Fin (2 * g)) = ⟨2 * i.val + 2, by omega⟩ :=
    Fin.ext (by simp; ring)
  rw [e1, e2]

/-- The inputs of Section 8.2. -/
structure CycloData (p : ℕ) [Fact p.Prime] (V : Type*) [AddCommGroup V] [Module ℚ_[p] V]
    [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V] (g : ℕ) where
  /-- `L j = 𝔪^j` -/
  F : Filtration p V
  /-- `Γ_K` -/
  Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)
  hp : p ≠ 2
  /-- `e = p - 1` -/
  he : F.e = p - 1
  /-- residue degree; `d = 2g = (p - 1) f` -/
  f : ℕ
  hdeg : 2 * g = (p - 1) * f
  hg : 1 ≤ g
  /-- `Λ = log U¹` -/
  Λ : Submodule ℤ_[p] V
  /-- Lemma 8.5(a): `𝔪² ⊆ Λ ⊆ 𝔪` -/
  hL2 : F.L 2 ≤ Λ
  hL1 : Λ ≤ F.L 1
  /-- Lemma 8.5(a): `[𝔪 : Λ] = p`, in the form `#(𝔪^p / pΛ) = p` (`𝔪^p = p𝔪`) -/
  hcardR : Nat.card (↥(F.L p) ⧸ (pMul Λ).comap (F.L p).subtype) = p
  /-- `#(𝔪^r / pΛ) = p^(f(e+1-r)+1)` for `2 ≤ r ≤ e` (Lemma 8.5(a) and `𝔪^j/𝔪^{j+1} ≅ F_q`) -/
  hcard : ∀ r : ℕ, 2 ≤ r → r ≤ F.e →
    Nat.card (↥(F.L r) ⧸ (pMul Λ).comap (F.L r).subtype) = p ^ (f * (F.e + 1 - r) + 1)
  /-- Lemma 8.5(c): if `f = 1` then `Λ = 𝔪²` -/
  hw1 : f = 1 → Λ = F.L 2
  /-- Lemma 8.5(c): if `f ≥ 2` then `Λ` has an element of valuation `1` -/
  hw2 : 2 ≤ f → ¬ Λ ≤ F.L 2
  /-- Lemma 8.6: the basis `z, y_2, …, y_d` of `Λ` -/
  b : Module.Basis (Fin (2 * g)) ℚ_[p] V
  hΛ : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1
  /-- `τ = Tr / p` -/
  τ : V →ₗ[ℚ_[p]] ℚ_[p]
  /-- Lemma 8.6 (with [Kondo, Theorem 1.3]): `Tr(z) = Tr(y_i) = 0` for `i ≥ 3` -/
  hker : ∀ i : Fin (2 * g), i.val ≠ 1 → τ (b i) = 0
  /-- Lemma 8.6: `Tr(y_2) ∈ p ℤ_p^×` -/
  hτ1 : ‖τ (b ⟨1, by omega⟩)‖ = 1
  /-- Lemma 8.5(b): `Tr(𝔪^r) = p ℤ_p` for `1 ≤ r ≤ e` -/
  htr : ∀ r : ℕ, 1 ≤ r → r ≤ F.e → ∃ x ∈ F.L r, ‖τ x‖ = 1
  /-- `Tr(𝔪^p) = p² ℤ_p` -/
  htrp : ∀ x ∈ F.L p, ‖τ x‖ ≤ ‖(p : ℚ_[p])‖
  /-- (Γ1) -/
  hΓΛ : ∀ γ ∈ Γ, ∀ x ∈ Λ, γ x ∈ Λ
  /-- (Γ2) -/
  hΓ2 : ∀ γ ∈ Γ, ∀ x, τ (γ x) = τ x
  /-- Lemma 8.5(d): `γ(𝔪) = 𝔪` (from Lemmas 8.1, 8.2: `log C_K = 𝔪^p = p 𝔪`, see `prop83`) -/
  hΓm : ∀ γ ∈ Γ, ∀ x ∈ F.L 1, γ x ∈ F.L 1
  /-- [Kondo26, Lemma 3.3]: the symplectic transvections of the block `U`, fixing `b 0`, `b 1` -/
  kondoT : ∀ v : V, (∀ i : Fin (2 * g), i.val < 2 → b.repr v i = 0) → (∀ i, ‖b.repr v i‖ ≤ 1) →
    ∀ a : ℤ_[p], ∃ γ ∈ Γ, ∀ x, γ x = x + ((a : ℚ_[p]) * blockForm b x v) • v
  /-- [Kondo26, Lemma 3.3]: `-1` on the pair `(b 2, b 3)` (an element of `Sp(U)`) -/
  kondoNeg : 2 ≤ g → ∃ γ ∈ Γ, ∀ i : Fin (2 * g), γ (b i) = if i.val = 2 ∨ i.val = 3 then -b i else b i
  /-- the coefficient `α` with `y_1 = α z` (Lemma 8.6) -/
  α : ℤ_[p]
  /-- `y_i = log rec_K⁻¹(x_i)` for `1 ≤ i ≤ d` (0-based), with the generators chosen as in Lemma 8.6 -/
  y : Module.Basis (Fin (2 * g)) ℚ_[p] V
  /-- Lemma 4.1 (with Theorem 3.1): free-group automorphisms fixing `z_1` and the boundary word are
  realized in `Γ` by their abelianization in the basis `y` -/
  hR : RealizesEven Γ y hg
  /-- Lemma 8.6: `y_1 = α z` -/
  hy0 : y ⟨0, by omega⟩ = (α : ℚ_[p]) • b ⟨0, by omega⟩
  /-- Lemma 8.6: `b j = y_{j+1}` for `j ≥ 1` (0-based) -/
  hyj : ∀ j : Fin (2 * g), j.val ≠ 0 → y j = b j

namespace CycloData

variable {g : ℕ} (K : CycloData p V g)

/-- the mixing map `M` on the first two pairs (Lemma 4.3 with Lemma 4.1), in the basis `b`:
`y_2 ↦ y_2 + y_1 + y_4`, `y_3 ↦ y_3 - y_1 - y_4` (`cycloM_of_realizes`) -/
theorem moveM (hg2 : 2 ≤ g) : ∃ γ ∈ K.Γ, ∀ i : Fin (2 * g),
    γ (K.b i) = if i.val = 1 then K.b i + (K.α : ℚ_[p]) • K.b ⟨0, by omega⟩ + K.b ⟨3, by omega⟩
      else if i.val = 2 then K.b i - (K.α : ℚ_[p]) • K.b ⟨0, by omega⟩ - K.b ⟨3, by omega⟩
      else K.b i :=
  cycloM_of_realizes hg2 K.Γ K.y K.hR K.b K.α K.hy0 K.hyj

/-- index of `z` -/
def iz : Fin (2 * g) := ⟨0, by have := K.hg; omega⟩

/-- index of `y_2` -/
def i1 : Fin (2 * g) := ⟨1, by have := K.hg; omega⟩

include K in
theorem three_le_p : 3 ≤ p := by
  have := (Fact.out : p.Prime).two_le
  have := K.hp
  omega

theorem p_eq : (p : ℤ) = 1 + K.F.e := by
  have h := K.he
  have := (Fact.out : p.Prime).two_le
  omega

theorem e_lt_p : K.F.e < p := by
  have := K.he
  have := (Fact.out : p.Prime).two_le
  omega

theorem f_pos : 1 ≤ K.f := by
  have h := K.hdeg
  have := K.hg
  rcases Nat.eq_zero_or_pos K.f with h0 | h0
  · rw [h0, mul_zero] at h; omega
  · exact h0

theorem integ_iff (x : V) : x ∈ K.Λ ↔ Integ K.b x := K.hΛ x

theorem mem_pMul_iff (x : V) : x ∈ pMul K.Λ ↔ ∀ i, ‖K.b.repr x i‖ ≤ ‖(p : ℚ_[p])‖ := by
  show (p : ℚ_[p])⁻¹ • x ∈ K.Λ ↔ _
  rw [K.hΛ]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_inv]
  have hp : 0 < ‖(p : ℚ_[p])‖ := norm_p_pos
  constructor
  · intro h i
    have := h i
    rwa [inv_mul_le_iff₀ hp, mul_one] at this
  · intro h i
    rw [inv_mul_le_iff₀ hp, mul_one]
    exact h i

theorem mem_pMul_iff_rd {x : V} (hx : Integ K.b x) : x ∈ pMul K.Λ ↔ rd K.b x = 0 := by
  rw [K.mem_pMul_iff, rd_eq_zero_iff K.b hx]

/-- `pΛ ⊆ 𝔪^p = p 𝔪` -/
theorem pMul_le_Lp : pMul K.Λ ≤ K.F.L p := by
  intro x hx
  rw [K.p_eq, K.F.shift]
  exact K.hL1 hx

theorem Lp_le {r : ℤ} (hr : r ≤ p) : K.F.L p ≤ K.F.L r := K.F.anti_le hr

theorem L_le_Λ {r : ℤ} (hr : 2 ≤ r) : K.F.L r ≤ K.Λ := (K.F.anti_le hr).trans K.hL2

theorem Lp_le_Λ : K.F.L p ≤ K.Λ := K.L_le_Λ (by have := K.three_le_p; omega)

/-- `Γ` preserves `𝔪^p = p 𝔪` -/
theorem hΓp : ∀ γ ∈ K.Γ, ∀ x ∈ K.F.L p, γ x ∈ K.F.L p := by
  intro γ hγ x hx
  rw [K.p_eq, K.F.shift] at hx ⊢
  have := K.hΓm γ hγ _ hx
  rwa [map_smul] at this

/-- `Γ` preserves `pΛ` -/
theorem hΓpΛ : ∀ γ ∈ K.Γ, ∀ x ∈ pMul K.Λ, γ x ∈ pMul K.Λ := by
  intro γ hγ x hx
  show (p : ℚ_[p])⁻¹ • γ x ∈ K.Λ
  rw [← map_smul]
  exact K.hΓΛ γ hγ _ hx

theorem hΓinteg : ∀ γ ∈ K.Γ, ∀ x, Integ K.b x → Integ K.b (γ x) := fun γ hγ x hx =>
  (K.integ_iff _).1 (K.hΓΛ γ hγ x ((K.integ_iff x).2 hx))

theorem tau_eq (x : V) : K.τ x = K.b.repr x K.i1 * K.τ (K.b K.i1) := by
  conv_lhs => rw [← K.b.sum_repr x]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single K.i1]
  · intro i _ hi
    rw [K.hker i (fun h => hi (Fin.ext (by simp [i1, h]))), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem norm_tau_b1 : ‖K.τ (K.b K.i1)‖ = 1 := K.hτ1

theorem tau_b1_ne : K.τ (K.b K.i1) ≠ 0 := by
  intro h
  have := K.norm_tau_b1
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem norm_tau_eq (x : V) : ‖K.τ x‖ = ‖K.b.repr x K.i1‖ := by
  rw [K.tau_eq, norm_mul, K.norm_tau_b1, mul_one]

/-- `Γ` fixes the coordinate of `y_2` (since it preserves the trace) -/
theorem coord1_inv {γ : V ≃ₗ[ℚ_[p]] V} (hγ : γ ∈ K.Γ) (x : V) :
    K.b.repr (γ x) K.i1 = K.b.repr x K.i1 := by
  have h := K.hΓ2 γ hγ x
  rw [K.tau_eq, K.tau_eq x] at h
  exact mul_right_cancel₀ K.tau_b1_ne h

theorem fin_lt_two (i : Fin (2 * g)) (hi : i.val < 2) : i = K.iz ∨ i = K.i1 := by
  by_cases h : i.val = 0
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext (by simp [i1]; omega))

theorem iz_ne_i1 : K.iz ≠ K.i1 := by
  intro h
  have := congrArg Fin.val h
  simp [iz, i1] at this

/-- the transvections of the block, reduced modulo `p` -/
theorem transv_lift (v : Fin (2 * (g - 1)) → ZMod p) (a : ZMod p) :
    ∃ γ ∈ K.Γ, ∀ x, Integ K.b x → blkC (rd K.b (γ x)) = Symp.transv v a (blkC (rd K.b x)) := by
  set w := liftV K.b (unblkC v) with hw
  have hw0 : ∀ i : Fin (2 * g), i.val < 2 → K.b.repr w i = 0 := fun i hi =>
    repr_liftV_eq_zero K.b (by simp only [unblkC]; rw [dif_neg (by omega)])
  have hwI : Integ K.b w := integ_liftV K.b _
  obtain ⟨γ, hγ, hγx⟩ := K.kondoT w hw0 hwI ((a.val : ℕ) : ℤ_[p])
  refine ⟨γ, hγ, fun x hx => ?_⟩
  have ha : ‖((((a.val : ℕ) : ℤ_[p])) : ℚ_[p])‖ ≤ 1 := (((a.val : ℕ) : ℤ_[p])).2
  have hc : ‖((((a.val : ℕ) : ℤ_[p])) : ℚ_[p]) * blockForm K.b x w‖ ≤ 1 :=
    norm_mul_le_one ha (norm_blockForm_le K.b hx hwI)
  rw [hγx x, rd_add K.b hx (integ_smul K.b hc hwI), rd_smul K.b hc hwI, rd_liftV,
    red_mul ha (norm_blockForm_le K.b hx hwI), red_coe, toZMod_natCast_val,
    red_blockForm K.b hx hwI, rd_liftV, blkC_add, blkC_smul, blkC_unblkC]
  rfl

/-- elements whose reduced coordinates agree outside the index `0` differ by an element of
`ℤ_p z + pΛ` -/
theorem exists_sub_smul_iz_mem {x x' : V} (hx : Integ K.b x) (hx' : Integ K.b x')
    (h1 : rd K.b x K.i1 = rd K.b x' K.i1) (hb : blkC (rd K.b x) = blkC (rd K.b x')) :
    x - x' - ((((rd K.b x K.iz - rd K.b x' K.iz).val : ℕ) : ℤ_[p])) • K.b K.iz ∈ pMul K.Λ := by
  set c := rd K.b x K.iz - rd K.b x' K.iz with hc
  have hd : Integ K.b (x - x') := integ_sub K.b hx hx'
  have hz : Integ K.b ((((c.val : ℕ) : ℤ_[p])) • K.b K.iz) :=
    integ_zsmul K.b _ (integ_basis K.b _)
  rw [K.mem_pMul_iff_rd (integ_sub K.b hd hz), rd_sub K.b hd hz, rd_sub K.b hx hx',
    rd_zsmul K.b _ (integ_basis K.b _), toZMod_natCast_val, rd_basis, sub_eq_zero]
  apply eq_of_blkC
  · intro i hi
    rcases K.fin_lt_two i hi with rfl | rfl
    · simp [hc]
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [h1, sub_self, Pi.single_apply, if_neg (Ne.symm K.iz_ne_i1), mul_zero]
  · rw [blkC_sub, hb, sub_self, blkC_smul, blkC_single_lt _ (by simp [iz]), smul_zero]

/-- some element of `𝔪^p` is not in `pΛ` (`#R = p > 1`) -/
theorem exists_Lp_not_pMul : ∃ x ∈ K.F.L p, x ∉ pMul K.Λ := by
  by_contra H
  push Not at H
  have := card_quot_le (A := K.F.L p) (P := pMul K.Λ) (T := Unit) (fun _ => ())
    (fun x hx x' hx' _ => sub_mem (H x hx) (H x' hx'))
  rw [K.hcardR, Nat.card_unique] at this
  have := (Fact.out : p.Prime).two_le
  omega

/-- `R` is a line: every element of `𝔪^p` outside `pΛ` spans `𝔪^p / pΛ` -/
theorem Lp_line {x : V} (hx : x ∈ K.F.L p) (hx' : x ∉ pMul K.Λ) :
    ∀ y ∈ K.F.L p, ∃ k : ZMod p, y - ((k.val : ℕ) : ℤ_[p]) • x ∈ pMul K.Λ := by
  have hxI : Integ K.b x := (K.integ_iff x).1 (K.Lp_le_Λ hx)
  have hrd : rd K.b x ≠ 0 := fun h => hx' ((K.mem_pMul_iff_rd hxI).2 h)
  haveI : Finite (↥(K.F.L p) ⧸ (pMul K.Λ).comap (K.F.L p).subtype) :=
    Nat.finite_of_card_ne_zero (by rw [K.hcardR]; exact (Fact.out : p.Prime).ne_zero)
  refine exists_sub_mem_of_card (fun k : ZMod p => ((k.val : ℕ) : ℤ_[p]) • x)
    (fun k => (K.F.L p).smul_mem _ hx) ?_ (le_of_eq (by rw [K.hcardR, Nat.card_zmod]))
  intro k k' hkk
  have hI : ∀ k : ZMod p, Integ K.b (((k.val : ℕ) : ℤ_[p]) • x) := fun k => integ_zsmul K.b _ hxI
  rw [K.mem_pMul_iff_rd (integ_sub K.b (hI k) (hI k')), rd_sub K.b (hI k) (hI k'),
    rd_zsmul K.b _ hxI, rd_zsmul K.b _ hxI, toZMod_natCast_val, toZMod_natCast_val, ← sub_smul,
    smul_eq_zero] at hkk
  rcases hkk with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hrd

/-- the map `M`: `x ↦ x + (x₁ - x₂) (α z + b 3)` in coordinates -/
theorem exists_M (hg2 : 2 ≤ g) : ∃ γ ∈ K.Γ, ∀ x, γ x = x + (K.b.repr x K.i1 -
    K.b.repr x ⟨2, by omega⟩) • ((K.α : ℚ_[p]) • K.b K.iz + K.b ⟨3, by omega⟩) := by
  obtain ⟨γ, hγ, hM⟩ := K.moveM hg2
  refine ⟨γ, hγ, fun x => ?_⟩
  set w : V := (K.α : ℚ_[p]) • K.b K.iz + K.b ⟨3, by omega⟩ with hw
  set i2 : Fin (2 * g) := ⟨2, by omega⟩ with hi2
  have hterm : ∀ i : Fin (2 * g), K.b.repr x i • (γ : V →ₗ[ℚ_[p]] V) (K.b i) =
      K.b.repr x i • K.b i + ((if i = K.i1 then K.b.repr x i • w else 0) -
        (if i = i2 then K.b.repr x i • w else 0)) := by
    intro i
    show K.b.repr x i • γ (K.b i) = _
    rw [hM i]
    by_cases h1 : i.val = 1
    · have hi : i = K.i1 := Fin.ext h1
      have hi' : i ≠ i2 := by intro h; rw [h] at h1; simp [hi2] at h1
      rw [if_pos h1, if_pos hi, if_neg hi', hw, sub_zero, ← smul_add, add_assoc]
      rfl
    · by_cases h2 : i.val = 2
      · have hi : i = i2 := Fin.ext h2
        have hi' : i ≠ K.i1 := fun h => h1 (by rw [h]; rfl)
        rw [if_neg h1, if_pos h2, if_neg hi', if_pos hi, hw, zero_sub, sub_sub, smul_sub,
          sub_eq_add_neg]
        rfl
      · have hi : i ≠ K.i1 := fun h => h1 (by rw [h]; rfl)
        have hi' : i ≠ i2 := fun h => h2 (by rw [h])
        rw [if_neg h1, if_neg h2, if_neg hi, if_neg hi', sub_zero, add_zero]
  rw [show γ x = (γ : V →ₗ[ℚ_[p]] V) x from rfl, apply_eq_sum K.b (γ : V →ₗ[ℚ_[p]] V) x,
    Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _),
    K.b.sum_repr, sub_smul]

/-- `-1` on the pair `(b 2, b 3)` in coordinates -/
theorem exists_Neg (hg2 : 2 ≤ g) : ∃ γ ∈ K.Γ, ∀ x, K.b.repr (γ x) K.i1 = K.b.repr x K.i1 ∧
    K.b.repr (γ x) ⟨2, by omega⟩ = -K.b.repr x ⟨2, by omega⟩ := by
  obtain ⟨γ, hγ, hN⟩ := K.kondoNeg hg2
  refine ⟨γ, hγ, fun x => ?_⟩
  have hd : ∀ i, (γ : V →ₗ[ℚ_[p]] V) (K.b i) =
      (if i.val = 2 ∨ i.val = 3 then (-1 : ℚ_[p]) else 1) • K.b i := by
    intro i
    show γ (K.b i) = _
    rw [hN i]
    split_ifs <;> simp
  have h := repr_apply_diag K.b (γ : V →ₗ[ℚ_[p]] V) _ hd x
  refine ⟨?_, ?_⟩
  · rw [show γ x = (γ : V →ₗ[ℚ_[p]] V) x from rfl, h]
    simp [i1]
  · rw [show γ x = (γ : V →ₗ[ℚ_[p]] V) x from rfl, h]
    simp

/-- Lemma 8.7: `𝔪^p = ℤ_p z + pΛ`, i.e. `R = 𝔪^p / pΛ = F_p z̄`. -/
theorem lemma87 : K.b K.iz ∈ K.F.L p ∧ ∀ x ∈ K.F.L p, ∃ t : ℤ_[p], x - t • K.b K.iz ∈ pMul K.Λ := by
  obtain ⟨x₀, hx₀, hx₀'⟩ := K.exists_Lp_not_pMul
  have hI : Integ K.b x₀ := (K.integ_iff _).1 (K.Lp_le_Λ hx₀)
  have hrd : rd K.b x₀ ≠ 0 := fun h => hx₀' ((K.mem_pMul_iff_rd hI).2 h)
  -- the coordinate of `y_2` vanishes modulo `p` (`Tr(𝔪^p) = p² ℤ_p`)
  have h1 : rd K.b x₀ K.i1 = 0 := by
    rw [rd_apply, red_eq_zero_iff' (hI _), ← K.norm_tau_eq]
    exact K.htrp x₀ hx₀
  -- the block vanishes modulo `p`: no line of the block is stable under the transvections
  have hblk : blkC (rd K.b x₀) = 0 := by
    by_contra hne
    obtain ⟨γ, hγ, hγx⟩ := exists_off_line K.b blkC K.transv_lift hne
    obtain ⟨k, hk⟩ := K.Lp_line hx₀ hx₀' (γ x₀) (K.hΓp γ hγ x₀ hx₀)
    have hγI : Integ K.b (γ x₀) := K.hΓinteg γ hγ x₀ hI
    have hkI : Integ K.b (((k.val : ℕ) : ℤ_[p]) • x₀) := integ_zsmul K.b _ hI
    rw [K.mem_pMul_iff_rd (integ_sub K.b hγI hkI), rd_sub K.b hγI hkI, sub_eq_zero,
      rd_zsmul K.b _ hI, toZMod_natCast_val] at hk
    apply hγx x₀ hI rfl
    rw [hk, blkC_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  -- hence `x₀ ≡ c z` with `c ≠ 0`
  set c := rd K.b x₀ K.iz with hc
  have hrdx : rd K.b x₀ = c • rd K.b (K.b K.iz) := by
    rw [rd_basis]
    apply eq_of_blkC
    · intro i hi
      rcases K.fin_lt_two i hi with rfl | rfl
      · simp [hc]
      · rw [h1, Pi.smul_apply, Pi.single_apply, if_neg (Ne.symm K.iz_ne_i1), smul_zero]
    · rw [hblk, blkC_smul, blkC_single_lt _ (by simp [iz]), smul_zero]
  have hc0 : c ≠ 0 := by
    intro h
    apply hrd
    rw [hrdx, h, zero_smul]
  -- `z ∈ 𝔪^p`
  have hbz : K.b K.iz ∈ K.F.L p := by
    set t : ℤ_[p] := (((c⁻¹).val : ℕ) : ℤ_[p]) with ht
    have htI : Integ K.b (t • x₀) := integ_zsmul K.b _ hI
    have hdiff : K.b K.iz - t • x₀ ∈ pMul K.Λ := by
      rw [K.mem_pMul_iff_rd (integ_sub K.b (integ_basis K.b _) htI),
        rd_sub K.b (integ_basis K.b _) htI, rd_zsmul K.b _ hI, ht, toZMod_natCast_val, hrdx,
        smul_smul, inv_mul_cancel₀ hc0, one_smul, sub_self]
    have := add_mem (K.pMul_le_Lp hdiff) ((K.F.L p).smul_mem t hx₀)
    rwa [sub_add_cancel] at this
  refine ⟨hbz, fun x hx => ?_⟩
  have hbz' : K.b K.iz ∉ pMul K.Λ := by
    rw [K.mem_pMul_iff_rd (integ_basis K.b _), rd_basis]
    intro h
    have := congrFun h K.iz
    rw [Pi.single_eq_same, Pi.zero_apply] at this
    exact one_ne_zero this
  obtain ⟨k, hk⟩ := K.Lp_line hbz hbz' x hx
  exact ⟨_, hk⟩

/-- elements whose reduced coordinates agree outside the index `0` are congruent modulo
`𝔪^p = ℤ_p z + pΛ` -/
theorem sub_mem_Lp_of_rd {x x' : V} (hx : Integ K.b x) (hx' : Integ K.b x')
    (h1 : rd K.b x K.i1 = rd K.b x' K.i1) (hb : blkC (rd K.b x) = blkC (rd K.b x')) :
    x - x' ∈ K.F.L p := by
  have h := K.exists_sub_smul_iz_mem hx hx' h1 hb
  have := add_mem (K.pMul_le_Lp h)
    ((K.F.L p).smul_mem ((((rd K.b x K.iz - rd K.b x' K.iz).val : ℕ) : ℤ_[p])) K.lemma87.1)
  rwa [sub_add_cancel] at this

/-- Lemma 8.8: `S_K(r) = Λ` for `2 ≤ r ≤ e`. -/
theorem lemma88 (r : ℕ) (hr2 : 2 ≤ r) (hre : r ≤ K.F.e) : S K.Γ (K.F.L r) = K.Λ := by
  have hep := K.e_lt_p
  set N := S K.Γ (K.F.L r) with hN
  have hLrΛ : K.F.L r ≤ K.Λ := K.L_le_Λ (by exact_mod_cast hr2)
  have hLpLr : K.F.L p ≤ K.F.L r := K.Lp_le (by exact_mod_cast (le_of_lt (lt_of_le_of_lt hre hep)))
  have hmemN : ∀ x ∈ K.F.L r, x ∈ N := fun x hx =>
    Submodule.subset_span ⟨1, K.Γ.one_mem, x, hx, rfl⟩
  have hstab : ∀ γ ∈ K.Γ, ∀ x ∈ N, γ x ∈ N := fun γ hγ x hx => S_stable K.Γ _ hγ hx
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, hγ, x, hx, rfl⟩
    exact K.hΓΛ γ hγ x (hLrΛ hx)
  have hpN : pMul K.Λ ≤ N := fun x hx => hmemN x (hLpLr (K.pMul_le_Lp hx))
  have hzN : K.b K.iz ∈ N := hmemN _ (hLpLr K.lemma87.1)
  obtain ⟨x, hx, hτx⟩ := K.htr r (by omega) hre
  have hxN : x ∈ N := hmemN x hx
  have hxI : Integ K.b x := (K.integ_iff x).1 (hLrΛ hx)
  have hc1 : ‖K.b.repr x K.i1‖ = 1 := by rw [← K.norm_tau_eq]; exact hτx
  -- the block basis vectors lie in `N`
  have hblock : ∀ j : Fin (2 * g), 2 ≤ j.val → K.b j ∈ N := by
    intro j hj
    have hg2 : 2 ≤ g := by have := j.2; omega
    set i3 : Fin (2 * g) := ⟨3, by omega⟩ with hi3
    -- `b 3 ∈ N`, from `M x - x` and `M (-1 x) - (-1 x)`
    have h3N : K.b i3 ∈ N := by
      obtain ⟨M, hM, hMx⟩ := K.exists_M hg2
      obtain ⟨Ng, hNg, hNgx⟩ := K.exists_Neg hg2
      set w : V := (K.α : ℚ_[p]) • K.b K.iz + K.b i3 with hw
      have hwN : ∀ c : ℚ_[p], ‖c‖ = 1 → c • w ∈ N → K.b i3 ∈ N := by
        intro c hc hcw
        have hw' : w ∈ N := mem_of_unit_smul_mem N hc hcw
        have : K.b i3 = w - (K.α : ℚ_[p]) • K.b K.iz := by rw [hw]; abel
        rw [this]
        exact sub_mem hw' (smul_mem_of_norm_le N K.α.2 hzN)
      have e1 : (K.b.repr x K.i1 - K.b.repr x ⟨2, by omega⟩) • w ∈ N := by
        have := sub_mem (hstab M hM x hxN) hxN
        rwa [hMx x, add_sub_cancel_left] at this
      have e2 : (K.b.repr x K.i1 + K.b.repr x ⟨2, by omega⟩) • w ∈ N := by
        have hNx := hstab Ng hNg x hxN
        have := sub_mem (hstab M hM _ hNx) hNx
        rw [hMx, add_sub_cancel_left, (hNgx x).1, (hNgx x).2, sub_neg_eq_add] at this
        exact this
      rcases unit_or_unit K.hp hc1 (hxI _) with h | h
      · exact hwN _ h e1
      · exact hwN _ h e2
    -- move `b 3` to `b j` by transvections
    have hu3 : blkC (rd K.b (K.b i3)) ≠ 0 := by
      rw [rd_basis, blkC_single _ (by simp [hi3])]
      intro h
      have := congrFun h ⟨1, by omega⟩
      rw [Pi.single_apply, if_pos (Fin.ext (by simp [hi3])), Pi.zero_apply] at this
      exact one_ne_zero this
    have huj : blkC (rd K.b (K.b j)) ≠ 0 := by
      rw [rd_basis, blkC_single _ hj]
      intro h
      have := congrFun h ⟨j.val - 2, by omega⟩
      rw [Pi.single_apply, if_pos rfl, Pi.zero_apply] at this
      exact one_ne_zero this
    obtain ⟨γ, hγ, hγx⟩ := exists_move K.b blkC K.hΓinteg K.transv_lift hu3 huj
    have hγI := K.hΓinteg γ hγ _ (integ_basis K.b i3)
    have h3ne : i3 ≠ K.i1 := by
      intro h; have := congrArg Fin.val h; simp [hi3, i1] at this
    have hjne : j ≠ K.i1 := by
      intro h; have := congrArg Fin.val h; simp [i1] at this; omega
    have h1 : rd K.b (γ (K.b i3)) K.i1 = rd K.b (K.b j) K.i1 := by
      rw [rd_apply, rd_apply, K.coord1_inv hγ, Module.Basis.repr_self, Module.Basis.repr_self,
        Finsupp.single_apply, Finsupp.single_apply, if_neg h3ne, if_neg hjne]
    have hmem := K.exists_sub_smul_iz_mem hγI (integ_basis K.b j) h1
      (hγx _ (integ_basis K.b i3) rfl)
    have hγN : γ (K.b i3) ∈ N := hstab γ hγ _ h3N
    have := sub_mem (sub_mem hγN (hpN hmem))
      (N.smul_mem ((((rd K.b (γ (K.b i3)) K.iz - rd K.b (K.b j) K.iz).val : ℕ) : ℤ_[p])) hzN)
    convert this using 1
    abel
  -- the other basis vectors
  have hothers : ∀ i : Fin (2 * g), i ≠ K.i1 → K.b i ∈ N := by
    intro i hi
    by_cases h0 : i.val = 0
    · have : i = K.iz := Fin.ext h0
      rw [this]
      exact hzN
    · exact hblock i (by have : i.val ≠ 1 := fun h => hi (Fin.ext h); omega)
  -- `y_2 ∈ N`, from `x`
  have h1N : K.b K.i1 ∈ N := by
    have hx_sum := K.b.sum_repr x
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ K.i1)] at hx_sum
    have hsum := eq_sub_of_add_eq hx_sum
    refine mem_of_unit_smul_mem N hc1 ?_
    rw [hsum]
    exact sub_mem hxN (Submodule.sum_mem _ (fun i hi =>
      smul_mem_of_norm_le N (hxI i) (hothers i (Finset.ne_of_mem_erase hi))))
  -- conclusion
  intro y hy
  rw [K.integ_iff] at hy
  rw [← K.b.sum_repr y]
  refine Submodule.sum_mem _ (fun i _ => smul_mem_of_norm_le N (hy i) ?_)
  by_cases hi : i = K.i1
  · rw [hi]
    exact h1N
  · exact hothers i hi

/-- the least valuation `w` of `Λ ∖ {0}` (Lemma 8.5(c)) -/
def w : ℤ := if K.f = 1 then 2 else 1

/-- `Λ ⊆ 𝔪^w` and `Λ ⊄ 𝔪^(w+1)` (Lemma 8.5(c)) -/
theorem w_spec : K.Λ ≤ K.F.L K.w ∧ ¬ K.Λ ≤ K.F.L (K.w + 1) := by
  unfold w
  split_ifs with hf
  · rw [K.hw1 hf]
    exact ⟨le_rfl, K.F.strict 2⟩
  · have hf2 : 2 ≤ K.f := by have := K.f_pos; omega
    exact ⟨K.hL1, by simpa using K.hw2 hf2⟩

/-- `Γ` preserves `𝔪^(1 + n e) = p^n 𝔪` -/
theorem hΓ1n (n : ℤ) : ∀ γ ∈ K.Γ, ∀ x ∈ K.F.L (1 + n * K.F.e), γ x ∈ K.F.L (1 + n * K.F.e) := by
  intro γ hγ x hx
  rw [K.F.mem_shift_zpow] at hx ⊢
  have := K.hΓm γ hγ _ hx
  rwa [map_smul] at this

/-- Theorem 8.9. Write `m = r + n e` with `1 ≤ r ≤ e`. If `r = 1` then `S_K(m) = 𝔪^m` and `a_K(m) = 0`;
if `r ≥ 2` then `S_K(m) = p^n Λ` and the least valuation of the images is `n e + w`
(`a_K(m) = r - 2` if `f = 1`, `r - 1` if `f ≥ 2`). -/
theorem thm89 (r n : ℤ) (hr1 : 1 ≤ r) (hre : r ≤ K.F.e) :
    (r = 1 → S K.Γ (K.F.L (r + n * K.F.e)) = K.F.L (r + n * K.F.e) ∧
        Reaches K.F K.Γ (K.F.L (r + n * K.F.e)) (r + n * K.F.e)) ∧
    (2 ≤ r → S K.Γ (K.F.L (r + n * K.F.e)) = pPow n K.Λ ∧
        Reaches K.F K.Γ (K.F.L (r + n * K.F.e)) (n * K.F.e + K.w)) := by
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · subst hr
    have hpres := K.hΓ1n n
    have hS : S K.Γ (K.F.L (1 + n * K.F.e)) = K.F.L (1 + n * K.F.e) := by
      refine le_antisymm (Submodule.span_le.mpr ?_)
        (fun x hx => Submodule.subset_span ⟨1, K.Γ.one_mem, x, hx, rfl⟩)
      rintro _ ⟨γ, hγ, x, hx, rfl⟩
      exact hpres γ hγ x hx
    exact ⟨hS, reaches_of_S_eq K.F K.Γ _ _ hpres hS⟩
  · lift r to ℕ using (by omega)
    have hr2 : 2 ≤ r := by exact_mod_cast hr
    have h88 := K.lemma88 r hr2 (by exact_mod_cast hre)
    have hLrΛ : K.F.L r ≤ K.Λ := K.L_le_Λ (by exact_mod_cast hr2)
    have hS : S K.Γ (K.F.L (r + n * K.F.e)) = pPow n K.Λ := by
      rw [S_shift, h88]
      rfl
    refine ⟨hS, ?_, ?_⟩
    · intro γ hγ x hx
      obtain ⟨z, hz, rfl⟩ := (K.F.mem_shift_iff_exists n r x).1 hx
      rw [map_smul, show n * (K.F.e : ℤ) + K.w = K.w + n * K.F.e by ring]
      exact (K.F.mem_shift_iff_exists n K.w _).2
        ⟨γ z, K.w_spec.1 (K.hΓΛ γ hγ z (hLrΛ hz)), rfl⟩
    · by_contra H
      push Not at H
      apply K.w_spec.2
      rw [← h88]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨γ, hγ, z, hz, rfl⟩
      have := H γ hγ (((p : ℚ_[p]) ^ n) • z) ((K.F.mem_shift_iff_exists n r _).2 ⟨z, hz, rfl⟩)
      rw [map_smul, show n * (K.F.e : ℤ) + K.w + 1 = (K.w + 1) + n * K.F.e by ring,
        K.F.mem_shift_iff_exists] at this
      obtain ⟨z', hz', hzz'⟩ := this
      have : γ z = z' := smul_right_injective V (zpow_ne_zero n padic_p_ne_zero) hzz'
      rw [this]
      exact hz'

end CycloData

end LogShellEdge
