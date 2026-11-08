import Mathlib

/-!
# Symplectic transvections act transitively on the nonzero vectors

This file proves that symplectic transvections act transitively on the nonzero vectors of the
standard symplectic space over an arbitrary field `K`.  It is used for Lemma 8.7, Lemma 8.8,
Proposition 8.13 and Remark 10.2 of the note, where Kondo's group `Sp_{2g}(ℤ_p)` is reduced
modulo `p` (so `K = 𝔽_p`).  The passage from `Sp_{2g}(ℤ_p)` to its reduction is not formalized
here; this file only treats transvections over a field.

## The general statements (namespace `LogShellEdge.Symp.Gen`)

Let `B` be an alternating (`B.IsAlt`) and nondegenerate (`B.Nondegenerate`) bilinear form on a
`K`-vector space `V` (no finiteness assumption is needed).  For `v : V` and `a : K` the
*symplectic transvection* is the linear map `Gen.transv B v a : x ↦ x + (a * B x v) • v`.

* `Gen.form_transv`: `B (T x) (T y) = B x y`.
* `Gen.transv_neg_comp`, `Gen.transv_comp_neg`: `Gen.transv B v (-a)` is the inverse of
  `Gen.transv B v a`; `Gen.transvEquiv` is the resulting linear automorphism.
* `Gen.applyList B l` applies the transvections `Gen.transv B v a` for the entries `(v, a)` of the
  list `l`, the head of the list first.
* `Gen.exists_list_transv`: for nonzero `x y` there is a list `l` of length `≤ 2` whose entries
  `(v, a)` all have `v ≠ 0` and `a ≠ 0` with `Gen.applyList B l x = y`.  Proof: pick `z` with
  `B x z ≠ 0` and `B z y ≠ 0` (it exists since `V` is not the union of the two proper subspaces
  `ker B x` and `ker B(·, y)`), and use `x ↦ z ↦ y`, where `T_{z-x, (B x z)⁻¹} x = z`.
* `Gen.orbit_eq_nonzero`: the orbit of a nonzero vector is `{0}ᶜ`.
* `Gen.exists_transv_not_mem_span`: for `x ≠ 0` some transvection moves `x` out of the line `K ∙ x`
  (so no line is stable under all transvections).

## The standard symplectic space (namespace `LogShellEdge.Symp`)

On `V = Fin (2 * g) → K` the form is, with the symplectic pairs `(2i, 2i+1)`,
`omega x y = ∑_{i < g} (x (2i+1) * y (2i) - x (2i) * y (2i+1))`,
so `ω(e_{2i}, e_{2i+1}) = -1`, `ω(e_{2i+1}, e_{2i}) = 1` (`omega_ev_od`, `omega_od_ev`) and `ω`
vanishes on the other pairs of basis vectors (`omega_single_single_eq_zero`).  Here `ev i = 2i` and
`od i = 2i+1` are the two indices of the `i`-th pair.  The transvection is
`transv v a x = x + (a * omega x v) • v`.

* `omega_self`, `omega_antisymm`, `omega_nondeg` (for `x ≠ 0` some basis vector `e` has
  `omega x e ≠ 0`), `omegaForm_isAlt`, `omegaForm_nondegenerate`.
* `omega_transv` (preservation), `transv_neg_comp`, `transv_comp_neg` (inverse),
  `exists_list_transv` (transitivity), `orbit_eq_nonzero` (the orbit of a nonzero vector is
  `{0}ᶜ`), `exists_transv_not_mem_span` (no line `K ∙ x`, `x ≠ 0`, is stable).

No hypothesis `1 ≤ g` is needed in the statements: it follows from the existence of a nonzero
vector.  In particular the case `g = 1` (`dim V = 2`) is included.
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge.Symp

/-! ## Transvections of an arbitrary alternating nondegenerate form -/

namespace Gen

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (B : LinearMap.BilinForm K V)

/-- The symplectic transvection `x ↦ x + (a * B x v) • v` of the bilinear form `B`. -/
def transv (v : V) (a : K) : V →ₗ[K] V where
  toFun x := x + (a * B x v) • v
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, mul_add, add_smul]
    abel
  map_smul' c x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    module

@[simp] theorem transv_apply (v : V) (a : K) (x : V) :
    transv B v a x = x + (a * B x v) • v := rfl

/-- Apply the transvections `transv B v a` for the entries `(v, a)` of the list `l`, in order:
the head of the list is applied first. -/
def applyList (l : List (V × K)) (x : V) : V :=
  l.foldl (fun y p => transv B p.1 p.2 y) x

variable {B}

/-- Transvections preserve the form. -/
theorem form_transv (hB : B.IsAlt) (v : V) (a : K) (x y : V) :
    B (transv B v a x) (transv B v a y) = B x y := by
  have hvv : B v v = 0 := hB.self_eq_zero v
  have hvy : B v y = -B y v := (hB.neg_eq y v).symm
  simp only [transv_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hvv, hvy]
  ring

theorem transv_neg_apply (hB : B.IsAlt) (v : V) (a : K) (x : V) :
    transv B v (-a) (transv B v a x) = x := by
  have hvv : B v v = 0 := hB.self_eq_zero v
  simp only [transv_apply, map_add, map_smul, hvv]
  module

theorem transv_apply_neg (hB : B.IsAlt) (v : V) (a : K) (x : V) :
    transv B v a (transv B v (-a) x) = x := by
  simpa using transv_neg_apply hB v (-a) x

/-- `transv B v (-a)` is a left inverse of `transv B v a`. -/
theorem transv_neg_comp (hB : B.IsAlt) (v : V) (a : K) :
    (transv B v (-a)).comp (transv B v a) = LinearMap.id :=
  LinearMap.ext (transv_neg_apply hB v a)

/-- `transv B v (-a)` is a right inverse of `transv B v a`. -/
theorem transv_comp_neg (hB : B.IsAlt) (v : V) (a : K) :
    (transv B v a).comp (transv B v (-a)) = LinearMap.id :=
  LinearMap.ext (transv_apply_neg hB v a)

/-- The transvection as a linear automorphism. -/
def transvEquiv (hB : B.IsAlt) (v : V) (a : K) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (transv B v a) (transv B v (-a)) (transv_comp_neg hB v a)
    (transv_neg_comp hB v a)

@[simp] theorem transvEquiv_apply (hB : B.IsAlt) (v : V) (a : K) (x : V) :
    transvEquiv hB v a x = transv B v a x := rfl

theorem transv_injective (hB : B.IsAlt) (v : V) (a : K) : Function.Injective (transv B v a) :=
  fun x y h => by
    have := congrArg (transv B v (-a)) h
    rwa [transv_neg_apply hB, transv_neg_apply hB] at this

/-! ### Lists of transvections -/

@[simp] theorem applyList_nil (x : V) : applyList B [] x = x := rfl

@[simp] theorem applyList_cons (p : V × K) (l : List (V × K)) (x : V) :
    applyList B (p :: l) x = applyList B l (transv B p.1 p.2 x) := rfl

theorem applyList_append (l₁ l₂ : List (V × K)) (x : V) :
    applyList B (l₁ ++ l₂) x = applyList B l₂ (applyList B l₁ x) := by
  simp only [applyList, List.foldl_append]

theorem applyList_add (l : List (V × K)) (x y : V) :
    applyList B l (x + y) = applyList B l x + applyList B l y := by
  induction l generalizing x y with
  | nil => rfl
  | cons p l ih => simp only [applyList_cons, map_add, ih]

theorem applyList_smul (l : List (V × K)) (c : K) (x : V) :
    applyList B l (c • x) = c • applyList B l x := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih => simp only [applyList_cons, map_smul, ih]

theorem applyList_zero (l : List (V × K)) : applyList B l 0 = 0 := by
  simpa using applyList_smul (B := B) l 0 0

variable (B) in
/-- `applyList B l` as a linear map. -/
def applyListLin (l : List (V × K)) : V →ₗ[K] V where
  toFun := applyList B l
  map_add' := applyList_add l
  map_smul' := applyList_smul l

@[simp] theorem applyListLin_apply (l : List (V × K)) (x : V) :
    applyListLin B l x = applyList B l x := rfl

theorem form_applyList (hB : B.IsAlt) (l : List (V × K)) (x y : V) :
    B (applyList B l x) (applyList B l y) = B x y := by
  induction l generalizing x y with
  | nil => rfl
  | cons p l ih => simp only [applyList_cons, ih, form_transv hB]

theorem applyList_injective (hB : B.IsAlt) (l : List (V × K)) :
    Function.Injective (applyList B l) := by
  induction l with
  | nil => exact Function.injective_id
  | cons p l ih => exact fun x y h => transv_injective hB p.1 p.2 (ih h)

/-- The inverse list: the inverse transvections, in reverse order. -/
def invList (l : List (V × K)) : List (V × K) :=
  (l.map fun p => (p.1, -p.2)).reverse

omit [AddCommGroup V] [Module K V] in
@[simp] theorem invList_nil : invList ([] : List (V × K)) = [] := rfl

omit [AddCommGroup V] [Module K V] in
theorem invList_cons (p : V × K) (l : List (V × K)) :
    invList (p :: l) = invList l ++ [(p.1, -p.2)] := by
  simp [invList]

theorem applyList_invList_applyList (hB : B.IsAlt) (l : List (V × K)) (x : V) :
    applyList B (invList l) (applyList B l x) = x := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
    rw [invList_cons, applyList_append, applyList_cons p l x, ih]
    exact transv_neg_apply hB p.1 p.2 x

theorem applyList_applyList_invList (hB : B.IsAlt) (l : List (V × K)) (x : V) :
    applyList B l (applyList B (invList l) x) = x := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
    rw [invList_cons, applyList_append, applyList_cons]
    simp only [applyList_cons, applyList_nil]
    rw [transv_apply_neg hB p.1 p.2, ih]

/-! ### Transitivity -/

theorem exists_form_ne_zero (hN : B.Nondegenerate) {x : V} (hx : x ≠ 0) : ∃ z, B x z ≠ 0 := by
  by_contra h
  refine hx (hN.1 x fun z => ?_)
  by_contra hz
  exact h ⟨z, hz⟩

/-- For nonzero `x` and `y` there is `z` with `B x z ≠ 0` and `B z y ≠ 0`: the vector space `V`
is not the union of the two proper subspaces `ker (B x)` and `ker (B · y)`. -/
theorem exists_form_ne_zero_ne_zero (hB : B.IsAlt) (hN : B.Nondegenerate) {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) : ∃ z, B x z ≠ 0 ∧ B z y ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_form_ne_zero hN hx
  obtain ⟨w, hw⟩ := exists_form_ne_zero hN hy
  have hw' : B w y ≠ 0 := by
    rw [← hB.neg_eq y w]
    exact neg_ne_zero.mpr hw
  by_cases huy : B u y = 0
  · by_cases hxw : B x w = 0
    · refine ⟨u + w, ?_, ?_⟩
      · rw [map_add, hxw, add_zero]
        exact hu
      · rw [LinearMap.map_add₂, huy, zero_add]
        exact hw'
    · exact ⟨w, hxw, hw'⟩
  · exact ⟨u, hu, huy⟩

/-- If `B x z ≠ 0`, the transvection `T_{z - x, (B x z)⁻¹}` sends `x` to `z`. -/
theorem transv_sub_inv (hB : B.IsAlt) {x z : V} (h : B x z ≠ 0) :
    transv B (z - x) (B x z)⁻¹ x = z := by
  rw [transv_apply, map_sub, hB.self_eq_zero x, sub_zero, inv_mul_cancel₀ h, one_smul]
  abel

/-- Transitivity: two nonzero vectors are related by a product of at most two transvections
`transv B v a` with `v ≠ 0` and `a ≠ 0`. -/
theorem exists_list_transv (hB : B.IsAlt) (hN : B.Nondegenerate) {x y : V} (hx : x ≠ 0)
    (hy : y ≠ 0) :
    ∃ l : List (V × K), l.length ≤ 2 ∧ (∀ p ∈ l, p.1 ≠ 0 ∧ p.2 ≠ 0) ∧ applyList B l x = y := by
  obtain ⟨z, hxz, hzy⟩ := exists_form_ne_zero_ne_zero hB hN hx hy
  refine ⟨[(z - x, (B x z)⁻¹), (y - z, (B z y)⁻¹)], by simp, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · refine ⟨fun h => hxz ?_, inv_ne_zero hxz⟩
      rw [← sub_eq_zero.mp h]
      exact hB.self_eq_zero _
    · refine ⟨fun h => hzy ?_, inv_ne_zero hzy⟩
      rw [sub_eq_zero.mp h]
      exact hB.self_eq_zero _
  · simp only [applyList_cons, applyList_nil]
    rw [transv_sub_inv hB hxz, transv_sub_inv hB hzy]

theorem exists_applyList_eq_iff (hB : B.IsAlt) (hN : B.Nondegenerate) {x y : V} (hx : x ≠ 0) :
    (∃ l : List (V × K), applyList B l x = y) ↔ y ≠ 0 := by
  constructor
  · rintro ⟨l, rfl⟩ h
    exact hx (applyList_injective hB l (h.trans (applyList_zero l).symm))
  · intro hy
    obtain ⟨l, -, -, hl⟩ := exists_list_transv hB hN hx hy
    exact ⟨l, hl⟩

/-- The orbit of a nonzero vector under the group generated by the transvections is the set of
all nonzero vectors. -/
theorem orbit_eq_nonzero (hB : B.IsAlt) (hN : B.Nondegenerate) {x : V} (hx : x ≠ 0) :
    Set.range (fun l : List (V × K) => applyList B l x) = {0}ᶜ := by
  ext y
  rw [Set.mem_range, Set.mem_compl_singleton_iff]
  exact exists_applyList_eq_iff hB hN hx

/-- No line is stable under all transvections: for `x ≠ 0` some transvection moves `x` out of
`K ∙ x`. -/
theorem exists_transv_not_mem_span (hB : B.IsAlt) (hN : B.Nondegenerate) {x : V} (hx : x ≠ 0) :
    ∃ (v : V) (a : K), transv B v a x ∉ K ∙ x := by
  obtain ⟨z, hz⟩ := exists_form_ne_zero hN hx
  refine ⟨z - x, (B x z)⁻¹, ?_⟩
  rw [transv_sub_inv hB hz]
  intro hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  apply hz
  rw [map_smul, hB.self_eq_zero x, smul_zero]

/-- The line `K ∙ x` (`x ≠ 0`) is not mapped into itself by some transvection. -/
theorem exists_transv_map_span_not_le (hB : B.IsAlt) (hN : B.Nondegenerate) {x : V}
    (hx : x ≠ 0) : ∃ (v : V) (a : K), ¬ (K ∙ x).map (transv B v a) ≤ K ∙ x := by
  obtain ⟨v, a, h⟩ := exists_transv_not_mem_span hB hN hx
  exact ⟨v, a, fun hle => h (hle (Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self x)))⟩

end Gen

/-! ## The standard symplectic space `Fin (2 * g) → K` -/

variable {K : Type*} [Field K] {g : ℕ}

/-- The index `2 i` of the `i`-th symplectic pair. -/
def ev (i : Fin g) : Fin (2 * g) := ⟨2 * i.val, by omega⟩

/-- The index `2 i + 1` of the `i`-th symplectic pair. -/
def od (i : Fin g) : Fin (2 * g) := ⟨2 * i.val + 1, by omega⟩

@[simp] theorem ev_val (i : Fin g) : (ev i).val = 2 * i.val := rfl

@[simp] theorem od_val (i : Fin g) : (od i).val = 2 * i.val + 1 := rfl

@[simp] theorem ev_inj {a b : Fin g} : ev a = ev b ↔ a = b := by
  simp only [Fin.ext_iff, ev_val]
  omega

@[simp] theorem od_inj {a b : Fin g} : od a = od b ↔ a = b := by
  simp only [Fin.ext_iff, od_val]
  omega

@[simp] theorem od_ne_ev (a b : Fin g) : od a ≠ ev b := by
  intro h
  have := congrArg Fin.val h
  simp only [od_val, ev_val] at this
  omega

@[simp] theorem ev_ne_od (a b : Fin g) : ev a ≠ od b := fun h => od_ne_ev b a h.symm

/-- Every index is `ev i` or `od i` for `i = j / 2`. -/
theorem eq_ev_or_od (j : Fin (2 * g)) :
    ∃ i : Fin g, (j = ev i ∨ j = od i) ∧ i.val = j.val / 2 := by
  refine ⟨⟨j.val / 2, by omega⟩, ?_, rfl⟩
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h
  · left
    ext
    simp only [ev_val]
    omega
  · right
    ext
    simp only [od_val]
    omega

/-- The standard alternating form on `Fin (2 * g) → K` with symplectic pairs `(2i, 2i+1)`:
`omega x y = ∑_{i < g} (x (2i+1) * y (2i) - x (2i) * y (2i+1))`. -/
def omega (x y : Fin (2 * g) → K) : K :=
  ∑ i : Fin g, (x (od i) * y (ev i) - x (ev i) * y (od i))

theorem omega_add_left (x x' y : Fin (2 * g) → K) :
    omega (x + x') y = omega x y + omega x' y := by
  simp only [omega, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem omega_smul_left (c : K) (x y : Fin (2 * g) → K) : omega (c • x) y = c * omega x y := by
  simp only [omega, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem omega_add_right (x y y' : Fin (2 * g) → K) :
    omega x (y + y') = omega x y + omega x y' := by
  simp only [omega, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem omega_smul_right (c : K) (x y : Fin (2 * g) → K) : omega x (c • y) = c * omega x y := by
  simp only [omega, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem omega_self (x : Fin (2 * g) → K) : omega x x = 0 := by
  simp only [omega]
  refine Finset.sum_eq_zero fun i _ => ?_
  ring

theorem omega_antisymm (x y : Fin (2 * g) → K) : omega x y = -omega y x := by
  simp only [omega, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `omega` as a bilinear form. -/
def omegaForm : LinearMap.BilinForm K (Fin (2 * g) → K) :=
  LinearMap.mk₂ K omega omega_add_left omega_smul_left omega_add_right omega_smul_right

@[simp] theorem omegaForm_apply (x y : Fin (2 * g) → K) : omegaForm x y = omega x y := rfl

/-- Pairing with the basis vector `e_{2i}`. -/
theorem omega_single_ev (x : Fin (2 * g) → K) (i : Fin g) :
    omega x (Pi.single (ev i) 1) = x (od i) := by
  unfold omega
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- Pairing with the basis vector `e_{2i+1}`. -/
theorem omega_single_od (x : Fin (2 * g) → K) (i : Fin g) :
    omega x (Pi.single (od i) 1) = -x (ev i) := by
  unfold omega
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- `ω(e_{2i}, e_{2i+1}) = -1`. -/
theorem omega_ev_od (i : Fin g) :
    omega (Pi.single (ev i) (1 : K)) (Pi.single (od i) 1) = -1 := by
  rw [omega_single_od]
  simp

/-- `ω(e_{2i+1}, e_{2i}) = 1`. -/
theorem omega_od_ev (i : Fin g) :
    omega (Pi.single (od i) (1 : K)) (Pi.single (ev i) 1) = 1 := by
  rw [omega_single_ev]
  simp

/-- `ω` vanishes on every pair of basis vectors that is not a symplectic pair
`{e_{2i}, e_{2i+1}}`. -/
theorem omega_single_single_eq_zero {j k : Fin (2 * g)} (h : j.val / 2 ≠ k.val / 2 ∨ j = k) :
    omega (Pi.single j (1 : K)) (Pi.single k 1) = 0 := by
  obtain ⟨i, hk | hk, -⟩ := eq_ev_or_od k
  · subst hk
    rw [omega_single_ev, Pi.single_apply, if_neg]
    intro hj
    subst hj
    rcases h with h | h
    · simp only [od_val, ev_val] at h
      omega
    · exact od_ne_ev i i h
  · subst hk
    rw [omega_single_od, Pi.single_apply, if_neg, neg_zero]
    intro hj
    subst hj
    rcases h with h | h
    · simp only [od_val, ev_val] at h
      omega
    · exact ev_ne_od i i h

/-- Nondegeneracy: a nonzero vector pairs nontrivially with some basis vector. -/
theorem omega_nondeg {x : Fin (2 * g) → K} (hx : x ≠ 0) :
    ∃ k : Fin (2 * g), omega x (Pi.single k 1) ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  obtain ⟨i, hji | hji, -⟩ := eq_ev_or_od j
  · refine ⟨od i, ?_⟩
    rw [omega_single_od, neg_ne_zero, ← hji]
    exact hj
  · refine ⟨ev i, ?_⟩
    rw [omega_single_ev, ← hji]
    exact hj

theorem omegaForm_isAlt : (omegaForm : LinearMap.BilinForm K (Fin (2 * g) → K)).IsAlt :=
  fun x => omega_self x

theorem omegaForm_nondegenerate :
    (omegaForm : LinearMap.BilinForm K (Fin (2 * g) → K)).Nondegenerate := by
  have hL : ∀ x : Fin (2 * g) → K, (∀ y, omega x y = 0) → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨k, hk⟩ := omega_nondeg hne
    exact hk (hx _)
  refine ⟨fun x hx => hL x hx, fun y hy => hL y fun x => ?_⟩
  have h' : omega x y = 0 := hy x
  rw [omega_antisymm, h', neg_zero]

/-! ### Transvections of the standard symplectic space -/

/-- The symplectic transvection `x ↦ x + (a * omega x v) • v` of `Fin (2 * g) → K`. -/
def transv (v : Fin (2 * g) → K) (a : K) : (Fin (2 * g) → K) →ₗ[K] (Fin (2 * g) → K) :=
  Gen.transv omegaForm v a

@[simp] theorem transv_apply (v : Fin (2 * g) → K) (a : K) (x : Fin (2 * g) → K) :
    transv v a x = x + (a * omega x v) • v := rfl

/-- Transvections preserve `omega`. -/
theorem omega_transv (v : Fin (2 * g) → K) (a : K) (x y : Fin (2 * g) → K) :
    omega (transv v a x) (transv v a y) = omega x y :=
  Gen.form_transv omegaForm_isAlt v a x y

/-- `transv v (-a)` is a left inverse of `transv v a`. -/
theorem transv_neg_comp (v : Fin (2 * g) → K) (a : K) :
    (transv v (-a)).comp (transv v a) = LinearMap.id :=
  Gen.transv_neg_comp omegaForm_isAlt v a

/-- `transv v (-a)` is a right inverse of `transv v a`. -/
theorem transv_comp_neg (v : Fin (2 * g) → K) (a : K) :
    (transv v a).comp (transv v (-a)) = LinearMap.id :=
  Gen.transv_comp_neg omegaForm_isAlt v a

theorem transv_neg_apply (v : Fin (2 * g) → K) (a : K) (x : Fin (2 * g) → K) :
    transv v (-a) (transv v a x) = x :=
  Gen.transv_neg_apply omegaForm_isAlt v a x

theorem transv_apply_neg (v : Fin (2 * g) → K) (a : K) (x : Fin (2 * g) → K) :
    transv v a (transv v (-a) x) = x :=
  Gen.transv_apply_neg omegaForm_isAlt v a x

/-- The transvection as a linear automorphism of `Fin (2 * g) → K`. -/
def transvEquiv (v : Fin (2 * g) → K) (a : K) : (Fin (2 * g) → K) ≃ₗ[K] (Fin (2 * g) → K) :=
  Gen.transvEquiv omegaForm_isAlt v a

@[simp] theorem transvEquiv_apply (v : Fin (2 * g) → K) (a : K) (x : Fin (2 * g) → K) :
    transvEquiv v a x = transv v a x := rfl

/-- Apply the transvections `transv v a` for the entries `(v, a)` of `l`, in order (the head of
the list first). -/
def applyList (l : List ((Fin (2 * g) → K) × K)) (x : Fin (2 * g) → K) : Fin (2 * g) → K :=
  Gen.applyList omegaForm l x

@[simp] theorem applyList_nil (x : Fin (2 * g) → K) : applyList [] x = x := rfl

@[simp] theorem applyList_cons (p : (Fin (2 * g) → K) × K) (l : List ((Fin (2 * g) → K) × K))
    (x : Fin (2 * g) → K) : applyList (p :: l) x = applyList l (transv p.1 p.2 x) := rfl

theorem applyList_append (l₁ l₂ : List ((Fin (2 * g) → K) × K)) (x : Fin (2 * g) → K) :
    applyList (l₁ ++ l₂) x = applyList l₂ (applyList l₁ x) :=
  Gen.applyList_append l₁ l₂ x

theorem omega_applyList (l : List ((Fin (2 * g) → K) × K)) (x y : Fin (2 * g) → K) :
    omega (applyList l x) (applyList l y) = omega x y :=
  Gen.form_applyList omegaForm_isAlt l x y

theorem applyList_zero (l : List ((Fin (2 * g) → K) × K)) : applyList l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [applyList_cons, map_zero, ih]

theorem applyList_add (l : List ((Fin (2 * g) → K) × K)) (x y : Fin (2 * g) → K) :
    applyList l (x + y) = applyList l x + applyList l y := by
  induction l generalizing x y with
  | nil => rfl
  | cons p l ih => simp only [applyList_cons, map_add, ih]

theorem applyList_smul (l : List ((Fin (2 * g) → K) × K)) (c : K) (x : Fin (2 * g) → K) :
    applyList l (c • x) = c • applyList l x := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih => simp only [applyList_cons, map_smul, ih]

theorem applyList_injective (l : List ((Fin (2 * g) → K) × K)) :
    Function.Injective (applyList l) :=
  Gen.applyList_injective omegaForm_isAlt l

/-- `Gen.invList l` undoes `l`. -/
theorem applyList_invList_applyList (l : List ((Fin (2 * g) → K) × K)) (x : Fin (2 * g) → K) :
    applyList (Gen.invList l) (applyList l x) = x :=
  Gen.applyList_invList_applyList omegaForm_isAlt l x

theorem applyList_applyList_invList (l : List ((Fin (2 * g) → K) × K)) (x : Fin (2 * g) → K) :
    applyList l (applyList (Gen.invList l) x) = x :=
  Gen.applyList_applyList_invList omegaForm_isAlt l x

/-- Transitivity: any two nonzero vectors of `Fin (2 * g) → K` are related by a product of at
most two transvections `transv v a` with `v ≠ 0` and `a ≠ 0`. -/
theorem exists_list_transv {x y : Fin (2 * g) → K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ l : List ((Fin (2 * g) → K) × K),
      l.length ≤ 2 ∧ (∀ p ∈ l, p.1 ≠ 0 ∧ p.2 ≠ 0) ∧ applyList l x = y :=
  Gen.exists_list_transv omegaForm_isAlt omegaForm_nondegenerate hx hy

/-- The orbit of a nonzero vector under the transvections is the set of all nonzero vectors. -/
theorem orbit_eq_nonzero {x : Fin (2 * g) → K} (hx : x ≠ 0) :
    Set.range (fun l : List ((Fin (2 * g) → K) × K) => applyList l x) = {0}ᶜ :=
  Gen.orbit_eq_nonzero omegaForm_isAlt omegaForm_nondegenerate hx

/-- For `x ≠ 0`, the vectors reachable from `x` by transvections are exactly the nonzero ones. -/
theorem exists_applyList_eq_iff {x y : Fin (2 * g) → K} (hx : x ≠ 0) :
    (∃ l : List ((Fin (2 * g) → K) × K), applyList l x = y) ↔ y ≠ 0 :=
  Gen.exists_applyList_eq_iff omegaForm_isAlt omegaForm_nondegenerate hx

/-- No line is stable under all transvections: for `x ≠ 0` some transvection moves `x` out of
`K ∙ x` (for every `g`, including `g = 1`). -/
theorem exists_transv_not_mem_span {x : Fin (2 * g) → K} (hx : x ≠ 0) :
    ∃ (v : Fin (2 * g) → K) (a : K), transv v a x ∉ K ∙ x :=
  Gen.exists_transv_not_mem_span omegaForm_isAlt omegaForm_nondegenerate hx

/-- The line `K ∙ x` (`x ≠ 0`) is not mapped into itself by some transvection. -/
theorem exists_transv_map_span_not_le {x : Fin (2 * g) → K} (hx : x ≠ 0) :
    ∃ (v : Fin (2 * g) → K) (a : K), ¬ (K ∙ x).map (transv v a) ≤ K ∙ x :=
  Gen.exists_transv_map_span_not_le omegaForm_isAlt omegaForm_nondegenerate hx

end LogShellEdge.Symp

end
