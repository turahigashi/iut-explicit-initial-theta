import LogShellEdge.Reuse.ShearFreeGroup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# Free-group moves fixing the boundary word

This file formalizes the free-group parts of Lemma 4.2, of Lemma 4.3 and of Proposition 4.4 of the
note "How far automorphisms of a p-adic absolute Galois group move the ring of integers"
(`paper/log_shell_edge.tex`). Lemma 4.3 itself (the automorphisms `Z`, `H`, `J` of `F(a,b,c,d)`
fixing `δ = [a,b][c,d]`, and `M = Ψ Z Ψ⁻¹` with `M(a) = a`, `M(δ) = δ` and abelianization
`T_{a+d}`) is the imported file `LogShellEdge.Reuse.ShearFreeGroup`; it is used here, not reproved.

## Conventions

* The commutator is `[u,v] = u v u⁻¹ v⁻¹` (`cmt`). The letters of `FreeGroup (Fin n)` are
  `z i = FreeGroup.of i`; the generators `x_1, …, x_d` of the note are `z 0, …, z (d-1)` here
  (`x_0` and the group `𝒢` of the presentation do not occur).
* `vecN : FreeGroup (Fin n) → (Fin n → ℤ)` is the abelianization, written additively, and
  `e_i = Pi.single i 1`.
* Even case `n = 2g`: the pairs are `(z (2i), z (2i+1))`, the boundary word is
  `evenBoundary g = ∏_{i<g} [z (2i), z (2i+1)]`, and the form is `formE g`
  (`⟨e_{2i}, e_{2i+1}⟩ = -1`, `⟨e_{2i+1}, e_{2i}⟩ = 1`, `0` otherwise). The special letter is
  `z 0` (`= a`), its partner `z 1` (`= b`).
* Odd case `n = 2g+1`: the special letter is `z 0`, the pairs are `(z (2i+1), z (2i+2))`, the
  boundary word is `oddBoundary g = ∏_{i<g} [z (2i+1), z (2i+2)]`, and the form is `formO g` (the
  same on the pairs; `e_0` pairs to `0` with everything).
* The boundary words are defined through the ordered product `prodUpTo` (factors in increasing
  order); `evenBoundary_eq_list` and `oddBoundary_eq_list` write them as products of lists.

## Main results

* Lemma 4.2 (i): `mulAE` (`a ↦ a b`) and `mulBE` (`b ↦ b a`) are automorphisms of `F(a,b)`, with
  inverses `a ↦ a b⁻¹` and `b ↦ b a⁻¹`, fixing `[a,b]` (`mulAE_cmt`, `mulBE_cmt`); in any
  `FreeGroup (Fin n)` through `extendE` (`extend_mulA_values`, `extend_mulB_values`).
* Lemma 4.2 (ii): `pairSwap` (`a ↦ c`, `b ↦ d`, `c ↦ D⁻¹ a D`, `d ↦ D⁻¹ b D` with `D = [c,d]`; it is
  `H⁻¹`, with inverse `H`) fixes `[a,b][c,d]` (`pairSwap_delta`) and exchanges the two pairs on the
  abelianization (`vecN_pairSwap`); in any `FreeGroup (Fin n)`: `extend_pairSwap_values`.
* After Lemma 4.3: `UdE = M ∘ (b ↦ b a)⁻¹ ∘ (c ↦ c d⁻¹)⁻¹` and `UcE = J_c⁻¹ ∘ UdE ∘ J_c` fix `a`
  and `δ` and induce `U_d` and `U_c` (`vecN_U4`).
* Extensions: `extendE` extends an automorphism of the free group on one pair, or on two adjacent
  pairs, by the identity on the other letters; if it fixes the commutator (resp. the product of the
  two commutators), the extension fixes the boundary word (`extend_bdry_single`,
  `extend_bdry_pair`).
* Proposition 4.4 (a), `n = 2g`: `evenTa` (`z 1 ↦ z 1 · z 0`) induces `T_a`, `a = e_0`
  (`evenTa_vec`); for `2 ≤ j < 2g`, `evenU g j` induces
  `U_{e_j} : e_i ↦ e_i + ⟨e_i, e_0⟩ e_j + ⟨e_i, e_j⟩ e_0` (`evenU_vec`), and its inverse induces
  `U_{-e_j}` (`evenU_symm_vec`). All of them fix `z 0` and `evenBoundary g`. `evenU` is the base
  move `U_c` or `U_d` on the first two pairs, conjugated by the swaps `evenSwap` of the pairs
  `k, k+1` (`k ≥ 1`), which fix `z 0`, `z 1` and the boundary word.
* Proposition 4.4 (b), `n = 2g+1`: for each pair `(u, v) = (z (2k+1), z (2k+2))`, `oddPairU g k`
  (`u ↦ u v`) and `oddPairV g k` (`v ↦ v u`), and for adjacent pairs `oddSwap g k`; all of them fix
  `z 0` and `oddBoundary g`, and their abelianizations are `e_u ↦ e_u + e_v`, `e_v ↦ e_v + e_u`
  and the exchange of the two pairs.

These are the free-group conditions used with Lemma 4.1 of the note (for the automorphisms
extended by the identity on `x_0` and on `𝒢`, which are not modelled here): the `_fix0` theorems
say that `x_1` is fixed, the `_boundary` theorems that the product of commutators is fixed as an
element. Every `_vec` theorem gives the image of every basis vector explicitly in terms of
`Pi.single` (for the swaps, `Pi.single (swapIdx p h i) 1`, with `swapIdx_val'` and `swapIdx_p0`,
…, `swapIdx_p3`).

## Not claimed here

The passage from these automorphisms of free groups to automorphisms of `G_K` (Lemma 4.1 of the
note, through the Jannsen–Wingberg presentation) and to the induced maps on `Λ` is not formalized;
nothing in this file is about Galois groups.
-/

namespace LogShellEdge.FG

open LogShellEdge.ShearFreeGroup

/-! ## 1. Commutators and the abelianization -/

/-- The commutator `[u, v] = u v u⁻¹ v⁻¹` (the convention of the note and of Jannsen–Wingberg). -/
def cmt {G : Type*} [Group G] (u v : G) : G := u * v * u⁻¹ * v⁻¹

theorem map_cmt {G H : Type*} [Group G] [Group H] (f : G →* H) (u v : G) :
    f (cmt u v) = cmt (f u) (f v) := by
  simp only [cmt, map_mul, map_inv]

/-- On `F4` it is the commutator `comm` of `LogShellEdge.Reuse.ShearFreeGroup`. -/
theorem cmt_eq_comm (u v : F4) : cmt u v = LogShellEdge.ShearFreeGroup.comm u v := rfl

theorem comm_def (u v : F4) :
    LogShellEdge.ShearFreeGroup.comm u v = u * v * u⁻¹ * v⁻¹ := rfl

section Abelianization

variable {m n : ℕ}

/-- The abelianization `FreeGroup (Fin n) → ℤⁿ`, written additively: the exponent sum of each
letter. -/
def vecN (x : FreeGroup (Fin n)) : Fin n → ℤ :=
  Multiplicative.toAdd (FreeGroup.lift (fun j => Multiplicative.ofAdd (Pi.single j (1 : ℤ))) x)

@[simp] theorem vecN_mul (x y : FreeGroup (Fin n)) : vecN (x * y) = vecN x + vecN y := by
  simp only [vecN, map_mul, toAdd_mul]

@[simp] theorem vecN_inv (x : FreeGroup (Fin n)) : vecN x⁻¹ = -vecN x := by
  simp only [vecN, map_inv, toAdd_inv]

@[simp] theorem vecN_one : vecN (1 : FreeGroup (Fin n)) = 0 := by
  simp only [vecN, map_one, toAdd_one]

@[simp] theorem vecN_of (i : Fin n) : vecN (FreeGroup.of i) = Pi.single i 1 := by
  simp only [vecN, FreeGroup.lift_apply_of, toAdd_ofAdd]

@[simp] theorem vecN_cmt (u v : FreeGroup (Fin n)) : vecN (cmt u v) = 0 := by
  simp only [cmt, vecN_mul, vecN_inv]
  abel

/-- On `F4` it is the abelianization `vec` of `LogShellEdge.Reuse.ShearFreeGroup`. -/
theorem vecN_eq_vec (x : F4) : vecN x = vec x := rfl

/-- The additive map `ℤᵐ → ℤⁿ` sending the basis vector `e_a` to `f a`. -/
def linExt (f : Fin m → Fin n → ℤ) (v : Fin m → ℤ) : Fin n → ℤ := fun t => ∑ a, v a * f a t

variable (f : Fin m → Fin n → ℤ)

@[simp] theorem linExt_zero : linExt f 0 = 0 := by
  funext t
  simp [linExt]

@[simp] theorem linExt_add (v w : Fin m → ℤ) : linExt f (v + w) = linExt f v + linExt f w := by
  funext t
  simp [linExt, add_mul, Finset.sum_add_distrib]

@[simp] theorem linExt_neg (v : Fin m → ℤ) : linExt f (-v) = -linExt f v := by
  funext t
  simp [linExt, neg_mul, Finset.sum_neg_distrib]

@[simp] theorem linExt_sub (v w : Fin m → ℤ) : linExt f (v - w) = linExt f v - linExt f w := by
  funext t
  simp [linExt, sub_mul, Finset.sum_sub_distrib]

@[simp] theorem linExt_smul (c : ℤ) (v : Fin m → ℤ) : linExt f (c • v) = c • linExt f v := by
  funext t
  simp [linExt, Finset.mul_sum, mul_assoc]

@[simp] theorem linExt_ite (c : Prop) [Decidable c] (v : Fin m → ℤ) :
    linExt f (if c then v else 0) = if c then linExt f v else 0 := by
  split_ifs <;> simp

@[simp] theorem linExt_single (a : Fin m) : linExt f (Pi.single a 1) = f a := by
  funext t
  simp [linExt, Pi.single_apply]

/-- The abelianization of a homomorphism of free groups is the additive map determined by the
abelianizations of the images of the letters. -/
theorem vecN_hom (φ : FreeGroup (Fin m) →* FreeGroup (Fin n)) (x : FreeGroup (Fin m)) :
    vecN (φ x) = linExt (fun a => vecN (φ (FreeGroup.of a))) (vecN x) := by
  refine FreeGroup.induction_on x ?_ ?_ ?_ ?_
  · simp
  · intro a
    simp
  · intro a _
    simp
  · intro x y hx hy
    simp [hx, hy]

/-- Composition of the additive maps `linExt`. -/
theorem linExt_linExt {l : ℕ} (f : Fin m → Fin n → ℤ) (g : Fin l → Fin m → ℤ) (v : Fin l → ℤ) :
    linExt f (linExt g v) = linExt (fun t => linExt f (g t)) v := by
  funext s
  simp only [linExt, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem linExt_id (v : Fin n → ℤ) : linExt (fun t => Pi.single t 1) v = v := by
  funext s
  simp [linExt, Pi.single_apply]

end Abelianization

/-! ## 2. Ordered products and the boundary words -/

section Products

variable {G : Type*} [Group G]

/-- The ordered product `f 0 * f 1 * ⋯ * f (N - 1)`. -/
def prodUpTo (f : ℕ → G) : ℕ → G
  | 0 => 1
  | N + 1 => prodUpTo f N * f N

@[simp] theorem prodUpTo_zero (f : ℕ → G) : prodUpTo f 0 = 1 := rfl

theorem prodUpTo_succ (f : ℕ → G) (N : ℕ) : prodUpTo f (N + 1) = prodUpTo f N * f N := rfl

/-- The ordered product is the product of the list `[f 0, …, f (N-1)]`. -/
theorem prodUpTo_eq_list (f : ℕ → G) (N : ℕ) :
    prodUpTo f N = (List.ofFn (fun i : Fin N => f i.val)).prod := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [prodUpTo_succ, ih, List.ofFn_succ_last, List.prod_append]
    simp

/-- An endomorphism fixing every factor fixes the ordered product. -/
theorem prodUpTo_fixed (F : G →* G) (f : ℕ → G) (N : ℕ) (hf : ∀ i < N, F (f i) = f i) :
    F (prodUpTo f N) = prodUpTo f N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [prodUpTo_succ, map_mul, ih (fun i hi => hf i (by omega)), hf N (by omega)]

/-- An endomorphism fixing every factor except two adjacent ones, and fixing the product of those
two, fixes the ordered product. -/
theorem prodUpTo_fixed_pair (F : G →* G) (f : ℕ → G) (k N : ℕ) (hN : k + 2 ≤ N)
    (hf : ∀ i < N, i ≠ k → i ≠ k + 1 → F (f i) = f i)
    (hk : F (f k * f (k + 1)) = f k * f (k + 1)) :
    F (prodUpTo f N) = prodUpTo f N := by
  obtain ⟨t, rfl⟩ : ∃ t, N = k + 2 + t := ⟨N - (k + 2), by omega⟩
  induction t with
  | zero =>
    have h0 : F (prodUpTo f k) = prodUpTo f k :=
      prodUpTo_fixed F f k (fun i hi => hf i (by omega) (by omega) (by omega))
    rw [show k + 2 + 0 = k + 1 + 1 by omega, prodUpTo_succ, prodUpTo_succ, mul_assoc, map_mul, h0,
      hk]
  | succ t ih =>
    rw [show k + 2 + (t + 1) = k + 2 + t + 1 by omega, prodUpTo_succ, map_mul,
      ih (by omega) (fun i hi => hf i (by omega)), hf _ (by omega) (by omega) (by omega)]

end Products

/-- The letter `z t` of `FreeGroup (Fin n)` (and `1` if `t ≥ n`; this case does not occur below). -/
def zN (n t : ℕ) : FreeGroup (Fin n) := if h : t < n then FreeGroup.of ⟨t, h⟩ else 1

theorem zN_of_lt {n t : ℕ} (h : t < n) : zN n t = FreeGroup.of ⟨t, h⟩ := dif_pos h

/-- `bdry n s G = [z s, z (s+1)] [z (s+2), z (s+3)] ⋯ [z (2G-2+s), z (2G-1+s)]` in
`FreeGroup (Fin n)`. -/
def bdry (n s G : ℕ) : FreeGroup (Fin n) :=
  prodUpTo (fun i => cmt (zN n (2 * i + s)) (zN n (2 * i + s + 1))) G

/-- Even case `n = 2g`: the boundary word `∏_{i=0}^{g-1} [z(2i), z(2i+1)]` (ordered, `i`
increasing). -/
def evenBoundary (g : ℕ) : FreeGroup (Fin (2 * g)) := bdry (2 * g) 0 g

/-- Odd case `n = 2g+1`: the boundary word `∏_{i=0}^{g-1} [z(2i+1), z(2i+2)]` (ordered, `i`
increasing); the letter `z 0` does not occur. -/
def oddBoundary (g : ℕ) : FreeGroup (Fin (2 * g + 1)) := bdry (2 * g + 1) 1 g

/-- The boundary word written as a list product over `Fin g`. -/
theorem evenBoundary_eq_list (g : ℕ) :
    evenBoundary g = (List.ofFn (fun i : Fin g =>
      cmt (FreeGroup.of (⟨2 * i.val, by omega⟩ : Fin (2 * g)))
        (FreeGroup.of (⟨2 * i.val + 1, by omega⟩ : Fin (2 * g))))).prod := by
  rw [evenBoundary, bdry, prodUpTo_eq_list]
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  rw [zN_of_lt (by omega), zN_of_lt (by omega)]
  rfl

/-- The odd boundary word written as a list product over `Fin g`. -/
theorem oddBoundary_eq_list (g : ℕ) :
    oddBoundary g = (List.ofFn (fun i : Fin g =>
      cmt (FreeGroup.of (⟨2 * i.val + 1, by omega⟩ : Fin (2 * g + 1)))
        (FreeGroup.of (⟨2 * i.val + 2, by omega⟩ : Fin (2 * g + 1))))).prod := by
  rw [oddBoundary, bdry, prodUpTo_eq_list]
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  rw [zN_of_lt (by omega), zN_of_lt (by omega)]

/-! ## 3. Extending an automorphism of a block of consecutive letters -/

section Extension

variable {m n : ℕ}

/-- The letters `p, p+1, …, p+m-1` of `Fin n`. -/
def off (p : ℕ) (h : p + m ≤ n) (a : Fin m) : Fin n := ⟨p + a.val, by have := a.isLt; omega⟩

@[simp] theorem off_val (p : ℕ) (h : p + m ≤ n) (a : Fin m) : (off p h a).val = p + a.val := rfl

theorem exists_off (p : ℕ) (h : p + m ≤ n) (i : Fin n) (hi : p ≤ i.val ∧ i.val < p + m) :
    ∃ a : Fin m, i = off p h a :=
  ⟨⟨i.val - p, by omega⟩, Fin.ext (by simp only [off_val]; omega)⟩

/-- Images of the letters under the extension. -/
def extGen (p : ℕ) (h : p + m ≤ n) (φ : FreeGroup (Fin m) →* FreeGroup (Fin m)) (i : Fin n) :
    FreeGroup (Fin n) :=
  if hi : p ≤ i.val ∧ i.val < p + m then
    FreeGroup.map (off p h) (φ (FreeGroup.of ⟨i.val - p, by omega⟩))
  else FreeGroup.of i

/-- The extension of `φ`, acting on the letters `p, …, p+m-1` through `φ` and fixing the others. -/
def extend (p : ℕ) (h : p + m ≤ n) (φ : FreeGroup (Fin m) →* FreeGroup (Fin m)) :
    FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (extGen p h φ)

theorem extend_of_off (p : ℕ) (h : p + m ≤ n) (φ : FreeGroup (Fin m) →* FreeGroup (Fin m))
    (a : Fin m) :
    extend p h φ (FreeGroup.of (off p h a)) = FreeGroup.map (off p h) (φ (FreeGroup.of a)) := by
  have ha := a.isLt
  rw [extend, FreeGroup.lift_apply_of, extGen, dif_pos (by simp only [off_val]; omega)]
  have : (⟨(off p h a).val - p, by simp only [off_val]; omega⟩ : Fin m) = a :=
    Fin.ext (by simp only [off_val]; omega)
  rw [this]

theorem extend_of_out (p : ℕ) (h : p + m ≤ n) (φ : FreeGroup (Fin m) →* FreeGroup (Fin m))
    (i : Fin n) (hi : ¬ (p ≤ i.val ∧ i.val < p + m)) :
    extend p h φ (FreeGroup.of i) = FreeGroup.of i := by
  rw [extend, FreeGroup.lift_apply_of, extGen, dif_neg hi]

theorem extend_map (p : ℕ) (h : p + m ≤ n) (φ : FreeGroup (Fin m) →* FreeGroup (Fin m))
    (x : FreeGroup (Fin m)) :
    extend p h φ (FreeGroup.map (off p h) x) = FreeGroup.map (off p h) (φ x) := by
  have : (extend p h φ).comp (FreeGroup.map (off p h)) = (FreeGroup.map (off p h)).comp φ :=
    FreeGroup.ext_hom _ _ (fun a => by simp [extend_of_off])
  exact DFunLike.congr_fun this x

theorem extend_comp (p : ℕ) (h : p + m ≤ n) (φ ψ : FreeGroup (Fin m) →* FreeGroup (Fin m)) :
    extend p h (φ.comp ψ) = (extend p h φ).comp (extend p h ψ) := by
  apply FreeGroup.ext_hom
  intro i
  by_cases hi : p ≤ i.val ∧ i.val < p + m
  · obtain ⟨a, rfl⟩ := exists_off p h i hi
    simp [extend_of_off, extend_map]
  · simp [extend_of_out _ _ _ _ hi]

theorem extend_id (p : ℕ) (h : p + m ≤ n) :
    extend p h (MonoidHom.id (FreeGroup (Fin m))) = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro i
  by_cases hi : p ≤ i.val ∧ i.val < p + m
  · obtain ⟨a, rfl⟩ := exists_off p h i hi
    simp [extend_of_off]
  · simp [extend_of_out _ _ _ _ hi]

theorem symm_comp_self_hom {G : Type*} [Group G] (e : G ≃* G) :
    e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G :=
  MonoidHom.ext fun x => by simp

theorem self_comp_symm_hom {G : Type*} [Group G] (e : G ≃* G) :
    e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G :=
  MonoidHom.ext fun x => by simp

/-- An automorphism of `FreeGroup (Fin m)` extends to an automorphism of `FreeGroup (Fin n)`
acting on the letters `p, …, p+m-1` and fixing the others. -/
def extendE (p : ℕ) (h : p + m ≤ n) (e : FreeGroup (Fin m) ≃* FreeGroup (Fin m)) :
    FreeGroup (Fin n) ≃* FreeGroup (Fin n) :=
  MonoidHom.toMulEquiv (extend p h e.toMonoidHom) (extend p h e.symm.toMonoidHom)
    (by rw [← extend_comp, symm_comp_self_hom, extend_id])
    (by rw [← extend_comp, self_comp_symm_hom, extend_id])

@[simp] theorem extendE_apply (p : ℕ) (h : p + m ≤ n) (e : FreeGroup (Fin m) ≃* FreeGroup (Fin m))
    (x : FreeGroup (Fin n)) : extendE p h e x = extend p h e.toMonoidHom x := rfl

@[simp] theorem extendE_symm_apply (p : ℕ) (h : p + m ≤ n)
    (e : FreeGroup (Fin m) ≃* FreeGroup (Fin m)) (x : FreeGroup (Fin n)) :
    (extendE p h e).symm x = extend p h e.symm.toMonoidHom x := rfl

theorem vecN_map_off (p : ℕ) (h : p + m ≤ n) (x : FreeGroup (Fin m)) :
    vecN (FreeGroup.map (off p h) x) = linExt (fun b => Pi.single (off p h b) 1) (vecN x) := by
  rw [vecN_hom]
  simp [FreeGroup.map.of]

theorem vecN_extend_off (p : ℕ) (h : p + m ≤ n) (φ : FreeGroup (Fin m) →* FreeGroup (Fin m))
    (a : Fin m) :
    vecN (extend p h φ (FreeGroup.of (off p h a))) =
      linExt (fun b => Pi.single (off p h b) 1) (vecN (φ (FreeGroup.of a))) := by
  rw [extend_of_off, vecN_map_off]

theorem vecN_extend_out (p : ℕ) (h : p + m ≤ n) (φ : FreeGroup (Fin m) →* FreeGroup (Fin m))
    (i : Fin n) (hi : ¬ (p ≤ i.val ∧ i.val < p + m)) :
    vecN (extend p h φ (FreeGroup.of i)) = Pi.single i 1 := by
  rw [extend_of_out _ _ _ _ hi, vecN_of]

/-- The extension fixes the letters outside the block. -/
theorem extend_zN (p : ℕ) (h : p + m ≤ n) (φ : FreeGroup (Fin m) →* FreeGroup (Fin m)) (t : ℕ)
    (ht : t < p ∨ p + m ≤ t) : extend p h φ (zN n t) = zN n t := by
  unfold zN
  split_ifs with h'
  · exact extend_of_out p h φ _ (by simp only; omega)
  · exact map_one _

theorem zN_eq_off (p : ℕ) (h : p + m ≤ n) (a : Fin m) (t : ℕ) (ht : t = p + a.val) :
    zN n t = FreeGroup.of (off p h a) := by
  subst ht
  rw [zN_of_lt (by have := a.isLt; omega)]
  rfl

end Extension

/-! ## 4. The extensions fix the boundary words

The moves of Lemmas 4.2 and 4.3 act on one pair or on two adjacent pairs; extended by the identity
on the other letters, they fix the boundary word (as used in the proof of Proposition 4.4). -/

/-- The free group on one pair `(z 0, z 1)`. -/
abbrev F2 : Type := FreeGroup (Fin 2)

/-- If `φ` acts on one pair and fixes its commutator `[z 0, z 1]`, then its extension to the pair
`(z p, z (p+1))`, `p = 2k + s`, fixes `bdry n s G` (for `k < G`). -/
theorem extend_bdry_single (n s G k p : ℕ) (hp : p = 2 * k + s) (h : p + 2 ≤ n) (hG : k < G)
    (φ : F2 →* F2)
    (hφ : φ (cmt (FreeGroup.of 0) (FreeGroup.of 1)) = cmt (FreeGroup.of 0) (FreeGroup.of 1)) :
    extend p h φ (bdry n s G) = bdry n s G := by
  subst hp
  unfold bdry
  apply prodUpTo_fixed
  intro i hi
  by_cases hik : i = k
  · subst hik
    have key : cmt (zN n (2 * i + s)) (zN n (2 * i + s + 1)) =
        FreeGroup.map (off (2 * i + s) h) (cmt (FreeGroup.of 0) (FreeGroup.of 1)) := by
      rw [zN_eq_off (2 * i + s) h 0 _ (by simp), zN_eq_off (2 * i + s) h 1 _ (by simp), map_cmt,
        FreeGroup.map.of, FreeGroup.map.of]
    rw [key, extend_map, hφ]
  · rw [map_cmt, extend_zN _ _ _ _ (by omega), extend_zN _ _ _ _ (by omega)]

/-- If `φ : F4 → F4` fixes `δ = [a,b][c,d]`, then its extension to two adjacent pairs
`(z p, …, z (p+3))`, `p = 2k + s`, fixes `bdry n s G` (for `k + 1 < G`): the boundary word is
(prefix) · (the two adjacent commutators) · (suffix), and the prefix and suffix are fixed letter by
letter. -/
theorem extend_bdry_pair (n s G k p : ℕ) (hp : p = 2 * k + s) (h : p + 4 ≤ n) (hG : k + 1 < G)
    (φ : F4 →* F4) (hφ : φ delta = delta) : extend p h φ (bdry n s G) = bdry n s G := by
  subst hp
  unfold bdry
  apply prodUpTo_fixed_pair _ _ k G (by omega)
  · intro i hi hik hik1
    rw [map_cmt, extend_zN _ _ _ _ (by omega), extend_zN _ _ _ _ (by omega)]
  · have key : cmt (zN n (2 * k + s)) (zN n (2 * k + s + 1)) *
          cmt (zN n (2 * (k + 1) + s)) (zN n (2 * (k + 1) + s + 1)) =
        FreeGroup.map (off (2 * k + s) h) delta := by
      rw [zN_eq_off (2 * k + s) h 0 _ (by simp), zN_eq_off (2 * k + s) h 1 _ (by simp),
        zN_eq_off (2 * k + s) h 2 _ (by simp; omega), zN_eq_off (2 * k + s) h 3 _ (by simp; omega)]
      simp only [delta, R, Q, comm_def, cmt, ga, gb, gc, gd, map_mul, map_inv, FreeGroup.map.of]
    rw [key, extend_map, hφ]

/-- `extend_bdry_single` for the automorphism `extendE`. -/
theorem extendE_bdry_single (n s G k p : ℕ) (hp : p = 2 * k + s) (h : p + 2 ≤ n) (hG : k < G)
    (e : F2 ≃* F2)
    (he : e (cmt (FreeGroup.of 0) (FreeGroup.of 1)) = cmt (FreeGroup.of 0) (FreeGroup.of 1)) :
    extendE p h e (bdry n s G) = bdry n s G :=
  extend_bdry_single n s G k p hp h hG e.toMonoidHom he

/-- `extend_bdry_pair` for the automorphism `extendE`. -/
theorem extendE_bdry_pair (n s G k p : ℕ) (hp : p = 2 * k + s) (h : p + 4 ≤ n) (hG : k + 1 < G)
    (e : F4 ≃* F4) (he : e delta = delta) : extendE p h e (bdry n s G) = bdry n s G :=
  extend_bdry_pair n s G k p hp h hG e.toMonoidHom he

/-! ## 5. The alternating forms -/

/-- The even alternating form on indices: `⟨e_{2i}, e_{2i+1}⟩ = -1`, `⟨e_{2i+1}, e_{2i}⟩ = 1`,
and `0` on all other pairs of basis vectors. -/
def omegaNat (a b : ℕ) : ℤ :=
  if a % 2 = 0 ∧ b = a + 1 then -1 else if a % 2 = 1 ∧ a = b + 1 then 1 else 0

theorem omegaNat_pair (i : ℕ) : omegaNat (2 * i) (2 * i + 1) = -1 := by
  rw [omegaNat, if_pos (show 2 * i % 2 = 0 ∧ 2 * i + 1 = 2 * i + 1 by omega)]

theorem omegaNat_pair' (i : ℕ) : omegaNat (2 * i + 1) (2 * i) = 1 := by
  rw [omegaNat, if_neg (show ¬ ((2 * i + 1) % 2 = 0 ∧ 2 * i = 2 * i + 1 + 1) by omega),
    if_pos (show (2 * i + 1) % 2 = 1 ∧ 2 * i + 1 = 2 * i + 1 by omega)]

theorem omegaNat_antisymm (a b : ℕ) : omegaNat b a = -omegaNat a b := by
  simp only [omegaNat]
  split_ifs <;> omega

/-- The bilinear form on `ℤⁿ` with matrix `ω`. -/
def bform {n : ℕ} (ω : Fin n → Fin n → ℤ) (v w : Fin n → ℤ) : ℤ := ∑ i, ∑ j, ω i j * v i * w j

section BForm

variable {n : ℕ} (ω : Fin n → Fin n → ℤ)

theorem bform_single (a b : Fin n) : bform ω (Pi.single a 1) (Pi.single b 1) = ω a b := by
  simp [bform, Pi.single_apply]

theorem bform_add_left (u v w : Fin n → ℤ) : bform ω (u + v) w = bform ω u w + bform ω v w := by
  simp [bform, mul_add, add_mul, Finset.sum_add_distrib]

theorem bform_add_right (u v w : Fin n → ℤ) : bform ω u (v + w) = bform ω u v + bform ω u w := by
  simp [bform, mul_add, Finset.sum_add_distrib]

theorem bform_smul_left (c : ℤ) (v w : Fin n → ℤ) : bform ω (c • v) w = c * bform ω v w := by
  simp only [bform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem bform_smul_right (c : ℤ) (v w : Fin n → ℤ) : bform ω v (c • w) = c * bform ω v w := by
  simp only [bform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end BForm

/-- The alternating form of the even case `n = 2g`: the pairs are `(e_{2i}, e_{2i+1})`, with
`⟨e_{2i}, e_{2i+1}⟩ = -1` and `⟨e_{2i+1}, e_{2i}⟩ = 1`. -/
def formE (g : ℕ) : (Fin (2 * g) → ℤ) → (Fin (2 * g) → ℤ) → ℤ :=
  bform (fun i j => omegaNat i.val j.val)

/-- The alternating form of the odd case `n = 2g+1`: the pairs are `(e_{2i+1}, e_{2i+2})`, with
`⟨e_{2i+1}, e_{2i+2}⟩ = -1` and `⟨e_{2i+2}, e_{2i+1}⟩ = 1`; `e_0` pairs to `0` with everything. -/
def formO (g : ℕ) : (Fin (2 * g + 1) → ℤ) → (Fin (2 * g + 1) → ℤ) → ℤ :=
  bform (fun i j => if i.val = 0 ∨ j.val = 0 then 0 else omegaNat (i.val - 1) (j.val - 1))

@[simp] theorem formE_single (g : ℕ) (i j : Fin (2 * g)) :
    formE g (Pi.single i 1) (Pi.single j 1) =
      if i.val % 2 = 0 ∧ j.val = i.val + 1 then -1
      else if i.val % 2 = 1 ∧ i.val = j.val + 1 then 1 else 0 :=
  bform_single _ i j

@[simp] theorem formO_single (g : ℕ) (i j : Fin (2 * g + 1)) :
    formO g (Pi.single i 1) (Pi.single j 1) =
      if i.val % 2 = 1 ∧ j.val = i.val + 1 then -1
      else if i.val % 2 = 0 ∧ 0 < j.val ∧ i.val = j.val + 1 then 1 else 0 := by
  rw [formO, bform_single, omegaNat]
  split_ifs <;> omega

theorem formE_single_eq (g : ℕ) (i j : Fin (2 * g)) :
    formE g (Pi.single i 1) (Pi.single j 1) = omegaNat i.val j.val :=
  bform_single _ i j

theorem formE_add_left (g : ℕ) (u v w : Fin (2 * g) → ℤ) :
    formE g (u + v) w = formE g u w + formE g v w := bform_add_left _ u v w
theorem formE_add_right (g : ℕ) (u v w : Fin (2 * g) → ℤ) :
    formE g u (v + w) = formE g u v + formE g u w := bform_add_right _ u v w
theorem formE_smul_left (g : ℕ) (c : ℤ) (v w : Fin (2 * g) → ℤ) :
    formE g (c • v) w = c * formE g v w := bform_smul_left _ c v w
theorem formE_smul_right (g : ℕ) (c : ℤ) (v w : Fin (2 * g) → ℤ) :
    formE g v (c • w) = c * formE g v w := bform_smul_right _ c v w
theorem formO_add_left (g : ℕ) (u v w : Fin (2 * g + 1) → ℤ) :
    formO g (u + v) w = formO g u w + formO g v w := bform_add_left _ u v w
theorem formO_add_right (g : ℕ) (u v w : Fin (2 * g + 1) → ℤ) :
    formO g u (v + w) = formO g u v + formO g u w := bform_add_right _ u v w
theorem formO_smul_left (g : ℕ) (c : ℤ) (v w : Fin (2 * g + 1) → ℤ) :
    formO g (c • v) w = c * formO g v w := bform_smul_left _ c v w
theorem formO_smul_right (g : ℕ) (c : ℤ) (v w : Fin (2 * g + 1) → ℤ) :
    formO g v (c • w) = c * formO g v w := bform_smul_right _ c v w

/-! ## 6. Lemma 4.2 (i): the moves inside one pair -/

def mulAGen : Fin 2 → F2
  | 0 => FreeGroup.of 0 * FreeGroup.of 1
  | 1 => FreeGroup.of 1

def mulAInvGen : Fin 2 → F2
  | 0 => FreeGroup.of 0 * (FreeGroup.of 1)⁻¹
  | 1 => FreeGroup.of 1

def mulBGen : Fin 2 → F2
  | 0 => FreeGroup.of 0
  | 1 => FreeGroup.of 1 * FreeGroup.of 0

def mulBInvGen : Fin 2 → F2
  | 0 => FreeGroup.of 0
  | 1 => FreeGroup.of 1 * (FreeGroup.of 0)⁻¹

/-- `a ↦ a b` (`b` fixed). -/
def mulA : F2 →* F2 := FreeGroup.lift mulAGen
/-- `a ↦ a b⁻¹` (`b` fixed). -/
def mulAInv : F2 →* F2 := FreeGroup.lift mulAInvGen
/-- `b ↦ b a` (`a` fixed). -/
def mulB : F2 →* F2 := FreeGroup.lift mulBGen
/-- `b ↦ b a⁻¹` (`a` fixed). -/
def mulBInv : F2 →* F2 := FreeGroup.lift mulBInvGen

section F2Values

@[simp] theorem mulA_0 : mulA (FreeGroup.of 0) = FreeGroup.of 0 * FreeGroup.of 1 :=
  FreeGroup.lift_apply_of
@[simp] theorem mulA_1 : mulA (FreeGroup.of 1) = FreeGroup.of 1 := FreeGroup.lift_apply_of
@[simp] theorem mulAInv_0 : mulAInv (FreeGroup.of 0) = FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ :=
  FreeGroup.lift_apply_of
@[simp] theorem mulAInv_1 : mulAInv (FreeGroup.of 1) = FreeGroup.of 1 := FreeGroup.lift_apply_of
@[simp] theorem mulB_0 : mulB (FreeGroup.of 0) = FreeGroup.of 0 := FreeGroup.lift_apply_of
@[simp] theorem mulB_1 : mulB (FreeGroup.of 1) = FreeGroup.of 1 * FreeGroup.of 0 :=
  FreeGroup.lift_apply_of
@[simp] theorem mulBInv_0 : mulBInv (FreeGroup.of 0) = FreeGroup.of 0 := FreeGroup.lift_apply_of
@[simp] theorem mulBInv_1 : mulBInv (FreeGroup.of 1) = FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ :=
  FreeGroup.lift_apply_of

end F2Values

/-- Two homomorphisms out of `F2` agree if they agree on the two letters. -/
theorem hom_ext2 {G : Type*} [Group G] {f g : F2 →* G}
    (h0 : f (FreeGroup.of 0) = g (FreeGroup.of 0)) (h1 : f (FreeGroup.of 1) = g (FreeGroup.of 1)) :
    f = g := by
  apply FreeGroup.ext_hom
  intro i
  match i with
  | 0 => exact h0
  | 1 => exact h1

/-- Lemma 4.2 (i): `a ↦ a b` is an automorphism, with inverse `a ↦ a b⁻¹`. -/
def mulAE : F2 ≃* F2 :=
  MonoidHom.toMulEquiv mulA mulAInv
    (hom_ext2 (by simp [mul_assoc]) (by simp)) (hom_ext2 (by simp [mul_assoc]) (by simp))

/-- Lemma 4.2 (i): `b ↦ b a` is an automorphism, with inverse `b ↦ b a⁻¹`. -/
def mulBE : F2 ≃* F2 :=
  MonoidHom.toMulEquiv mulB mulBInv
    (hom_ext2 (by simp) (by simp [mul_assoc])) (hom_ext2 (by simp) (by simp [mul_assoc]))

@[simp] theorem mulAE_apply (x : F2) : mulAE x = mulA x := rfl
@[simp] theorem mulAE_symm_apply (x : F2) : mulAE.symm x = mulAInv x := rfl
@[simp] theorem mulBE_apply (x : F2) : mulBE x = mulB x := rfl
@[simp] theorem mulBE_symm_apply (x : F2) : mulBE.symm x = mulBInv x := rfl

/-- Lemma 4.2 (i): `[ab, b] = [a, b]`. -/
theorem mulAE_cmt :
    mulAE (cmt (FreeGroup.of 0) (FreeGroup.of 1)) = cmt (FreeGroup.of 0) (FreeGroup.of 1) := by
  rw [mulAE_apply, map_cmt, mulA_0, mulA_1]
  simp only [cmt]
  group

/-- Lemma 4.2 (i): `[a, ba] = [a, b]`. -/
theorem mulBE_cmt :
    mulBE (cmt (FreeGroup.of 0) (FreeGroup.of 1)) = cmt (FreeGroup.of 0) (FreeGroup.of 1) := by
  rw [mulBE_apply, map_cmt, mulB_0, mulB_1]
  simp only [cmt]
  group

theorem vecN_mulAE (a : Fin 2) :
    vecN (mulAE (FreeGroup.of a)) = Pi.single a 1 + (if a.val = 0 then Pi.single 1 1 else 0) := by
  fin_cases a <;> simp

theorem vecN_mulBE (a : Fin 2) :
    vecN (mulBE (FreeGroup.of a)) = Pi.single a 1 + (if a.val = 1 then Pi.single 0 1 else 0) := by
  fin_cases a <;> simp

/-! ## 7. Lemma 4.2 (ii): the swap of two adjacent pairs -/

/-- Lemma 4.2 (ii): with `D = [c,d]`, the automorphism `a ↦ c, b ↦ d, c ↦ D⁻¹ a D, d ↦ D⁻¹ b D`.
It is the inverse `H⁻¹` of the automorphism `H` of `LogShellEdge.Reuse.ShearFreeGroup`; its inverse
is `H`:
`a ↦ C c C⁻¹, b ↦ C d C⁻¹, c ↦ a, d ↦ b` with `C = [a,b]`. -/
def pairSwap : F4 ≃* F4 := Hequiv.symm

theorem pairSwap_apply (x : F4) : pairSwap x = Hinv x := rfl
theorem pairSwap_symm_apply (x : F4) : pairSwap.symm x = H x := rfl

theorem pairSwap_values :
    pairSwap ga = gc ∧ pairSwap gb = gd ∧ pairSwap gc = Q⁻¹ * ga * Q ∧ pairSwap gd = Q⁻¹ * gb * Q :=
  ⟨Hinv_a, Hinv_b, Hinv_c, Hinv_d⟩

theorem pairSwap_symm_values :
    pairSwap.symm ga = R * gc * R⁻¹ ∧ pairSwap.symm gb = R * gd * R⁻¹ ∧ pairSwap.symm gc = ga ∧
      pairSwap.symm gd = gb :=
  ⟨H_a, H_b, H_c, H_d⟩

/-- Lemma 4.2 (ii): the swap fixes `[a,b][c,d]` (the image of the commutator product is
`[c,d] · D⁻¹[a,b]D = [a,b] D`). -/
theorem pairSwap_delta : pairSwap delta = delta := Hinv_delta

theorem pairSwap_symm_delta : pairSwap.symm delta = delta := H_delta

/-- The permutation `0 ↔ 2`, `1 ↔ 3` of `Fin 4`. -/
def swap4 (a : Fin 4) : Fin 4 := ⟨(a.val + 2) % 4, Nat.mod_lt _ (by norm_num)⟩

/-- Lemma 4.2 (ii): on the abelianization the swap exchanges the two pairs. -/
theorem vecN_pairSwap (a : Fin 4) : vecN (pairSwap (FreeGroup.of a)) = Pi.single (swap4 a) 1 := by
  fin_cases a <;> simp [pairSwap_apply, Hinv, hInvGen, Q, comm_def, ga, gb, gc, gd, swap4]

theorem vecN_pairSwap_symm (a : Fin 4) :
    vecN (pairSwap.symm (FreeGroup.of a)) = Pi.single (swap4 a) 1 := by
  fin_cases a <;> simp [pairSwap_symm_apply, H, hGen, R, comm_def, ga, gb, gc, gd, swap4]

/-! ## 8. The automorphisms `U_d` and `U_c` of `F(a,b,c,d)`

This is the construction following Lemma 4.3 of the note. On the abelianization of `F4` (letters
`a, b, c, d` = `e₀, e₁, e₂, e₃`) the form is `⟨a,b⟩ = ⟨c,d⟩ = -1`, and `T_v(x) = x + ⟨x,v⟩ v`.
The note puts `U_w(x) = x + ⟨x,a⟩ w + ⟨x,w⟩ a` for `⟨a,w⟩ = 0`, and realizes
`U_d = T_{a+d} T_a⁻¹ T_d⁻¹` by the composite of `M` (whose abelianization is `T_{a+d}`, `M_ab` of
`LogShellEdge.Reuse.ShearFreeGroup`) with the inverses of `b ↦ b a` (inducing `T_a`) and of
`c ↦ c d⁻¹` (inducing `T_d`). Conjugating by `J` applied to the second pair (`c ↦ c d c⁻¹`,
`d ↦ c⁻¹`) gives `U_c`. -/

def tbGen : Fin 4 → F4
  | 0 => ga
  | 1 => gb * ga
  | 2 => gc
  | 3 => gd

def tbInvGen : Fin 4 → F4
  | 0 => ga
  | 1 => gb * ga⁻¹
  | 2 => gc
  | 3 => gd

def tcGen : Fin 4 → F4
  | 0 => ga
  | 1 => gb
  | 2 => gc * gd⁻¹
  | 3 => gd

def tcInvGen : Fin 4 → F4
  | 0 => ga
  | 1 => gb
  | 2 => gc * gd
  | 3 => gd

def jcGen : Fin 4 → F4
  | 0 => ga
  | 1 => gb
  | 2 => gc * gd * gc⁻¹
  | 3 => gc⁻¹

def jcInvGen : Fin 4 → F4
  | 0 => ga
  | 1 => gb
  | 2 => gd⁻¹
  | 3 => gd * gc * gd⁻¹

/-- `b ↦ b a` on `F4` (it induces `T_a`). -/
def TB : F4 →* F4 := FreeGroup.lift tbGen
/-- `b ↦ b a⁻¹` on `F4`. -/
def TBinv : F4 →* F4 := FreeGroup.lift tbInvGen
/-- `c ↦ c d⁻¹` on `F4` (it induces `T_d`). -/
def TC : F4 →* F4 := FreeGroup.lift tcGen
/-- `c ↦ c d` on `F4`. -/
def TCinv : F4 →* F4 := FreeGroup.lift tcInvGen
/-- `J` applied to the second pair: `c ↦ c d c⁻¹`, `d ↦ c⁻¹`. -/
def JC : F4 →* F4 := FreeGroup.lift jcGen
/-- The inverse of `JC`: `c ↦ d⁻¹`, `d ↦ d c d⁻¹`. -/
def JCinv : F4 →* F4 := FreeGroup.lift jcInvGen

section F4Values

@[simp] theorem TB_a : TB ga = ga := FreeGroup.lift_apply_of
@[simp] theorem TB_b : TB gb = gb * ga := FreeGroup.lift_apply_of
@[simp] theorem TB_c : TB gc = gc := FreeGroup.lift_apply_of
@[simp] theorem TB_d : TB gd = gd := FreeGroup.lift_apply_of
@[simp] theorem TBinv_a : TBinv ga = ga := FreeGroup.lift_apply_of
@[simp] theorem TBinv_b : TBinv gb = gb * ga⁻¹ := FreeGroup.lift_apply_of
@[simp] theorem TBinv_c : TBinv gc = gc := FreeGroup.lift_apply_of
@[simp] theorem TBinv_d : TBinv gd = gd := FreeGroup.lift_apply_of
@[simp] theorem TC_a : TC ga = ga := FreeGroup.lift_apply_of
@[simp] theorem TC_b : TC gb = gb := FreeGroup.lift_apply_of
@[simp] theorem TC_c : TC gc = gc * gd⁻¹ := FreeGroup.lift_apply_of
@[simp] theorem TC_d : TC gd = gd := FreeGroup.lift_apply_of
@[simp] theorem TCinv_a : TCinv ga = ga := FreeGroup.lift_apply_of
@[simp] theorem TCinv_b : TCinv gb = gb := FreeGroup.lift_apply_of
@[simp] theorem TCinv_c : TCinv gc = gc * gd := FreeGroup.lift_apply_of
@[simp] theorem TCinv_d : TCinv gd = gd := FreeGroup.lift_apply_of
@[simp] theorem JC_a : JC ga = ga := FreeGroup.lift_apply_of
@[simp] theorem JC_b : JC gb = gb := FreeGroup.lift_apply_of
@[simp] theorem JC_c : JC gc = gc * gd * gc⁻¹ := FreeGroup.lift_apply_of
@[simp] theorem JC_d : JC gd = gc⁻¹ := FreeGroup.lift_apply_of
@[simp] theorem JCinv_a : JCinv ga = ga := FreeGroup.lift_apply_of
@[simp] theorem JCinv_b : JCinv gb = gb := FreeGroup.lift_apply_of
@[simp] theorem JCinv_c : JCinv gc = gd⁻¹ := FreeGroup.lift_apply_of
@[simp] theorem JCinv_d : JCinv gd = gd * gc * gd⁻¹ := FreeGroup.lift_apply_of

end F4Values

def TBE : F4 ≃* F4 :=
  MonoidHom.toMulEquiv TB TBinv
    (hom_ext4 (by simp) (by simp [mul_assoc]) (by simp) (by simp))
    (hom_ext4 (by simp) (by simp [mul_assoc]) (by simp) (by simp))

def TCE : F4 ≃* F4 :=
  MonoidHom.toMulEquiv TC TCinv
    (hom_ext4 (by simp) (by simp) (by simp [mul_assoc]) (by simp))
    (hom_ext4 (by simp) (by simp) (by simp [mul_assoc]) (by simp))

def JCE : F4 ≃* F4 :=
  MonoidHom.toMulEquiv JC JCinv
    (hom_ext4 (by simp) (by simp) (by simp only [MonoidHom.comp_apply, JC_c, map_mul, map_inv,
        JCinv_c, JCinv_d, MonoidHom.id_apply]; group) (by simp))
    (hom_ext4 (by simp) (by simp) (by simp) (by simp only [MonoidHom.comp_apply, JCinv_d, map_mul,
        map_inv, JC_c, JC_d, MonoidHom.id_apply]; group))

theorem TBinv_delta : TBinv delta = delta := by
  simp only [delta, R, Q, comm_def, map_mul, map_inv, TBinv_a, TBinv_b, TBinv_c, TBinv_d]
  group

theorem TCinv_delta : TCinv delta = delta := by
  simp only [delta, R, Q, comm_def, map_mul, map_inv, TCinv_a, TCinv_b, TCinv_c, TCinv_d]
  group

theorem JC_delta : JC delta = delta := by
  simp only [delta, R, Q, comm_def, map_mul, map_inv, JC_a, JC_b, JC_c, JC_d]
  group

theorem JCinv_delta : JCinv delta = delta := by
  simp only [delta, R, Q, comm_def, map_mul, map_inv, JCinv_a, JCinv_b, JCinv_c, JCinv_d]
  group

/-- The automorphism inducing `U_d`: `M ∘ (b ↦ b a)⁻¹ ∘ (c ↦ c d⁻¹)⁻¹`. -/
def UdE : F4 ≃* F4 := (TCE.symm.trans TBE.symm).trans Mequiv

/-- The automorphism inducing `U_c`: `J_c⁻¹ ∘ U_d ∘ J_c`. -/
def UcE : F4 ≃* F4 := JCE.trans (UdE.trans JCE.symm)

theorem UdE_apply (x : F4) : UdE x = M (TBinv (TCinv x)) := rfl

theorem UcE_apply (x : F4) : UcE x = JCinv (UdE (JC x)) := rfl

theorem UdE_a : UdE ga = ga := by
  rw [UdE_apply, TCinv_a, TBinv_a, M_a]

theorem UcE_a : UcE ga = ga := by
  rw [UcE_apply, JC_a, UdE_a, JCinv_a]

theorem UdE_delta : UdE delta = delta := by
  rw [UdE_apply, TCinv_delta, TBinv_delta, M_delta]

theorem UcE_delta : UcE delta = delta := by
  rw [UcE_apply, JC_delta, UdE_delta, JCinv_delta]

@[simp] theorem vecN_ga : vecN ga = Pi.single 0 1 := vecN_of 0
@[simp] theorem vecN_gb : vecN gb = Pi.single 1 1 := vecN_of 1
@[simp] theorem vecN_gc : vecN gc = Pi.single 2 1 := vecN_of 2
@[simp] theorem vecN_gd : vecN gd = Pi.single 3 1 := vecN_of 3

/-- The abelianization of an endomorphism of `F4`, through the images of `a, b, c, d`. -/
theorem vecN_hom4 (φ : F4 →* F4) (x : F4) :
    vecN (φ x) = linExt ![vecN (φ ga), vecN (φ gb), vecN (φ gc), vecN (φ gd)] (vecN x) := by
  rw [vecN_hom]
  congr 1
  funext a
  fin_cases a <;> rfl

theorem vecN_M_values :
    vecN (M ga) = Pi.single 0 1 ∧ vecN (M gb) = Pi.single 0 1 + Pi.single 1 1 + Pi.single 3 1 ∧
      vecN (M gc) = Pi.single 2 1 - Pi.single 0 1 - Pi.single 3 1 ∧
        vecN (M gd) = Pi.single 3 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := M_ab
  obtain ⟨g0, g1, g2, g3⟩ := vec_gen
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [vecN_eq_vec, h0, h1, h2, h3, g0, g1, g2, g3]

/-- `U_d`: `a ↦ a`, `b ↦ b + d`, `c ↦ c - a`, `d ↦ d` on the abelianization. -/
theorem vecN_UdE_values :
    vecN (UdE ga) = Pi.single 0 1 ∧ vecN (UdE gb) = Pi.single 1 1 + Pi.single 3 1 ∧
      vecN (UdE gc) = Pi.single 2 1 - Pi.single 0 1 ∧ vecN (UdE gd) = Pi.single 3 1 := by
  obtain ⟨m0, m1, m2, m3⟩ := vecN_M_values
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [UdE_a, vecN_ga]
  · rw [UdE_apply, TCinv_b, TBinv_b, map_mul, map_inv, vecN_mul, vecN_inv, m1, m0]
    abel
  · rw [UdE_apply, TCinv_c, map_mul, TBinv_c, TBinv_d, map_mul, vecN_mul, m2, m3]
    abel
  · rw [UdE_apply, TCinv_d, TBinv_d, m3]

theorem vecN_JCinv (x : F4) :
    vecN (JCinv x) =
      linExt ![Pi.single 0 1, Pi.single 1 1, -Pi.single 3 1, Pi.single 2 1] (vecN x) := by
  rw [vecN_hom4]
  have hd : vecN (JCinv gd) = Pi.single 2 1 := by
    rw [JCinv_d, vecN_mul, vecN_mul, vecN_inv, vecN_gd, vecN_gc]
    abel
  rw [hd, JCinv_a, JCinv_b, JCinv_c, vecN_inv, vecN_ga, vecN_gb, vecN_gd]

/-- `U_c`: `a ↦ a`, `b ↦ b + c`, `c ↦ c`, `d ↦ d + a` on the abelianization. -/
theorem vecN_UcE_values :
    vecN (UcE ga) = Pi.single 0 1 ∧ vecN (UcE gb) = Pi.single 1 1 + Pi.single 2 1 ∧
      vecN (UcE gc) = Pi.single 2 1 ∧ vecN (UcE gd) = Pi.single 3 1 + Pi.single 0 1 := by
  obtain ⟨u0, u1, u2, u3⟩ := vecN_UdE_values
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [UcE_a, vecN_ga]
  · rw [UcE_apply, JC_b, vecN_JCinv, u1]
    simp
  · have : vecN (UdE (JC gc)) = Pi.single 3 1 := by
      rw [JC_c, map_mul, map_mul, map_inv, vecN_mul, vecN_mul, vecN_inv, u3]
      abel
    rw [UcE_apply, vecN_JCinv, this]
    simp
  · have : vecN (UdE (JC gd)) = Pi.single 0 1 - Pi.single 2 1 := by
      rw [JC_d, map_inv, vecN_inv, u2]
      abel
    rw [UcE_apply, vecN_JCinv, this]
    simp
    abel

/-- The two base moves: `U4 0 = U_c` and `U4 1 = U_d`. -/
def U4 : Fin 2 → (F4 ≃* F4)
  | 0 => UcE
  | 1 => UdE

theorem U4_a (r : Fin 2) : U4 r ga = ga := by
  match r with
  | 0 => exact UcE_a
  | 1 => exact UdE_a

theorem U4_delta (r : Fin 2) : U4 r delta = delta := by
  match r with
  | 0 => exact UcE_delta
  | 1 => exact UdE_delta

/-- `U4 r` induces `U_w` with `w = e_{2+r}`: `e_a ↦ e_a + ⟨e_a, e_0⟩ w + ⟨e_a, w⟩ e_0`. -/
theorem vecN_U4 (r : Fin 2) (a : Fin 4) :
    vecN (U4 r (FreeGroup.of a)) =
      Pi.single a 1 + omegaNat a.val 0 • Pi.single (⟨2 + r.val, by omega⟩ : Fin 4) 1 +
        omegaNat a.val (2 + r.val) • Pi.single 0 1 := by
  obtain ⟨c0, c1, c2, c3⟩ := vecN_UcE_values
  obtain ⟨d0, d1, d2, d3⟩ := vecN_UdE_values
  have e0 : (FreeGroup.of 0 : F4) = ga := rfl
  have e1 : (FreeGroup.of 1 : F4) = gb := rfl
  have e2 : (FreeGroup.of 2 : F4) = gc := rfl
  have e3 : (FreeGroup.of 3 : F4) = gd := rfl
  have u0 : U4 0 = UcE := rfl
  have u1 : U4 1 = UdE := rfl
  match r, a with
  | 0, 0 => rw [u0, e0, c0]; simp [omegaNat]
  | 0, 1 => rw [u0, e1, c1]; simp [omegaNat]
  | 0, 2 => rw [u0, e2, c2]; simp [omegaNat]
  | 0, 3 => rw [u0, e3, c3]; simp [omegaNat]
  | 1, 0 => rw [u1, e0, d0]; simp [omegaNat]
  | 1, 1 => rw [u1, e1, d1]; simp [omegaNat]
  | 1, 2 => rw [u1, e2, d2]; simp [omegaNat, sub_eq_add_neg]
  | 1, 3 => rw [u1, e3, d3]; simp [omegaNat]

/-! ## 9. The permutation of letters exchanging two adjacent pairs -/

/-- Split all `if`s and close the arithmetic goals (clearing the `True` conjuncts that `split_ifs`
leaves behind, which `omega` does not read). -/
local macro "omega_ifs" : tactic =>
  `(tactic| (split_ifs <;>
    (try simp only [and_true, true_and, and_false, false_and, not_true_eq_false, not_false_eq_true,
      true_or, or_true, false_or, or_false] at *) <;> omega))

section SwapIdx

variable {n : ℕ}

/-- The permutation of `Fin n` exchanging the letters `p, p+1` with `p+2, p+3` (and fixing the
others): the action of the swap of two adjacent pairs on the indices. -/
def swapIdx (p : ℕ) (h : p + 4 ≤ n) (i : Fin n) : Fin n :=
  if hi : p ≤ i.val ∧ i.val < p + 4 then ⟨p + (i.val - p + 2) % 4, by omega⟩ else i

theorem swapIdx_val (p : ℕ) (h : p + 4 ≤ n) (i : Fin n) :
    (swapIdx p h i).val =
      if p ≤ i.val ∧ i.val < p + 4 then p + (i.val - p + 2) % 4 else i.val := by
  unfold swapIdx
  split_ifs <;> rfl

/-- Explicitly: `p ↦ p+2`, `p+1 ↦ p+3`, `p+2 ↦ p`, `p+3 ↦ p+1`, other letters fixed. -/
theorem swapIdx_val' (p : ℕ) (h : p + 4 ≤ n) (i : Fin n) :
    (swapIdx p h i).val =
      if p ≤ i.val ∧ i.val < p + 2 then i.val + 2
      else if p + 2 ≤ i.val ∧ i.val < p + 4 then i.val - 2 else i.val := by
  rw [swapIdx_val]
  omega_ifs

theorem swapIdx_swapIdx (p : ℕ) (h : p + 4 ≤ n) (i : Fin n) : swapIdx p h (swapIdx p h i) = i := by
  apply Fin.ext
  simp only [swapIdx_val]
  omega_ifs

theorem swapIdx_of_out (p : ℕ) (h : p + 4 ≤ n) (i : Fin n) (hi : ¬ (p ≤ i.val ∧ i.val < p + 4)) :
    swapIdx p h i = i := by
  unfold swapIdx
  rw [dif_neg hi]

theorem swapIdx_p0 (p : ℕ) (h : p + 4 ≤ n) : swapIdx p h ⟨p, by omega⟩ = ⟨p + 2, by omega⟩ :=
  Fin.ext (by simp only [swapIdx_val']; omega_ifs)

theorem swapIdx_p1 (p : ℕ) (h : p + 4 ≤ n) : swapIdx p h ⟨p + 1, by omega⟩ = ⟨p + 3, by omega⟩ :=
  Fin.ext (by simp only [swapIdx_val']; omega_ifs)

theorem swapIdx_p2 (p : ℕ) (h : p + 4 ≤ n) : swapIdx p h ⟨p + 2, by omega⟩ = ⟨p, by omega⟩ :=
  Fin.ext (by simp only [swapIdx_val']; omega_ifs)

theorem swapIdx_p3 (p : ℕ) (h : p + 4 ≤ n) : swapIdx p h ⟨p + 3, by omega⟩ = ⟨p + 1, by omega⟩ :=
  Fin.ext (by simp only [swapIdx_val']; omega_ifs)

theorem off_swap4 (p : ℕ) (h : p + 4 ≤ n) (a : Fin 4) :
    off p h (swap4 a) = swapIdx p h (off p h a) := by
  have ha := a.isLt
  apply Fin.ext
  rw [swapIdx_val, off_val, off_val, if_pos (show p ≤ p + a.val ∧ p + a.val < p + 4 by omega)]
  simp only [swap4]
  omega

/-- The even form is invariant under the exchange of two adjacent pairs (`p` even). -/
theorem omegaNat_swapIdx (p : ℕ) (h : p + 4 ≤ n) (hp : p % 2 = 0) (i j : Fin n) :
    omegaNat (swapIdx p h i).val (swapIdx p h j).val = omegaNat i.val j.val := by
  simp only [swapIdx_val, omegaNat]
  omega_ifs

/-- The even form against a letter below the block is unchanged by the exchange (`p` even). -/
theorem omegaNat_swapIdx_fix (p : ℕ) (h : p + 4 ≤ n) (hp : p % 2 = 0) (i : Fin n) (c : ℕ)
    (hc : c < p) : omegaNat (swapIdx p h i).val c = omegaNat i.val c := by
  simp only [swapIdx_val, omegaNat]
  omega_ifs

end SwapIdx

/-! ## 10. Extended moves: generic facts -/

section ExtendMoves

variable {m n : ℕ}

theorem extend_of_eq_off (p : ℕ) (h : p + m ≤ n) (φ : FreeGroup (Fin m) →* FreeGroup (Fin m))
    (a : Fin m) (i : Fin n) (hi : i.val = p + a.val) (ha : φ (FreeGroup.of a) = FreeGroup.of a) :
    extend p h φ (FreeGroup.of i) = FreeGroup.of i := by
  obtain rfl : i = off p h a := Fin.ext hi
  rw [extend_of_off, ha, FreeGroup.map.of]

theorem extend_of_eq_off' (p : ℕ) (h : p + m ≤ n) (φ : FreeGroup (Fin m) →* FreeGroup (Fin m))
    (a : Fin m) (i : Fin n) (hi : i.val = p + a.val) :
    extend p h φ (FreeGroup.of i) = FreeGroup.map (off p h) (φ (FreeGroup.of a)) := by
  obtain rfl : i = off p h a := Fin.ext hi
  rw [extend_of_off]

/-- On words: `z p ↦ z p · z (p+1)`, and `z (p+1)` is fixed (Lemma 4.2 (i) in
`FreeGroup (Fin n)`). -/
theorem extend_mulA_values (p : ℕ) (h : p + 2 ≤ n) :
    extend p h mulAE.toMonoidHom (FreeGroup.of ⟨p, by omega⟩) =
        FreeGroup.of ⟨p, by omega⟩ * FreeGroup.of ⟨p + 1, by omega⟩ ∧
      extend p h mulAE.toMonoidHom (FreeGroup.of ⟨p + 1, by omega⟩) =
        FreeGroup.of ⟨p + 1, by omega⟩ := by
  constructor
  · rw [extend_of_eq_off' p h _ 0 _ (by simp)]
    simp [off]
  · rw [extend_of_eq_off' p h _ 1 _ (by simp)]
    simp [off]

/-- On words: `z (p+1) ↦ z (p+1) · z p`, and `z p` is fixed (Lemma 4.2 (i) in
`FreeGroup (Fin n)`). -/
theorem extend_mulB_values (p : ℕ) (h : p + 2 ≤ n) :
    extend p h mulBE.toMonoidHom (FreeGroup.of ⟨p, by omega⟩) = FreeGroup.of ⟨p, by omega⟩ ∧
      extend p h mulBE.toMonoidHom (FreeGroup.of ⟨p + 1, by omega⟩) =
        FreeGroup.of ⟨p + 1, by omega⟩ * FreeGroup.of ⟨p, by omega⟩ := by
  constructor
  · rw [extend_of_eq_off' p h _ 0 _ (by simp)]
    simp [off]
  · rw [extend_of_eq_off' p h _ 1 _ (by simp)]
    simp [off]

/-- On words, the extended swap (Lemma 4.2 (ii) in `FreeGroup (Fin n)`): `z p ↦ z (p+2)`,
`z (p+1) ↦ z (p+3)`, `z (p+2) ↦ D⁻¹ z p D`, `z (p+3) ↦ D⁻¹ z (p+1) D` with
`D = [z (p+2), z (p+3)]`. -/
theorem extend_pairSwap_values (p : ℕ) (h : p + 4 ≤ n) :
    extend p h pairSwap.toMonoidHom (FreeGroup.of ⟨p, by omega⟩) = FreeGroup.of ⟨p + 2, by omega⟩ ∧
      extend p h pairSwap.toMonoidHom (FreeGroup.of ⟨p + 1, by omega⟩) =
        FreeGroup.of ⟨p + 3, by omega⟩ ∧
      extend p h pairSwap.toMonoidHom (FreeGroup.of ⟨p + 2, by omega⟩) =
        (cmt (FreeGroup.of ⟨p + 2, by omega⟩) (FreeGroup.of ⟨p + 3, by omega⟩))⁻¹ *
          FreeGroup.of ⟨p, by omega⟩ *
            cmt (FreeGroup.of ⟨p + 2, by omega⟩) (FreeGroup.of ⟨p + 3, by omega⟩) ∧
      extend p h pairSwap.toMonoidHom (FreeGroup.of ⟨p + 3, by omega⟩) =
        (cmt (FreeGroup.of ⟨p + 2, by omega⟩) (FreeGroup.of ⟨p + 3, by omega⟩))⁻¹ *
          FreeGroup.of ⟨p + 1, by omega⟩ *
            cmt (FreeGroup.of ⟨p + 2, by omega⟩) (FreeGroup.of ⟨p + 3, by omega⟩) := by
  obtain ⟨v0, v1, v2, v3⟩ := pairSwap_values
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [extend_of_eq_off' p h _ 0 _ (by simp), MulEquiv.coe_toMonoidHom,
      show (FreeGroup.of 0 : F4) = ga from rfl, v0]
    simp [gc, off]
  · rw [extend_of_eq_off' p h _ 1 _ (by simp), MulEquiv.coe_toMonoidHom,
      show (FreeGroup.of 1 : F4) = gb from rfl, v1]
    simp [gd, off]
  · rw [extend_of_eq_off' p h _ 2 _ (by simp), MulEquiv.coe_toMonoidHom,
      show (FreeGroup.of 2 : F4) = gc from rfl, v2]
    simp [Q, comm_def, cmt, ga, gc, gd, off]
  · rw [extend_of_eq_off' p h _ 3 _ (by simp), MulEquiv.coe_toMonoidHom,
      show (FreeGroup.of 3 : F4) = gd from rfl, v3]
    simp [Q, comm_def, cmt, gb, gc, gd, off]

/-- The abelianization of an automorphism, through the images of the letters. -/
theorem vecN_equiv (e : FreeGroup (Fin n) ≃* FreeGroup (Fin n)) (x : FreeGroup (Fin n)) :
    vecN (e x) = linExt (fun a => vecN (e (FreeGroup.of a))) (vecN x) :=
  vecN_hom e.toMonoidHom x

/-- The abelianization of the inverse: if the abelianization of `e` sends `W i` to `e_i` for every
`i`, then `W i` is the abelianization of `e⁻¹ (z i)`. -/
theorem vecN_symm_of (e : FreeGroup (Fin n) ≃* FreeGroup (Fin n)) (W : Fin n → Fin n → ℤ)
    (hW : ∀ i, linExt (fun t => vecN (e (FreeGroup.of t))) (W i) = Pi.single i 1) (i : Fin n) :
    vecN (e.symm (FreeGroup.of i)) = W i := by
  have key : ∀ t, linExt (fun s => vecN (e.symm (FreeGroup.of s))) (vecN (e (FreeGroup.of t))) =
      Pi.single t 1 := by
    intro t
    rw [← vecN_equiv, MulEquiv.symm_apply_apply, vecN_of]
  calc vecN (e.symm (FreeGroup.of i))
      = linExt (fun s => vecN (e.symm (FreeGroup.of s))) (Pi.single i 1) := by rw [linExt_single]
    _ = linExt (fun s => vecN (e.symm (FreeGroup.of s)))
          (linExt (fun t => vecN (e (FreeGroup.of t))) (W i)) := by rw [hW]
    _ = linExt (fun t => linExt (fun s => vecN (e.symm (FreeGroup.of s)))
          (vecN (e (FreeGroup.of t)))) (W i) := linExt_linExt _ _ _
    _ = linExt (fun t => Pi.single t 1) (W i) := by simp only [key]
    _ = W i := linExt_id _

theorem symm_fixed {G : Type*} [Group G] (e : G ≃* G) (x : G) (h : e x = x) : e.symm x = x :=
  (MulEquiv.symm_apply_eq e).mpr h.symm

/-- The swap of the two adjacent pairs at the letters `p, …, p+3` permutes the basis vectors by
`swapIdx`. -/
theorem vecN_extend_pairSwap (p : ℕ) (h : p + 4 ≤ n) (i : Fin n) :
    vecN (extend p h pairSwap.toMonoidHom (FreeGroup.of i)) = Pi.single (swapIdx p h i) 1 := by
  by_cases hi : p ≤ i.val ∧ i.val < p + 4
  · obtain ⟨a, rfl⟩ := exists_off p h i hi
    rw [vecN_extend_off, MulEquiv.coe_toMonoidHom, vecN_pairSwap, linExt_single, off_swap4]
  · rw [vecN_extend_out _ _ _ _ hi, swapIdx_of_out _ _ _ hi]

theorem vecN_extend_pairSwap_symm (p : ℕ) (h : p + 4 ≤ n) (i : Fin n) :
    vecN (extend p h pairSwap.symm.toMonoidHom (FreeGroup.of i)) = Pi.single (swapIdx p h i) 1 := by
  by_cases hi : p ≤ i.val ∧ i.val < p + 4
  · obtain ⟨a, rfl⟩ := exists_off p h i hi
    rw [vecN_extend_off, MulEquiv.coe_toMonoidHom, vecN_pairSwap_symm, linExt_single, off_swap4]
  · rw [vecN_extend_out _ _ _ _ hi, swapIdx_of_out _ _ _ hi]

/-- `u ↦ u v` at the pair `(u, v) = (z p, z (p+1))`: `e_u ↦ e_u + e_v`, the other basis vectors
fixed. -/
theorem vecN_extend_mulA (p : ℕ) (h : p + 2 ≤ n) (i : Fin n) :
    vecN (extend p h mulAE.toMonoidHom (FreeGroup.of i)) =
      Pi.single i 1 + (if i.val = p then Pi.single ⟨p + 1, by omega⟩ 1 else 0) := by
  by_cases hi : p ≤ i.val ∧ i.val < p + 2
  · obtain ⟨a, rfl⟩ := exists_off p h i hi
    rw [vecN_extend_off, MulEquiv.coe_toMonoidHom, vecN_mulAE]
    simp only [linExt_add, linExt_ite, linExt_single, off_val]
    by_cases ha : a.val = 0
    · rw [if_pos ha, if_pos (show p + a.val = p by omega)]
      rfl
    · rw [if_neg ha, if_neg (show ¬ (p + a.val = p) by omega)]
  · rw [vecN_extend_out _ _ _ _ hi, if_neg (show ¬ (i.val = p) by omega), add_zero]

/-- `v ↦ v u` at the pair `(u, v) = (z p, z (p+1))`: `e_v ↦ e_v + e_u`, the other basis vectors
fixed. -/
theorem vecN_extend_mulB (p : ℕ) (h : p + 2 ≤ n) (i : Fin n) :
    vecN (extend p h mulBE.toMonoidHom (FreeGroup.of i)) =
      Pi.single i 1 + (if i.val = p + 1 then Pi.single ⟨p, by omega⟩ 1 else 0) := by
  by_cases hi : p ≤ i.val ∧ i.val < p + 2
  · obtain ⟨a, rfl⟩ := exists_off p h i hi
    rw [vecN_extend_off, MulEquiv.coe_toMonoidHom, vecN_mulBE]
    simp only [linExt_add, linExt_ite, linExt_single, off_val]
    by_cases ha : a.val = 1
    · rw [if_pos ha, if_pos (show p + a.val = p + 1 by omega)]
      rfl
    · rw [if_neg ha, if_neg (show ¬ (p + a.val = p + 1) by omega)]
  · rw [vecN_extend_out _ _ _ _ hi, if_neg (show ¬ (i.val = p + 1) by omega), add_zero]

end ExtendMoves

/-! ## 11. Proposition 4.4 (a): the even case `n = 2g`

Letters `z 0, …, z (2g-1)`, pairs `(z (2i), z (2i+1))`, boundary word `evenBoundary g`,
form `formE g`. The special letter is `z 0` (`= a`), its partner `z 1` (`= b`). -/

/-- `T_a` (Kondo's `φ`): `z 1 ↦ z 1 · z 0`, all other letters fixed. -/
def evenTa (g : ℕ) (hg : 1 ≤ g) : FreeGroup (Fin (2 * g)) ≃* FreeGroup (Fin (2 * g)) :=
  extendE 0 (by omega) mulBE

theorem evenTa_fix0 (g : ℕ) (hg : 1 ≤ g) :
    evenTa g hg (FreeGroup.of ⟨0, by omega⟩) = FreeGroup.of ⟨0, by omega⟩ := by
  rw [evenTa, extendE_apply]
  exact extend_of_eq_off 0 _ _ 0 _ rfl (by simp)

/-- On words: `evenTa` is `z 1 ↦ z 1 · z 0`, and fixes every other letter. -/
theorem evenTa_values (g : ℕ) (hg : 1 ≤ g) :
    evenTa g hg (FreeGroup.of ⟨1, by omega⟩) =
        FreeGroup.of ⟨1, by omega⟩ * FreeGroup.of ⟨0, by omega⟩ ∧
      ∀ i : Fin (2 * g), i.val ≠ 1 → evenTa g hg (FreeGroup.of i) = FreeGroup.of i := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [evenTa, extendE_apply]
    exact (extend_mulB_values 0 (by omega)).2
  · rw [evenTa, extendE_apply]
    by_cases h0 : i.val = 0
    · exact extend_of_eq_off 0 _ _ 0 _ (by simp [h0]) (by simp)
    · exact extend_of_out _ _ _ _ (by omega)

theorem evenTa_boundary (g : ℕ) (hg : 1 ≤ g) : evenTa g hg (evenBoundary g) = evenBoundary g := by
  rw [evenTa, extendE_apply, evenBoundary]
  exact extend_bdry_single (2 * g) 0 g 0 0 (by omega) _ (by omega) _ mulBE_cmt

/-- The abelianization of `evenTa` is `T_a` with `a = e₀`: `e₁ ↦ e₁ + e₀`, other basis vectors
fixed. -/
theorem evenTa_vec (g : ℕ) (hg : 1 ≤ g) (i : Fin (2 * g)) :
    vecN (evenTa g hg (FreeGroup.of i)) =
      Pi.single i 1 + (if i.val = 1 then Pi.single ⟨0, by omega⟩ 1 else 0) := by
  rw [evenTa, extendE_apply, vecN_extend_mulB]

/-- The same, written as `T_a(x) = x + ⟨x, a⟩ a`. -/
theorem evenTa_vec_form (g : ℕ) (hg : 1 ≤ g) (i : Fin (2 * g)) :
    vecN (evenTa g hg (FreeGroup.of i)) =
      Pi.single i 1 +
        formE g (Pi.single i 1) (Pi.single ⟨0, by omega⟩ 1) • Pi.single ⟨0, by omega⟩ 1 := by
  rw [evenTa_vec, formE_single_eq]
  by_cases hi : i.val = 1
  · rw [if_pos hi, hi, show omegaNat 1 0 = 1 by decide, one_smul]
  · have h0 : omegaNat i.val 0 = 0 := by
      simp only [omegaNat]
      omega_ifs
    rw [if_neg hi, h0, zero_smul]

/-- The swap (Lemma 4.2 (ii)) of the adjacent pairs `k` and `k+1` (letters `2k, …, 2k+3`), `k ≥ 1`;
it fixes the pair `0`. -/
def evenSwap (g k : ℕ) (hk : 1 ≤ k) (hk' : k + 1 < g) :
    FreeGroup (Fin (2 * g)) ≃* FreeGroup (Fin (2 * g)) :=
  extendE (2 * k) (by have := hk; omega) pairSwap

theorem evenSwap_fix0 (g k : ℕ) (hk : 1 ≤ k) (hk' : k + 1 < g) :
    evenSwap g k hk hk' (FreeGroup.of ⟨0, by omega⟩) = FreeGroup.of ⟨0, by omega⟩ := by
  rw [evenSwap, extendE_apply]
  exact extend_of_out _ _ _ _ (by simp only; omega)

theorem evenSwap_fix1 (g k : ℕ) (hk : 1 ≤ k) (hk' : k + 1 < g) :
    evenSwap g k hk hk' (FreeGroup.of ⟨1, by omega⟩) = FreeGroup.of ⟨1, by omega⟩ := by
  rw [evenSwap, extendE_apply]
  exact extend_of_out _ _ _ _ (by simp only; omega)

theorem evenSwap_symm_fix0 (g k : ℕ) (hk : 1 ≤ k) (hk' : k + 1 < g) :
    (evenSwap g k hk hk').symm (FreeGroup.of ⟨0, by omega⟩) = FreeGroup.of ⟨0, by omega⟩ := by
  rw [evenSwap, extendE_symm_apply]
  exact extend_of_out _ _ _ _ (by simp only; omega)

theorem evenSwap_boundary (g k : ℕ) (hk : 1 ≤ k) (hk' : k + 1 < g) :
    evenSwap g k hk hk' (evenBoundary g) = evenBoundary g := by
  rw [evenSwap, extendE_apply, evenBoundary]
  exact extend_bdry_pair (2 * g) 0 g k (2 * k) (by omega) _ hk' _ pairSwap_delta

theorem evenSwap_symm_boundary (g k : ℕ) (hk : 1 ≤ k) (hk' : k + 1 < g) :
    (evenSwap g k hk hk').symm (evenBoundary g) = evenBoundary g := by
  rw [evenSwap, extendE_symm_apply, evenBoundary]
  exact extend_bdry_pair (2 * g) 0 g k (2 * k) (by omega) _ hk' _ pairSwap_symm_delta

/-- On the abelianization the swap exchanges the pairs `k` and `k+1` (`swapIdx_val'`). -/
theorem evenSwap_vec (g k : ℕ) (hk : 1 ≤ k) (hk' : k + 1 < g) (i : Fin (2 * g)) :
    vecN (evenSwap g k hk hk' (FreeGroup.of i)) = Pi.single (swapIdx (2 * k) (by omega) i) 1 := by
  rw [evenSwap, extendE_apply, vecN_extend_pairSwap]

theorem evenSwap_symm_vec (g k : ℕ) (hk : 1 ≤ k) (hk' : k + 1 < g) (i : Fin (2 * g)) :
    vecN ((evenSwap g k hk hk').symm (FreeGroup.of i)) =
      Pi.single (swapIdx (2 * k) (by omega) i) 1 := by
  rw [evenSwap, extendE_symm_apply, vecN_extend_pairSwap_symm]

/-- The abelianization of the swap preserves the form `formE`. -/
theorem evenSwap_vec_form (g k : ℕ) (hk : 1 ≤ k) (hk' : k + 1 < g) (i j : Fin (2 * g)) :
    formE g (vecN (evenSwap g k hk hk' (FreeGroup.of i)))
        (vecN (evenSwap g k hk hk' (FreeGroup.of j))) =
      formE g (Pi.single i 1) (Pi.single j 1) := by
  rw [evenSwap_vec, evenSwap_vec, formE_single_eq, formE_single_eq,
    omegaNat_swapIdx _ _ (by omega)]

/-- The base moves on the first two pairs (letters `0, …, 3`): `U4 r` extended, `r = 0, 1`;
they induce `U_{e₂}` and `U_{e₃}`. -/
def evenUbase (g : ℕ) (hg : 2 ≤ g) (r : Fin 2) :
    FreeGroup (Fin (2 * g)) ≃* FreeGroup (Fin (2 * g)) :=
  extendE 0 (by omega) (U4 r)

/-- The move inducing `U_{e_j}` for `j = 2(k+1) + r`: the base move conjugated by the swaps of the
pairs `1, 2`, …, `k, k+1`. -/
def evenUaux (g : ℕ) (hg : 2 ≤ g) (r : Fin 2) :
    (k : ℕ) → k + 1 < g → (FreeGroup (Fin (2 * g)) ≃* FreeGroup (Fin (2 * g)))
  | 0, _ => evenUbase g hg r
  | k + 1, hk =>
    (evenSwap g (k + 1) (by omega) hk).symm.trans
      ((evenUaux g hg r k (by omega)).trans (evenSwap g (k + 1) (by omega) hk))

theorem evenUaux_zero (g : ℕ) (hg : 2 ≤ g) (r : Fin 2) (hk : 0 + 1 < g) :
    evenUaux g hg r 0 hk = evenUbase g hg r := rfl

theorem evenUaux_succ_apply (g : ℕ) (hg : 2 ≤ g) (r : Fin 2) (k : ℕ) (hk : k + 1 + 1 < g)
    (x : FreeGroup (Fin (2 * g))) :
    evenUaux g hg r (k + 1) hk x =
      evenSwap g (k + 1) (by omega) hk
        (evenUaux g hg r k (by omega) ((evenSwap g (k + 1) (by omega) hk).symm x)) := rfl

/-- `U_{e_j}` for `2 ≤ j < 2g` (so `g ≥ 2`): `e_i ↦ e_i + ⟨e_i, e_0⟩ e_j + ⟨e_i, e_j⟩ e_0`. -/
def evenU (g : ℕ) (j : Fin (2 * g)) (hj : 2 ≤ j.val) :
    FreeGroup (Fin (2 * g)) ≃* FreeGroup (Fin (2 * g)) :=
  evenUaux g (by omega) ⟨j.val % 2, by omega⟩ (j.val / 2 - 1) (by omega)

theorem evenUbase_fix0 (g : ℕ) (hg : 2 ≤ g) (r : Fin 2) :
    evenUbase g hg r (FreeGroup.of ⟨0, by omega⟩) = FreeGroup.of ⟨0, by omega⟩ := by
  rw [evenUbase, extendE_apply]
  exact extend_of_eq_off 0 _ _ 0 _ rfl (U4_a r)

theorem evenUbase_boundary (g : ℕ) (hg : 2 ≤ g) (r : Fin 2) :
    evenUbase g hg r (evenBoundary g) = evenBoundary g := by
  rw [evenUbase, extendE_apply, evenBoundary]
  exact extend_bdry_pair (2 * g) 0 g 0 0 (by omega) _ (by omega) _ (U4_delta r)

theorem evenUbase_vec (g : ℕ) (hg : 2 ≤ g) (r : Fin 2) (J : Fin (2 * g)) (hJ : J.val = 2 + r.val)
    (i : Fin (2 * g)) :
    vecN (evenUbase g hg r (FreeGroup.of i)) =
      Pi.single i 1 + omegaNat i.val 0 • Pi.single J 1 +
        omegaNat i.val J.val • Pi.single (⟨0, by omega⟩ : Fin (2 * g)) 1 := by
  rw [evenUbase, extendE_apply]
  have h4 : 0 + 4 ≤ 2 * g := by omega
  by_cases hi : 0 ≤ i.val ∧ i.val < 0 + 4
  · obtain ⟨a, rfl⟩ := exists_off 0 h4 i hi
    rw [vecN_extend_off, MulEquiv.coe_toMonoidHom, vecN_U4]
    simp only [linExt_add, linExt_smul, linExt_single]
    have e1 : off 0 h4 (⟨2 + r.val, by omega⟩ : Fin 4) = J :=
      Fin.ext (by simp only [off_val]; omega)
    have e2 : off 0 h4 (0 : Fin 4) = ⟨0, by omega⟩ := Fin.ext (by simp)
    rw [e1, e2, off_val, Nat.zero_add, hJ]
  · have h0 : omegaNat i.val 0 = 0 := by
      simp only [omegaNat]
      omega_ifs
    have h1 : omegaNat i.val J.val = 0 := by
      have := r.isLt
      simp only [omegaNat]
      omega_ifs
    rw [vecN_extend_out _ _ _ _ hi, h0, h1, zero_smul, zero_smul, add_zero, add_zero]

theorem evenUaux_fix0 (g : ℕ) (hg : 2 ≤ g) (r : Fin 2) (k : ℕ) (hk : k + 1 < g) :
    evenUaux g hg r k hk (FreeGroup.of ⟨0, by omega⟩) = FreeGroup.of ⟨0, by omega⟩ := by
  induction k with
  | zero => exact evenUbase_fix0 g hg r
  | succ k ih =>
    rw [evenUaux_succ_apply, evenSwap_symm_fix0, ih, evenSwap_fix0]

theorem evenUaux_boundary (g : ℕ) (hg : 2 ≤ g) (r : Fin 2) (k : ℕ) (hk : k + 1 < g) :
    evenUaux g hg r k hk (evenBoundary g) = evenBoundary g := by
  induction k with
  | zero => exact evenUbase_boundary g hg r
  | succ k ih =>
    rw [evenUaux_succ_apply, evenSwap_symm_boundary, ih, evenSwap_boundary]

theorem evenUaux_vec (g : ℕ) (hg : 2 ≤ g) (r : Fin 2) (k : ℕ) (hk : k + 1 < g) (J : Fin (2 * g))
    (hJ : J.val = 2 * (k + 1) + r.val) (i : Fin (2 * g)) :
    vecN (evenUaux g hg r k hk (FreeGroup.of i)) =
      Pi.single i 1 + omegaNat i.val 0 • Pi.single J 1 +
        omegaNat i.val J.val • Pi.single (⟨0, by omega⟩ : Fin (2 * g)) 1 := by
  induction k generalizing i J with
  | zero => exact evenUbase_vec g hg r J (by omega) i
  | succ k ih =>
    have hp : (2 * (k + 1)) % 2 = 0 := by omega
    have h4 : 2 * (k + 1) + 4 ≤ 2 * g := by omega
    have hτJ : (swapIdx (2 * (k + 1)) h4 J).val = 2 * (k + 1) + r.val := by
      have := r.isLt
      rw [swapIdx_val]
      omega_ifs
    rw [evenUaux_succ_apply, vecN_equiv, vecN_equiv, evenSwap_symm_vec, linExt_single,
      ih (by omega) (swapIdx (2 * (k + 1)) h4 J) hτJ]
    simp only [evenSwap_vec, linExt_add, linExt_smul, linExt_single]
    have h0 : swapIdx (2 * (k + 1)) h4 (⟨0, by omega⟩ : Fin (2 * g)) = ⟨0, by omega⟩ :=
      swapIdx_of_out _ _ _ (by simp only; omega)
    rw [swapIdx_swapIdx, swapIdx_swapIdx, h0, omegaNat_swapIdx_fix _ h4 hp i 0 (by omega),
      omegaNat_swapIdx _ h4 hp i J]

/-- Proposition 4.4 (a): `evenU` fixes `z 0`. -/
theorem evenU_fix0 (g : ℕ) (j : Fin (2 * g)) (hj : 2 ≤ j.val) :
    evenU g j hj (FreeGroup.of ⟨0, by omega⟩) = FreeGroup.of ⟨0, by omega⟩ :=
  evenUaux_fix0 _ _ _ _ _

/-- Proposition 4.4 (a): `evenU` fixes the boundary word. -/
theorem evenU_boundary (g : ℕ) (j : Fin (2 * g)) (hj : 2 ≤ j.val) :
    evenU g j hj (evenBoundary g) = evenBoundary g :=
  evenUaux_boundary _ _ _ _ _

/-- Proposition 4.4 (a): the abelianization of `evenU g j` is
`U_{e_j} : e_i ↦ e_i + ⟨e_i, e_0⟩ e_j + ⟨e_i, e_j⟩ e_0`. -/
theorem evenU_vec (g : ℕ) (j : Fin (2 * g)) (hj : 2 ≤ j.val) (i : Fin (2 * g)) :
    vecN (evenU g j hj (FreeGroup.of i)) =
      Pi.single i 1 + formE g (Pi.single i 1) (Pi.single ⟨0, by omega⟩ 1) • Pi.single j 1 +
        formE g (Pi.single i 1) (Pi.single j 1) • Pi.single ⟨0, by omega⟩ 1 := by
  rw [evenU, evenUaux_vec g (by omega) ⟨j.val % 2, by omega⟩ (j.val / 2 - 1) (by omega) j
    (by simp only; omega) i, formE_single_eq, formE_single_eq]

theorem evenU_symm_fix0 (g : ℕ) (j : Fin (2 * g)) (hj : 2 ≤ j.val) :
    (evenU g j hj).symm (FreeGroup.of ⟨0, by omega⟩) = FreeGroup.of ⟨0, by omega⟩ :=
  symm_fixed _ _ (evenU_fix0 g j hj)

theorem evenU_symm_boundary (g : ℕ) (j : Fin (2 * g)) (hj : 2 ≤ j.val) :
    (evenU g j hj).symm (evenBoundary g) = evenBoundary g :=
  symm_fixed _ _ (evenU_boundary g j hj)

/-- Proposition 4.4 (a), the other sign: the inverse of `evenU g j` induces
`U_{-e_j} = U_{e_j}⁻¹ : e_i ↦ e_i - ⟨e_i, e_0⟩ e_j - ⟨e_i, e_j⟩ e_0`. -/
theorem evenU_symm_vec (g : ℕ) (j : Fin (2 * g)) (hj : 2 ≤ j.val) (i : Fin (2 * g)) :
    vecN ((evenU g j hj).symm (FreeGroup.of i)) =
      Pi.single i 1 - formE g (Pi.single i 1) (Pi.single ⟨0, by omega⟩ 1) • Pi.single j 1 -
        formE g (Pi.single i 1) (Pi.single j 1) • Pi.single ⟨0, by omega⟩ 1 := by
  refine vecN_symm_of _ (fun i => Pi.single i 1 -
    formE g (Pi.single i 1) (Pi.single ⟨0, by omega⟩ 1) • Pi.single j 1 -
      formE g (Pi.single i 1) (Pi.single j 1) • Pi.single ⟨0, by omega⟩ 1) (fun t => ?_) i
  simp only [evenU_vec, linExt_sub, linExt_smul, linExt_single, formE_single_eq]
  have h1 : omegaNat j.val 0 = 0 := by
    simp only [omegaNat]
    omega_ifs
  have h2 : omegaNat j.val j.val = 0 := by
    simp only [omegaNat]
    omega_ifs
  have h3 : omegaNat 0 0 = 0 := by decide
  have h4 : omegaNat 0 j.val = 0 := by
    simp only [omegaNat]
    omega_ifs
  rw [h1, h2, h3, h4]
  simp only [zero_smul, add_zero]
  abel

/-! ## 12. Proposition 4.4 (b): the odd case `n = 2g+1`

Letters `z 0, …, z (2g)`; the special letter is `z 0`, the pairs are `(z (2k+1), z (2k+2))`, the
boundary word is `oddBoundary g` (in which `z 0` does not occur), and the form is `formO g`. -/

/-- `u ↦ u v` for the pair `(u, v) = (z (2k+1), z (2k+2))`, other letters fixed. -/
def oddPairU (g : ℕ) (k : Fin g) : FreeGroup (Fin (2 * g + 1)) ≃* FreeGroup (Fin (2 * g + 1)) :=
  extendE (2 * k.val + 1) (by omega) mulAE

/-- `v ↦ v u` for the pair `(u, v) = (z (2k+1), z (2k+2))`, other letters fixed. -/
def oddPairV (g : ℕ) (k : Fin g) : FreeGroup (Fin (2 * g + 1)) ≃* FreeGroup (Fin (2 * g + 1)) :=
  extendE (2 * k.val + 1) (by omega) mulBE

/-- The swap (Lemma 4.2 (ii)) of the adjacent pairs `k` and `k+1` (letters `2k+1, …, 2k+4`). -/
def oddSwap (g k : ℕ) (hk : k + 1 < g) :
    FreeGroup (Fin (2 * g + 1)) ≃* FreeGroup (Fin (2 * g + 1)) :=
  extendE (2 * k + 1) (by omega) pairSwap

theorem oddPairU_fix0 (g : ℕ) (k : Fin g) :
    oddPairU g k (FreeGroup.of ⟨0, by omega⟩) = FreeGroup.of ⟨0, by omega⟩ := by
  rw [oddPairU, extendE_apply]
  exact extend_of_out _ _ _ _ (by simp only; omega)

theorem oddPairV_fix0 (g : ℕ) (k : Fin g) :
    oddPairV g k (FreeGroup.of ⟨0, by omega⟩) = FreeGroup.of ⟨0, by omega⟩ := by
  rw [oddPairV, extendE_apply]
  exact extend_of_out _ _ _ _ (by simp only; omega)

theorem oddSwap_fix0 (g k : ℕ) (hk : k + 1 < g) :
    oddSwap g k hk (FreeGroup.of ⟨0, by omega⟩) = FreeGroup.of ⟨0, by omega⟩ := by
  rw [oddSwap, extendE_apply]
  exact extend_of_out _ _ _ _ (by simp only; omega)

/-- On words: `oddPairU g k` is `u ↦ u v` for `(u, v) = (z (2k+1), z (2k+2))`, and fixes every other
letter. -/
theorem oddPairU_values (g : ℕ) (k : Fin g) :
    oddPairU g k (FreeGroup.of ⟨2 * k.val + 1, by omega⟩) =
        FreeGroup.of ⟨2 * k.val + 1, by omega⟩ * FreeGroup.of ⟨2 * k.val + 2, by omega⟩ ∧
      ∀ i : Fin (2 * g + 1), i.val ≠ 2 * k.val + 1 →
        oddPairU g k (FreeGroup.of i) = FreeGroup.of i := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [oddPairU, extendE_apply]
    exact (extend_mulA_values (2 * k.val + 1) (by omega)).1
  · rw [oddPairU, extendE_apply]
    by_cases h1 : i.val = 2 * k.val + 2
    · exact extend_of_eq_off _ _ _ 1 _ (by simp [h1]) (by simp)
    · exact extend_of_out _ _ _ _ (by omega)

/-- On words: `oddPairV g k` is `v ↦ v u` for `(u, v) = (z (2k+1), z (2k+2))`, and fixes every other
letter. -/
theorem oddPairV_values (g : ℕ) (k : Fin g) :
    oddPairV g k (FreeGroup.of ⟨2 * k.val + 2, by omega⟩) =
        FreeGroup.of ⟨2 * k.val + 2, by omega⟩ * FreeGroup.of ⟨2 * k.val + 1, by omega⟩ ∧
      ∀ i : Fin (2 * g + 1), i.val ≠ 2 * k.val + 2 →
        oddPairV g k (FreeGroup.of i) = FreeGroup.of i := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [oddPairV, extendE_apply]
    exact (extend_mulB_values (2 * k.val + 1) (by omega)).2
  · rw [oddPairV, extendE_apply]
    by_cases h0 : i.val = 2 * k.val + 1
    · exact extend_of_eq_off _ _ _ 0 _ (by simp [h0]) (by simp)
    · exact extend_of_out _ _ _ _ (by omega)

theorem oddPairU_boundary (g : ℕ) (k : Fin g) : oddPairU g k (oddBoundary g) = oddBoundary g := by
  rw [oddPairU, extendE_apply, oddBoundary]
  exact extend_bdry_single (2 * g + 1) 1 g k.val (2 * k.val + 1) rfl _ k.isLt _ mulAE_cmt

theorem oddPairV_boundary (g : ℕ) (k : Fin g) : oddPairV g k (oddBoundary g) = oddBoundary g := by
  rw [oddPairV, extendE_apply, oddBoundary]
  exact extend_bdry_single (2 * g + 1) 1 g k.val (2 * k.val + 1) rfl _ k.isLt _ mulBE_cmt

theorem oddSwap_boundary (g k : ℕ) (hk : k + 1 < g) :
    oddSwap g k hk (oddBoundary g) = oddBoundary g := by
  rw [oddSwap, extendE_apply, oddBoundary]
  exact extend_bdry_pair (2 * g + 1) 1 g k (2 * k + 1) rfl _ hk _ pairSwap_delta

/-- The abelianization of `u ↦ u v`: `e_u ↦ e_u + e_v` (`u = 2k+1`, `v = 2k+2`), other basis vectors
fixed. -/
theorem oddPairU_vec (g : ℕ) (k : Fin g) (i : Fin (2 * g + 1)) :
    vecN (oddPairU g k (FreeGroup.of i)) =
      Pi.single i 1 +
        (if i.val = 2 * k.val + 1 then Pi.single ⟨2 * k.val + 2, by omega⟩ 1 else 0) := by
  rw [oddPairU, extendE_apply]
  exact vecN_extend_mulA _ _ i

/-- The abelianization of `v ↦ v u`: `e_v ↦ e_v + e_u` (`u = 2k+1`, `v = 2k+2`), other basis vectors
fixed. -/
theorem oddPairV_vec (g : ℕ) (k : Fin g) (i : Fin (2 * g + 1)) :
    vecN (oddPairV g k (FreeGroup.of i)) =
      Pi.single i 1 +
        (if i.val = 2 * k.val + 2 then Pi.single ⟨2 * k.val + 1, by omega⟩ 1 else 0) := by
  rw [oddPairV, extendE_apply]
  exact vecN_extend_mulB _ _ i

/-- The abelianization of the swap exchanges the pairs `k` and `k+1` (`swapIdx_val'`:
`2k+1 ↔ 2k+3`, `2k+2 ↔ 2k+4`). -/
theorem oddSwap_vec (g k : ℕ) (hk : k + 1 < g) (i : Fin (2 * g + 1)) :
    vecN (oddSwap g k hk (FreeGroup.of i)) = Pi.single (swapIdx (2 * k + 1) (by omega) i) 1 := by
  rw [oddSwap, extendE_apply, vecN_extend_pairSwap]

/-- The abelianization of the swap preserves the form `formO`. -/
theorem oddSwap_vec_form (g k : ℕ) (hk : k + 1 < g) (i j : Fin (2 * g + 1)) :
    formO g (vecN (oddSwap g k hk (FreeGroup.of i))) (vecN (oddSwap g k hk (FreeGroup.of j))) =
      formO g (Pi.single i 1) (Pi.single j 1) := by
  rw [oddSwap_vec, oddSwap_vec, formO_single, formO_single]
  simp only [swapIdx_val]
  omega_ifs

/-! ## Axioms -/

end LogShellEdge.FG
