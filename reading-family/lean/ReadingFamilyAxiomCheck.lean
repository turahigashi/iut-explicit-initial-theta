/-
ReadingFamily: the readings of Corollary 3.12 and the conservation of the height load.

Corollary 3.12 of IUT III compares the log-volume `-|log q|` of the `q`-pilot with the log-volume
`M` of the holomorphic hull of the union of possible images of the Θ-pilot, and Theorem 1.10 of
IUT IV bounds `M` from above by a number `U`. How `M` is computed depends on how the statement is
read. Five axes are considered here:

* (Ind1): where the theta value of label `j` may sit among the `j + 1` factors (`V`: only in the
  factor `j`; `L`: label permutations fixing `0`; `L0`: all label permutations);
* (Ind3): the whole tensor packet of log-shells (container) or only the actual images of units
  and of the iterated log-links (iteration);
* (Ind2): the units `ℤ_p^×` with the field automorphisms, or all lattice automorphisms of the
  log-shells;
* whether the union of the possible images is replaced by its holomorphic hull;
* the archimedean container (`π^{j+1}·B_I` or the unit ball of the tensor-product metric).

Without the hull, the iteration reading is a union of pure tensors, of volume zero; it is left
out. This leaves 36 readings (`card_admissible`).

The file shows, in a finite model:

* the ends `a = |log q|`, `k` (the mean of `j^2`) and IV's constant `C` take no reading, so
  Corollary 3.12 and the upper bound of IV together give the same height bound `(k - 1) a ≤ C`
  in every reading (`Datum.conservation`);
* the value of a reading is a Θ-part, decided by its (Ind1)-axis alone, plus a remainder
  (`Datum.M`); in the component model the Θ-part is the hull of the theta values over the
  allowed factors (`thetaPart`), it is `-k a` for `V` (`thetaPart_V`), it increases from `V` to
  `L` to `L0` (`thetaPart_mono`), it scales with the `q`-orders (`thetaPart_smul`), and it equals
  the value for `V` when the `q`-orders agree (`thetaPart_eq_V_of_const`) but not otherwise
  (`thetaPart_V_lt_L0`, `thetaPart_V_lt_L`);
* the reading only moves the load `(k - 1) a` between the two statements: Corollary 3.12
  carries `(x - 1) a` and IV carries `(k - x) a`, with `x = -Θ/a ≤ k` (`Datum.cor_iff`,
  `Datum.iv_iff`, `Datum.load_sum`, `Datum.loadIV_nonneg`); one of the two loads is at least half
  of the wall (`Datum.half_load_le_max`);
* when `q` is replaced by `q^N` (the Θ-parts scale with `N`, the remainders stay bounded), no
  reading keeps both statements true for all `N` (`Family.no_uniform_reading`); if IV holds for
  all `N`, its load is `0` and Corollary 3.12 is the whole wall (`Family.iv_uniform`); if
  Corollary 3.12 holds for all `N`, then `x ≤ 1` and IV carries at least the whole wall
  (`Family.cor_uniform`);
* with one bad and one good place above a prime, each of weight `1/2` or with the bad weight
  below `1/2` (the situation of Belyi points), the reading `L0` has `x ≤ 1`
  (`twoPlace_x_L0_le_one`).

Everything here is about this finite model; nothing here is inter-universal Teichmüller theory.
-/
import Mathlib

namespace ReadingFamily

open Finset

/-! ## 1. The readings -/

/-- (Ind1): where the theta value of label `j` may sit. -/
inductive Ind1 where
  | V
  | L
  | L0
  deriving DecidableEq, Fintype, Repr

/-- (Ind3): the whole container or only the actual images. -/
inductive Ind3 where
  | container
  | iteration
  deriving DecidableEq, Fintype, Repr

/-- (Ind2): the units or all lattice automorphisms of the log-shells. -/
inductive Ind2 where
  | units
  | lattice
  deriving DecidableEq, Fintype, Repr

/-- The archimedean container. -/
inductive Arch where
  | small
  | large
  deriving DecidableEq, Fintype, Repr

/-- A reading of Corollary 3.12: the five axes. `hull = true` takes the holomorphic hull of the
union of the possible images. -/
structure Reading where
  ind1 : Ind1
  ind3 : Ind3
  ind2 : Ind2
  hull : Bool
  arch : Arch
  deriving DecidableEq, Fintype, Repr

/-- Without the hull, the iteration reading is a union of pure tensors (volume zero). -/
def Reading.Admissible (R : Reading) : Prop := R.ind3 = .container ∨ R.hull = true

instance : DecidablePred Reading.Admissible := fun R => by
  unfold Reading.Admissible
  infer_instance

/-- There are 36 admissible readings. -/
theorem card_admissible : (univ.filter Reading.Admissible).card = 36 := by decide

/-! ## 2. The Θ-part in the component model -/

section Model

variable {V : Type*} [Fintype V]

/-- The weight of a tuple of places: the product of the weights of its entries. -/
def tupleWeight (w : V → ℝ) {n : ℕ} (t : Fin n → V) : ℝ := ∏ i, w (t i)

/-- The weighted average of a function on the tuples of length `n`. -/
def wavg (w : V → ℝ) (n : ℕ) (f : (Fin n → V) → ℝ) : ℝ := ∑ t, tupleWeight w t * f t

/-- The factors where the theta value of label `j` may sit. For `j ≥ 1` the set for `L` is
`{1, …, j}`. -/
def pos : Ind1 → (j : ℕ) → Finset (Fin (j + 1))
  | .V, j => {Fin.last j}
  | .L, j => insert (Fin.last j) (univ.erase 0)
  | .L0, _ => univ

theorem last_mem_pos (r : Ind1) (j : ℕ) : Fin.last j ∈ pos r j := by
  cases r <;> simp [pos]

theorem pos_nonempty (r : Ind1) (j : ℕ) : (pos r j).Nonempty := ⟨_, last_mem_pos r j⟩

theorem pos_V_subset (r : Ind1) (j : ℕ) : pos .V j ⊆ pos r j := by
  show {Fin.last j} ⊆ pos r j
  rw [Finset.singleton_subset_iff]
  exact last_mem_pos r j

theorem pos_subset_L0 (r : Ind1) (j : ℕ) : pos r j ⊆ pos .L0 j := Finset.subset_univ _

/-- The Θ-part at a component: the largest of the theta values over the allowed factors (the
union of the possible balls has the largest ball as its hull). -/
noncomputable def thetaHull (Q : V → ℝ) (r : Ind1) (j : ℕ) (t : Fin (j + 1) → V) : ℝ :=
  (pos r j).sup' (pos_nonempty r j) (fun i => -((j : ℝ) ^ 2) * Q (t i))

omit [Fintype V] in
theorem thetaHull_V (Q : V → ℝ) (j : ℕ) (t : Fin (j + 1) → V) :
    thetaHull Q .V j t = -((j : ℝ) ^ 2) * Q (t (Fin.last j)) := by
  simp [thetaHull, pos]

omit [Fintype V] in
theorem thetaHull_le_of_subset (Q : V → ℝ) {r r' : Ind1} (j : ℕ) (h : pos r j ⊆ pos r' j)
    (t : Fin (j + 1) → V) : thetaHull Q r j t ≤ thetaHull Q r' j t :=
  Finset.sup'_mono _ h (pos_nonempty r j)

omit [Fintype V] in
theorem thetaHull_nonpos (Q : V → ℝ) (hQ : ∀ v, 0 ≤ Q v) (r : Ind1) (j : ℕ)
    (t : Fin (j + 1) → V) : thetaHull Q r j t ≤ 0 := by
  refine Finset.sup'_le _ _ (fun i _ => ?_)
  have h1 := hQ (t i)
  have h2 := sq_nonneg (j : ℝ)
  nlinarith

/-- `sup'` commutes with multiplication by a nonnegative constant. -/
theorem sup'_const_mul {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) {c : ℝ}
    (hc : 0 ≤ c) : s.sup' hs (fun i => c * f i) = c * s.sup' hs f := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun i hi => mul_le_mul_of_nonneg_left (Finset.le_sup' f hi) hc)
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hs f
    rw [he]
    exact Finset.le_sup' (fun i => c * f i) hi

omit [Fintype V] in
/-- Scaling the `q`-orders by `N ≥ 0` scales the Θ-part at each component by `N`. -/
theorem thetaHull_smul (Q : V → ℝ) {N : ℝ} (hN : 0 ≤ N) (r : Ind1) (j : ℕ)
    (t : Fin (j + 1) → V) : thetaHull (fun v => N * Q v) r j t = N * thetaHull Q r j t := by
  unfold thetaHull
  rw [← sup'_const_mul _ _ _ hN]
  congr 1
  funext i
  ring

theorem wavg_mono (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) {n : ℕ} {f g : (Fin n → V) → ℝ}
    (h : ∀ t, f t ≤ g t) : wavg w n f ≤ wavg w n g := by
  unfold wavg
  apply Finset.sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left (h t) (Finset.prod_nonneg (fun i _ => hw (t i)))

theorem wavg_smul (w : V → ℝ) {n : ℕ} (c : ℝ) (f : (Fin n → V) → ℝ) :
    wavg w n (fun t => c * f t) = c * wavg w n f := by
  unfold wavg
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  ring

/-- The average of a function of one factor is its average over the places. -/
theorem wavg_factor (w : V → ℝ) (hw : ∑ v, w v = 1) {n : ℕ} (i₀ : Fin n) (g : V → ℝ) :
    wavg w n (fun t => g (t i₀)) = ∑ v, w v * g v := by
  unfold wavg tupleWeight
  have key : ∀ t : Fin n → V, (∏ i, w (t i)) * g (t i₀)
      = ∏ i, (w (t i) * if i = i₀ then g (t i) else 1) := by
    intro t
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' univ i₀ (fun i => g (t i))]
    simp
  simp_rw [key]
  rw [← Fintype.prod_sum (fun i v => w v * if i = i₀ then g v else 1)]
  have hfac : ∀ i : Fin n, (∑ v, w v * if i = i₀ then g v else 1)
      = if i = i₀ then ∑ v, w v * g v else 1 := by
    intro i
    split_ifs <;> simp [hw]
  simp_rw [hfac]
  rw [Finset.prod_ite_eq' univ i₀ (fun _ => ∑ v, w v * g v)]
  simp

/-- The Θ-part of the (Ind1)-reading `r`, averaged over the components (weights `w`) and the
levels `j = 1, …, ls` (procession normalization). -/
noncomputable def thetaPart (w Q : V → ℝ) (ls : ℕ) (r : Ind1) : ℝ :=
  (1 / ls) * ∑ j ∈ Icc 1 ls, wavg w (j + 1) (thetaHull Q r j)

/-- The degree of the `q`-pilot. -/
def qdeg (w Q : V → ℝ) : ℝ := ∑ v, w v * Q v

/-- The mean `k` of `j^2` over `j = 1, …, ls`. -/
noncomputable def kmean (ls : ℕ) : ℝ := (1 / ls) * ∑ j ∈ Icc 1 ls, ((j : ℝ) ^ 2)

/-- Reading `V`: the Θ-part is `-k` times the degree of the `q`-pilot. -/
theorem thetaPart_V (w Q : V → ℝ) (hw : ∑ v, w v = 1) (ls : ℕ) :
    thetaPart w Q ls .V = -kmean ls * qdeg w Q := by
  have h : ∀ j : ℕ, wavg w (j + 1) (thetaHull Q .V j) = -((j : ℝ) ^ 2) * qdeg w Q := by
    intro j
    have hθ : thetaHull Q .V j = fun t => (fun v => -((j : ℝ) ^ 2) * Q v) (t (Fin.last j)) := by
      funext t
      exact thetaHull_V Q j t
    rw [hθ, wavg_factor w hw (Fin.last j) (fun v => -((j : ℝ) ^ 2) * Q v)]
    unfold qdeg
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    ring
  unfold thetaPart kmean
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  rw [← Finset.sum_mul]
  have : ∑ j ∈ Icc 1 ls, -((j : ℝ) ^ 2) = -∑ j ∈ Icc 1 ls, ((j : ℝ) ^ 2) := by
    rw [Finset.sum_neg_distrib]
  rw [this]
  ring

/-- A larger set of allowed factors gives a larger Θ-part. -/
theorem thetaPart_le_of_subset (w Q : V → ℝ) (hw : ∀ v, 0 ≤ w v) (ls : ℕ) {r r' : Ind1}
    (h : ∀ j, pos r j ⊆ pos r' j) : thetaPart w Q ls r ≤ thetaPart w Q ls r' := by
  unfold thetaPart
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  exact wavg_mono w hw (fun t => thetaHull_le_of_subset Q j (h j) t)

/-- The order `V ≤ L ≤ L0`, and every reading lies between `V` and `L0`. -/
theorem thetaPart_mono (w Q : V → ℝ) (hw : ∀ v, 0 ≤ w v) (ls : ℕ) (r : Ind1) :
    thetaPart w Q ls .V ≤ thetaPart w Q ls r ∧ thetaPart w Q ls r ≤ thetaPart w Q ls .L0 :=
  ⟨thetaPart_le_of_subset w Q hw ls (fun j => pos_V_subset r j),
    thetaPart_le_of_subset w Q hw ls (fun j => pos_subset_L0 r j)⟩

/-- Every reading has Θ-part at least `-k a`, so `x ≤ k`. -/
theorem thetaPart_ge (w Q : V → ℝ) (hw0 : ∀ v, 0 ≤ w v) (hw1 : ∑ v, w v = 1) (ls : ℕ)
    (r : Ind1) : -kmean ls * qdeg w Q ≤ thetaPart w Q ls r := by
  rw [← thetaPart_V w Q hw1 ls]
  exact (thetaPart_mono w Q hw0 ls r).1

theorem thetaPart_nonpos (w Q : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hQ : ∀ v, 0 ≤ Q v) (ls : ℕ)
    (r : Ind1) : thetaPart w Q ls r ≤ 0 := by
  unfold thetaPart
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  apply Finset.sum_nonpos
  intro j _
  have h := wavg_mono w hw (f := thetaHull Q r j) (g := fun _ => (0 : ℝ))
    (fun t => thetaHull_nonpos Q hQ r j t)
  simpa [wavg] using h

/-- Replacing `q` by `q^N` (the `q`-orders by `N Q`) scales the Θ-part by `N`. -/
theorem thetaPart_smul (w Q : V → ℝ) (ls : ℕ) {N : ℝ} (hN : 0 ≤ N) (r : Ind1) :
    thetaPart w (fun v => N * Q v) ls r = N * thetaPart w Q ls r := by
  unfold thetaPart
  have h : ∀ j : ℕ, wavg w (j + 1) (thetaHull (fun v => N * Q v) r j)
      = N * wavg w (j + 1) (thetaHull Q r j) := by
    intro j
    rw [← wavg_smul]
    congr 1
    funext t
    exact thetaHull_smul Q hN r j t
  rw [Finset.sum_congr rfl (fun j _ => h j), ← Finset.mul_sum]
  ring

theorem qdeg_smul (w Q : V → ℝ) (N : ℝ) : qdeg w (fun v => N * Q v) = N * qdeg w Q := by
  unfold qdeg
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  ring

/-- If all places of positive weight have the same `q`-order, every reading has the Θ-part of
`V`. -/
theorem thetaPart_eq_V_of_const (w Q : V → ℝ) (hw : ∀ v, 0 ≤ w v) (ls : ℕ) (c : ℝ)
    (hc : ∀ v, 0 < w v → Q v = c) (r : Ind1) : thetaPart w Q ls r = thetaPart w Q ls .V := by
  unfold thetaPart
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold wavg
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases h0 : tupleWeight w t = 0
  · rw [h0, zero_mul, zero_mul]
  · have hall : ∀ i, Q (t i) = c := by
      intro i
      apply hc
      have hne : w (t i) ≠ 0 := by
        intro hz
        apply h0
        unfold tupleWeight
        exact Finset.prod_eq_zero (Finset.mem_univ i) hz
      exact lt_of_le_of_ne (hw (t i)) (Ne.symm hne)
    congr 1
    unfold thetaHull
    have hf : (fun i : Fin (j + 1) => -((j : ℝ) ^ 2) * Q (t i)) = fun _ => -((j : ℝ) ^ 2) * c := by
      funext i
      rw [hall i]
    rw [hf, Finset.sup'_const, Finset.sup'_const]

/-- A sum of nonnegative terms with one positive term is positive, in the form used below. -/
theorem wavg_lt_of_exists (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) {n : ℕ} {f g : (Fin n → V) → ℝ}
    (h : ∀ t, f t ≤ g t) (t₀ : Fin n → V) (ht₀ : 0 < tupleWeight w t₀) (hlt : f t₀ < g t₀) :
    wavg w n f < wavg w n g := by
  unfold wavg
  apply Finset.sum_lt_sum
  · intro t _
    exact mul_le_mul_of_nonneg_left (h t) (Finset.prod_nonneg (fun i _ => hw (t i)))
  · exact ⟨t₀, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt ht₀⟩

/-- If two places of positive weight have different `q`-orders, the reading `L0` has a strictly
larger Θ-part than `V` (level `j = 1` already sees it). -/
theorem thetaPart_V_lt_L0 (w Q : V → ℝ) (hw : ∀ v, 0 ≤ w v) (ls : ℕ) (hls : 1 ≤ ls) {u v : V}
    (hu : 0 < w u) (hv : 0 < w v) (huv : Q u < Q v) :
    thetaPart w Q ls .V < thetaPart w Q ls .L0 := by
  unfold thetaPart
  have hls' : (0 : ℝ) < 1 / (ls : ℝ) := by
    have : (0 : ℝ) < ls := by exact_mod_cast hls
    positivity
  apply mul_lt_mul_of_pos_left _ hls'
  apply Finset.sum_lt_sum
  · intro j _
    exact wavg_mono w hw (fun t => thetaHull_le_of_subset Q j (pos_V_subset .L0 j) t)
  · refine ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hls⟩, ?_⟩
    let t₀ : Fin 2 → V := ![u, v]
    have hw₀ : 0 < tupleWeight w t₀ := by
      simp [tupleWeight, t₀, Fin.prod_univ_two]
      exact mul_pos hu hv
    refine wavg_lt_of_exists w hw (fun t => thetaHull_le_of_subset Q 1 (pos_V_subset .L0 1) t)
      t₀ hw₀ ?_
    have hV : thetaHull Q .V 1 t₀ = -(((1 : ℕ) : ℝ) ^ 2) * Q v := by
      rw [thetaHull_V]
      rfl
    have hL0 : -(((1 : ℕ) : ℝ) ^ 2) * Q u ≤ thetaHull Q .L0 1 t₀ := by
      have h := Finset.le_sup' (fun i : Fin 2 => -(((1 : ℕ) : ℝ) ^ 2) * Q (t₀ i))
        (show (0 : Fin 2) ∈ pos .L0 1 from Finset.mem_univ _)
      simpa [thetaHull, t₀] using h
    rw [hV]
    have : -(((1 : ℕ) : ℝ) ^ 2) * Q v < -(((1 : ℕ) : ℝ) ^ 2) * Q u := by
      norm_num
      exact huv
    linarith

/-- The same for the reading `L`, which needs a level `j ≥ 2` (at `j = 1` the reading `L` is
the reading `V`). -/
theorem thetaPart_V_lt_L (w Q : V → ℝ) (hw : ∀ v, 0 ≤ w v) (ls : ℕ) (hls : 2 ≤ ls) {u v : V}
    (hu : 0 < w u) (hv : 0 < w v) (huv : Q u < Q v) :
    thetaPart w Q ls .V < thetaPart w Q ls .L := by
  unfold thetaPart
  have hls' : (0 : ℝ) < 1 / (ls : ℝ) := by
    have : (0 : ℝ) < ls := by exact_mod_cast (show 0 < ls by omega)
    positivity
  apply mul_lt_mul_of_pos_left _ hls'
  apply Finset.sum_lt_sum
  · intro j _
    exact wavg_mono w hw (fun t => thetaHull_le_of_subset Q j (pos_V_subset .L j) t)
  · refine ⟨2, Finset.mem_Icc.mpr ⟨by norm_num, hls⟩, ?_⟩
    let t₀ : Fin 3 → V := ![u, u, v]
    have hw₀ : 0 < tupleWeight w t₀ := by
      simp [tupleWeight, t₀, Fin.prod_univ_three]
      exact mul_pos (mul_pos hu hu) hv
    refine wavg_lt_of_exists w hw (fun t => thetaHull_le_of_subset Q 2 (pos_V_subset .L 2) t)
      t₀ hw₀ ?_
    have hV : thetaHull Q .V 2 t₀ = -(((2 : ℕ) : ℝ) ^ 2) * Q v := by
      rw [thetaHull_V]
      rfl
    have hmem : (1 : Fin 3) ∈ pos .L 2 := by decide
    have hL : -(((2 : ℕ) : ℝ) ^ 2) * Q u ≤ thetaHull Q .L 2 t₀ := by
      have h := Finset.le_sup' (fun i : Fin 3 => -(((2 : ℕ) : ℝ) ^ 2) * Q (t₀ i)) hmem
      simpa [thetaHull, t₀] using h
    rw [hV]
    have : -(((2 : ℕ) : ℝ) ^ 2) * Q v < -(((2 : ℕ) : ℝ) ^ 2) * Q u := by
      norm_num
      exact huv
    linarith

end Model

/-! ## 3. The two statements and the load -/

/-- A datum: the ends of the comparison, which take no reading, and the value of each reading,
written as the Θ-part of its (Ind1)-axis plus a remainder. A Kummer shift that grows with the
`q`-orders belongs to the Θ-part (it can only raise it); a bounded one belongs to the remainder. -/
structure Datum where
  /-- `|log q|`, the degree of the `q`-pilot -/
  a : ℝ
  /-- the mean of `j^2` -/
  k : ℝ
  /-- the constant of IV's upper bound `U = -k a + C` -/
  C : ℝ
  /-- the Θ-part of an (Ind1)-reading -/
  theta : Ind1 → ℝ
  /-- the remainder of a reading -/
  rest : Reading → ℝ
  a_pos : 0 < a
  one_lt_k : 1 < k
  theta_ge : ∀ r, -k * a ≤ theta r

namespace Datum

variable (D : Datum)

/-- The value `-|log Θ|` of the reading `R`. -/
def M (R : Reading) : ℝ := D.theta R.ind1 + D.rest R

/-- IV's upper bound. -/
def U : ℝ := -D.k * D.a + D.C

/-- Corollary 3.12 in the reading `R`. -/
def Cor (R : Reading) : Prop := -D.a ≤ D.M R

/-- The upper bound of IV in the reading `R`. -/
def IV (R : Reading) : Prop := D.M R ≤ D.U

/-- The height bound. It mentions no reading. -/
def Height : Prop := (D.k - 1) * D.a ≤ D.C

/-- The split point of an (Ind1)-reading. -/
noncomputable def x (r : Ind1) : ℝ := -D.theta r / D.a

/-- The part of the wall that Corollary 3.12 carries. -/
noncomputable def loadCor (r : Ind1) : ℝ := (D.x r - 1) * D.a

/-- The part of the wall that the upper bound of IV carries. -/
noncomputable def loadIV (r : Ind1) : ℝ := (D.k - D.x r) * D.a

theorem theta_eq (r : Ind1) : D.theta r = -D.x r * D.a := by
  unfold x
  field_simp [D.a_pos.ne']

/-- In every reading, the two statements together give the same height bound. -/
theorem conservation (R : Reading) (h1 : D.Cor R) (h2 : D.IV R) : D.Height := by
  unfold Cor IV U Height at *
  linarith

/-- The two slacks add up to the slack of the height bound, whatever the reading. -/
theorem slack_sum (R : Reading) :
    (D.M R + D.a) + (D.U - D.M R) = D.C - (D.k - 1) * D.a := by
  unfold U
  ring

theorem cor_iff (R : Reading) : D.Cor R ↔ D.loadCor R.ind1 ≤ D.rest R := by
  unfold Cor M loadCor
  rw [D.theta_eq]
  constructor <;> intro h <;> linarith

theorem iv_iff (R : Reading) : D.IV R ↔ D.loadIV R.ind1 ≤ D.C - D.rest R := by
  unfold IV M U loadIV
  rw [D.theta_eq]
  constructor <;> intro h <;> linarith

/-- The two loads always add up to the wall `(k - 1) a`. -/
theorem load_sum (r : Ind1) : D.loadCor r + D.loadIV r = (D.k - 1) * D.a := by
  unfold loadCor loadIV
  ring

theorem x_le_k (r : Ind1) : D.x r ≤ D.k := by
  have h := D.theta_ge r
  rw [D.theta_eq] at h
  have ha := D.a_pos
  nlinarith

theorem loadIV_nonneg (r : Ind1) : 0 ≤ D.loadIV r := by
  unfold loadIV
  exact mul_nonneg (sub_nonneg.mpr (D.x_le_k r)) D.a_pos.le

theorem loadIV_eq_zero_iff (r : Ind1) : D.loadIV r = 0 ↔ D.theta r = -D.k * D.a := by
  unfold loadIV
  rw [D.theta_eq]
  have ha := D.a_pos
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · have : D.x r = D.k := by linarith
      rw [this]
    · linarith
  · intro h
    have : D.x r = D.k := by
      have h' : (D.x r - D.k) * D.a = 0 := by linarith
      rcases mul_eq_zero.mp h' with h'' | h''
      · linarith
      · linarith
    rw [this]
    ring

theorem wall_pos : 0 < (D.k - 1) * D.a :=
  mul_pos (sub_pos.mpr D.one_lt_k) D.a_pos

/-- One of the two statements carries at least half of the wall. -/
theorem half_load_le_max (r : Ind1) : (D.k - 1) * D.a / 2 ≤ max (D.loadCor r) (D.loadIV r) := by
  have h := D.load_sum r
  rcases le_total (D.loadCor r) (D.loadIV r) with h' | h'
  · rw [max_eq_right h']
    linarith
  · rw [max_eq_left h']
    linarith

/-- No reading makes both loads nonpositive. -/
theorem not_both_loads_nonpos (r : Ind1) : ¬ (D.loadCor r ≤ 0 ∧ D.loadIV r ≤ 0) := by
  rintro ⟨h1, h2⟩
  have := D.load_sum r
  have := D.wall_pos
  linarith

/-- The height bound is the sum of the two statements, in the form of their loads and budgets. -/
theorem height_iff_sum (R : Reading) :
    D.Height ↔ D.loadCor R.ind1 + D.loadIV R.ind1 ≤ D.rest R + (D.C - D.rest R) := by
  unfold Height
  rw [D.load_sum]
  constructor <;> intro h <;> linarith

/-- If IV is replaced by the bound that holds automatically in the reading `R`
(`M R ≤ Θ + hi` with `rest R ≤ hi`), the two statements give only `loadCor ≤ hi`: the coefficient
of `a` falls short of the wall by exactly the load of IV. -/
theorem adapted_bound (R : Reading) (hi : ℝ) (hrest : D.rest R ≤ hi) (h : D.Cor R) :
    D.loadCor R.ind1 ≤ hi ∧ D.loadCor R.ind1 = (D.k - 1) * D.a - D.loadIV R.ind1 := by
  refine ⟨le_trans ((D.cor_iff R).mp h) hrest, ?_⟩
  have := D.load_sum R.ind1
  linarith

/-- The summary for one reading. -/
theorem summary (R : Reading) :
    (D.Cor R → D.IV R → D.Height) ∧
    (D.M R + D.a) + (D.U - D.M R) = D.C - (D.k - 1) * D.a ∧
    (D.Cor R ↔ D.loadCor R.ind1 ≤ D.rest R) ∧
    (D.IV R ↔ D.loadIV R.ind1 ≤ D.C - D.rest R) ∧
    D.loadCor R.ind1 + D.loadIV R.ind1 = (D.k - 1) * D.a ∧
    0 ≤ D.loadIV R.ind1 ∧
    (D.k - 1) * D.a / 2 ≤ max (D.loadCor R.ind1) (D.loadIV R.ind1) :=
  ⟨D.conservation R, D.slack_sum R, D.cor_iff R, D.iv_iff R, D.load_sum R.ind1,
    D.loadIV_nonneg R.ind1, D.half_load_le_max R.ind1⟩

end Datum

/-! ## 4. Replacing `q` by `q^N` -/

/-- A family of data: `q` replaced by `q^N`. The degree and the Θ-parts scale with `N`; `k` and
`C` stay; the remainders stay in a fixed interval. -/
structure Family where
  a : ℝ
  k : ℝ
  C : ℝ
  theta : Ind1 → ℝ
  rest : ℕ → Reading → ℝ
  lo : Reading → ℝ
  hi : Reading → ℝ
  a_pos : 0 < a
  one_lt_k : 1 < k
  theta_ge : ∀ r, -k * a ≤ theta r
  rest_lo : ∀ N R, lo R ≤ rest N R
  rest_hi : ∀ N R, rest N R ≤ hi R

namespace Family

variable (F : Family)

/-- The member with `q^N`, for `N ≥ 1`. -/
noncomputable def scaled (N : ℕ) (hN : 1 ≤ N) : Datum where
  a := N * F.a
  k := F.k
  C := F.C
  theta := fun r => N * F.theta r
  rest := F.rest N
  a_pos := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact mul_pos this F.a_pos
  one_lt_k := F.one_lt_k
  theta_ge := fun r => by
    have h := F.theta_ge r
    have hN' : (0 : ℝ) ≤ N := by positivity
    nlinarith

/-- The split point does not depend on `N`. -/
theorem x_scaled (N : ℕ) (hN : 1 ≤ N) (r : Ind1) : (F.scaled N hN).x r = -F.theta r / F.a := by
  have hN' : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  simp only [Datum.x, scaled]
  field_simp

/-- No reading keeps Corollary 3.12 and the upper bound of IV true for all `N`. -/
theorem no_uniform_reading (R : Reading) :
    ∃ N0 : ℕ, ∀ N (hN : 1 ≤ N), N0 ≤ N → ¬ ((F.scaled N hN).Cor R ∧ (F.scaled N hN).IV R) := by
  have hw : 0 < (F.k - 1) * F.a := mul_pos (sub_pos.mpr F.one_lt_k) F.a_pos
  refine ⟨⌈F.C / ((F.k - 1) * F.a)⌉₊ + 1, fun N hN hN0 ⟨h1, h2⟩ => ?_⟩
  have hH := (F.scaled N hN).conservation R h1 h2
  simp only [Datum.Height, scaled] at hH
  have hNbig : F.C / ((F.k - 1) * F.a) < N := by
    have h3 : (⌈F.C / ((F.k - 1) * F.a)⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN0
    have h4 := Nat.le_ceil (F.C / ((F.k - 1) * F.a))
    linarith
  rw [div_lt_iff₀ hw] at hNbig
  nlinarith

/-- If the upper bound of IV holds for all `N`, the reading puts no load on IV, and
Corollary 3.12 is the whole wall `(k - 1) N a ≤ rest`. -/
theorem iv_uniform (R : Reading) (h : ∀ N (hN : 1 ≤ N), (F.scaled N hN).IV R) :
    F.theta R.ind1 = -F.k * F.a ∧
      ∀ N (hN : 1 ≤ N), ((F.scaled N hN).Cor R ↔ (F.k - 1) * (N * F.a) ≤ F.rest N R) := by
  have htheta : F.theta R.ind1 = -F.k * F.a := by
    by_contra hne
    have hgt : -F.k * F.a < F.theta R.ind1 := lt_of_le_of_ne (F.theta_ge R.ind1) (Ne.symm hne)
    set g := F.theta R.ind1 + F.k * F.a with hg
    have hgpos : 0 < g := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt ((F.C - F.lo R) / g)
    have hN1 : 1 ≤ N + 1 := by omega
    have hIV := h (N + 1) hN1
    simp only [Datum.IV, Datum.M, Datum.U, scaled] at hIV
    have hlo := F.rest_lo (N + 1) R
    have hNg : F.C - F.lo R < (N : ℝ) * g := by
      rw [div_lt_iff₀ hgpos] at hN
      linarith
    push_cast at hIV
    nlinarith
  refine ⟨htheta, fun N hN => ?_⟩
  simp only [Datum.Cor, Datum.M, scaled]
  rw [htheta]
  constructor <;> intro h' <;> nlinarith

/-- If Corollary 3.12 holds for all `N`, then `x ≤ 1`, and the upper bound of IV carries at
least the whole wall. -/
theorem cor_uniform (R : Reading) (h : ∀ N (hN : 1 ≤ N), (F.scaled N hN).Cor R) :
    -F.a ≤ F.theta R.ind1 ∧
      ∀ N (hN : 1 ≤ N), (F.scaled N hN).IV R → (F.k - 1) * (N * F.a) ≤ F.C - F.rest N R := by
  have htheta : -F.a ≤ F.theta R.ind1 := by
    by_contra hlt
    push Not at hlt
    set g := -F.a - F.theta R.ind1 with hg
    have hgpos : 0 < g := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (F.hi R / g)
    have hN1 : 1 ≤ N + 1 := by omega
    have hCor := h (N + 1) hN1
    simp only [Datum.Cor, Datum.M, scaled] at hCor
    have hhi := F.rest_hi (N + 1) R
    have hNg : F.hi R < (N : ℝ) * g := by
      rw [div_lt_iff₀ hgpos] at hN
      linarith
    push_cast at hCor
    nlinarith
  refine ⟨htheta, fun N hN hIV => ?_⟩
  simp only [Datum.IV, Datum.M, Datum.U, scaled] at hIV
  have hN' : (0 : ℝ) ≤ N := by positivity
  nlinarith

theorem M_scaled (N : ℕ) (hN : 1 ≤ N) (R : Reading) :
    (F.scaled N hN).M R = N * F.theta R.ind1 + F.rest N R := rfl

/-- The Θ-part is the slope of the value of the reading in `N`: the split into the Θ-part and
the remainder is decided by the family, not chosen. -/
theorem tendsto_slope (R : Reading) :
    Filter.Tendsto (fun N : ℕ => ((N : ℝ) * F.theta R.ind1 + F.rest N R) / N) Filter.atTop
      (nhds (F.theta R.ind1)) := by
  have h0 : Filter.Tendsto (fun N : ℕ => F.rest N R / (N : ℝ)) Filter.atTop (nhds 0) := by
    have hlo := tendsto_const_div_atTop_nhds_zero_nat (F.lo R)
    have hhi := tendsto_const_div_atTop_nhds_zero_nat (F.hi R)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop 0] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      exact div_le_div_of_nonneg_right (F.rest_lo N R) hN'.le
    · filter_upwards [Filter.eventually_gt_atTop 0] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      exact div_le_div_of_nonneg_right (F.rest_hi N R) hN'.le
  have h1 : Filter.Tendsto (fun N : ℕ => F.theta R.ind1 + F.rest N R / (N : ℝ)) Filter.atTop
      (nhds (F.theta R.ind1)) := by
    simpa using (tendsto_const_nhds (x := F.theta R.ind1)).add h0
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [add_div, mul_div_cancel_left₀ _ hN']

end Family

/-! ## 5. The model gives a datum and a family -/

section Instances

variable {P : Type*} [Fintype P] {V : P → Type*} [∀ p, Fintype (V p)]

/-- Several primes: each prime `p` has its places `V p`, weights `w p`, `q`-orders `Q p`, and
enters with the coefficient `c p ≥ 0` (its `log p`). -/
noncomputable def thetaSum (c : P → ℝ) (w Q : ∀ p, V p → ℝ) (ls : ℕ) (r : Ind1) : ℝ :=
  ∑ p, c p * thetaPart (w p) (Q p) ls r

noncomputable def qdegSum (c : P → ℝ) (w Q : ∀ p, V p → ℝ) : ℝ := ∑ p, c p * qdeg (w p) (Q p)

theorem thetaSum_V (c : P → ℝ) (w Q : ∀ p, V p → ℝ) (hw1 : ∀ p, ∑ v, w p v = 1) (ls : ℕ) :
    thetaSum c w Q ls .V = -kmean ls * qdegSum c w Q := by
  unfold thetaSum qdegSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [thetaPart_V (w p) (Q p) (hw1 p) ls]
  ring

theorem thetaSum_ge (c : P → ℝ) (hc : ∀ p, 0 ≤ c p) (w Q : ∀ p, V p → ℝ)
    (hw0 : ∀ p v, 0 ≤ w p v) (hw1 : ∀ p, ∑ v, w p v = 1) (ls : ℕ) (r : Ind1) :
    -kmean ls * qdegSum c w Q ≤ thetaSum c w Q ls r := by
  rw [← thetaSum_V c w Q hw1 ls]
  unfold thetaSum
  apply Finset.sum_le_sum
  intro p _
  exact mul_le_mul_of_nonneg_left (thetaPart_mono (w p) (Q p) (hw0 p) ls r).1 (hc p)

theorem thetaSum_smul (c : P → ℝ) (w Q : ∀ p, V p → ℝ) (ls : ℕ) {N : ℝ} (hN : 0 ≤ N)
    (r : Ind1) : thetaSum c w (fun p v => N * Q p v) ls r = N * thetaSum c w Q ls r := by
  unfold thetaSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [thetaPart_smul (w p) (Q p) ls hN r]
  ring

theorem qdegSum_smul (c : P → ℝ) (w Q : ∀ p, V p → ℝ) (N : ℝ) :
    qdegSum c w (fun p v => N * Q p v) = N * qdegSum c w Q := by
  unfold qdegSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [qdeg_smul]
  ring

theorem sum_sq (n : ℕ) : ∑ j ∈ Icc 1 n, ((j : ℝ) ^ 2) = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

theorem kmean_eq (ls : ℕ) (hls : 1 ≤ ls) : kmean ls = (ls + 1) * (2 * ls + 1) / 6 := by
  unfold kmean
  rw [sum_sq]
  have h : (ls : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

theorem one_lt_kmean (ls : ℕ) (hls : 2 ≤ ls) : 1 < kmean ls := by
  rw [kmean_eq ls (by omega)]
  have h : (2 : ℝ) ≤ ls := by exact_mod_cast hls
  nlinarith

/-- The model, with any remainders and any constant `C`, is a datum. -/
noncomputable def modelDatum (c : P → ℝ) (hc : ∀ p, 0 ≤ c p) (w Q : ∀ p, V p → ℝ)
    (hw0 : ∀ p v, 0 ≤ w p v) (hw1 : ∀ p, ∑ v, w p v = 1) (ls : ℕ) (hls : 2 ≤ ls)
    (ha : 0 < qdegSum c w Q) (C : ℝ) (rest : Reading → ℝ) : Datum where
  a := qdegSum c w Q
  k := kmean ls
  C := C
  theta := thetaSum c w Q ls
  rest := rest
  a_pos := ha
  one_lt_k := one_lt_kmean ls hls
  theta_ge := thetaSum_ge c hc w Q hw0 hw1 ls

/-- In the model, the reading `V` puts no load on IV. -/
theorem modelDatum_loadIV_V (c : P → ℝ) (hc : ∀ p, 0 ≤ c p) (w Q : ∀ p, V p → ℝ)
    (hw0 : ∀ p v, 0 ≤ w p v) (hw1 : ∀ p, ∑ v, w p v = 1) (ls : ℕ) (hls : 2 ≤ ls)
    (ha : 0 < qdegSum c w Q) (C : ℝ) (rest : Reading → ℝ) :
    (modelDatum c hc w Q hw0 hw1 ls hls ha C rest).loadIV .V = 0 :=
  ((modelDatum c hc w Q hw0 hw1 ls hls ha C rest).loadIV_eq_zero_iff .V).mpr
    (thetaSum_V c w Q hw1 ls)

/-- The model, with remainders bounded in `N`, is a family; its member at `N` is the model with
the `q`-orders `N Q`. -/
noncomputable def modelFamily (c : P → ℝ) (hc : ∀ p, 0 ≤ c p) (w Q : ∀ p, V p → ℝ)
    (hw0 : ∀ p v, 0 ≤ w p v) (hw1 : ∀ p, ∑ v, w p v = 1) (ls : ℕ) (hls : 2 ≤ ls)
    (ha : 0 < qdegSum c w Q) (C : ℝ) (rest : ℕ → Reading → ℝ) (lo hi : Reading → ℝ)
    (hlo : ∀ N R, lo R ≤ rest N R) (hhi : ∀ N R, rest N R ≤ hi R) : Family where
  a := qdegSum c w Q
  k := kmean ls
  C := C
  theta := thetaSum c w Q ls
  rest := rest
  lo := lo
  hi := hi
  a_pos := ha
  one_lt_k := one_lt_kmean ls hls
  theta_ge := thetaSum_ge c hc w Q hw0 hw1 ls
  rest_lo := hlo
  rest_hi := hhi

theorem modelFamily_scaled (c : P → ℝ) (hc : ∀ p, 0 ≤ c p) (w Q : ∀ p, V p → ℝ)
    (hw0 : ∀ p v, 0 ≤ w p v) (hw1 : ∀ p, ∑ v, w p v = 1) (ls : ℕ) (hls : 2 ≤ ls)
    (ha : 0 < qdegSum c w Q) (C : ℝ) (rest : ℕ → Reading → ℝ) (lo hi : Reading → ℝ)
    (hlo : ∀ N R, lo R ≤ rest N R) (hhi : ∀ N R, rest N R ≤ hi R) (N : ℕ) (hN : 1 ≤ N) :
    ((modelFamily c hc w Q hw0 hw1 ls hls ha C rest lo hi hlo hhi).scaled N hN).a
        = qdegSum c w (fun p v => N * Q p v) ∧
      ∀ r, ((modelFamily c hc w Q hw0 hw1 ls hls ha C rest lo hi hlo hhi).scaled N hN).theta r
        = thetaSum c w (fun p v => N * Q p v) ls r := by
  have hN' : (0 : ℝ) ≤ N := by positivity
  refine ⟨?_, fun r => ?_⟩
  · simp only [Family.scaled, modelFamily]
    rw [qdegSum_smul]
  · simp only [Family.scaled, modelFamily]
    rw [thetaSum_smul c w Q ls hN' r]

end Instances

/-! ## 6. Two places above one prime: a bad one and a good one -/

section TwoPlaces

/-- Two kinds of places: `true` (bad: weight `p`, `q`-order `Qb`) and `false` (good). -/
def w2 (p : ℝ) : Bool → ℝ := fun b => if b then p else 1 - p

def Q2 (Qb : ℝ) : Bool → ℝ := fun b => if b then Qb else 0

theorem sum_w2 (p : ℝ) : ∑ b, w2 p b = 1 := by simp [w2]

theorem w2_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) : 0 ≤ w2 p b := by
  cases b <;> simp [w2] <;> linarith

theorem qdeg_two (p Qb : ℝ) : qdeg (w2 p) (Q2 Qb) = p * Qb := by
  simp [qdeg, w2, Q2]

/-- With two kinds of places, the Θ-part of `L0` at a component is `-j^2 Qb` if every factor sits
at the bad place, and `0` otherwise. -/
theorem thetaHull_L0_two (Qb : ℝ) (hQb : 0 ≤ Qb) (j : ℕ) (t : Fin (j + 1) → Bool) :
    thetaHull (Q2 Qb) .L0 j t = if (∀ i, t i = true) then -((j : ℝ) ^ 2) * Qb else 0 := by
  unfold thetaHull
  simp only [pos]
  split_ifs with h
  · have hc : (fun i : Fin (j + 1) => -((j : ℝ) ^ 2) * Q2 Qb (t i))
        = fun _ => -((j : ℝ) ^ 2) * Qb := by
      funext i
      simp [Q2, h i]
    rw [hc, Finset.sup'_const]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hi' : t i = false := by simpa using hi
    apply le_antisymm
    · refine Finset.sup'_le _ _ (fun i' _ => ?_)
      have hj := mul_nonneg (sq_nonneg (j : ℝ)) hQb
      rcases Bool.eq_false_or_eq_true (t i') with hb | hb <;> (simp [Q2, hb]; try linarith)
    · have h0 : -((j : ℝ) ^ 2) * Q2 Qb (t i) = 0 := by simp [Q2, hi']
      rw [← h0]
      exact Finset.le_sup' (fun i : Fin (j + 1) => -((j : ℝ) ^ 2) * Q2 Qb (t i)) (mem_univ i)

theorem wavg_thetaHull_L0_two (p Qb : ℝ) (hQb : 0 ≤ Qb) (j : ℕ) :
    wavg (w2 p) (j + 1) (thetaHull (Q2 Qb) .L0 j) = -((j : ℝ) ^ 2) * Qb * p ^ (j + 1) := by
  unfold wavg
  simp_rw [thetaHull_L0_two Qb hQb j]
  rw [Fintype.sum_eq_single (fun _ => true)]
  · simp [tupleWeight, w2]
    ring
  · intro t ht
    have h : ¬ ∀ i, t i = true := fun h => ht (funext h)
    simp [h]

/-- `A(p) = (1 / ls) ∑_{j=1}^{ls} j^2 p^j`. -/
noncomputable def Afun (p : ℝ) (ls : ℕ) : ℝ := (1 / ls) * ∑ j ∈ Icc 1 ls, ((j : ℝ) ^ 2 * p ^ j)

/-- Two places: the Θ-part of `L0` is `-(p Qb) A(p)`, so its split point is `x = A(p)`. -/
theorem thetaPart_L0_two (p Qb : ℝ) (hQb : 0 ≤ Qb) (ls : ℕ) :
    thetaPart (w2 p) (Q2 Qb) ls .L0 = -(p * Qb) * Afun p ls := by
  unfold thetaPart Afun
  rw [Finset.sum_congr rfl (fun j _ => wavg_thetaHull_L0_two p Qb hQb j)]
  have h : ∀ j ∈ Icc 1 ls, -((j : ℝ) ^ 2) * Qb * p ^ (j + 1) = -(p * Qb) * ((j : ℝ) ^ 2 * p ^ j) := by
    intro j _
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
  ring

/-- `∑_{j=1}^{n} j^2 / 2^j = 6 - (n^2 + 4n + 6) / 2^n`. -/
theorem sum_sq_half (n : ℕ) :
    ∑ j ∈ Icc 1 n, ((j : ℝ) ^ 2 * (1 / 2) ^ j) = 6 - ((n : ℝ) ^ 2 + 4 * n + 6) / 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    rw [one_div_pow, pow_succ]
    field_simp
    ring

theorem Afun_half_le_one (ls : ℕ) (hls : 1 ≤ ls) : Afun (1 / 2) ls ≤ 1 := by
  unfold Afun
  rw [sum_sq_half]
  have hls' : (0 : ℝ) < ls := by exact_mod_cast hls
  rw [one_div_mul_eq_div, div_le_one hls']
  rcases (show ls ≤ 5 ∨ 6 ≤ ls by omega) with h | h
  · interval_cases ls <;> norm_num
  · have h0 : (0 : ℝ) ≤ ((ls : ℝ) ^ 2 + 4 * ls + 6) / 2 ^ ls := by positivity
    have h6 : (6 : ℝ) ≤ ls := by exact_mod_cast h
    linarith

theorem Afun_mono {p p' : ℝ} (hp : 0 ≤ p) (hpp : p ≤ p') (ls : ℕ) : Afun p ls ≤ Afun p' ls := by
  unfold Afun
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hpp j) (sq_nonneg _)

/-- Two places, the bad one of weight at most `1/2` (the situation of Belyi points): the reading
`L0` has `x ≤ 1`, so Corollary 3.12 carries no load and IV carries at least the whole wall. -/
theorem twoPlace_x_L0_le_one {p Qb : ℝ} (hp : 0 < p) (hp2 : p ≤ 1 / 2) (hQb : 0 < Qb) (ls : ℕ)
    (hls : 1 ≤ ls) :
    -(thetaPart (w2 p) (Q2 Qb) ls .L0) / qdeg (w2 p) (Q2 Qb) ≤ 1 := by
  rw [thetaPart_L0_two p Qb hQb.le ls, qdeg_two]
  have hpQ : 0 < p * Qb := mul_pos hp hQb
  have hA : Afun p ls ≤ 1 := (Afun_mono hp.le hp2 ls).trans (Afun_half_le_one ls hls)
  rw [div_le_one hpQ]
  nlinarith [mul_le_mul_of_nonneg_left hA hpQ.le]

/-! ### A family of this kind: the two readings `V` and `L0` put the load on opposite sides -/

/-- One prime, a bad and a good place of weight `1/2` each, `q`-order `1` at the bad place, `ls`
levels, IV's constant `C`, and remainder `0` in every reading. -/
noncomputable def belyiFamily (ls : ℕ) (hls : 2 ≤ ls) (C : ℝ) : Family :=
  modelFamily (P := Unit) (V := fun _ => Bool) (fun _ => 1) (fun _ => zero_le_one)
    (fun _ => w2 (1 / 2)) (fun _ => Q2 1)
    (fun _ b => w2_nonneg (by norm_num) (by norm_num) b) (fun _ => sum_w2 _) ls hls
    (by simp [qdegSum, qdeg_two]) C (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ _ => le_refl _) (fun _ _ => le_refl _)

theorem belyiFamily_a (ls : ℕ) (hls : 2 ≤ ls) (C : ℝ) : (belyiFamily ls hls C).a = 1 / 2 := by
  simp [belyiFamily, modelFamily, qdegSum, qdeg_two]

theorem belyiFamily_theta_L0 (ls : ℕ) (hls : 2 ≤ ls) (C : ℝ) :
    (belyiFamily ls hls C).theta .L0 = -(1 / 2) * Afun (1 / 2) ls := by
  simp only [belyiFamily, modelFamily, thetaSum, Finset.univ_unique, Finset.sum_singleton, one_mul]
  rw [thetaPart_L0_two (1 / 2) 1 zero_le_one ls]
  ring

theorem belyiFamily_theta_V (ls : ℕ) (hls : 2 ≤ ls) (C : ℝ) :
    (belyiFamily ls hls C).theta .V = -kmean ls * (1 / 2) := by
  simp only [belyiFamily, modelFamily, thetaSum, Finset.univ_unique, Finset.sum_singleton, one_mul]
  rw [thetaPart_V _ _ (sum_w2 _) ls, qdeg_two]
  ring

/-- Reading `L0`: Corollary 3.12 holds for every `N`. -/
theorem belyi_cor_L0 (ls : ℕ) (hls : 2 ≤ ls) (C : ℝ) (R : Reading) (hR : R.ind1 = .L0)
    (N : ℕ) (hN : 1 ≤ N) : ((belyiFamily ls hls C).scaled N hN).Cor R := by
  show -((N : ℝ) * (belyiFamily ls hls C).a)
    ≤ (N : ℝ) * (belyiFamily ls hls C).theta R.ind1 + (belyiFamily ls hls C).rest N R
  have hrest : (belyiFamily ls hls C).rest N R = 0 := rfl
  rw [hR, belyiFamily_theta_L0, belyiFamily_a, hrest]
  have hA : Afun (1 / 2) ls ≤ 1 := Afun_half_le_one ls (by omega)
  have hN' : (0 : ℝ) ≤ N := by positivity
  nlinarith

/-- Reading `L0`: the upper bound of IV fails once `N` is large. -/
theorem belyi_iv_L0_fails (ls : ℕ) (hls : 2 ≤ ls) (C : ℝ) (R : Reading) (hR : R.ind1 = .L0) :
    ∃ N0 : ℕ, ∀ N (hN : 1 ≤ N), N0 ≤ N → ¬ ((belyiFamily ls hls C).scaled N hN).IV R := by
  obtain ⟨N0, h⟩ := (belyiFamily ls hls C).no_uniform_reading R
  exact ⟨N0, fun N hN hN0 hIV => h N hN hN0 ⟨belyi_cor_L0 ls hls C R hR N hN, hIV⟩⟩

/-- Reading `V`: with `C ≥ 0` the upper bound of IV holds for every `N`. -/
theorem belyi_iv_V (ls : ℕ) (hls : 2 ≤ ls) (C : ℝ) (hC : 0 ≤ C) (R : Reading) (hR : R.ind1 = .V)
    (N : ℕ) (hN : 1 ≤ N) : ((belyiFamily ls hls C).scaled N hN).IV R := by
  show (N : ℝ) * (belyiFamily ls hls C).theta R.ind1 + (belyiFamily ls hls C).rest N R
    ≤ -(belyiFamily ls hls C).k * ((N : ℝ) * (belyiFamily ls hls C).a) + (belyiFamily ls hls C).C
  have hrest : (belyiFamily ls hls C).rest N R = 0 := rfl
  have hk : (belyiFamily ls hls C).k = kmean ls := rfl
  have hC' : (belyiFamily ls hls C).C = C := rfl
  rw [hR, belyiFamily_theta_V, belyiFamily_a, hrest, hk, hC']
  nlinarith

/-- Reading `V`: Corollary 3.12 fails for every `N`. -/
theorem belyi_cor_V_fails (ls : ℕ) (hls : 2 ≤ ls) (C : ℝ) (R : Reading) (hR : R.ind1 = .V)
    (N : ℕ) (hN : 1 ≤ N) : ¬ ((belyiFamily ls hls C).scaled N hN).Cor R := by
  show ¬ (-((N : ℝ) * (belyiFamily ls hls C).a)
    ≤ (N : ℝ) * (belyiFamily ls hls C).theta R.ind1 + (belyiFamily ls hls C).rest N R)
  have hrest : (belyiFamily ls hls C).rest N R = 0 := rfl
  rw [hR, belyiFamily_theta_V, belyiFamily_a, hrest]
  have hk := one_lt_kmean ls hls
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  intro h
  nlinarith

end TwoPlaces

end ReadingFamily

#print axioms ReadingFamily.card_admissible
#print axioms ReadingFamily.thetaPart_V
#print axioms ReadingFamily.thetaPart_mono
#print axioms ReadingFamily.thetaPart_ge
#print axioms ReadingFamily.thetaPart_nonpos
#print axioms ReadingFamily.thetaPart_smul
#print axioms ReadingFamily.thetaPart_eq_V_of_const
#print axioms ReadingFamily.thetaPart_V_lt_L0
#print axioms ReadingFamily.thetaPart_V_lt_L
#print axioms ReadingFamily.Datum.conservation
#print axioms ReadingFamily.Datum.slack_sum
#print axioms ReadingFamily.Datum.cor_iff
#print axioms ReadingFamily.Datum.iv_iff
#print axioms ReadingFamily.Datum.load_sum
#print axioms ReadingFamily.Datum.loadIV_nonneg
#print axioms ReadingFamily.Datum.loadIV_eq_zero_iff
#print axioms ReadingFamily.Datum.half_load_le_max
#print axioms ReadingFamily.Datum.not_both_loads_nonpos
#print axioms ReadingFamily.Datum.adapted_bound
#print axioms ReadingFamily.Datum.summary
#print axioms ReadingFamily.Family.x_scaled
#print axioms ReadingFamily.Family.no_uniform_reading
#print axioms ReadingFamily.Family.iv_uniform
#print axioms ReadingFamily.Family.cor_uniform
#print axioms ReadingFamily.thetaSum_V
#print axioms ReadingFamily.thetaSum_ge
#print axioms ReadingFamily.thetaSum_smul
#print axioms ReadingFamily.modelDatum_loadIV_V
#print axioms ReadingFamily.modelFamily_scaled
#print axioms ReadingFamily.thetaPart_L0_two
#print axioms ReadingFamily.twoPlace_x_L0_le_one
#print axioms ReadingFamily.Family.tendsto_slope
#print axioms ReadingFamily.belyiFamily_theta_L0
#print axioms ReadingFamily.belyi_cor_L0
#print axioms ReadingFamily.belyi_iv_L0_fails
#print axioms ReadingFamily.belyi_iv_V
#print axioms ReadingFamily.belyi_cor_V_fails

#print axioms ReadingFamily.Reading.Admissible
#print axioms ReadingFamily.card_admissible
#print axioms ReadingFamily.tupleWeight
#print axioms ReadingFamily.wavg
#print axioms ReadingFamily.pos
#print axioms ReadingFamily.last_mem_pos
#print axioms ReadingFamily.pos_nonempty
#print axioms ReadingFamily.pos_V_subset
#print axioms ReadingFamily.pos_subset_L0
#print axioms ReadingFamily.thetaHull
#print axioms ReadingFamily.thetaHull_V
#print axioms ReadingFamily.thetaHull_le_of_subset
#print axioms ReadingFamily.thetaHull_nonpos
#print axioms ReadingFamily.sup'_const_mul
#print axioms ReadingFamily.thetaHull_smul
#print axioms ReadingFamily.wavg_mono
#print axioms ReadingFamily.wavg_smul
#print axioms ReadingFamily.wavg_factor
#print axioms ReadingFamily.thetaPart
#print axioms ReadingFamily.qdeg
#print axioms ReadingFamily.kmean
#print axioms ReadingFamily.thetaPart_V
#print axioms ReadingFamily.thetaPart_le_of_subset
#print axioms ReadingFamily.thetaPart_mono
#print axioms ReadingFamily.thetaPart_ge
#print axioms ReadingFamily.thetaPart_nonpos
#print axioms ReadingFamily.thetaPart_smul
#print axioms ReadingFamily.qdeg_smul
#print axioms ReadingFamily.thetaPart_eq_V_of_const
#print axioms ReadingFamily.wavg_lt_of_exists
#print axioms ReadingFamily.thetaPart_V_lt_L0
#print axioms ReadingFamily.thetaPart_V_lt_L
#print axioms ReadingFamily.Datum.M
#print axioms ReadingFamily.Datum.U
#print axioms ReadingFamily.Datum.Cor
#print axioms ReadingFamily.Datum.IV
#print axioms ReadingFamily.Datum.Height
#print axioms ReadingFamily.Datum.x
#print axioms ReadingFamily.Datum.loadCor
#print axioms ReadingFamily.Datum.loadIV
#print axioms ReadingFamily.Datum.theta_eq
#print axioms ReadingFamily.Datum.conservation
#print axioms ReadingFamily.Datum.slack_sum
#print axioms ReadingFamily.Datum.cor_iff
#print axioms ReadingFamily.Datum.iv_iff
#print axioms ReadingFamily.Datum.load_sum
#print axioms ReadingFamily.Datum.x_le_k
#print axioms ReadingFamily.Datum.loadIV_nonneg
#print axioms ReadingFamily.Datum.loadIV_eq_zero_iff
#print axioms ReadingFamily.Datum.wall_pos
#print axioms ReadingFamily.Datum.half_load_le_max
#print axioms ReadingFamily.Datum.not_both_loads_nonpos
#print axioms ReadingFamily.Datum.height_iff_sum
#print axioms ReadingFamily.Datum.adapted_bound
#print axioms ReadingFamily.Datum.summary
#print axioms ReadingFamily.Family.scaled
#print axioms ReadingFamily.Family.x_scaled
#print axioms ReadingFamily.Family.no_uniform_reading
#print axioms ReadingFamily.Family.iv_uniform
#print axioms ReadingFamily.Family.cor_uniform
#print axioms ReadingFamily.Family.M_scaled
#print axioms ReadingFamily.Family.tendsto_slope
#print axioms ReadingFamily.thetaSum
#print axioms ReadingFamily.qdegSum
#print axioms ReadingFamily.thetaSum_V
#print axioms ReadingFamily.thetaSum_ge
#print axioms ReadingFamily.thetaSum_smul
#print axioms ReadingFamily.qdegSum_smul
#print axioms ReadingFamily.sum_sq
#print axioms ReadingFamily.kmean_eq
#print axioms ReadingFamily.one_lt_kmean
#print axioms ReadingFamily.modelDatum
#print axioms ReadingFamily.modelDatum_loadIV_V
#print axioms ReadingFamily.modelFamily
#print axioms ReadingFamily.modelFamily_scaled
#print axioms ReadingFamily.w2
#print axioms ReadingFamily.Q2
#print axioms ReadingFamily.sum_w2
#print axioms ReadingFamily.w2_nonneg
#print axioms ReadingFamily.qdeg_two
#print axioms ReadingFamily.thetaHull_L0_two
#print axioms ReadingFamily.wavg_thetaHull_L0_two
#print axioms ReadingFamily.Afun
#print axioms ReadingFamily.thetaPart_L0_two
#print axioms ReadingFamily.sum_sq_half
#print axioms ReadingFamily.Afun_half_le_one
#print axioms ReadingFamily.Afun_mono
#print axioms ReadingFamily.twoPlace_x_L0_le_one
#print axioms ReadingFamily.belyiFamily
#print axioms ReadingFamily.belyiFamily_a
#print axioms ReadingFamily.belyiFamily_theta_L0
#print axioms ReadingFamily.belyiFamily_theta_V
#print axioms ReadingFamily.belyi_cor_L0
#print axioms ReadingFamily.belyi_iv_L0_fails
#print axioms ReadingFamily.belyi_iv_V
#print axioms ReadingFamily.belyi_cor_V_fails
