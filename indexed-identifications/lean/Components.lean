/-
Components: the quantitative core of Part II of
"Reading the IUT dispute through indexed identifications", version 2.0.0.

The model has one prime, a finite set `V` of places above it, weights `w : V → ℝ` and
`q`-orders `Q : V → ℝ`. At level `j` there are `j + 1` factors, and a component is a tuple
`t : Fin (j + 1) → V` of places, one for each factor. The Θ-pilot puts the value `-j^2 * Q (t j)`
on the component `t`: the theta value sits in the factor `j` (the last factor). A permutation of
the factors moves it to another factor.

Everything here is about this finite model; nothing here is inter-universal Teichmüller theory.
-/
import Mathlib

namespace Components

open Finset

/-! ## Tuples, weights and the action of the permutations of the factors -/

variable {V : Type*}

/-- The weight of a tuple of places: the product of the weights of its entries. -/
def tupleWeight (w : V → ℝ) {n : ℕ} (t : Fin n → V) : ℝ := ∏ i, w (t i)

/-- The weighted average of a function on the tuples of length `n`. -/
def wavg [Fintype V] (w : V → ℝ) (n : ℕ) (f : (Fin n → V) → ℝ) : ℝ := ∑ t, tupleWeight w t * f t

/-- A permutation `σ` of the factors acts on values: the new value at `t` is the old value at
`t ∘ σ`. -/
def act {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : (Fin n → V) → ℝ) : (Fin n → V) → ℝ :=
  fun t => x (t ∘ σ)

/-- The hull of the possible images under a nonempty finite set `S` of permutations: at each
component, the largest of the values (the union of balls is the largest ball). -/
noncomputable def hull {n : ℕ} (S : Finset (Equiv.Perm (Fin n))) (hS : S.Nonempty)
    (x : (Fin n → V) → ℝ) : (Fin n → V) → ℝ :=
  fun t => S.sup' hS (fun σ => act σ x t)

/-- The Θ-pilot at level `j`: the theta value `q^{j^2}` sits in the factor `j`. -/
def theta (Q : V → ℝ) (j : ℕ) : (Fin (j + 1) → V) → ℝ :=
  fun t => -((j : ℝ) ^ 2) * Q (t (Fin.last j))

/-! ## The two readings at one level -/

/-- Reading `S_a` (all permutations): the hull at `t` is the best factor of `t`. -/
theorem hull_univ_theta (Q : V → ℝ) (j : ℕ) (t : Fin (j + 1) → V) :
    hull (univ : Finset (Equiv.Perm (Fin (j + 1)))) univ_nonempty (theta Q j) t
      = univ.sup' univ_nonempty (fun i : Fin (j + 1) => -((j : ℝ) ^ 2) * Q (t i)) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun σ _ => ?_)
    exact Finset.le_sup' (fun i : Fin (j + 1) => -((j : ℝ) ^ 2) * Q (t i))
      (mem_univ (σ (Fin.last j)))
  · refine Finset.sup'_le _ _ (fun i _ => ?_)
    have h : act (Equiv.swap (Fin.last j) i) (theta Q j) t = -((j : ℝ) ^ 2) * Q (t i) := by
      simp [act, theta, Equiv.swap_apply_left]
    rw [← h]
    exact Finset.le_sup' (fun σ => act σ (theta Q j) t) (mem_univ _)

/-- The largest of `-c * g i` is `-c` times the smallest of `g i`, for `c ≥ 0`. -/
theorem sup'_neg_mul {ι : Type*} (c : ℝ) (hc : 0 ≤ c) (s : Finset ι) (hs : s.Nonempty)
    (g : ι → ℝ) : s.sup' hs (fun i => -c * g i) = -c * s.inf' hs g := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun i hi => ?_)
    have : s.inf' hs g ≤ g i := Finset.inf'_le g hi
    nlinarith
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' hs g
    rw [he]
    exact Finset.le_sup' (fun i => -c * g i) hi

/-- Reading `S_a` at a component: `-j^2` times the smallest `q`-order among the factors. -/
theorem hull_univ_theta_min (Q : V → ℝ) (j : ℕ) (t : Fin (j + 1) → V) :
    hull (univ : Finset (Equiv.Perm (Fin (j + 1)))) univ_nonempty (theta Q j) t
      = -((j : ℝ) ^ 2) * univ.inf' univ_nonempty (fun i => Q (t i)) := by
  rw [hull_univ_theta]
  exact sup'_neg_mul _ (sq_nonneg _) _ _ (fun i => Q (t i))

/-- Reading `S_b` (permutations fixing the factor `j`): nothing changes. -/
theorem hull_fix_theta (Q : V → ℝ) (j : ℕ) (S : Finset (Equiv.Perm (Fin (j + 1))))
    (hS : S.Nonempty) (hfix : ∀ σ ∈ S, σ (Fin.last j) = Fin.last j) :
    hull S hS (theta Q j) = theta Q j := by
  funext t
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun σ hσ => ?_)
    simp [act, theta, hfix σ hσ]
  · have hS' := hS
    obtain ⟨σ, hσ⟩ := hS'
    have h : act σ (theta Q j) t = theta Q j t := by
      simp [act, theta, hfix σ hσ]
    rw [← h]
    exact Finset.le_sup' (fun σ => act σ (theta Q j) t) hσ

/-- If all places have the same `q`-order, the two readings agree. -/
theorem hull_univ_const (Q0 : ℝ) (j : ℕ) :
    hull (univ : Finset (Equiv.Perm (Fin (j + 1)))) univ_nonempty
      (theta (fun _ : V => Q0) j) = theta (fun _ : V => Q0) j := by
  funext t
  rw [hull_univ_theta]
  simp [theta, Finset.sup'_const]

/-- A larger set of permutations gives a larger hull. -/
theorem hull_mono {n : ℕ} {S S' : Finset (Equiv.Perm (Fin n))} (hS : S.Nonempty)
    (hS' : S'.Nonempty) (h : S ⊆ S') (x : (Fin n → V) → ℝ) (t : Fin n → V) :
    hull S hS x t ≤ hull S' hS' x t := by
  unfold hull
  exact Finset.sup'_mono _ h hS

/-- If the identity is among the permutations, the hull lies above the value itself. -/
theorem le_hull {n : ℕ} (S : Finset (Equiv.Perm (Fin n))) (hS : S.Nonempty)
    (h1 : (1 : Equiv.Perm (Fin n)) ∈ S) (x : (Fin n → V) → ℝ) (t : Fin n → V) :
    x t ≤ hull S hS x t := by
  have h : act 1 x t = x t := by simp [act]
  rw [← h]
  exact Finset.le_sup' (fun σ => act σ x t) h1

/-! ## Averages: measuring each image separately -/

/-- The weight of a tuple does not change when the factors are permuted. -/
theorem tupleWeight_comp (w : V → ℝ) {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : Fin n → V) :
    tupleWeight w (t ∘ σ) = tupleWeight w t := by
  unfold tupleWeight
  exact Equiv.prod_comp σ (fun i => w (t i))

/-- The weighted average of an image is the weighted average of the value: measuring each
image separately gives the same number for every image. -/
theorem wavg_act [Fintype V] (w : V → ℝ) {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : (Fin n → V) → ℝ) :
    wavg w n (act σ x) = wavg w n x := by
  unfold wavg act
  refine Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl V)) _ _ (fun t => ?_)
  have he : (Equiv.arrowCongr σ.symm (Equiv.refl V)) t = t ∘ σ := by
    funext i
    simp [Equiv.arrowCongr_apply]
  rw [he, tupleWeight_comp]

/-- Averages are monotone for nonnegative weights. -/
theorem wavg_mono [Fintype V] (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) {n : ℕ} {f g : (Fin n → V) → ℝ}
    (h : ∀ t, f t ≤ g t) : wavg w n f ≤ wavg w n g := by
  unfold wavg
  apply Finset.sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left (h t) (Finset.prod_nonneg (fun i _ => hw (t i)))

/-- The average of a function of one factor is its average over the places. -/
theorem wavg_factor [Fintype V] (w : V → ℝ) (hw : ∑ v, w v = 1) {n : ℕ} (i₀ : Fin n) (g : V → ℝ) :
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

/-- Reading `S_a`, averaged: `-j^2` times the average of the smallest `q`-order among the
factors (the expected minimum of `j + 1` independent draws). -/
theorem wavg_hull_univ [Fintype V] (w : V → ℝ) (Q : V → ℝ) (j : ℕ) :
    wavg w (j + 1) (hull univ univ_nonempty (theta Q j))
      = -((j : ℝ) ^ 2) * wavg w (j + 1) (fun t => univ.inf' univ_nonempty (fun i => Q (t i))) := by
  unfold wavg
  simp_rw [hull_univ_theta_min]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  ring

/-! ## The hull takes the maximum of the possible images; a symmetrization takes their average -/

/-- The average of the possible images at each component (a symmetrization over `S`). -/
noncomputable def symm {n : ℕ} (S : Finset (Equiv.Perm (Fin n))) (x : (Fin n → V) → ℝ) :
    (Fin n → V) → ℝ :=
  fun t => (1 / (S.card : ℝ)) * ∑ σ ∈ S, act σ x t

/-- At each component the average of the possible images lies below their maximum. -/
theorem symm_le_hull {n : ℕ} (S : Finset (Equiv.Perm (Fin n))) (hS : S.Nonempty)
    (x : (Fin n → V) → ℝ) (t : Fin n → V) : symm S x t ≤ hull S hS x t := by
  unfold symm hull
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  rw [one_div_mul_eq_div, div_le_iff₀ hc]
  calc ∑ σ ∈ S, act σ x t ≤ ∑ _σ ∈ S, S.sup' hS (fun σ => act σ x t) :=
        Finset.sum_le_sum (fun σ hσ => Finset.le_sup' (fun σ => act σ x t) hσ)
    _ = S.sup' hS (fun σ => act σ x t) * S.card := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- After the weighted average over the components, the symmetrization changes nothing. -/
theorem wavg_symm [Fintype V] (w : V → ℝ) {n : ℕ} (S : Finset (Equiv.Perm (Fin n)))
    (hS : S.Nonempty) (x : (Fin n → V) → ℝ) : wavg w n (symm S x) = wavg w n x := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have h1 : wavg w n (symm S x) = (1 / (S.card : ℝ)) * ∑ σ ∈ S, wavg w n (act σ x) := by
    unfold wavg symm
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun t _ => ?_))
    ring
  rw [h1, Finset.sum_congr rfl (fun σ _ => wavg_act w σ x), Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- IV's symmetrization over the position `i†`: at each component, the average over the
`j + 1` factors of the value that the theta value would give in that factor. -/
noncomputable def thetaSym (Q : V → ℝ) (j : ℕ) : (Fin (j + 1) → V) → ℝ :=
  fun t => (1 / ((j : ℝ) + 1)) * ∑ i, -((j : ℝ) ^ 2) * Q (t i)

/-- At each component the symmetrized value lies below the hull of reading `S_a`. -/
theorem thetaSym_le_hull (Q : V → ℝ) (j : ℕ) (t : Fin (j + 1) → V) :
    thetaSym Q j t ≤ hull univ univ_nonempty (theta Q j) t := by
  rw [hull_univ_theta]
  unfold thetaSym
  have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [one_div_mul_eq_div, div_le_iff₀ hpos]
  calc ∑ i, -((j : ℝ) ^ 2) * Q (t i)
        ≤ ∑ _i : Fin (j + 1), univ.sup' univ_nonempty (fun i => -((j : ℝ) ^ 2) * Q (t i)) :=
        Finset.sum_le_sum (fun i _ => Finset.le_sup' (fun i => -((j : ℝ) ^ 2) * Q (t i)) (mem_univ i))
    _ = univ.sup' univ_nonempty (fun i => -((j : ℝ) ^ 2) * Q (t i)) * ((j : ℝ) + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- After the weighted average over the components, the symmetrization over `i†` gives the same
value as the theta value in the factor `j` (cf. the first equality of IUT IV, Prop. 1.7). -/
theorem wavg_thetaSym [Fintype V] (w : V → ℝ) (hw : ∑ v, w v = 1) (Q : V → ℝ) (j : ℕ) :
    wavg w (j + 1) (thetaSym Q j) = wavg w (j + 1) (theta Q j) := by
  have hθ : wavg w (j + 1) (theta Q j) = ∑ v, w v * (-((j : ℝ) ^ 2) * Q v) :=
    wavg_factor w hw (Fin.last j) (fun v => -((j : ℝ) ^ 2) * Q v)
  have h2 : ∀ i : Fin (j + 1), ∑ t : Fin (j + 1) → V, tupleWeight w t * (-((j : ℝ) ^ 2) * Q (t i))
      = ∑ v, w v * (-((j : ℝ) ^ 2) * Q v) :=
    fun i => wavg_factor w hw i (fun v => -((j : ℝ) ^ 2) * Q v)
  rw [hθ]
  unfold wavg thetaSym
  calc ∑ t, tupleWeight w t * ((1 / ((j : ℝ) + 1)) * ∑ i, -((j : ℝ) ^ 2) * Q (t i))
      = (1 / ((j : ℝ) + 1)) * ∑ i, ∑ t, tupleWeight w t * (-((j : ℝ) ^ 2) * Q (t i)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun t _ => ?_))
        ring
    _ = (1 / ((j : ℝ) + 1)) * ∑ _i : Fin (j + 1), ∑ v, w v * (-((j : ℝ) ^ 2) * Q v) := by
        rw [Finset.sum_congr rfl (fun i _ => h2 i)]
    _ = ∑ v, w v * (-((j : ℝ) ^ 2) * Q v) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp

/-! ## Two kinds of places -/

/-- Two kinds of places: `true` (bad: weight `p`, `q`-order `Qb`) and `false` (good). -/
def w2 (p : ℝ) : Bool → ℝ := fun b => if b then p else 1 - p

/-- The `q`-orders of the two kinds of places. -/
def Q2 (Qb : ℝ) : Bool → ℝ := fun b => if b then Qb else 0

theorem sum_w2 (p : ℝ) : ∑ b, w2 p b = 1 := by simp [w2]

theorem w2_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) : 0 ≤ w2 p b := by
  cases b <;> simp [w2] <;> linarith

/-- With two kinds of places, the hull in reading `S_a` is `-j^2 Qb` if every factor sits at a
bad place, and `0` otherwise. -/
theorem hull_univ_two (Qb : ℝ) (hQb : 0 ≤ Qb) (j : ℕ) (t : Fin (j + 1) → Bool) :
    hull univ univ_nonempty (theta (Q2 Qb) j) t
      = if (∀ i, t i = true) then -((j : ℝ) ^ 2) * Qb else 0 := by
  rw [hull_univ_theta]
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

/-- With two kinds of places, the expected minimum of `j + 1` draws is `Qb p^{j+1}`. -/
theorem wavg_hull_two (p Qb : ℝ) (hQb : 0 ≤ Qb) (j : ℕ) :
    wavg (w2 p) (j + 1) (hull univ univ_nonempty (theta (Q2 Qb) j))
      = -((j : ℝ) ^ 2) * Qb * p ^ (j + 1) := by
  unfold wavg
  simp_rw [hull_univ_two Qb hQb j]
  rw [Fintype.sum_eq_single (fun _ => true)]
  · simp [tupleWeight, w2]
    ring
  · intro t ht
    have h : ¬ ∀ i, t i = true := fun h => ht (funext h)
    simp [h]

/-- With two kinds of places, the average of the Θ-pilot itself is `-j^2 p Qb`. -/
theorem wavg_theta_two (p Qb : ℝ) (j : ℕ) :
    wavg (w2 p) (j + 1) (theta (Q2 Qb) j) = -((j : ℝ) ^ 2) * (p * Qb) := by
  have hθ : theta (Q2 Qb) j = fun t => (fun v => -((j : ℝ) ^ 2) * Q2 Qb v) (t (Fin.last j)) := rfl
  rw [hθ, wavg_factor (w2 p) (sum_w2 p) (Fin.last j) (fun v => -((j : ℝ) ^ 2) * Q2 Qb v),
    Fintype.sum_bool]
  show p * (-((j : ℝ) ^ 2) * Qb) + (1 - p) * (-((j : ℝ) ^ 2) * 0) = -((j : ℝ) ^ 2) * (p * Qb)
  ring

/-! ## Procession-normalized values: the average over the levels `j = 1, …, ls` -/

/-- The mean `k` of `j^2` over `j = 1, …, ls`. -/
noncomputable def kmean (ls : ℕ) : ℝ := (1 / ls) * ∑ j ∈ Icc 1 ls, ((j : ℝ) ^ 2)

/-- `A(p) = (1 / ls) * ∑_{j=1}^{ls} j^2 p^j`. -/
noncomputable def Afun (p : ℝ) (ls : ℕ) : ℝ := (1 / ls) * ∑ j ∈ Icc 1 ls, ((j : ℝ) ^ 2 * p ^ j)

/-- The value of the hull in reading `S_a`, averaged over the levels. -/
noncomputable def muA (p Qb : ℝ) (ls : ℕ) : ℝ :=
  (1 / ls) * ∑ j ∈ Icc 1 ls, wavg (w2 p) (j + 1) (hull univ univ_nonempty (theta (Q2 Qb) j))

/-- The value of the Θ-pilot itself (reading `S_b`), averaged over the levels. -/
noncomputable def muB (p Qb : ℝ) (ls : ℕ) : ℝ :=
  (1 / ls) * ∑ j ∈ Icc 1 ls, wavg (w2 p) (j + 1) (theta (Q2 Qb) j)

theorem muA_eq (p Qb : ℝ) (hQb : 0 ≤ Qb) (ls : ℕ) : muA p Qb ls = -(p * Qb) * Afun p ls := by
  unfold muA Afun
  rw [Finset.sum_congr rfl (fun j _ => wavg_hull_two p Qb hQb j)]
  have h : ∀ j ∈ Icc 1 ls, -((j : ℝ) ^ 2) * Qb * p ^ (j + 1) = -(p * Qb) * ((j : ℝ) ^ 2 * p ^ j) := by
    intro j _
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
  ring

theorem muB_eq (p Qb : ℝ) (ls : ℕ) : muB p Qb ls = -(p * Qb) * kmean ls := by
  unfold muB kmean
  rw [Finset.sum_congr rfl (fun j _ => wavg_theta_two p Qb j)]
  have h : ∀ j ∈ Icc 1 ls, -((j : ℝ) ^ 2) * (p * Qb) = -(p * Qb) * ((j : ℝ) ^ 2) := by
    intro j _
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
  ring

/-- `∑_{j=1}^{n} j^2 = n (n + 1) (2n + 1) / 6`. -/
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

/-- With `l = 2 ls + 1`, the mean of `j^2` is `l (l + 1) / 12`. -/
theorem kmean_eq_l (ls : ℕ) (hls : 1 ≤ ls) :
    kmean ls = (2 * ls + 1) * ((2 * ls + 1) + 1) / 12 := by
  rw [kmean_eq ls hls]
  ring

theorem kmean_gt_one (ls : ℕ) (hls : 2 ≤ ls) : 1 < kmean ls := by
  rw [kmean_eq ls (by omega)]
  have h : (2 : ℝ) ≤ ls := by exact_mod_cast hls
  nlinarith

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

/-- If at most half of the weight sits at bad places, then `A(p) ≤ 1`, for every `ls ≥ 1`. -/
theorem Afun_le_one_of_le_half {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) (ls : ℕ) (hls : 1 ≤ ls) :
    Afun p ls ≤ 1 :=
  (Afun_mono hp hp2 ls).trans (Afun_half_le_one ls hls)

theorem Afun_lt_kmean {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) (ls : ℕ) (hls : 1 ≤ ls) :
    Afun p ls < kmean ls := by
  unfold Afun kmean
  have hls' : (0 : ℝ) < ls := by exact_mod_cast hls
  apply mul_lt_mul_of_pos_left _ (by positivity)
  apply Finset.sum_lt_sum
  · intro j _
    have h : p ^ j ≤ 1 := pow_le_one₀ hp hp1.le
    have hj := sq_nonneg (j : ℝ)
    nlinarith
  · refine ⟨1, by simp [hls], ?_⟩
    simp
    linarith

/-! ## Corollary 3.12 and the upper bound of IV in the model -/

/-- Corollary 3.12 in the model: the value `-Q` of the `q`-pilot lies below the value `M` of the
hull plus the blur `E` of (Ind2), (Ind3). -/
def Cor312 (M E Q : ℝ) : Prop := -Q ≤ M + E

/-- The upper bound of IV in the model, with the constant `C`. -/
def IVbound (M E Q k C : ℝ) : Prop := M + E ≤ -k * Q + C

/-- The conservation law: for any hull value `M`, the two statements together give the height
bound. -/
theorem conservation {M E Q k C : ℝ} (h1 : Cor312 M E Q) (h2 : IVbound M E Q k C) :
    (k - 1) * Q ≤ C := by
  unfold Cor312 IVbound at *
  linarith

/-- Reading `S_b`: Corollary 3.12 is `(k - 1) Q ≤ E`. -/
theorem cor312_B_iff (p Qb E : ℝ) (ls : ℕ) :
    Cor312 (muB p Qb ls) E (p * Qb) ↔ (kmean ls - 1) * (p * Qb) ≤ E := by
  unfold Cor312
  rw [muB_eq]
  constructor <;> intro h <;> linarith

/-- Reading `S_b`: the upper bound of IV is `E ≤ C`. -/
theorem iv_B_iff (p Qb E C : ℝ) (ls : ℕ) :
    IVbound (muB p Qb ls) E (p * Qb) (kmean ls) C ↔ E ≤ C := by
  unfold IVbound
  rw [muB_eq]
  constructor <;> intro h <;> linarith

/-- Reading `S_a`: if `A(p) ≤ 1`, Corollary 3.12 holds for every `Qb ≥ 0` and every `E ≥ 0`. -/
theorem cor312_A_of {p Qb E : ℝ} (hp : 0 ≤ p) (hQb : 0 ≤ Qb) (hE : 0 ≤ E) (ls : ℕ)
    (hA : Afun p ls ≤ 1) : Cor312 (muA p Qb ls) E (p * Qb) := by
  unfold Cor312
  rw [muA_eq p Qb hQb]
  have hpQ : 0 ≤ p * Qb := mul_nonneg hp hQb
  nlinarith [mul_le_mul_of_nonneg_left hA hpQ]

/-- Reading `S_a` with `E = 0`: Corollary 3.12 holds exactly when `A(p) ≤ 1`. -/
theorem cor312_A_iff {p Qb : ℝ} (hpQ : 0 < p * Qb) (hQb : 0 ≤ Qb) (ls : ℕ) :
    Cor312 (muA p Qb ls) 0 (p * Qb) ↔ Afun p ls ≤ 1 := by
  unfold Cor312
  rw [muA_eq p Qb hQb]
  constructor
  · intro h
    by_contra hA
    push Not at hA
    nlinarith
  · intro hA
    nlinarith [mul_le_mul_of_nonneg_left hA hpQ.le]

/-- Reading `S_a`: the upper bound of IV fails as soon as `Qb` is large. -/
theorem iv_A_fails {p E C : ℝ} (hp : 0 < p) (hp1 : p < 1) (ls : ℕ) (hls : 1 ≤ ls) :
    ∃ Q0 : ℝ, ∀ Qb, Q0 < Qb → ¬ IVbound (muA p Qb ls) E (p * Qb) (kmean ls) C := by
  have hgap : 0 < kmean ls - Afun p ls := sub_pos.mpr (Afun_lt_kmean hp.le hp1 ls hls)
  have hpos : 0 < p * (kmean ls - Afun p ls) := mul_pos hp hgap
  refine ⟨max 0 ((C - E) / (p * (kmean ls - Afun p ls))), fun Qb hQb => ?_⟩
  have hQb0 : 0 ≤ Qb := le_trans (le_max_left _ _) hQb.le
  unfold IVbound
  rw [muA_eq p Qb hQb0]
  intro h
  have h2 : (C - E) / (p * (kmean ls - Afun p ls)) < Qb := lt_of_le_of_lt (le_max_right _ _) hQb
  rw [div_lt_iff₀ hpos] at h2
  nlinarith

/-- The `IV` reading implies the reading `S_a` (the hull of `S_a` is larger). -/
theorem muB_le_muA (p Qb : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ls : ℕ) :
    muB p Qb ls ≤ muA p Qb ls := by
  unfold muA muB
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  exact wavg_mono (w2 p) (w2_nonneg hp0 hp1)
    (fun t => le_hull _ _ (Finset.mem_univ _) _ t)

theorem cor312_A_of_B {p Qb E : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ls : ℕ)
    (h : Cor312 (muB p Qb ls) E (p * Qb)) : Cor312 (muA p Qb ls) E (p * Qb) := by
  unfold Cor312 at *
  linarith [muB_le_muA p Qb hp0 hp1 ls]

theorem iv_B_of_A {p Qb E C : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ls : ℕ)
    (h : IVbound (muA p Qb ls) E (p * Qb) (kmean ls) C) :
    IVbound (muB p Qb ls) E (p * Qb) (kmean ls) C := by
  unfold IVbound at *
  linarith [muB_le_muA p Qb hp0 hp1 ls]

/-- Replacing `q` by `q^N`: in reading `S_b`, Corollary 3.12 fails for large `N`. -/
theorem cor312_B_fails_scaled {p Qb E : ℝ} (hp : 0 < p) (hQb : 0 < Qb) (ls : ℕ)
    (hk : 1 < kmean ls) :
    ∃ N0 : ℝ, ∀ N, N0 < N → ¬ Cor312 (muB p (N * Qb) ls) E (p * (N * Qb)) := by
  have hpos : 0 < (kmean ls - 1) * (p * Qb) := mul_pos (by linarith) (mul_pos hp hQb)
  refine ⟨E / ((kmean ls - 1) * (p * Qb)), fun N hN => ?_⟩
  rw [cor312_B_iff]
  intro h
  rw [div_lt_iff₀ hpos] at hN
  nlinarith

/-- Replacing `q` by `q^N`: in reading `S_a`, Corollary 3.12 holds for every `N ≥ 0` when
`A(p) ≤ 1`. -/
theorem cor312_A_scaled {p Qb E : ℝ} (hp : 0 ≤ p) (hQb : 0 ≤ Qb) (hE : 0 ≤ E) (ls : ℕ)
    (hA : Afun p ls ≤ 1) (N : ℝ) (hN : 0 ≤ N) :
    Cor312 (muA p (N * Qb) ls) E (p * (N * Qb)) :=
  cor312_A_of hp (mul_nonneg hN hQb) hE ls hA

/-- The mixed pair (Corollary 3.12 in reading `S_a`, the bound of IV in reading `S_b`) holds for
every `Qb ≥ 0` when `p ≤ 1/2` and `E ≤ C`: it gives no bound on `Q`. -/
theorem mixed_pair_holds {p Qb E C : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) (hQb : 0 ≤ Qb)
    (hE : 0 ≤ E) (hEC : E ≤ C) (ls : ℕ) (hls : 1 ≤ ls) :
    Cor312 (muA p Qb ls) E (p * Qb) ∧ IVbound (muB p Qb ls) E (p * Qb) (kmean ls) C :=
  ⟨cor312_A_of hp hQb hE ls (Afun_le_one_of_le_half hp hp2 ls hls),
    (iv_B_iff p Qb E C ls).mpr hEC⟩

end Components

#print axioms Components.hull_univ_theta
#print axioms Components.hull_univ_theta_min
#print axioms Components.hull_fix_theta
#print axioms Components.hull_univ_const
#print axioms Components.hull_mono
#print axioms Components.le_hull
#print axioms Components.wavg_act
#print axioms Components.wavg_factor
#print axioms Components.symm_le_hull
#print axioms Components.wavg_symm
#print axioms Components.thetaSym_le_hull
#print axioms Components.wavg_thetaSym
#print axioms Components.wavg_hull_univ
#print axioms Components.wavg_hull_two
#print axioms Components.wavg_theta_two
#print axioms Components.muA_eq
#print axioms Components.muB_eq
#print axioms Components.kmean_eq_l
#print axioms Components.kmean_gt_one
#print axioms Components.sum_sq_half
#print axioms Components.Afun_le_one_of_le_half
#print axioms Components.Afun_lt_kmean
#print axioms Components.conservation
#print axioms Components.cor312_B_iff
#print axioms Components.iv_B_iff
#print axioms Components.cor312_A_of
#print axioms Components.cor312_A_iff
#print axioms Components.iv_A_fails
#print axioms Components.cor312_A_of_B
#print axioms Components.iv_B_of_A
#print axioms Components.cor312_B_fails_scaled
#print axioms Components.cor312_A_scaled
#print axioms Components.mixed_pair_holds
