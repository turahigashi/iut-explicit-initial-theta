import LogShellEdge.Reuse.Logshell.LocalFieldLogSurjective
import LogShellEdge.Reuse.Logshell.LocalFieldLogAdd
import Mathlib.Data.Nat.Choose.Dvd

/-!
# The logarithm on `U¹ = 1 + 𝔪` of a small field (Lemma 2.2(a)(b) of the note)

This file formalizes Lemma 2.2(a)(b) (`l:small`) of the note for a normed, complete, ultrametric
extension `K` of `ℚ_p`, i.e. for the carrier of the reused files

    [NormedField K] [NormedAlgebra ℚ_[p] K] [CompleteSpace K] [IsUltrametricDist K].

The role of `𝔪` is played by the closed ball `B ρ = {x | ‖x‖ ≤ ρ}` of radius `ρ = ‖π‖`, where
`ρ ^ e = ‖p‖` and `e ≤ p - 2` (`K` is small, Definition 2.1 of the note).  When `K` is a finite
extension of `ℚ_p` with ramification index `e`, the norm is discrete and `B ρ = 𝔪`; discreteness is
not used here.

## What is reused

The series `log1p x = Σ (-1)^n x^(n+1)/(n+1)` and its basic properties are those of the reused files
in `LogShellEdge/Reuse/Logshell/` (namespaces `LogShellEdge.Logshell.*`): summability for `‖x‖ < 1`, the
splitting of `log1p x` into the head `x` and a tail, the ultrametric bound for `x^m - y^m`, and the
homomorphism property `log1p (x + y + x y) = log1p x + log1p y` for `‖x‖, ‖y‖ < 1`.  The reused files
prove the isometry and the bijection on the ball of radius `1/4`.  That ball is smaller than `B ρ` in
general (for `p = 3`, `e = 1` the radius is `ρ = 1/3`), so those two results are not invoked; their
proofs (the contraction estimate and the Banach fixed point argument of `LocalFieldLogSurjective`)
are rerun here on `B ρ`.

## What is new

The coefficient estimate of the note's proof of (b): for `n ≥ 2`,
`(n - 1) - e·v_p(n) ≥ 1` (if `k = v_p(n) ≥ 1`, then `e k ≤ (p - 2) k < p^k - 1 ≤ n - 1`).
In norm terms `ρ ^ (n - 1) ≤ ρ · ‖n‖`, because `‖n‖ = ‖p‖ ^ v_p(n) = ρ ^ (e·v_p(n))`.
Hence the tail `g x = log1p x - x` satisfies `‖g x - g y‖ ≤ ρ ‖x - y‖` on `B ρ`, with the uniform
contraction constant `ρ < 1`.

## Main results (in the order of the note)

* `norm_log1p_eq`: `‖log1p x‖ = ‖x‖` on `B ρ` (Lemma 2.2(b): `log` preserves the valuation);
* `log1p_bijOn`: `log1p` maps `B ρ` bijectively onto `B ρ` (Lemma 2.2(b));
* `log_hom_on_ball`: `log1p ((1 + x)(1 + y) - 1) = log1p x + log1p y` on `B ρ`; with `log1p_bijOn`
  this says that `1 + x ↦ log1p x` is a group isomorphism `U¹ ≅ 𝔪` (Lemma 2.2(b));
* `no_nontrivial_pth_root`: `ζ ^ p = 1` and `‖ζ - 1‖ ≤ ρ` imply `ζ = 1` (Lemma 2.2(a) inside `U¹`);
  `eq_one_of_pow_eq_one`: more generally `U¹` is torsion-free (the "in particular" of (a));
* `mu_p_not_subset`: the note's `μ_p ⊄ K`: every `ζ` with `ζ ^ p = 1` is `1`, under the explicit
  discreteness hypothesis `hdisc : ∀ x, ‖x‖ < 1 → ‖x‖ ≤ ρ` (i.e. `{‖x‖ < 1} = B ρ`, which is what
  `B ρ = 𝔪` means for a discretely valued `K`).  It rests on `norm_sub_one_lt_one_of_pow_eq_one`
  (`ζ ^ p = 1 ⟹ ‖ζ - 1‖ < 1`, no hypothesis on `e` or `ρ`), which replaces the residue field
  argument of the note.  `eq_one_of_pow_prime_pow_eq_one` extends it to `ζ ^ (p ^ k) = 1`, and
  `padic_hdisc`, `padic_mu_p_trivial` check that the hypotheses hold for `K = ℚ_p` (`p ≥ 3`).

The hypotheses are explicit arguments, and each theorem takes only those its proof uses:
`e ≤ p - 2` and `ρ ^ e = ‖p‖` for (a) and for the norm and bijection statements of (b), `0 < ρ` in
addition for the bijection (`log1p_bijOn`), and only `ρ ^ e = ‖p‖` (which gives `ρ < 1`) for the
homomorphism property (`log_hom_on_ball`).  The hypothesis `1 ≤ e` of the note is not needed: it
follows from `ρ ^ e = ‖p‖` (`one_le_of_pow_eq_norm_p`).  `hypotheses_nonvacuous` checks that the
hypotheses can be met (`p ≥ 3`, `e = 1`, `ρ = ‖p‖`).  No residue field, finite dimension or local
compactness is assumed anywhere; the only place where discreteness enters is the explicit
hypothesis `hdisc` of `mu_p_not_subset` and `eq_one_of_pow_prime_pow_eq_one`.
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge.SmallLog

open LogShellEdge.Logshell.LocalFieldLogIsometry (log1p term log1p_zero log_eq_head_add_tail summable_signed)
open LogShellEdge.Logshell.LocalFieldLogContraction (norm_pow_sub_pow_le)

/-! ## 1. Arithmetic: `e·v_p(n) + 2 ≤ n` for `n ≥ 2` -/

/-- `e·k + 2 ≤ q^k` for every `k ≥ 1`, when `e + 2 ≤ q`. -/
theorem mul_add_two_le_pow (e q : ℕ) (hq : e + 2 ≤ q) (k : ℕ) (hk : 1 ≤ k) :
    e * k + 2 ≤ q ^ k := by
  induction k, hk using Nat.le_induction with
  | base => simpa using hq
  | succ k hk ih =>
    have hpos : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
    have h1 : q ^ k * (e + 2) ≤ q ^ k * q := Nat.mul_le_mul_left _ hq
    have h2 : e * 1 ≤ e * q ^ k := Nat.mul_le_mul_left _ hpos
    rw [pow_succ]
    nlinarith [Nat.zero_le (e * k)]

section Arith

variable (p : ℕ) [hp : Fact p.Prime]

/-- The arithmetic in the note's proof of Lemma 2.2(b): if `e ≤ p - 2` and `n ≥ 2`, then
`e·v_p(n) + 2 ≤ n`, i.e. `(n - 1) - e·v_p(n) ≥ 1`.  For `k = v_p(n) ≥ 1`,
`e k ≤ (p - 2) k < p^k - 1 ≤ n - 1`; for `k = 0` it is `n ≥ 2`. -/
theorem mul_padicValNat_add_two_le (e : ℕ) (hep : e ≤ p - 2) (n : ℕ) (hn : 2 ≤ n) :
    e * padicValNat p n + 2 ≤ n := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hq : e + 2 ≤ p := by omega
  have hdvd : p ^ padicValNat p n ∣ n := pow_padicValNat_dvd
  have hle : p ^ padicValNat p n ≤ n := Nat.le_of_dvd (by omega) hdvd
  rcases Nat.eq_zero_or_pos (padicValNat p n) with hk | hk
  · rw [hk]
    omega
  · have := mul_add_two_le_pow e p hq (padicValNat p n) hk
    omega

/-- `‖n‖ = ‖p‖ ^ v_p(n)` in `ℚ_p`, for `n ≠ 0`. -/
theorem padic_norm_natCast_eq (n : ℕ) (hn : n ≠ 0) :
    ‖((n : ℕ) : ℚ_[p])‖ = ‖((p : ℕ) : ℚ_[p])‖ ^ padicValNat p n := by
  have hcast : ((n : ℚ_[p])) = (((n : ℚ)) : ℚ_[p]) := by push_cast; ring
  have hne : ((n : ℚ)) ≠ 0 := by exact_mod_cast hn
  have hnorm : ‖((n : ℚ_[p]))‖ = ((padicNorm p (n : ℚ) : ℚ) : ℝ) := by
    rw [hcast]; exact_mod_cast Padic.eq_padicNorm (p := p) (n : ℚ)
  have hval : padicNorm p (n : ℚ) = (p : ℚ) ^ (-(padicValNat p n : ℤ)) := by
    rw [padicNorm, if_neg hne, padicValRat.of_nat]
  rw [hnorm, hval, Padic.norm_p, Rat.cast_zpow, Rat.cast_natCast, zpow_neg, zpow_natCast, inv_pow]

end Arith

/-! ## 2. The ball `B ρ` -/

section Ball

variable {K : Type*} [NormedField K]

/-- The closed ball `B ρ = {x | ‖x‖ ≤ ρ}`.  It is `𝔪` when `K` is a finite extension of `ℚ_p`
and `ρ = ‖π‖`; discreteness of the norm is not used in this file. -/
def B (ρ : ℝ) : Set K := {x : K | ‖x‖ ≤ ρ}

@[simp] theorem mem_B {ρ : ℝ} {x : K} : x ∈ B ρ ↔ ‖x‖ ≤ ρ := Iff.rfl

end Ball

/-! ## 3. Norms of integers in `K` and the radius `ρ` -/

section Norm

variable (p : ℕ) [hp : Fact p.Prime]
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]

/-- The norm of an integer in `K` is its `p`-adic norm (the algebra map is an isometry). -/
theorem norm_natCast_K (m : ℕ) : ‖((m : ℕ) : K)‖ = ‖((m : ℕ) : ℚ_[p])‖ := by
  rw [← norm_algebraMap' K ((m : ℕ) : ℚ_[p]), map_natCast]

/-- `‖n‖ = ‖p‖ ^ v_p(n)` in `K`, for `n ≠ 0`. -/
theorem norm_natCast_eq (n : ℕ) (hn : n ≠ 0) :
    ‖((n : ℕ) : K)‖ = ‖((p : ℕ) : K)‖ ^ padicValNat p n := by
  rw [norm_natCast_K p n, norm_natCast_K p p, padic_norm_natCast_eq p n hn]

theorem norm_p_pos : 0 < ‖((p : ℕ) : K)‖ := by
  rw [norm_natCast_K p p, Padic.norm_p]
  exact inv_pos.mpr (by exact_mod_cast hp.out.pos)

theorem norm_p_lt_one : ‖((p : ℕ) : K)‖ < 1 := by
  rw [norm_natCast_K p p]
  exact Padic.norm_p_lt_one

/-- `ρ < 1` (from `ρ ^ e = ‖p‖ < 1`). -/
theorem rho_lt_one {e : ℕ} {ρ : ℝ} (hρe : ρ ^ e = ‖((p : ℕ) : K)‖) : ρ < 1 := by
  by_contra h
  have h1 : 1 ≤ ρ ^ e := one_le_pow₀ (not_lt.mp h)
  have h2 := norm_p_lt_one p (K := K)
  linarith

/-- The hypothesis `1 ≤ e` of the note follows from `ρ ^ e = ‖p‖` (as `ρ ^ 0 = 1 ≠ ‖p‖`). -/
theorem one_le_of_pow_eq_norm_p {e : ℕ} {ρ : ℝ} (hρe : ρ ^ e = ‖((p : ℕ) : K)‖) : 1 ≤ e := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero] at hρe
    have := norm_p_lt_one p (K := K)
    linarith
  · exact he

/-- The coefficient estimate behind Lemma 2.2(b): for `n ≥ 2` and `0 ≤ M ≤ ρ`,
`M ^ (n - 1) ≤ ρ · ‖n‖`.  Indeed `‖n‖ = ‖p‖ ^ v_p(n) = ρ ^ (e·v_p(n))`, and
`e·v_p(n) + 1 ≤ n - 1` by `mul_padicValNat_add_two_le`. -/
theorem pow_pred_le_mul_norm_natCast {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ}
    (hρe : ρ ^ e = ‖((p : ℕ) : K)‖) (n : ℕ) (hn : 2 ≤ n) {M : ℝ} (hM0 : 0 ≤ M) (hMρ : M ≤ ρ) :
    M ^ (n - 1) ≤ ρ * ‖((n : ℕ) : K)‖ := by
  have hρ0 : 0 ≤ ρ := hM0.trans hMρ
  have hρ1 : ρ < 1 := rho_lt_one p hρe
  have hk := mul_padicValNat_add_two_le p e hep n hn
  have hnorm : ‖((n : ℕ) : K)‖ = ρ ^ (e * padicValNat p n) := by
    rw [norm_natCast_eq p n (by omega), ← hρe, ← pow_mul]
  rw [hnorm, ← pow_succ']
  calc M ^ (n - 1) ≤ ρ ^ (n - 1) := pow_le_pow_left₀ hM0 hMρ _
    _ ≤ ρ ^ (e * padicValNat p n + 1) := pow_le_pow_of_le_one hρ0 hρ1.le (by omega)

/-- Nondegeneracy: for `p ≥ 3`, `e = 1` and `ρ = ‖p‖` satisfy the hypotheses, and `B ρ` contains
the nonzero element `p`. -/
theorem hypotheses_nonvacuous (hp3 : 3 ≤ p) :
    (1 : ℕ) ≤ p - 2 ∧ ‖((p : ℕ) : K)‖ ^ 1 = ‖((p : ℕ) : K)‖ ∧ 0 < ‖((p : ℕ) : K)‖ ∧
      ((p : ℕ) : K) ∈ B ‖((p : ℕ) : K)‖ ∧ ((p : ℕ) : K) ≠ 0 := by
  refine ⟨by omega, pow_one _, norm_p_pos p, mem_B.mpr le_rfl, ?_⟩
  rw [← norm_ne_zero_iff]
  exact (norm_p_pos p).ne'

end Norm

/-! ## 4. The tail `g x = log1p x - x` is a contraction with constant `ρ` on `B ρ` -/

section Ultra

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Powers stay in `U¹`: `‖(1 + x) ^ n - 1‖ ≤ ‖x‖` for `‖x‖ < 1`. -/
theorem norm_one_add_pow_sub_one_le {x : K} (hx : ‖x‖ < 1) (n : ℕ) :
    ‖(1 + x) ^ n - 1‖ ≤ ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (1 + x) ^ (n + 1) - 1 = ((1 + x) ^ n - 1) + (x + ((1 + x) ^ n - 1) * x) := by ring
    rw [h1]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
    rw [norm_mul]
    calc ‖(1 + x) ^ n - 1‖ * ‖x‖ ≤ 1 * ‖x‖ :=
          mul_le_mul_of_nonneg_right (ih.trans hx.le) (norm_nonneg x)
      _ = ‖x‖ := one_mul _

variable (p : ℕ) [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K]

/-- One term of the tail: `‖term x (n+1) - term y (n+1)‖ ≤ ρ ‖x - y‖` when `‖x‖, ‖y‖ ≤ M ≤ ρ`
(the reused `LocalFieldLogContraction.norm_term_sub_le` has the constant `1/2` for `M ≤ 1/4`). -/
theorem norm_term_sub_le {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ} (hρe : ρ ^ e = ‖((p : ℕ) : K)‖)
    (x y : K) (n : ℕ) {M : ℝ} (hM0 : 0 ≤ M) (hMρ : M ≤ ρ) (hxM : ‖x‖ ≤ M) (hyM : ‖y‖ ≤ M) :
    ‖term x (n + 1) - term y (n + 1)‖ ≤ ρ * ‖x - y‖ := by
  have hrwx : term x (n + 1) = (-1 : K) ^ (n + 1) * (x ^ (n + 2) / ((n + 2 : ℕ) : K)) := rfl
  have hrwy : term y (n + 1) = (-1 : K) ^ (n + 1) * (y ^ (n + 2) / ((n + 2 : ℕ) : K)) := rfl
  have hcomb : term x (n + 1) - term y (n + 1)
      = (-1 : K) ^ (n + 1) * ((x ^ (n + 2) - y ^ (n + 2)) / ((n + 2 : ℕ) : K)) := by
    rw [hrwx, hrwy]
    ring
  rw [hcomb, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div]
  have hnum := norm_pow_sub_pow_le x y (n + 2) (by omega) M hM0 hxM hyM
  have hcore := pow_pred_le_mul_norm_natCast p hep hρe (n + 2) (by omega) hM0 hMρ
  rw [show n + 2 - 1 = n + 1 by omega] at hnum hcore
  have hden : 0 < ‖((n + 2 : ℕ) : K)‖ := by
    rw [norm_natCast_eq p (n + 2) (by omega)]
    exact pow_pos (norm_p_pos p) _
  rw [div_le_iff₀ hden]
  calc ‖x ^ (n + 2) - y ^ (n + 2)‖ ≤ ‖x - y‖ * M ^ (n + 1) := hnum
    _ ≤ ‖x - y‖ * (ρ * ‖((n + 2 : ℕ) : K)‖) := mul_le_mul_of_nonneg_left hcore (norm_nonneg _)
    _ = ρ * ‖x - y‖ * ‖((n + 2 : ℕ) : K)‖ := by ring

variable [CompleteSpace K]

/-- The tail `g x = log1p x - x` is a contraction with constant `ρ` on `B ρ`:
`‖g x - g y‖ ≤ ρ ‖x - y‖` (the reused `LocalFieldLogContraction.norm_tail_sub_le` is the same
statement with radius and constant `1/4`, `1/2`). -/
theorem norm_tail_sub_le {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ} (hρe : ρ ^ e = ‖((p : ℕ) : K)‖)
    {x y : K} (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    ‖(log1p x - x) - (log1p y - y)‖ ≤ ρ * ‖x - y‖ := by
  have hρ1 : ρ < 1 := rho_lt_one p hρe
  have hxlt : ‖x‖ < 1 := lt_of_le_of_lt hx hρ1
  have hylt : ‖y‖ < 1 := lt_of_le_of_lt hy hρ1
  have htx : log1p x - x = ∑' n : ℕ, term x (n + 1) := by
    rw [log_eq_head_add_tail p x hxlt]
    ring
  have hty : log1p y - y = ∑' n : ℕ, term y (n + 1) := by
    rw [log_eq_head_add_tail p y hylt]
    ring
  have hsx : Summable (fun n : ℕ => term x (n + 1)) :=
    (summable_signed p x hxlt).comp_injective (add_left_injective 1)
  have hsy : Summable (fun n : ℕ => term y (n + 1)) :=
    (summable_signed p y hylt).comp_injective (add_left_injective 1)
  rw [htx, hty, ← hsx.tsum_sub hsy]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  exact norm_term_sub_le p hep hρe x y n (le_trans (norm_nonneg x) (le_max_left _ _))
    (max_le hx hy) (le_max_left _ _) (le_max_right _ _)

/-- `‖log1p x - x‖ ≤ ρ ‖x‖` on `B ρ`: for `n ≥ 2`, `‖x^n/n‖ ≤ ρ ‖x‖ < ‖x‖`. -/
theorem norm_tail_le {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ} (hρe : ρ ^ e = ‖((p : ℕ) : K)‖)
    {x : K} (hx : ‖x‖ ≤ ρ) : ‖log1p x - x‖ ≤ ρ * ‖x‖ := by
  have h0 : ‖(0 : K)‖ ≤ ρ := by simpa using (norm_nonneg x).trans hx
  have h := norm_tail_sub_le p hep hρe hx h0
  simpa [log1p_zero p (K := K)] using h

/-! ## 5. Lemma 2.2(b): `log` preserves the norm on `B ρ` -/

/-- **Lemma 2.2(b), valuation preserving.**  Let `K` be a normed complete ultrametric extension of
`ℚ_p`, `e ≤ p - 2` and `ρ ^ e = ‖p‖` (`ρ = ‖π‖`).  Then `‖log (1 + x)‖ = ‖x‖` for every
`x ∈ B ρ = {x | ‖x‖ ≤ ρ}` (`= 𝔪`).  The reused `LocalFieldLogIsometry.norm_log1p_eq` is the same
statement on the ball of radius `1/4`. -/
theorem norm_log1p_eq {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ} (hρe : ρ ^ e = ‖((p : ℕ) : K)‖)
    {x : K} (hx : x ∈ B ρ) : ‖log1p x‖ = ‖x‖ := by
  rw [mem_B] at hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [log1p_zero p]
  · have hρ1 : ρ < 1 := rho_lt_one p hρe
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hstrict : ‖log1p x - x‖ < ‖x‖ :=
      (norm_tail_le p hep hρe hx).trans_lt (mul_lt_of_lt_one_left hxpos hρ1)
    have hsplit : log1p x = x + (log1p x - x) := by ring
    rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hstrict.ne']
    exact max_eq_left hstrict.le

/-! ## 6. Lemma 2.2(b): `log` is a bijection of `B ρ` onto itself -/

/-- `log1p` is injective on `B ρ` (directly from the contraction estimate, as in
`LocalFieldLogSurjective.log1p_injOn`). -/
theorem log1p_injOn {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ} (hρe : ρ ^ e = ‖((p : ℕ) : K)‖) :
    Set.InjOn (log1p : K → K) (B ρ) := by
  intro x hx y hy hlog
  rw [mem_B] at hx hy
  have hcon := norm_tail_sub_le p hep hρe hx hy
  have hrw : (log1p x - x) - (log1p y - y) = -(x - y) := by
    rw [hlog]
    ring
  rw [hrw, norm_neg] at hcon
  by_contra hne
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have := mul_lt_of_lt_one_left hpos (rho_lt_one p hρe)
  linarith

/-- The map `x ↦ y - (log1p x - x)` of the closed ball of radius `ρ` into itself; a fixed point
`x` satisfies `log1p x = y` (`LocalFieldLogSurjective.F` with radius `ρ` instead of `1/4`). -/
def banachMap {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ} (hρe : ρ ^ e = ‖((p : ℕ) : K)‖)
    (y : K) (hy : ‖y‖ ≤ ρ) (x : Metric.closedBall (0 : K) ρ) : Metric.closedBall (0 : K) ρ :=
  ⟨y - (log1p (x : K) - (x : K)), by
    have hx : ‖(x : K)‖ ≤ ρ := mem_closedBall_zero_iff.mp x.2
    have hρ1 : ρ < 1 := rho_lt_one p hρe
    have hg : ‖log1p (x : K) - (x : K)‖ ≤ ρ :=
      (norm_tail_le p hep hρe hx).trans
        (mul_le_of_le_one_right ((norm_nonneg _).trans hx) (hx.trans hρ1.le))
    rw [mem_closedBall_zero_iff, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy ?_)
    rwa [norm_neg]⟩

/-- `banachMap` is `ρ`-Lipschitz. -/
theorem lipschitz_banachMap {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ} (hρ : 0 < ρ)
    (hρe : ρ ^ e = ‖((p : ℕ) : K)‖) (y : K) (hy : ‖y‖ ≤ ρ) :
    LipschitzWith ⟨ρ, hρ.le⟩ (banachMap p hep hρe y hy) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have ha : ‖(a : K)‖ ≤ ρ := mem_closedBall_zero_iff.mp a.2
  have hb : ‖(b : K)‖ ≤ ρ := mem_closedBall_zero_iff.mp b.2
  have hcon := norm_tail_sub_le p hep hρe ha hb
  have hdist : dist (banachMap p hep hρe y hy a) (banachMap p hep hρe y hy b)
      = ‖(log1p (a : K) - (a : K)) - (log1p (b : K) - (b : K))‖ := by
    rw [Subtype.dist_eq, dist_eq_norm]
    simp only [banachMap]
    rw [show y - (log1p (a : K) - (a : K)) - (y - (log1p (b : K) - (b : K))) =
        -((log1p (a : K) - (a : K)) - (log1p (b : K) - (b : K))) by ring, norm_neg]
  rw [hdist, Subtype.dist_eq, dist_eq_norm]
  exact hcon

/-- `banachMap` is a contraction, since `ρ < 1`. -/
theorem contracting_banachMap {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ} (hρ : 0 < ρ)
    (hρe : ρ ^ e = ‖((p : ℕ) : K)‖) (y : K) (hy : ‖y‖ ≤ ρ) :
    ContractingWith ⟨ρ, hρ.le⟩ (banachMap p hep hρe y hy) := by
  refine ⟨?_, lipschitz_banachMap p hep hρ hρe y hy⟩
  have hρ1 : ρ < 1 := rho_lt_one p hρe
  exact NNReal.coe_lt_coe.mp (by rw [NNReal.coe_one]; exact hρ1)

/-- `log1p` maps `B ρ` onto `B ρ` (Banach fixed point theorem for `banachMap`). -/
theorem log1p_surjOn {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ} (hρ : 0 < ρ)
    (hρe : ρ ^ e = ‖((p : ℕ) : K)‖) {y : K} (hy : ‖y‖ ≤ ρ) :
    ∃ x : K, ‖x‖ ≤ ρ ∧ log1p x = y := by
  haveI : Nonempty (Metric.closedBall (0 : K) ρ) := ⟨⟨0, by simpa using hρ.le⟩⟩
  haveI : CompleteSpace (Metric.closedBall (0 : K) ρ) :=
    (Metric.isClosed_closedBall (x := (0 : K)) (ε := ρ)).completeSpace_coe
  have hc := contracting_banachMap p hep hρ hρe y hy
  let xs : Metric.closedBall (0 : K) ρ := hc.fixedPoint (banachMap p hep hρe y hy)
  have hfix : banachMap p hep hρe y hy xs = xs := hc.fixedPoint_isFixedPt
  refine ⟨(xs : K), mem_closedBall_zero_iff.mp xs.2, ?_⟩
  have hval : y - (log1p (xs : K) - (xs : K)) = (xs : K) := congrArg Subtype.val hfix
  linear_combination -hval

/-- **Lemma 2.2(b), bijectivity.**  Let `K` be a normed complete ultrametric extension of `ℚ_p`,
`e ≤ p - 2`, `0 < ρ` and `ρ ^ e = ‖p‖` (`ρ = ‖π‖`).  Then `log1p` maps the closed ball
`B ρ = {x | ‖x‖ ≤ ρ}` (`= 𝔪`) bijectively onto itself.  The reused
`LocalFieldLogSurjective.log1p_bijOn` is the same statement on the ball of radius `1/4`. -/
theorem log1p_bijOn {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ} (hρ : 0 < ρ)
    (hρe : ρ ^ e = ‖((p : ℕ) : K)‖) :
    Set.BijOn (log1p : K → K) (B ρ) (B ρ) := by
  refine ⟨fun x hx => ?_, log1p_injOn p hep hρe, fun y hy => ?_⟩
  · rw [mem_B, norm_log1p_eq p hep hρe hx]
    exact hx
  · obtain ⟨x, hx, hxy⟩ := log1p_surjOn p hep hρ hρe hy
    exact ⟨x, hx, hxy⟩

/-! ## 7. Lemma 2.2(b): `log` is a homomorphism on `U¹ = 1 + B ρ` -/

/-- **Lemma 2.2(b), homomorphism.**  For `x, y ∈ B ρ` (where `ρ ^ e = ‖p‖`),
`log ((1 + x)(1 + y)) = log (1 + x) + log (1 + y)`.  This is the reused
`LocalFieldLogAdd.log1p_add` (valid for `‖x‖, ‖y‖ < 1`), since `ρ < 1`.  With `log1p_bijOn` it
says that `1 + x ↦ log1p x` is a group isomorphism from `U¹ = 1 + B ρ` onto `B ρ`. -/
theorem log_hom_on_ball {e : ℕ} {ρ : ℝ} (hρe : ρ ^ e = ‖((p : ℕ) : K)‖)
    {x y : K} (hx : x ∈ B ρ) (hy : y ∈ B ρ) :
    log1p ((1 + x) * (1 + y) - 1) = log1p x + log1p y := by
  have hρ1 : ρ < 1 := rho_lt_one p hρe
  rw [show (1 + x) * (1 + y) - 1 = x + y + x * y by ring]
  exact LogShellEdge.Logshell.LocalFieldLogAdd.log1p_add p x y (lt_of_le_of_lt hx hρ1)
    (lt_of_le_of_lt hy hρ1)

include p in
/-- `log1p ((1 + x) ^ n - 1) = n · log1p x` for `‖x‖ < 1` (iterating `LocalFieldLogAdd.log1p_add`). -/
theorem log1p_one_add_pow_sub_one {x : K} (hx : ‖x‖ < 1) (n : ℕ) :
    log1p ((1 + x) ^ n - 1) = (n : K) * log1p x := by
  induction n with
  | zero => simp [log1p_zero p (K := K)]
  | succ n ih =>
    have ha : ‖(1 + x) ^ n - 1‖ < 1 := (norm_one_add_pow_sub_one_le hx n).trans_lt hx
    have h1 : (1 + x) ^ (n + 1) - 1 = ((1 + x) ^ n - 1) + x + ((1 + x) ^ n - 1) * x := by ring
    rw [h1, LogShellEdge.Logshell.LocalFieldLogAdd.log1p_add p _ _ ha hx, ih]
    push_cast
    ring

/-! ## 8. Lemma 2.2(a): no nontrivial roots of unity in `U¹ = 1 + B ρ` -/

/-- **Lemma 2.2(a), "in particular `U¹` is torsion-free".**  Let `K` be a normed complete
ultrametric extension of `ℚ_p`, `e ≤ p - 2` and `ρ ^ e = ‖p‖`.  If `ζ ^ n = 1` for some `n ≥ 1`
and `‖ζ - 1‖ ≤ ρ`, then `ζ = 1`.  Proof: `n · log1p (ζ - 1) = log1p (ζ ^ n - 1) = 0`, so
`log1p (ζ - 1) = 0`, so `ζ - 1 = 0` by `norm_log1p_eq`. -/
theorem eq_one_of_pow_eq_one {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ} (hρe : ρ ^ e = ‖((p : ℕ) : K)‖)
    {ζ : K} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) (hζρ : ‖ζ - 1‖ ≤ ρ) : ζ = 1 := by
  have hρ1 : ρ < 1 := rho_lt_one p hρe
  have hx1 : ‖ζ - 1‖ < 1 := hζρ.trans_lt hρ1
  have hlog := log1p_one_add_pow_sub_one p hx1 n
  have hzero : (1 + (ζ - 1)) ^ n - 1 = 0 := by
    rw [show 1 + (ζ - 1) = ζ by ring, hζ, sub_self]
  rw [hzero, log1p_zero p] at hlog
  have hn0 : (n : K) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_natCast_eq p n hn]
    exact (pow_pos (norm_p_pos p) _).ne'
  have hl0 : log1p (ζ - 1) = 0 := by
    rcases mul_eq_zero.mp hlog.symm with h | h
    · exact absurd h hn0
    · exact h
  have hnorm := norm_log1p_eq p hep hρe (x := ζ - 1) hζρ
  rw [hl0, norm_zero] at hnorm
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm.symm)

/-- **Lemma 2.2(a) inside `U¹`.**  Let `K` be a normed complete ultrametric extension of `ℚ_p`,
`e ≤ p - 2` and `ρ ^ e = ‖p‖`.  If `ζ ^ p = 1` and `‖ζ - 1‖ ≤ ρ`, then `ζ = 1`: the group
`U¹ = 1 + B ρ` contains no nontrivial `p`-th root of unity.

The note's `μ_p ⊄ K` is `mu_p_not_subset` below: there `‖ζ - 1‖ ≤ ρ` is derived from
`ζ ^ p = 1` and the explicit discreteness hypothesis `hdisc`.  Without some such hypothesis the
assumption `‖ζ - 1‖ ≤ ρ` cannot be dropped: in `ℂ_p` a primitive `p`-th root of unity has
`‖ζ - 1‖ = p ^ (-1/(p-1)) > ρ`. -/
theorem no_nontrivial_pth_root {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ}
    (hρe : ρ ^ e = ‖((p : ℕ) : K)‖) {ζ : K} (hζ : ζ ^ p = 1) (hζρ : ‖ζ - 1‖ ≤ ρ) : ζ = 1 :=
  eq_one_of_pow_eq_one p hep hρe hp.out.ne_zero hζ hζρ

end Ultra

/-! ## 9. Lemma 2.2(a), `μ_p ⊄ K`, under an explicit discreteness hypothesis

The note argues through the residue field.  Here the input is instead an inequality valid in every
normed ultrametric extension of `ℚ_p` (`norm_sub_one_lt_one_of_pow_eq_one`: `ζ ^ p = 1` implies
`‖ζ - 1‖ < 1`), together with the explicit hypothesis
`hdisc : ∀ x, ‖x‖ < 1 → ‖x‖ ≤ ρ`, which says that the open unit ball is `B ρ`; this is what
`B ρ = 𝔪` means when `K` is discretely valued with `‖π‖ = ρ`. -/

/-- The binomial expansion used below: for `n = k + 2`,
`(x + 1) ^ n - 1 - x ^ n = Σ_{0 < m < n} C(n, m) x ^ m` (written with `m + 1` for `m < k + 1`). -/
theorem add_one_pow_sub_one_sub_pow {R : Type*} [CommRing R] (x : R) (k : ℕ) :
    (x + 1) ^ (k + 2) - 1 - x ^ (k + 2) =
      ∑ m ∈ Finset.range (k + 1), x ^ (m + 1) * (((k + 2).choose (m + 1) : ℕ) : R) := by
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one]
  ring

section Discrete

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- In an ultrametric normed field, an integer divisible by `q` has norm at most `‖q‖`
(integers have norm `≤ 1`). -/
theorem norm_natCast_le_of_dvd {q n : ℕ} (h : q ∣ n) : ‖((n : ℕ) : K)‖ ≤ ‖((q : ℕ) : K)‖ := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, norm_mul]
  calc ‖((q : ℕ) : K)‖ * ‖((c : ℕ) : K)‖ ≤ ‖((q : ℕ) : K)‖ * 1 :=
        mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_natCast_le_one K c) (norm_nonneg _)
    _ = ‖((q : ℕ) : K)‖ := mul_one _

variable (p : ℕ) [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K]

/-- **`ζ ^ p = 1` implies `‖ζ - 1‖ < 1`**, in any normed ultrametric extension `K` of `ℚ_p`
(completeness is not used, and there is no hypothesis on `e` or `ρ`).  Proof: `‖ζ‖ = 1`, so
`x = ζ - 1` has `‖x‖ ≤ 1`; in `0 = (x + 1) ^ p - 1 = x ^ p + Σ_{0 < m < p} C(p, m) x ^ m` every middle
term has norm `≤ ‖p‖` because `p ∣ C(p, m)`; hence `‖x‖ ^ p ≤ ‖p‖ < 1`. -/
theorem norm_sub_one_lt_one_of_pow_eq_one {ζ : K} (hζ : ζ ^ p = 1) : ‖ζ - 1‖ < 1 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hζ1 : ‖ζ‖ = 1 := by
    have h : ‖ζ‖ ^ p = 1 := by rw [← norm_pow, hζ, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hp.out.ne_zero).mp h
  have hx1 : ‖ζ - 1‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max ζ (-1)
    rw [norm_neg, norm_one, hζ1, max_self, ← sub_eq_add_neg] at h
    exact h
  obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
  have hexp : (ζ - 1 + 1) ^ p - 1 - (ζ - 1) ^ p =
      ∑ m ∈ Finset.range (k + 1), (ζ - 1) ^ (m + 1) * ((p.choose (m + 1) : ℕ) : K) := by
    rw [hk]
    exact add_one_pow_sub_one_sub_pow (ζ - 1) k
  have hlhs : (ζ - 1 + 1) ^ p - 1 - (ζ - 1) ^ p = -((ζ - 1) ^ p) := by
    rw [sub_add_cancel, hζ]
    ring
  have hsum : ‖∑ m ∈ Finset.range (k + 1), (ζ - 1) ^ (m + 1) * ((p.choose (m + 1) : ℕ) : K)‖
      ≤ ‖((p : ℕ) : K)‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro m hm
    have hm' : m < k + 1 := Finset.mem_range.mp hm
    have hdvd : p ∣ p.choose (m + 1) := hp.out.dvd_choose_self (by omega) (by omega)
    rw [norm_mul, norm_pow]
    calc ‖ζ - 1‖ ^ (m + 1) * ‖((p.choose (m + 1) : ℕ) : K)‖ ≤ 1 * ‖((p : ℕ) : K)‖ :=
          mul_le_mul (pow_le_one₀ (norm_nonneg _) hx1) (norm_natCast_le_of_dvd hdvd)
            (norm_nonneg _) zero_le_one
      _ = ‖((p : ℕ) : K)‖ := one_mul _
  have hpow : ‖ζ - 1‖ ^ p ≤ ‖((p : ℕ) : K)‖ := by
    have h : ‖-((ζ - 1) ^ p)‖ ≤ ‖((p : ℕ) : K)‖ := by
      rw [← hlhs, hexp]
      exact hsum
    rwa [norm_neg, norm_pow] at h
  by_contra h
  have h1 : 1 ≤ ‖ζ - 1‖ ^ p := one_le_pow₀ (not_lt.mp h)
  have h2 := norm_p_lt_one p (K := K)
  linarith

variable [CompleteSpace K]

/-- **Lemma 2.2(a), `μ_p ⊄ K`.**  Let `K` be a normed complete ultrametric extension of `ℚ_p`,
`e ≤ p - 2` and `ρ ^ e = ‖p‖`, and assume the discreteness hypothesis
`hdisc : ∀ x, ‖x‖ < 1 → ‖x‖ ≤ ρ` (the open unit ball is `B ρ`; this holds when `K` is discretely
valued with `‖π‖ = ρ`, e.g. a finite extension of `ℚ_p` with ramification index `e`).  Then every
`ζ ∈ K` with `ζ ^ p = 1` equals `1`.  Proof: `‖ζ - 1‖ < 1` (`norm_sub_one_lt_one_of_pow_eq_one`),
so `‖ζ - 1‖ ≤ ρ` by `hdisc`, and `no_nontrivial_pth_root` applies.  No residue field is used. -/
theorem mu_p_not_subset {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ} (hρe : ρ ^ e = ‖((p : ℕ) : K)‖)
    (hdisc : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ρ) {ζ : K} (hζ : ζ ^ p = 1) : ζ = 1 :=
  no_nontrivial_pth_root p hep hρe hζ (hdisc _ (norm_sub_one_lt_one_of_pow_eq_one p hζ))

/-- Under the same hypotheses as `mu_p_not_subset` (`e ≤ p - 2`, `ρ ^ e = ‖p‖`, `hdisc`), `K` has
no nontrivial `p`-power root of unity: `ζ ^ (p ^ k) = 1` implies `ζ = 1` (induction on `k`). -/
theorem eq_one_of_pow_prime_pow_eq_one {e : ℕ} (hep : e ≤ p - 2) {ρ : ℝ}
    (hρe : ρ ^ e = ‖((p : ℕ) : K)‖) (hdisc : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ρ) {ζ : K} (k : ℕ)
    (hζ : ζ ^ (p ^ k) = 1) : ζ = 1 := by
  induction k with
  | zero => simpa using hζ
  | succ k ih =>
    apply ih
    apply mu_p_not_subset p hep hρe hdisc
    rw [← pow_mul, ← pow_succ]
    exact hζ

end Discrete

/-! ## 10. The discreteness hypothesis is not vacuous: `K = ℚ_p` -/

section PadicExample

variable (p : ℕ) [hp : Fact p.Prime]

/-- In `ℚ_p` the discreteness hypothesis `hdisc` holds with `ρ = ‖p‖`: `‖x‖ < 1` implies
`‖x‖ ≤ ‖p‖` (the norm takes values in `p ^ ℤ ∪ {0}`). -/
theorem padic_hdisc : ∀ x : ℚ_[p], ‖x‖ < 1 → ‖x‖ ≤ ‖((p : ℕ) : ℚ_[p])‖ := by
  intro x hx
  rw [Padic.norm_p, ← zpow_neg_one, Padic.norm_le_pow_iff_norm_lt_pow_add_one]
  simpa using hx

/-- Non-vacuity of `mu_p_not_subset`: for `p ≥ 3`, `K = ℚ_p` with `e = 1` and `ρ = ‖p‖` satisfies
all of its hypotheses (`1 ≤ p - 2`, `‖p‖ ^ 1 = ‖p‖`, `padic_hdisc`); so `ℚ_p` has no nontrivial
`p`-th root of unity. -/
theorem padic_mu_p_trivial (hp3 : 3 ≤ p) {ζ : ℚ_[p]} (hζ : ζ ^ p = 1) : ζ = 1 :=
  mu_p_not_subset p (K := ℚ_[p]) (e := 1) (by omega) (pow_one _) (padic_hdisc p) hζ

end PadicExample

end LogShellEdge.SmallLog

/-! ## Axioms -/
