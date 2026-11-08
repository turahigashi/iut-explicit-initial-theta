import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import LogShellEdge.Reuse.Logshell.PadicLogIsometry

/-!
# The logarithm series on a complete ultrametric normed `ℚ_p`-algebra

`log1p x = Σ (-1)^n x^(n+1)/(n+1)` (`term`, `summable_signed`, `log1p_zero`), the splitting of
`log1p x` into `x` and a tail (`log_eq_head_add_tail`), and `norm_log1p_eq` on the ball of radius
`1/4`.

Adapted from an earlier, unpublished Lean development of the author: the comments were
rewritten, the namespace was renamed and a few unused summary statements were removed; the
remaining definitions and proofs are unchanged.
-/

namespace LogShellEdge.Logshell.LocalFieldLogIsometry

open LogShellEdge.Logshell.PadicLogSummable

variable (p : ℕ) [hp : Fact p.Prime]
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]
  [CompleteSpace K] [IsUltrametricDist K]

include p hp

theorem norm_natCast_ge_extension (n : ℕ) (hn : n ≠ 0) :
    (1 : ℝ) / (n : ℝ) ≤ ‖((n : ℕ) : K)‖ := by
  calc
    (1 : ℝ) / (n : ℝ) ≤ ‖((n : ℕ) : ℚ_[p])‖ := norm_natCast_ge p n hn
    _ = ‖algebraMap ℚ_[p] K (((n : ℕ) : ℚ_[p]))‖ :=
      (norm_algebraMap' K (((n : ℕ) : ℚ_[p]))).symm
    _ = ‖((n : ℕ) : K)‖ := by simp

theorem norm_log_term_le_extension (x : K) (n : ℕ) (hn : n ≠ 0) :
    ‖x ^ n / (n : K)‖ ≤ (n : ℝ) * ‖x‖ ^ n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hnorm := norm_natCast_ge_extension (p := p) (K := K) n hn
  have hden : (0 : ℝ) < ‖(n : K)‖ := by
    have hone : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    linarith
  rw [norm_div, norm_pow, div_le_iff₀ hden]
  have hone : (1 : ℝ) ≤ (n : ℝ) * ‖(n : K)‖ := by
    have h := (div_le_iff₀ hnpos).mp hnorm
    linarith [h]
  calc
    ‖x‖ ^ n = ‖x‖ ^ n * 1 := by ring
    _ ≤ ‖x‖ ^ n * ((n : ℝ) * ‖(n : K)‖) :=
      mul_le_mul_of_nonneg_left hone (by positivity)
    _ = (n : ℝ) * ‖x‖ ^ n * ‖(n : K)‖ := by ring

noncomputable def term (x : K) (n : ℕ) : K :=
  (-1 : K) ^ n * (x ^ (n + 1) / ((n + 1 : ℕ) : K))

theorem summable_signed (x : K) (hx : ‖x‖ < 1) :
    Summable (term x) := by
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => ((n : ℝ) + 1) * ‖x‖ ^ (n + 1))
  · have hgeo := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (r := ‖x‖) (by simpa using hx))
    have hshift : Summable
        (fun n : ℕ => (((n + 1 : ℕ)) : ℝ) ^ 1 * ‖x‖ ^ (n + 1)) :=
      (summable_nat_add_iff 1).mpr hgeo
    simpa [pow_one] using hshift
  · intro n
    have hbound := norm_log_term_le_extension (p := p) (K := K)
      x (n + 1) (Nat.succ_ne_zero n)
    have hsign : ‖(-1 : K) ^ n‖ = 1 := by simp
    rw [term, norm_mul, hsign, one_mul]
    simpa using hbound

noncomputable def log1p (x : K) : K :=
  ∑' n : ℕ, term x n

theorem log1p_zero : log1p (0 : K) = 0 := by
  simp only [log1p]
  convert tsum_zero with n
  simp [term]

theorem norm_tail_term_le (x : K) (n : ℕ) :
    ‖term x (n + 1)‖ ≤ ((n : ℝ) + 2) * ‖x‖ ^ (n + 2) := by
  have hbound := norm_log_term_le_extension (p := p) (K := K)
    x (n + 2) (by omega)
  rw [term, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hcast : (((n + 2 : ℕ)) : ℝ) = (n : ℝ) + 2 := by
    push_cast
    ring
  rw [hcast] at hbound
  exact hbound

theorem norm_tail_le (x : K) (hx : ‖x‖ ≤ 1 / 4) :
    ‖∑' n : ℕ, term x (n + 1)‖ ≤ ‖x‖ / 2 := by
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  have hterm := norm_tail_term_le (p := p) x n
  have hcoeff := LogShellEdge.Logshell.PadicLogIsometry.coeff_bound (norm_nonneg x) hx n
  have hsplit : ‖x‖ ^ (n + 2) = ‖x‖ ^ (n + 1) * ‖x‖ := by ring
  have hchain : ((n : ℝ) + 2) * ‖x‖ ^ (n + 2) =
      (((n : ℝ) + 2) * ‖x‖ ^ (n + 1)) * ‖x‖ := by
    rw [hsplit]
    ring
  have hfin : (((n : ℝ) + 2) * ‖x‖ ^ (n + 1)) * ‖x‖ ≤
      (1 / 2) * ‖x‖ :=
    mul_le_mul_of_nonneg_right hcoeff (norm_nonneg x)
  rw [hchain] at hterm
  linarith

theorem log_eq_head_add_tail (x : K) (hx : ‖x‖ < 1) :
    log1p x = x + ∑' n : ℕ, term x (n + 1) := by
  have hsum := summable_signed (p := p) x hx
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have hzero : term x 0 = x := by simp [term]
  rw [log1p, ← hsplit, Finset.sum_range_one, hzero]

theorem norm_log1p_eq (x : K) (hx : ‖x‖ ≤ 1 / 4) :
    ‖log1p x‖ = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [log1p_zero (p := p) (K := K)]
  · have hlt : ‖x‖ < 1 := lt_of_le_of_lt hx (by norm_num)
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have htail := norm_tail_le (p := p) x hx
    have hstrict : ‖∑' n : ℕ, term x (n + 1)‖ < ‖x‖ := by
      linarith
    have hne : ‖x‖ ≠ ‖∑' n : ℕ, term x (n + 1)‖ :=
      ne_of_gt hstrict
    rw [log_eq_head_add_tail (p := p) x hlt,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne]
    exact max_eq_left hstrict.le

theorem log1p_eq_zero_iff (x : K) (hx : ‖x‖ ≤ 1 / 4) :
    log1p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have : ‖x‖ = 0 := by
      rw [← norm_log1p_eq (p := p) x hx, h, norm_zero]
    exact norm_eq_zero.mp this
  · rintro rfl
    exact log1p_zero (p := p)

theorem one_not_mem_small_ball : ¬ (‖(1 : K)‖ ≤ 1 / 4) := by
  norm_num

theorem small_ball_has_nonzero :
    ∃ x : K, x ≠ 0 ∧ ‖x‖ ≤ 1 / 4 := by
  let q : ℚ_[p] := ((p : ℕ) : ℚ_[p]) ^ 2
  refine ⟨algebraMap ℚ_[p] K q, ?_, ?_⟩
  · have hq : q ≠ 0 := by
      dsimp [q]
      exact pow_ne_zero 2 (by exact_mod_cast hp.out.ne_zero)
    simpa using (map_ne_zero (f := algebraMap ℚ_[p] K)).mpr hq
  · rw [norm_algebraMap' K q]
    dsimp [q]
    rw [norm_pow, Padic.norm_p]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
      rw [inv_le_inv₀ hppos (by norm_num : (0:ℝ) < 2)]
      exact hp2
    have hinvpos : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
    nlinarith [hinv, hinvpos]

end LogShellEdge.Logshell.LocalFieldLogIsometry
