import LogShellEdge.Reuse.Logshell.PadicLogSummable
import LogShellEdge.Reuse.Logshell.PadicLogAdd
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The function `padicLog1p` on `ℚ_p`

`padicLog1p x = Σ (-1)^n x^(n+1)/(n+1)`, `padicLog1p 0 = 0`, and the addition formula
`padicLog1p_add`.

Adapted from an earlier, unpublished Lean development of the author: the comments were
rewritten, the namespace was renamed and a few unused summary statements were removed; the
remaining definitions and proofs are unchanged.
-/

namespace LogShellEdge.Logshell.PadicLogDef

open LogShellEdge.Logshell.PadicLogSummable

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable def padicLog1p (x : ℚ_[p]) : ℚ_[p] :=
  ∑' n : ℕ, (-1 : ℚ_[p]) ^ n * (x ^ (n + 1) / ((n + 1 : ℕ) : ℚ_[p]))

theorem summable_signed (x : ℚ_[p]) (hx : ‖x‖ < 1) :
    Summable (fun n : ℕ => (-1 : ℚ_[p]) ^ n * (x ^ (n + 1) / ((n + 1 : ℕ) : ℚ_[p]))) := by
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => ((n : ℝ) + 1) * ‖x‖ ^ (n + 1))
  · have := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (r := ‖x‖) (by simpa using hx))
    have hshift : Summable (fun n : ℕ => (((n+1 : ℕ)) : ℝ) ^ 1 * ‖x‖ ^ (n+1)) :=
      (summable_nat_add_iff 1).mpr this
    simpa [pow_one] using hshift
  · intro n
    have hne : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
    have hb := norm_term_le p x (n + 1) hne
    have hsign : ‖(-1 : ℚ_[p]) ^ n‖ = 1 := by
      rw [norm_pow, norm_neg, norm_one, one_pow]
    rw [norm_mul, hsign, one_mul]
    simpa using hb

theorem padicLog1p_zero : padicLog1p p 0 = 0 := by
  simp only [padicLog1p]
  convert tsum_zero with n
  simp

theorem padicLog1p_add (x y : ℚ_[p]) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    padicLog1p p (x + y + x * y) = padicLog1p p x + padicLog1p p y := by
  change LogShellEdge.Logshell.PadicLogFubini.Padic.logSeries1p p (x + y + x * y) =
    LogShellEdge.Logshell.PadicLogFubini.Padic.logSeries1p p x +
      LogShellEdge.Logshell.PadicLogFubini.Padic.logSeries1p p y
  exact LogShellEdge.Logshell.PadicLogAdd.Padic.logSeries1p_add p x y hx hy

end LogShellEdge.Logshell.PadicLogDef
