import LogShellEdge.Reuse.Logshell.LocalFieldLogFubini
import LogShellEdge.Reuse.Logshell.PadicLogAdd
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.CharP.Algebra

/-!
# The addition formula of the logarithm over a complete ultrametric normed `ℚ_p`-algebra

`log1p_add`: `log1p (x + y + x y) = log1p x + log1p y` for `‖x‖, ‖y‖ < 1`.

Adapted from an earlier, unpublished Lean development of the author: the comments were
rewritten, the namespace was renamed and a few unused summary statements were removed; the
remaining definitions and proofs are unchanged.
-/

namespace LogShellEdge.Logshell.LocalFieldLogAdd

open scoped PowerSeries
open PowerSeries
open LogShellEdge.Logshell.PadicLogFubini
open LogShellEdge.Logshell.LocalFieldLogFubini LogShellEdge.Logshell.LocalFieldLogIsometry

variable (p : ℕ) [hp : Fact p.Prime]
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]
  [CompleteSpace K] [IsUltrametricDist K]

include p hp

theorem logSeries1p_add (x y : K) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    logSeries1p (x + y + x * y) = logSeries1p x + logSeries1p y := by
  letI : CharZero K :=
    charZero_of_injective_ringHom (algebraMap ℚ_[p] K).injective
  let u : K⟦X⟧ := pathSeries x 0
  let v : K⟦X⟧ := pathSeries y 0
  have hu0 : constantCoeff u = 0 := by simp [u, pathSeries]
  have hv0 : constantCoeff v = 0 := by simp [v, pathSeries]
  have hformal := LogShellEdge.Logshell.PadicLogAdd.Formal.log_subst_mul (A := K) hu0 hv0
  have hpath : u + v + u * v = pathSeries (x + y) (x * y) := by
    simp [u, v, pathSeries]
    ring
  rw [hpath] at hformal
  have hsum : ‖x + y‖ < 1 :=
    (IsUltrametricDist.norm_add_le_max x y).trans_lt ((max_lt_iff).2 ⟨hx, hy⟩)
  have hprod : ‖x * y‖ < 1 := by
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg x) hx hy.le
  have hxy : max ‖x + y‖ ‖x * y‖ < 1 := (max_lt_iff).2 ⟨hsum, hprod⟩
  have hx0 : max ‖x‖ ‖(0 : K)‖ < 1 := by simpa using hx
  have hy0 : max ‖y‖ ‖(0 : K)‖ < 1 := by simpa using hy
  have hsx := summable_coeff_log_subst_path (p := p) x 0 hx0
  have hsy := summable_coeff_log_subst_path (p := p) y 0 hy0
  have hcoeff (m : ℕ) :
      coeff m ((PowerSeries.log K).subst (pathSeries (x + y) (x * y))) =
        coeff m ((PowerSeries.log K).subst (pathSeries x 0)) +
          coeff m ((PowerSeries.log K).subst (pathSeries y 0)) := by
    simpa [u, v] using congrArg (coeff m) hformal
  calc
    logSeries1p (x + y + x * y) =
        ∑' m : ℕ, coeff m
          ((PowerSeries.log K).subst (pathSeries (x + y) (x * y))) :=
      (tsum_coeff_log_subst_path_eq_logSeries1p (p := p) (x + y) (x * y) hxy).symm
    _ = ∑' m : ℕ,
        (coeff m ((PowerSeries.log K).subst (pathSeries x 0)) +
          coeff m ((PowerSeries.log K).subst (pathSeries y 0))) := by
      apply tsum_congr
      exact hcoeff
    _ = (∑' m : ℕ, coeff m ((PowerSeries.log K).subst (pathSeries x 0))) +
        ∑' m : ℕ, coeff m ((PowerSeries.log K).subst (pathSeries y 0)) :=
      hsx.tsum_add hsy
    _ = logSeries1p x + logSeries1p y := by
      rw [tsum_coeff_log_subst_path_eq_logSeries1p (p := p) x 0 hx0,
        tsum_coeff_log_subst_path_eq_logSeries1p (p := p) y 0 hy0]
      simp

theorem log1p_add (x y : K) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    log1p (x + y + x * y) = log1p x + log1p y := by
  change logSeries1p (x + y + x * y) = logSeries1p x + logSeries1p y
  exact logSeries1p_add (p := p) x y hx hy

end LogShellEdge.Logshell.LocalFieldLogAdd
