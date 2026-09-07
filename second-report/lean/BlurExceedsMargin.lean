/-!
# The deficit between the combined blur and the stage margin is a constant

Arithmetic over the integers only; nothing about inter-universal Teichmüller theory
is asserted here.  What the two quantities mean, and why one would compare them, is
stated in the accompanying note and is marked there as a *reading*, not a theorem.

Fix a prime `l >= 5`, put `ls = (l-1)/2`, and write the depth as `s = N / l` for a
positive integer `N`.  Both quantities are scaled by `l` to stay in the integers:

* `margin l N j = j^2 N - l (j+2)`   -- `l` times the stage-`j` margin `j^2 s - (j+2)`
* `blur ls N    = ls^2 N`            -- `l` times `ls^2 s`, the diameter of
                                        `{0} u {j^2 s : 1 <= j <= ls}`

The datum's entry condition is `N > 3l`, i.e. `s > 3`, which makes `margin l N 1`
positive.

The content is: the blur dominates every stage margin, and at the top stage the
excess is exactly `l (ls + 2)` -- a constant independent of the depth `N`.  A deeper
datum therefore does not escape.
-/

namespace BlurMargin

/-- `l` times the stage-`j` margin. -/
def margin (l N j : Nat) : Int := (j * j * N : Nat) - (l * (j + 2) : Nat)
/-- `l` times the combined blur. -/
def blur (ls N : Nat) : Int := (ls * ls * N : Nat)

/-- **At the top stage the excess is exactly `l (ls + 2)`.** -/
theorem excess_at_top (l ls N : Nat) :
    blur ls N - margin l N ls = (l * (ls + 2) : Nat) := by
  simp only [blur, margin]
  generalize ((ls * ls * N : Nat) : Int) = A
  generalize ((l * (ls + 2) : Nat) : Int) = B
  omega

/-- **The excess does not depend on the depth.**  Two data of different depth give
the same value, so making the datum deeper changes both quantities by the same
amount. -/
theorem excess_independent_of_depth (l ls N M : Nat) :
    blur ls N - margin l N ls = blur ls M - margin l M ls := by
  rw [excess_at_top l ls N, excess_at_top l ls M]

/-- **The blur dominates every stage.**  Stated without subtraction, in `Nat`. -/
theorem blur_dominates (ls N j l : Nat) (hj : j ≤ ls) :
    j * j * N ≤ ls * ls * N + l * (j + 2) :=
  Nat.le_trans (Nat.mul_le_mul_right N (Nat.mul_le_mul hj hj)) (Nat.le_add_right _ _)

/-! ## The first report's datum: `l = 7`, `N = 29`, so `s = 29/7` and `ls = 3` -/

theorem datum_margins :
    margin 7 29 1 = 8 ∧ margin 7 29 2 = 88 ∧ margin 7 29 3 = 226 := by
  refine ⟨by decide, by decide, by decide⟩

theorem datum_blur : blur 3 29 = 261 := by decide

/-- The excess for the datum is `35 = 7 * 5`, i.e. `5` before the scaling by `l`. -/
theorem datum_excess : blur 3 29 - margin 7 29 3 = 35 := by decide

/-- A much deeper datum, `N = 1000`, has a far larger blur and a far larger margin,
and **exactly the same excess**. -/
theorem deeper_datum : blur 3 1000 = 9000 ∧ margin 7 1000 3 = 8965
    ∧ blur 3 1000 - margin 7 1000 3 = 35 := by
  refine ⟨by decide, by decide, by decide⟩

/-- And one just above the entry threshold, `N = 22` (`3l = 21`). -/
theorem shallow_datum : margin 7 22 1 = 1 ∧ blur 3 22 - margin 7 22 3 = 35 := by
  refine ⟨by decide, by decide⟩

end BlurMargin
