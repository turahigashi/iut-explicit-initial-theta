import Cor312LogVolume.logshell.PadicLogSummable
import Cor312LogVolume.logshell.HullIsSpan
import Cor312LogVolume.logshell.PadicLogAdd
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Module.Basic

namespace CitedLV.PadicLogDef

open CitedLV.PadicLogSummable

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

noncomputable def logShell (S : Set ℚ_[p]) : Submodule ℤ_[p] ℚ_[p] :=
  CitedLV.Hull.hull (R := ℤ_[p]) (padicLog1p p '' S)

theorem logShell_units_stable (S : Set ℚ_[p]) (u : ℤ_[p]ˣ) {y : ℚ_[p]}
    (hy : y ∈ logShell p S) :
    (u : ℤ_[p]) • y ∈ logShell p S :=
  CitedLV.Hull.hull_units_stable (R := ℤ_[p]) _ u hy

theorem logShell_units_stable_iff (S : Set ℚ_[p]) (u : ℤ_[p]ˣ) {y : ℚ_[p]} :
    (u : ℤ_[p]) • y ∈ logShell p S ↔ y ∈ logShell p S :=
  CitedLV.Hull.hull_units_stable_iff (R := ℤ_[p]) _ u

theorem logImage_subset_logShell (S : Set ℚ_[p]) :
    padicLog1p p '' S ⊆ (logShell p S : Set ℚ_[p]) :=
  CitedLV.Hull.subset_hull (R := ℤ_[p]) _

theorem logShell_mono {S T : Set ℚ_[p]} (h : S ⊆ T) :
    logShell p S ≤ logShell p T :=
  CitedLV.Hull.hull_mono (R := ℤ_[p]) (Set.image_mono h)

theorem padicLog1p_add (x y : ℚ_[p]) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    padicLog1p p (x + y + x * y) = padicLog1p p x + padicLog1p p y := by
  change CitedLV.PadicLogFubini.Padic.logSeries1p p (x + y + x * y) =
    CitedLV.PadicLogFubini.Padic.logSeries1p p x +
      CitedLV.PadicLogFubini.Padic.logSeries1p p y
  exact CitedLV.PadicLogAdd.Padic.logSeries1p_add p x y hx hy

theorem padicLog_is_hom_of_small (x y : ℚ_[p]) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    padicLog1p p (x + y + x * y) = padicLog1p p x + padicLog1p p y :=
  padicLog1p_add p x y hx hy

theorem grounded_logShell (S T : Set ℚ_[p]) (u : ℤ_[p]ˣ) (h : S ⊆ T) :
    (padicLog1p p 0 = 0) ∧
    (padicLog1p p '' S ⊆ (logShell p S : Set ℚ_[p])) ∧
    (∀ y : ℚ_[p], (u : ℤ_[p]) • y ∈ logShell p S ↔ y ∈ logShell p S) ∧
    (logShell p S ≤ logShell p T) :=
  ⟨padicLog1p_zero p,
   logImage_subset_logShell p S,
   fun y => logShell_units_stable_iff p S u,
   logShell_mono p h⟩

end CitedLV.PadicLogDef
