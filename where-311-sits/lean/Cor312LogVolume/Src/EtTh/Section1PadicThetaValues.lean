import Cor312LogVolume.Src.EtTh.Section1ThetaValueAnalyticFacts
import Mathlib.NumberTheory.Padics.Complex

noncomputable section

namespace Src.EtTh.PadicThetaValues

open Src.EtTh.ThetaValueArithmetic

variable (p : ℕ) [Fact (Nat.Prime p)]

private theorem exists_unit_root (q : ℂ_[p]ˣ) (n : ℕ) (hn : 0 < n) :
    ∃ x : ℂ_[p]ˣ, x ^ n = q := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (q : ℂ_[p]) hn
  have hne : x ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (Nat.ne_of_gt hn)] at hx
    exact (Units.ne_zero q) hx.symm
  refine ⟨Units.mk0 x hne, ?_⟩
  apply Units.ext
  simpa using hx

def unitRoot (q : ℂ_[p]ˣ) (n : ℕ) (hn : 0 < n) : ℂ_[p]ˣ :=
  Classical.choose (exists_unit_root p q n hn)

theorem unitRoot_pow (q : ℂ_[p]ˣ) (n : ℕ) (hn : 0 < n) :
    unitRoot p q n hn ^ n = q :=
  Classical.choose_spec (exists_unit_root p q n hn)

def imaginaryUnit : ℂ_[p]ˣ := unitRoot p (-1) 2 (by norm_num)

theorem imaginaryUnit_sq : imaginaryUnit p ^ 2 = -1 :=
  unitRoot_pow p (-1) 2 (by norm_num)

def thetaParameter (q : ℂ_[p]ˣ) : ℂ_[p]ˣ := unitRoot p q 2 (by norm_num)

theorem thetaParameter_sq (q : ℂ_[p]ˣ) : thetaParameter p q ^ 2 = q :=
  unitRoot_pow p q 2 (by norm_num)

theorem thetaParameter_small (q : ℂ_[p]ˣ) (hq : ‖(q : ℂ_[p])‖ < 1) :
    ‖(thetaParameter p q : ℂ_[p])‖ < 1 := by
  have heq : ‖(thetaParameter p q : ℂ_[p])‖ ^ 2 = ‖(q : ℂ_[p])‖ := by
    rw [← norm_pow]
    exact congrArg (fun x : ℂ_[p]ˣ => ‖(x : ℂ_[p])‖) (thetaParameter_sq p q)
  by_contra h
  have hge : 1 ≤ ‖(thetaParameter p q : ℂ_[p])‖ := le_of_not_gt h
  have := one_le_pow₀ hge (n := 2)
  linarith

def analyticFacts (q : ℂ_[p]ˣ) (hq : ‖(q : ℂ_[p])‖ < 1) :
    PublishedThetaFacts (thetaParameter p q) (imaginaryUnit p) :=
  publishedThetaFactsOfCompleteUltrametric (thetaParameter p q) (imaginaryUnit p)
    (imaginaryUnit_sq p) (thetaParameter_small p q hq)

def rootValues (q : ℂ_[p]ˣ) (ell j : ℕ) : Set ℂ_[p]ˣ :=
  normalizedRootValues (thetaParameter p q) (imaginaryUnit p) ell j

theorem mem_rootValues_iff_power (q : ℂ_[p]ˣ) (hq : ‖(q : ℂ_[p])‖ < 1)
    (ell j : ℕ) (t : ℂ_[p]ˣ) :
    t ∈ rootValues p q ell j ↔ t ^ (2 * ell) = q ^ (j * j) := by
  simpa [rootValues, thetaParameter_sq] using
    mem_normalizedRootValues_iff_power (thetaParameter p q) (imaginaryUnit p)
      (imaginaryUnit_sq p) (analyticFacts p q hq) ell j t

theorem rootValues_nonempty (q : ℂ_[p]ˣ) (hq : ‖(q : ℂ_[p])‖ < 1)
    (ell j : ℕ) (hell : 0 < ell) : (rootValues p q ell j).Nonempty := by
  let r := unitRoot p q (2 * ell) (by omega)
  refine ⟨r ^ (j * j), (mem_rootValues_iff_power p q hq ell j _).mpr ?_⟩
  rw [← pow_mul, Nat.mul_comm (j * j) (2 * ell), pow_mul]
  rw [show r ^ (2 * ell) = q from unitRoot_pow p q (2 * ell) (by omega)]

end Src.EtTh.PadicThetaValues
