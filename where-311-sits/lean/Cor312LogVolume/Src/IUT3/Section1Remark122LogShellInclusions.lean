import Mathlib
import Cor312LogVolume.Src.IUT3.Section3Proposition39ivLogLinkVolume
import Cor312LogVolume.Src.Lib.PadicLog.LocalFieldLogThird

namespace Src.IUT3.Remark122

open Metric Set SrcLib.LocalFieldLogIsometry Src.IUT3.Proposition39iv

section Nonarch

variable (p : ℕ) [Fact p.Prime] {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [CompleteSpace K]
  [IsUltrametricDist K]

def pStar : ℕ := if p = 2 then 4 else p

def intO : Set K := closedBall (0 : K) 1

def principalUnits : Set K := {u | ‖u - 1‖ < 1}

def logShell : Set K := {x | ∃ u ∈ principalUnits, ((pStar p : ℕ) : K) * x = logUnit u}

variable {p}

include p

theorem norm_natCast_K (n : ℕ) : ‖(n : K)‖ = ‖(n : ℚ_[p])‖ := by
  have := norm_algebraMap' K (n : ℚ_[p])
  simpa using this

theorem norm_pStar_le : ‖((pStar p : ℕ) : K)‖ ≤ 1 / 3 := by
  rw [norm_natCast_K (p := p)]
  unfold pStar
  split_ifs with h2
  · subst h2
    have h : ((4 : ℕ) : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) ^ 2 := by push_cast; norm_num
    rw [h, norm_pow, Padic.norm_p]
    norm_num
  · rw [Padic.norm_p]
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
    rw [one_div]
    exact inv_anti₀ (by norm_num) hp3

theorem intO_subset_logShell : intO ⊆ logShell (K := K) p := by
  intro x hx
  rw [intO, mem_closedBall_zero_iff] at hx
  have hy : ‖((pStar p : ℕ) : K) * x‖ ≤ 1 / 3 := by
    rw [norm_mul]
    have := norm_pStar_le (p := p) (K := K)
    nlinarith [norm_nonneg ((pStar p : ℕ) : K), norm_nonneg x]
  obtain ⟨z, hz, hzy⟩ := SrcLib.LocalFieldLogThird.log1p_surjOn_third (p := p) _ hy
  refine ⟨1 + z, ?_, ?_⟩
  · show ‖1 + z - 1‖ < 1
    rw [add_sub_cancel_left]
    linarith
  · unfold logUnit
    rw [add_sub_cancel_left, hzy]

theorem principalUnits_mul {u v : K} (hu : u ∈ principalUnits) (hv : v ∈ principalUnits) :
    u * v ∈ principalUnits := by
  unfold principalUnits at *
  simp only [mem_setOf_eq] at *
  rw [show u * v - 1 = (u - 1) + (v - 1) + (u - 1) * (v - 1) by ring]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hu hv)
  · rw [norm_mul]
    nlinarith [norm_nonneg (u - 1), norm_nonneg (v - 1)]

theorem logUnit_mul {u v : K} (hu : u ∈ principalUnits) (hv : v ∈ principalUnits) :
    logUnit (u * v) = logUnit u + logUnit v := by
  unfold logUnit
  rw [show u * v - 1 = (u - 1) + (v - 1) + (u - 1) * (v - 1) by ring]
  exact SrcLib.LocalFieldLogAdd.log1p_add (p := p) _ _ hu hv

theorem one_mem_principalUnits : (1 : K) ∈ principalUnits := by
  show ‖(1 : K) - 1‖ < 1
  simp

theorem pow_mem_principalUnits {u : K} (hu : u ∈ principalUnits) (n : ℕ) : u ^ n ∈ principalUnits := by
  induction n with
  | zero => simpa using one_mem_principalUnits (p := p) (K := K)
  | succ n ih => rw [pow_succ]; exact principalUnits_mul (p := p) ih hu

theorem logUnit_pow {u : K} (hu : u ∈ principalUnits) (n : ℕ) : logUnit (u ^ n) = (n : K) * logUnit u := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    unfold logUnit
    rw [sub_self]
    exact log1p_zero (p := p)
  | succ n ih =>
    rw [pow_succ, logUnit_mul (p := p) (pow_mem_principalUnits (p := p) hu n) hu, ih]
    push_cast
    ring

theorem log_subset_logShell : logUnit '' principalUnits ⊆ logShell (K := K) p := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨u ^ pStar p, pow_mem_principalUnits (p := p) hu _, (logUnit_pow (p := p) hu _).symm⟩

end Nonarch

section Arch

open Complex Real

theorem arch_intO_subset : closedBall (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) π := by
  intro z hz
  rw [mem_closedBall_zero_iff] at hz ⊢
  linarith [Real.pi_gt_three]

theorem arch_units_subset_exp : sphere (0 : ℂ) 1 ⊆ Complex.exp '' closedBall (0 : ℂ) π := by
  intro w hw
  rw [mem_sphere_zero_iff_norm] at hw
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; exact zero_ne_one hw
  refine ⟨Complex.log w, ?_, Complex.exp_log hw0⟩
  rw [mem_closedBall_zero_iff]
  have hre : (Complex.log w).re = 0 := by
    rw [Complex.log_re, hw, Real.log_one]
  have him : |(Complex.log w).im| ≤ π := by
    rw [Complex.log_im, abs_le]
    exact ⟨le_of_lt (Complex.neg_pi_lt_arg w), Complex.arg_le_pi w⟩
  have : Complex.log w = ((Complex.log w).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact him

end Arch

theorem pStar_two : pStar 2 = 4 := rfl

theorem pStar_odd {p : ℕ} (hp : p ≠ 2) : pStar p = p := by
  simp [pStar, hp]

end Src.IUT3.Remark122

section Check
open Src.IUT3.Remark122
end Check
