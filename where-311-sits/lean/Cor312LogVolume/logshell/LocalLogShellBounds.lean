import Cor312LogVolume.logshell.LocalLogShellCompactness
import Cor312LogVolume.Src.IUT4.Section1Proposition12iLogBounds

set_option autoImplicit false
noncomputable section
namespace CitedLV.LocalLogShellBounds

open Metric Set
open Src.IUT3.Remark122 Src.IUT3.Proposition39iv
open Src.IUT4.Proposition12i
open CitedLV.LocalLogShellCompactness

variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]
  [CompleteSpace K] [IsUltrametricDist K] [ProperSpace K]

theorem logUnitsSet_eq_principalImage :
    logUnitsSet p K = (logUnit : K → K) '' principalUnits := by
  ext x
  constructor
  · rintro ⟨u, _, ζ, _, hprin, hx⟩
    exact ⟨u * ζ⁻¹, hprin, hx.symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, principalUnit_norm hu, 1, primeToPRoot_one p, ?_, ?_⟩
    · simpa using hu
    · simp

theorem principalImage_bounds (R : RamificationData p K) :
    closedBall (0 : K) ((p : ℝ) ^ (-aExp p R.e)) ⊆
        (logUnit : K → K) '' principalUnits ∧
      (logUnit : K → K) '' principalUnits ⊆
        closedBall (0 : K) ((p : ℝ) ^ bExp p R.e) := by
  rw [← logUnitsSet_eq_principalImage p]
  exact inclusions p R

theorem norm_le_of_mem_logShell (R : RamificationData p K) {x : K}
    (hx : x ∈ logShell p) :
    ‖x‖ ≤ (p : ℝ) ^ bExp p R.e / ‖((pStar p : ℕ) : K)‖ := by
  obtain ⟨u, hu, heq⟩ := hx
  have hlog := (principalImage_bounds p R).2 ⟨u, hu, rfl⟩
  rw [mem_closedBall_zero_iff, ← heq, norm_mul] at hlog
  exact (le_div_iff₀ (norm_pos_iff.mpr (pStar_ne_zero (K := K) p))).mpr
    (by simpa only [mul_comm] using hlog)

theorem logShell_subset_closedBall (R : RamificationData p K) :
    logShell (K := K) p ⊆
      closedBall 0 ((p : ℝ) ^ bExp p R.e / ‖((pStar p : ℕ) : K)‖) := by
  intro x hx
  exact mem_closedBall_zero_iff.mpr (norm_le_of_mem_logShell p R hx)

theorem principalImage_eq_small (R : RamificationData p K)
    (hp2 : p ≠ 2) (hep : R.e + 2 ≤ p) :
    (logUnit : K → K) '' principalUnits =
      closedBall 0 ((p : ℝ) ^ (-(1 / (R.e : ℝ)))) := by
  rw [← logUnitsSet_eq_principalImage p]
  exact logUnitsSet_eq_of_small_ramification p R hp2 hep

end CitedLV.LocalLogShellBounds
