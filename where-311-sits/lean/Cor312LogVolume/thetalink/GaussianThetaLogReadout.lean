import Cor312LogVolume.thetalink.GaussianMonoidFromThetaValues
import Cor312LogVolume.theorem311.ProcessionNormalizedLogVolume
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false

namespace CitedLV.ThetaLink.GaussianThetaLogReadout

open CitedLV.ThetaLink.GaussianMonoidFromThetaValues
open Src.EtTh.ThetaValueArithmetic
open scoped BigOperators

variable {K : Type*} [NormedField K]

theorem actualProfile_norm_pos (ell : ℕ) (ξ : Labels ell → Kˣ) (j : Labels ell) :
    0 < ‖(ξ j : K)‖ := norm_pos_iff.mpr (Units.ne_zero _)

theorem actualProfile_log_norm (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell : ℕ) (hell : 0 < ell)
    (ξ : Labels ell → Kˣ) (hξ : ξ ∈ actualProfiles s i ell)
    (j : Labels ell) :
    Real.log ‖(ξ j : K)‖ =
      (((j.val : ℝ) + 1) ^ 2 / (2 * (ell : ℝ))) * Real.log ‖((s ^ 2 : Kˣ) : K)‖ := by
  have hp := congrFun (actualProfile_pow_two_ell s i hi h ell ξ hξ) j
  change ξ j ^ (2 * ell) = (s ^ 2) ^ ((j.val + 1) * (j.val + 1)) at hp
  have hl := congrArg (fun z : Kˣ => Real.log ‖(z : K)‖) hp
  simp only [Units.val_pow_eq_pow_val, norm_pow, Real.log_pow] at hl
  have hscale : (2 * (ell : ℝ)) * Real.log ‖(ξ j : K)‖ =
      ((j.val : ℝ) + 1) ^ 2 * Real.log ‖((s ^ 2 : Kˣ) : K)‖ := by
    simp only [Units.val_pow_eq_pow_val, norm_pow, Real.log_pow]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
      pow_two] using hl
  have hd : (2 * (ell : ℝ)) ≠ 0 := by positivity
  apply (mul_left_cancel₀ hd)
  rw [hscale]
  field_simp

theorem actualProfile_norm_independent (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell : ℕ) (hell : 0 < ell)
    (ξ η : Labels ell → Kˣ)
    (hξ : ξ ∈ actualProfiles s i ell) (hη : η ∈ actualProfiles s i ell)
    (j : Labels ell) : ‖(ξ j : K)‖ = ‖(η j : K)‖ := by
  apply Real.log_injOn_pos (actualProfile_norm_pos ell ξ j)
    (actualProfile_norm_pos ell η j)
  rw [actualProfile_log_norm s i hi h ell hell ξ hξ,
    actualProfile_log_norm s i hi h ell hell η hη]

theorem gaussian_log_norm (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell : ℕ) (hell : 0 < ell)
    (ξ : Labels ell → Kˣ) (hξ : ξ ∈ actualProfiles s i ell)
    (u : normOneUnits K) (n : ℕ) (j : Labels ell) :
    Real.log ‖(((u : Kˣ) * ξ j ^ n : Kˣ) : K)‖ =
      (n : ℝ) * (((j.val : ℝ) + 1) ^ 2 / (2 * (ell : ℝ))) *
        Real.log ‖((s ^ 2 : Kˣ) : K)‖ := by
  have hu : ‖((u : Kˣ) : K)‖ = 1 := u.property
  rw [Units.val_mul, norm_mul, hu, one_mul, Units.val_pow_eq_pow_val,
    norm_pow, Real.log_pow, actualProfile_log_norm s i hi h ell hell ξ hξ]
  ring

theorem gaussian_sum_log_norm (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell : ℕ) (hell : 0 < ell)
    (ξ : Labels ell → Kˣ) (hξ : ξ ∈ actualProfiles s i ell)
    (u : normOneUnits K) (n : ℕ) :
    (∑ j : Labels ell, Real.log ‖(((u : Kˣ) * ξ j ^ n : Kˣ) : K)‖) =
      ((n : ℝ) * (∑ j : Labels ell, ((j.val : ℝ) + 1) ^ 2) /
        (2 * (ell : ℝ))) * Real.log ‖((s ^ 2 : Kˣ) : K)‖ := by
  simp_rw [gaussian_log_norm s i hi h ell hell ξ hξ u n]
  rw [← Finset.sum_mul]
  congr 1
  simp only [div_eq_mul_inv, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem gaussian_sum_log_norm_independent (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell : ℕ) (hell : 0 < ell)
    (ξ η : Labels ell → Kˣ)
    (hξ : ξ ∈ actualProfiles s i ell) (hη : η ∈ actualProfiles s i ell)
    (u v : normOneUnits K) (n : ℕ) :
    (∑ j : Labels ell, Real.log ‖(((u : Kˣ) * ξ j ^ n : Kˣ) : K)‖) =
      ∑ j : Labels ell, Real.log ‖(((v : Kˣ) * η j ^ n : Kˣ) : K)‖ := by
  rw [gaussian_sum_log_norm s i hi h ell hell ξ hξ,
    gaussian_sum_log_norm s i hi h ell hell η hη]

theorem gaussian_mean_log_norm (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell : ℕ) (hell : 0 < ell)
    (hlabels : 1 ≤ (ell - 1) / 2)
    (ξ : Labels ell → Kˣ) (hξ : ξ ∈ actualProfiles s i ell)
    (u : normOneUnits K) (n : ℕ) :
    CitedLV.Theorem311.ordinaryFinMean
      (fun j : Labels ell => Real.log ‖(((u : Kˣ) * ξ j ^ n : Kˣ) : K)‖) =
      (1 / 6) * (2 * (((ell - 1) / 2 : ℕ) : ℝ) + 1) *
        ((((ell - 1) / 2 : ℕ) : ℝ) + 1) *
        ((n : ℝ) / (2 * (ell : ℝ)) * Real.log ‖((s ^ 2 : Kˣ) : K)‖) := by
  calc
    _ = CitedLV.Theorem311.ordinaryFinMean
        (fun j : Labels ell => CitedLV.Procession.sqScaled
          ((n : ℝ) / (2 * (ell : ℝ)) * Real.log ‖((s ^ 2 : Kˣ) : K)‖)
          (j.val + 1)) := by
      congr 1
      funext j
      rw [gaussian_log_norm s i hi h ell hell ξ hξ u n j]
      simp only [CitedLV.Procession.sqScaled, Nat.cast_add, Nat.cast_one]
      ring
    _ = _ := CitedLV.Theorem311.ordinaryFinMean_sqScaled_formula _ _ hlabels

end CitedLV.ThetaLink.GaussianThetaLogReadout
