import Cor312LogVolume.independence.Cor312SourceBoundFamily
import Cor312LogVolume.thetalink.GaussianMonoidFromThetaValues

set_option autoImplicit false
noncomputable section

namespace CitedLV.Independence.Cor312SourceBoundSplitting

open Metric
open Src.EtTh.ThetaValueArithmetic
open Src.EtTh.PadicThetaValues
open CitedLV.ThetaLink.GaussianMonoidFromThetaValues
open CitedLV.Theorem311.P211Packet
open CitedLV.Independence.Cor312SourceBound
open CitedLV.Independence.Cor312SourceBoundFamily

abbrev ThetaProfile := Labels 7 → ℂ_[211]ˣ

def IsActualProfile (ξ : ThetaProfile) : Prop :=
  ξ ∈ actualProfiles (thetaParameter 211 tateUnit) (imaginaryUnit 211) 7

theorem profile_norm (ξ : ThetaProfile) (hξ : IsActualProfile ξ) (k : Labels 7) :
    ‖((ξ k : ℂ_[211]ˣ) : ℂ_[211])‖ = ((211 : ℝ)⁻¹) ^ (29 * ((k.val + 1) * (k.val + 1))) :=
  theta_root_norm (k.val + 1) (ξ k) (hξ k)

theorem gaussianMonoid_norm (ξ : ThetaProfile) (hξ : IsActualProfile ξ) (x : ThetaProfile)
    (hx : x ∈ gaussianMonoid (normOneUnits ℂ_[211]) ξ) :
    ∃ N : ℕ, ∀ k : Labels 7,
      ‖((x k : ℂ_[211]ˣ) : ℂ_[211])‖ = ((211 : ℝ)⁻¹) ^ (29 * N * ((k.val + 1) * (k.val + 1))) := by
  obtain ⟨u, N, rfl⟩ := hx
  refine ⟨N, fun k => ?_⟩
  have hu : ‖((u : ℂ_[211]ˣ) : ℂ_[211])‖ = 1 := u.2
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hu, one_mul]
  rw [profile_norm ξ hξ k, ← pow_mul]
  congr 1
  ring

theorem exists_actualProfile : ∃ ξ : ThetaProfile, IsActualProfile ξ := by
  refine ⟨fun k => (rootValues_nonempty 211 tateUnit tateUnit_small 7 (k.val + 1) (by norm_num)).some,
    fun k => (rootValues_nonempty 211 tateUnit tateUnit_small 7 (k.val + 1) (by norm_num)).some_mem⟩

def stage (k : Labels 7) : Fin (p211PacketSystem.lstar + 1) :=
  ⟨k.val + 1, by
    have h := k.isLt
    show k.val + 1 < 3 + 1
    omega⟩

theorem thetaPilot_from_profile (ξ : ThetaProfile) (hξ : IsActualProfile ξ) (k : Labels 7) :
    sourceThetaPilot () (stage k) = closedBall (0 : ℚ_[211]) ‖((ξ k : ℂ_[211]ˣ) : ℂ_[211])‖ := by
  rw [sourceThetaPilot_eq, qBall_eq, profile_norm ξ hξ k]
  rfl

theorem coeC_pow (x : ℚ_[211]) (n : ℕ) :
    ((x ^ n : ℚ_[211]) : ℂ_[211]) = ((x : ℚ_[211]) : ℂ_[211]) ^ n := by
  have h : ∀ y : ℚ_[211], ((y : ℚ_[211]) : ℂ_[211]) = algebraMap ℚ_[211] ℂ_[211] y := fun _ => rfl
  rw [h, h, map_pow]

theorem tateN_eq_pow (N : ℕ) : tateN N = tateParameter ^ N := by
  rw [tateN, tateParameter, qPilotScalar, ← pow_mul, ← pow_mul, ← pow_mul]
  congr 1
  ring

theorem tateUnit_pow (N : ℕ) : tateUnit ^ N = tateUnitN N := by
  ext
  rw [Units.val_pow_eq_pow_val]
  show ((tateParameter : ℚ_[211]) : ℂ_[211]) ^ N = ((tateN N : ℚ_[211]) : ℂ_[211])
  rw [tateN_eq_pow, coeC_pow]

theorem pow_isActual (ξ : ThetaProfile) (hξ : IsActualProfile ξ) (N : ℕ) (hN : 0 < N)
    (k : Labels 7) : (ξ ^ N) k ∈ rootValues 211 (tateUnitN N) 7 (k.val + 1) := by
  rw [mem_rootValues_iff_power 211 (tateUnitN N) (tateUnitN_small N hN)]
  have h := (mem_rootValues_iff_power 211 tateUnit tateUnit_small 7 (k.val + 1) (ξ k)).mp (hξ k)
  calc ((ξ ^ N) k) ^ (2 * 7) = ((ξ k) ^ (2 * 7)) ^ N := by
        rw [Pi.pow_apply, ← pow_mul, ← pow_mul, Nat.mul_comm N (2 * 7)]
    _ = (tateUnit ^ ((k.val + 1) * (k.val + 1))) ^ N := by rw [h]
    _ = (tateUnitN N) ^ ((k.val + 1) * (k.val + 1)) := by
        rw [← tateUnit_pow, ← pow_mul, ← pow_mul, Nat.mul_comm N]

theorem pow_not_isActual_succ (ξ : ThetaProfile) (hξ : IsActualProfile ξ) (N : ℕ) (k : Labels 7) :
    (ξ ^ N) k ∉ rootValues 211 (tateUnitN (N + 1)) 7 (k.val + 1) := by
  intro h
  have h1 := theta_root_normN (N + 1) (Nat.succ_pos N) (k.val + 1) _ h
  have h2 : ‖(((ξ ^ N) k : ℂ_[211]ˣ) : ℂ_[211])‖
      = ((211 : ℝ)⁻¹) ^ (29 * N * ((k.val + 1) * (k.val + 1))) := by
    simp only [Pi.pow_apply, Units.val_pow_eq_pow_val, norm_pow]
    rw [profile_norm ξ hξ k, ← pow_mul]
    congr 1
    ring
  rw [h1] at h2
  have he := pow_right_injective₀ (by norm_num : (0 : ℝ) < (211 : ℝ)⁻¹) (by norm_num : (211 : ℝ)⁻¹ ≠ 1) h2
  have hpos : 0 < (k.val + 1) * (k.val + 1) := by positivity
  have he' : 29 * (N + 1) * ((k.val + 1) * (k.val + 1)) = 29 * N * ((k.val + 1) * (k.val + 1)) := he
  nlinarith

theorem pow_mem_actualProfiles (ξ : ThetaProfile) (hξ : IsActualProfile ξ) (N : ℕ) (hN : 0 < N) :
    ξ ^ N ∈ actualProfiles (thetaParameter 211 (tateUnitN N)) (imaginaryUnit 211) 7 := by
  intro k
  exact pow_isActual ξ hξ N hN k

theorem family_from_monoid (ξ : ThetaProfile) (hξ : IsActualProfile ξ) (N : ℕ) (hN : 0 < N)
    (k : Labels 7) :
    (ξ ^ N) ∈ gaussianMonoid (normOneUnits ℂ_[211]) ξ ∧
      thetaValueRegionN N (k.val + 1) =
        closedBall (0 : ℚ_[211]) ‖(((ξ ^ N) k : ℂ_[211]ˣ) : ℂ_[211])‖ := by
  refine ⟨⟨1, N, by funext j; simp⟩, ?_⟩
  rw [thetaValueRegionN_eq N hN, qBall_eq]
  congr 1
  simp only [Pi.pow_apply, Units.val_pow_eq_pow_val, norm_pow]
  rw [profile_norm ξ hξ k, ← pow_mul]
  congr 1
  ring

end CitedLV.Independence.Cor312SourceBoundSplitting

section Check
open CitedLV.Independence.Cor312SourceBoundSplitting
end Check
