import Mathlib
import Cor312LogVolume.Src.IUT3.Section3Proposition35iiUpperSemiCompat

namespace Src.IUT3.Remark123

open Metric Set SrcLib.LocalFieldLogIsometry Src.IUT3.Proposition39iv Src.IUT3.Remark122
  Src.IUT3.Proposition35ii

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [CompleteSpace K]
  [IsUltrametricDist K]

include hp

omit [CompleteSpace K] in
theorem norm_eq_one_of_principal {w : K} (hw : ‖w - 1‖ < 1) : ‖w‖ = 1 := by
  have h1 : ‖(1 : K)‖ = 1 := by
    have := norm_algebraMap' K (1 : ℚ_[p]); simpa using this
  have hw' : w = 1 + (w - 1) := by ring
  have hne : ‖(1 : K)‖ ≠ ‖w - 1‖ := by rw [h1]; exact ne_of_gt hw
  rw [hw', IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, h1]
  exact max_eq_left (le_of_lt hw)

omit [CompleteSpace K] in
theorem principal_inv {w : K} (hw : ‖w - 1‖ < 1) : ‖w⁻¹ - 1‖ < 1 := by
  have hn := norm_eq_one_of_principal (p := p) hw
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  have : w⁻¹ - 1 = -(w - 1) * w⁻¹ := by field_simp; ring
  rw [this, norm_mul, norm_neg, norm_inv, hn, inv_one, mul_one]
  exact hw

theorem logUnit_principal_root {w : K} (hw : ‖w - 1‖ < 1) {n : ℕ} (hn : 0 < n) (hwn : w ^ n = 1) :
    logUnit w = 0 := by
  have hpow := logUnit_pow (p := p) hw n
  rw [hwn] at hpow
  have h0 : logUnit (1 : K) = 0 := by
    unfold logUnit; rw [sub_self]; exact log1p_zero (p := p)
  rw [h0] at hpow
  have hnK : (n : K) ≠ 0 := by
    intro h
    have := norm_natCast_K (p := p) (K := K) n
    rw [h, norm_zero] at this
    have hq : ‖(n : ℚ_[p])‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; exact_mod_cast hn.ne'
    exact hq this.symm
  exact (mul_eq_zero.mp hpow.symm).resolve_left hnK

theorem mult_to_additive {h u x y : K} (hh : LogRel p h x) (hu : LogRel p u y) : LogRel p (h * u) (x + y) := by
  obtain ⟨hh1, ζ, ⟨N, hN, hpN, hζN⟩, hprin, rfl⟩ := hh
  obtain ⟨hu1, ξ, ⟨M, hM, hpM, hξM⟩, hprin', rfl⟩ := hu
  refine ⟨by rw [norm_mul, hh1, hu1, one_mul], ζ * ξ, ⟨N * M, Nat.mul_pos hN hM, ?_, ?_⟩, ?_, ?_⟩
  · intro hdvd
    rcases (Nat.Prime.dvd_mul hp.out).mp hdvd with h1 | h1
    · exact hpN h1
    · exact hpM h1
  · rw [mul_pow, pow_mul, hζN, one_pow, one_mul, mul_comm N M, pow_mul, hξM, one_pow]
  · rw [show h * u * (ζ * ξ)⁻¹ = (h * ζ⁻¹) * (u * ξ⁻¹) by rw [mul_inv]; ring]
    exact principalUnits_mul (p := p) hprin hprin'
  · rw [show h * u * (ζ * ξ)⁻¹ = (h * ζ⁻¹) * (u * ξ⁻¹) by rw [mul_inv]; ring]
    exact (logUnit_mul (p := p) hprin hprin').symm

theorem log_root_of_unity {ζ x : K} (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) (h : LogRel p ζ x) : x = 0 := by
  obtain ⟨n, hn, hζn⟩ := hζ
  obtain ⟨_, ξ, ⟨N, hN, _, hξN⟩, hprin, rfl⟩ := h
  apply logUnit_principal_root (p := p) hprin (Nat.mul_pos hn hN)
  rw [mul_pow, inv_pow, pow_mul, hζn, one_pow, one_mul, mul_comm n N, pow_mul, hξN, one_pow, inv_one]

theorem root_of_unity_indeterminacy_vanishes {ζ u y z : K} (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (hζu : LogRel p (ζ * u) z) (hu : LogRel p u y) : z = y := by
  obtain ⟨n, hn, hζn⟩ := hζ
  obtain ⟨hζu1, ξ, ⟨N, hN, _, hξN⟩, hprin, rfl⟩ := hζu
  obtain ⟨hu1, η, ⟨M, hM, _, hηM⟩, hprin', rfl⟩ := hu
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
  have hη0 : η ≠ 0 := by intro h; rw [h, zero_pow hM.ne'] at hηM; exact zero_ne_one hηM

  set c := (ζ * u * ξ⁻¹) * (u * η⁻¹)⁻¹ with hc
  have hcprin : ‖c - 1‖ < 1 := principalUnits_mul (p := p) hprin (principal_inv (p := p) hprin')
  have hceq : c = ζ * η * ξ⁻¹ := by
    rw [hc]; field_simp
  have hcroot : c ^ (n * N * M) = 1 := by
    rw [hceq, mul_pow, mul_pow, inv_pow]
    have e1 : ζ ^ (n * N * M) = 1 := by rw [mul_assoc, pow_mul, hζn, one_pow]
    have e2 : η ^ (n * N * M) = 1 := by rw [show n * N * M = (n * N) * M by ring, pow_mul', hηM, one_pow]
    have e3 : ξ ^ (n * N * M) = 1 := by rw [show n * N * M = N * (n * M) by ring, pow_mul, hξN, one_pow]
    rw [e1, e2, e3]; simp
  have hlogc := logUnit_principal_root (p := p) hcprin (Nat.mul_pos (Nat.mul_pos hn hN) hM) hcroot
  have hsplit : ζ * u * ξ⁻¹ = (u * η⁻¹) * c := by
    rw [hc]
    have : u * η⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hη0)
    field_simp
  rw [hsplit, logUnit_mul (p := p) hprin' hcprin, hlogc, add_zero]

end Src.IUT3.Remark123

section Check
open Src.IUT3.Remark123
end Check
