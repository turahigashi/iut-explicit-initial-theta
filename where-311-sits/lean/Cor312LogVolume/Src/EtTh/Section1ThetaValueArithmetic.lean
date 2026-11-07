import Cor312LogVolume.Src.EtTh.Section1Proposition14ThetaSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Field.Basic
import Cor312LogVolume.Src.EtTh.Section5NonzeroIntegralRootLanding
import Mathlib.RingTheory.RootsOfUnity.Basic

noncomputable section
open Src.EtTh.Prop14

namespace Src.EtTh.ThetaValueArithmetic

variable {K : Type*} [NormedField K]

def thetaValue (s u : Kˣ) : K :=
  ∑' k : ℤ, thetaCoeff (s : K) k * (u : K) ^ k

private theorem series_scale (f : USeries K) (c u : Kˣ) :
    (∑' k : ℤ, f k * ((c * u : Kˣ) : K) ^ k) =
      ∑' k : ℤ, scale c f k * (u : K) ^ k := by
  apply tsum_congr
  intro k
  simp only [Units.val_mul, mul_zpow, scale, Units.val_zpow_eq_zpow_val]
  ring

private theorem series_monoMul (f : USeries K) (c : K) (m : ℤ) (u : Kˣ) :
    (∑' k : ℤ, monoMul c m f k * (u : K) ^ k) =
      (c * (u : K) ^ m) * ∑' k : ℤ, f k * (u : K) ^ k := by
  calc
    _ = ∑' k : ℤ, (c * (u : K) ^ m) *
        (f (k - m) * (u : K) ^ (k - m)) := by
      apply tsum_congr
      intro k
      have hu : (u : K) ^ k = (u : K) ^ (k - m) * (u : K) ^ m := by
        rw [← zpow_add₀ (Units.ne_zero u)]
        congr 1
        omega
      rw [monoMul, hu]
      ring
    _ = (c * (u : K) ^ m) *
        ∑' k : ℤ, f (k - m) * (u : K) ^ (k - m) := tsum_mul_left
    _ = _ := by
      congr 1
      simpa only [sub_eq_add_neg] using
        (Equiv.addRight (-m)).tsum_eq (fun k : ℤ => f k * (u : K) ^ k)

theorem thetaValue_negate (s u : Kˣ) :
    thetaValue s (-u) = -thetaValue s u := by
  have harg : -u = (-1 : Kˣ) * u := by simp
  unfold thetaValue
  rw [harg, series_scale, theta_negate, series_monoMul]
  simp

theorem thetaValue_quasiperiodic (s : Kˣ) (a : ℤ) (u : Kˣ) :
    thetaValue s (s ^ a * u) =
      (((-1 : Kˣ) ^ a * s ^ (-(a ^ 2)) * u ^ (-2 * a) : Kˣ) : K) *
        thetaValue s u := by
  unfold thetaValue
  rw [series_scale, theta_quasiperiodic, series_monoMul]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]

structure PublishedThetaFacts (s i : Kˣ) : Prop where
  small : ‖(s : K)‖ < 1
  summable : ∀ u : Kˣ, Summable (fun k : ℤ => thetaCoeff (s : K) k * (u : K) ^ k)
  nonzero_at_i : thetaValue s i ≠ 0

theorem PublishedThetaFacts.negate {s i : Kˣ} (_h : PublishedThetaFacts s i)
    (u : Kˣ) : thetaValue s (-u) = -thetaValue s u :=
  thetaValue_negate s u

theorem PublishedThetaFacts.quasi {s i : Kˣ} (_h : PublishedThetaFacts s i)
    (a : ℤ) (u : Kˣ) :
    thetaValue s (s ^ a * u) =
      (((-1 : Kˣ) ^ a * s ^ (-(a ^ 2)) * u ^ (-2 * a) : Kˣ) : K) *
        thetaValue s u :=
  thetaValue_quasiperiodic s a u

theorem shifted_i (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (j : ℤ) :
    thetaValue s (s ^ j * i) = ((s ^ (-(j ^ 2)) : Kˣ) : K) *
      thetaValue s i := by
  rw [h.quasi]
  have he : (-1 : Kˣ) ^ j * i ^ (-2 * j) = 1 := by
    rw [show -2 * j = -(2 * j) by ring, zpow_neg, zpow_mul]
    rw [show i ^ (2 : ℤ) = -1 by simpa using hi]
    exact mul_inv_cancel _
  have hc : (-1 : Kˣ) ^ j * s ^ (-(j ^ 2)) * i ^ (-2 * j) =
      s ^ (-(j ^ 2)) := by
    calc
      _ = ((-1 : Kˣ) ^ j * i ^ (-2 * j)) * s ^ (-(j ^ 2)) := by ac_rfl
      _ = _ := by rw [he, one_mul]
  rw [hc]

theorem normalized_inverse_value (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (j : ℕ) :
    thetaValue s i / thetaValue s (s ^ (j : ℤ) * i) =
      (s : K) ^ (j * j) := by
  rw [shifted_i s i hi h]
  have hp : (j : ℤ) ^ 2 = ((j * j : ℕ) : ℤ) := by
    simp [pow_two]
  rw [hp, zpow_neg, zpow_natCast]
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  field_simp [h.nonzero_at_i]

theorem normalized_root_pow (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell j : ℕ) (t : Kˣ)
    (ht : (t : K) ^ ell =
      thetaValue s i / thetaValue s (s ^ (j : ℤ) * i)) :
    t ^ ell = s ^ (j * j) := by
  apply Units.ext
  exact ht.trans (normalized_inverse_value s i hi h j)

theorem normalized_root_pow_two (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell j : ℕ) (t : Kˣ)
    (ht : (t : K) ^ ell =
      thetaValue s i / thetaValue s (s ^ (j : ℤ) * i)) :
    t ^ (2 * ell) = (s ^ 2) ^ (j * j) := by
  calc
    _ = (t ^ ell) ^ 2 := by rw [Nat.mul_comm 2 ell, pow_mul]
    _ = (s ^ (j * j)) ^ 2 := by rw [normalized_root_pow s i hi h ell j t ht]
    _ = _ := by rw [← pow_mul, Nat.mul_comm (j * j) 2, pow_mul]

theorem normalized_root_integral (R : Type*) [CommRing R] [Algebra R K]
    (s i : Kˣ) (hi : i ^ 2 = -1) (h : PublishedThetaFacts s i)
    (ell j : ℕ) (hell : 0 < ell) (t : Kˣ)
    (ht : (t : K) ^ ell =
      thetaValue s i / thetaValue s (s ^ (j : ℤ) * i))
    (hq : s ^ 2 ∈ Src.EtTh.NonzeroIntegral.nonzeroIntegral R K) :
    t ∈ Src.EtTh.NonzeroIntegral.nonzeroIntegral R K := by
  apply Src.EtTh.NonzeroIntegral.mem_of_pow_mem R K (n := 2 * ell)
    (Nat.mul_pos (show 0 < 2 by decide) hell)
  rw [normalized_root_pow_two s i hi h ell j t ht]
  exact (Src.EtTh.NonzeroIntegral.nonzeroIntegral R K).pow_mem hq (j * j)

theorem normalized_root_profile (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell j : ℕ) (t qRoot : Kˣ)
    (ht : (t : K) ^ ell =
      thetaValue s i / thetaValue s (s ^ (j : ℤ) * i))
    (hqRoot : qRoot ^ (2 * ell) = s ^ 2) :
    ∃ z : rootsOfUnity (2 * ell) K, t = (z : Kˣ) * qRoot ^ (j * j) := by
  have hden : (qRoot ^ (j * j)) ^ (2 * ell) = (s ^ 2) ^ (j * j) := by
    rw [← pow_mul, Nat.mul_comm (j * j) (2 * ell), pow_mul, hqRoot]
  have hz : (t / qRoot ^ (j * j)) ^ (2 * ell) = 1 := by
    rw [div_pow, normalized_root_pow_two s i hi h ell j t ht, hden]
    simp
  refine ⟨⟨t / qRoot ^ (j * j), ?_⟩, ?_⟩
  · exact hz
  · simp

theorem negative_normalized_inverse_value (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (j : ℕ) :
    thetaValue s i / thetaValue s (-(s ^ (j : ℤ) * i)) =
      -(s : K) ^ (j * j) := by
  rw [h.negate, div_neg, normalized_inverse_value s i hi h j]

theorem negative_normalized_root_pow_two (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell j : ℕ) (t : Kˣ)
    (ht : (t : K) ^ ell =
      thetaValue s i / thetaValue s (-(s ^ (j : ℤ) * i))) :
    t ^ (2 * ell) = (s ^ 2) ^ (j * j) := by
  apply Units.ext
  change (t : K) ^ (2 * ell) = ((s : K) ^ 2) ^ (j * j)
  rw [Nat.mul_comm 2 ell, pow_mul, ht,
    negative_normalized_inverse_value s i hi h j, neg_sq,
    ← pow_mul, Nat.mul_comm (j * j) 2, pow_mul]

def normalizedRootValues (s i : Kˣ) (ell j : ℕ) : Set Kˣ :=
  {t | (t : K) ^ ell =
      thetaValue s i / thetaValue s (s ^ (j : ℤ) * i) ∨
    (t : K) ^ ell =
      thetaValue s i / thetaValue s (-(s ^ (j : ℤ) * i))}

theorem mem_normalizedRootValues_iff_power (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell j : ℕ) (t : Kˣ) :
    t ∈ normalizedRootValues s i ell j ↔ t ^ (2 * ell) = (s ^ 2) ^ (j * j) := by
  constructor
  · rintro (ht | ht)
    · exact normalized_root_pow_two s i hi h ell j t ht
    · exact negative_normalized_root_pow_two s i hi h ell j t ht
  · intro ht
    have hsquare : ((t : K) ^ ell) ^ 2 = ((s : K) ^ (j * j)) ^ 2 := by
      calc
        _ = (t : K) ^ (2 * ell) := by rw [Nat.mul_comm 2 ell, pow_mul]
        _ = ((s : K) ^ 2) ^ (j * j) := by
          exact congrArg (fun u : Kˣ => (u : K)) ht
        _ = _ := by rw [← pow_mul, Nat.mul_comm 2 (j * j), pow_mul]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with he | he
    · exact Or.inl (he.trans (normalized_inverse_value s i hi h j).symm)
    · exact Or.inr (he.trans (negative_normalized_inverse_value s i hi h j).symm)

theorem normalizedRootValues_integral (R : Type*) [CommRing R] [Algebra R K]
    (s i : Kˣ) (hi : i ^ 2 = -1) (h : PublishedThetaFacts s i)
    (ell j : ℕ) (hell : 0 < ell) (t : Kˣ)
    (ht : t ∈ normalizedRootValues s i ell j)
    (hq : s ^ 2 ∈ Src.EtTh.NonzeroIntegral.nonzeroIntegral R K) :
    t ∈ Src.EtTh.NonzeroIntegral.nonzeroIntegral R K := by
  apply Src.EtTh.NonzeroIntegral.mem_of_pow_mem R K (n := 2 * ell)
    (Nat.mul_pos (show 0 < 2 by decide) hell)
  rw [(mem_normalizedRootValues_iff_power s i hi h ell j t).mp ht]
  exact (Src.EtTh.NonzeroIntegral.nonzeroIntegral R K).pow_mem hq (j * j)

theorem normalizedRootValues_profile_iff (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell j : ℕ) (t qRoot : Kˣ)
    (hqRoot : qRoot ^ (2 * ell) = s ^ 2) :
    t ∈ normalizedRootValues s i ell j ↔
      ∃ z : rootsOfUnity (2 * ell) K, t = (z : Kˣ) * qRoot ^ (j * j) := by
  have hden : (qRoot ^ (j * j)) ^ (2 * ell) = (s ^ 2) ^ (j * j) := by
    rw [← pow_mul, Nat.mul_comm (j * j) (2 * ell), pow_mul, hqRoot]
  constructor
  · intro ht
    have ht2 := (mem_normalizedRootValues_iff_power s i hi h ell j t).mp ht
    refine ⟨⟨t / qRoot ^ (j * j), ?_⟩, ?_⟩
    · change (t / qRoot ^ (j * j)) ^ (2 * ell) = 1
      rw [div_pow, ht2, hden]
      simp
    · simp
  · rintro ⟨z, ht⟩
    apply (mem_normalizedRootValues_iff_power s i hi h ell j t).mpr
    have hz : (z : Kˣ) ^ (2 * ell) = 1 := z.property
    rw [ht, mul_pow, hz, hden, one_mul]

theorem normalizedRootValues_nonempty (s i : Kˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell j : ℕ) (qRoot : Kˣ)
    (hqRoot : qRoot ^ (2 * ell) = s ^ 2) :
    (normalizedRootValues s i ell j).Nonempty := by
  refine ⟨qRoot ^ (j * j),
    (normalizedRootValues_profile_iff s i hi h ell j _ qRoot hqRoot).mpr ?_⟩
  exact ⟨1, by simp⟩

end Src.EtTh.ThetaValueArithmetic
