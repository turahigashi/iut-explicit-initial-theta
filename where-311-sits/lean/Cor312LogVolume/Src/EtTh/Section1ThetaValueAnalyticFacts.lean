import Cor312LogVolume.Src.EtTh.Section1ThetaValueArithmetic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.Ultra

noncomputable section
open Filter Topology Src.EtTh.Prop14

namespace Src.EtTh.ThetaValueArithmetic

private theorem summable_quadratic_geometric
    {K : Type*} [NormedField K] [CompleteSpace K]
    (s u : K) (hs : ‖s‖ < 1) :
    Summable (fun n : ℕ => s ^ (n * (n + 1)) * u ^ (2 * n + 1)) := by
  have ht : Tendsto
      (fun n : ℕ => (‖s‖ ^ n) ^ 2 * ‖s‖ ^ 2 * ‖u‖ ^ 2)
      atTop (𝓝 0) := by
    simpa using
      (((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg s) hs).pow 2).mul_const
        (‖s‖ ^ 2)).mul_const (‖u‖ ^ 2)
  apply summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num)
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  have hrec :
      s ^ ((n + 1) * (n + 1 + 1)) * u ^ (2 * (n + 1) + 1) =
        (s ^ (2 * n + 2) * u ^ 2) * (s ^ (n * (n + 1)) * u ^ (2 * n + 1)) := by
    rw [show (n + 1) * (n + 1 + 1) = (2 * n + 2) + n * (n + 1) by ring,
      show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by omega]
    simp only [pow_add]
    ring
  rw [hrec, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖s ^ (2 * n + 2) * u ^ 2‖ = (‖s‖ ^ n) ^ 2 * ‖s‖ ^ 2 * ‖u‖ ^ 2 := by
      rw [norm_mul, norm_pow, norm_pow, pow_add,
        show 2 * n = n * 2 by omega, pow_mul]
    _ ≤ 1 / 2 := hn.le

private theorem summable_theta_positive
    {K : Type*} [NormedField K] [CompleteSpace K]
    (s u : Kˣ) (hs : ‖(s : K)‖ < 1) :
    Summable (fun n : ℕ =>
      thetaCoeff (s : K) (2 * (n : ℤ) + 1) * (u : K) ^ (2 * (n : ℤ) + 1)) := by
  apply Summable.of_norm_bounded
    (summable_quadratic_geometric ‖(s : K)‖ ‖(u : K)‖ (by simpa using hs))
  intro n
  rw [thetaCoeff_odd]
  simp only [norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow,
    Units.val_neg, Units.val_one, norm_neg, norm_one, one_zpow, one_mul,
    norm_pow]
  norm_cast

theorem thetaValue_summable
    {K : Type*} [NormedField K] [CompleteSpace K]
    (s u : Kˣ) (hs : ‖(s : K)‖ < 1) :
    Summable (fun k : ℤ => thetaCoeff (s : K) k * (u : K) ^ k) := by
  have hp := summable_theta_positive s u hs
  have hn : Summable (fun n : ℕ =>
      thetaCoeff (s : K) (2 * (-((n : ℤ) + 1)) + 1) *
        (u : K) ^ (2 * (-((n : ℤ) + 1)) + 1)) := by
    apply (summable_theta_positive s u⁻¹ hs).neg.congr
    intro n
    have hc := congrFun (theta_invert s) (2 * (n : ℤ) + 1)
    simp only [invert, monoMul, sub_zero, neg_one_mul] at hc
    rw [show 2 * (-((n : ℤ) + 1)) + 1 = -(2 * (n : ℤ) + 1) by omega,
      hc]
    simp
  have hodd : Summable (fun n : ℤ =>
      thetaCoeff (s : K) (2 * n + 1) * (u : K) ^ (2 * n + 1)) :=
    hp.of_nat_of_neg_add_one hn
  have hinj : Function.Injective (fun n : ℤ => 2 * n + 1) := by
    intro a b hab
    change 2 * a + 1 = 2 * b + 1 at hab
    omega
  have hz : ∀ k ∉ Set.range (fun n : ℤ => 2 * n + 1),
      thetaCoeff (s : K) k * (u : K) ^ k = 0 := by
    intro k hk
    have hpar : k % 2 ≠ 1 := by
      intro h
      apply hk
      refine ⟨k / 2, ?_⟩
      change 2 * (k / 2) + 1 = k
      omega
    simp [thetaCoeff, hpar]
  exact (hinj.summable_iff hz).mp hodd

private theorem thetaValue_eq_tsum_odd
    {K : Type*} [NormedField K] (s u : Kˣ) :
    thetaValue s u = ∑' n : ℤ,
      thetaCoeff (s : K) (2 * n + 1) * (u : K) ^ (2 * n + 1) := by
  have hinj : Function.Injective (fun n : ℤ => 2 * n + 1) := by
    intro a b hab
    change 2 * a + 1 = 2 * b + 1 at hab
    omega
  apply Eq.symm
  unfold thetaValue
  apply hinj.tsum_eq (f := fun k : ℤ => thetaCoeff (s : K) k * (u : K) ^ k)
  intro k hk
  have hpar : k % 2 = 1 := by
    by_contra hp
    exact hk (by simp [thetaCoeff, hp])
  refine ⟨k / 2, ?_⟩
  change 2 * (k / 2) + 1 = k
  omega

private theorem thetaTerm_at_i
    {K : Type*} [NormedField K] (s i : Kˣ) (hi : i ^ 2 = -1) (n : ℤ) :
    thetaCoeff (s : K) (2 * n + 1) * (i : K) ^ (2 * n + 1) =
      (i : K) * (s : K) ^ (n * (n + 1)).toNat := by
  have hpow : (-1 : Kˣ) ^ n * i ^ (2 * n + 1) = i := by
    rw [zpow_add, zpow_one, zpow_mul,
      show i ^ (2 : ℤ) = -1 by simpa using hi]
    rw [← mul_assoc, ← zpow_add, show n + n = 2 * n by omega,
      zpow_mul, neg_one_zpow_two]
    simp
  rw [thetaCoeff_odd]
  have hv := congrArg (fun z : Kˣ => (z : K)) hpow
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val] at hv
  calc
    _ = ((((-1 : Kˣ) ^ n : Kˣ) : K) * (i : K) ^ (2 * n + 1)) *
        (s : K) ^ (n * (n + 1)).toNat := by ring
    _ = _ := by
      simp only [Units.val_zpow_eq_zpow_val]
      rw [hv]

theorem thetaValue_at_i
    {K : Type*} [NormedField K] [CompleteSpace K]
    (s i : Kˣ) (hi : i ^ 2 = -1) (hs : ‖(s : K)‖ < 1) :
    thetaValue s i = (2 * (i : K)) * ∑' n : ℕ, (s : K) ^ (n * (n + 1)) := by
  have hinj : Function.Injective (fun n : ℤ => 2 * n + 1) := by
    intro a b hab
    change 2 * a + 1 = 2 * b + 1 at hab
    omega
  have hodd : Summable (fun n : ℤ =>
      thetaCoeff (s : K) (2 * n + 1) * (i : K) ^ (2 * n + 1)) :=
    (thetaValue_summable s i hs).comp_injective hinj
  rw [thetaValue_eq_tsum_odd, ← tsum_nat_add_neg_add_one hodd, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [thetaTerm_at_i s i hi, thetaTerm_at_i s i hi]
  have hexp : (-((n : ℤ) + 1)) * (-((n : ℤ) + 1) + 1) =
      (n : ℤ) * ((n : ℤ) + 1) := by ring
  rw [hexp]
  have hexpNat : ((n : ℤ) * ((n : ℤ) + 1)).toNat = n * (n + 1) := by
    norm_cast
  rw [hexpNat]
  ring

theorem thetaValue_at_i_ne_zero
    {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
    (s i : Kˣ) (hi : i ^ 2 = -1) (hs : ‖(s : K)‖ < 1) :
    thetaValue s i ≠ 0 := by
  rw [thetaValue_at_i s i hi hs]
  apply mul_ne_zero (mul_ne_zero (by norm_num) (Units.ne_zero i))
  have hsum : Summable (fun n : ℕ => (s : K) ^ (n * (n + 1))) := by
    simpa using summable_quadratic_geometric (s : K) (1 : K) hs
  have htail : ‖∑' n : ℕ, (s : K) ^ ((n + 1) * (n + 1 + 1))‖ < 1 := by
    apply lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le ?_)
      (pow_lt_one₀ (norm_nonneg (s : K)) hs (by decide : (2 : ℕ) ≠ 0))
    intro n
    rw [norm_pow]
    apply pow_le_pow_of_le_one (norm_nonneg (s : K)) hs.le
    nlinarith
  rw [hsum.tsum_eq_zero_add]
  simp only [Nat.zero_mul, pow_zero]
  intro hzero
  have heq : (∑' n : ℕ, (s : K) ^ ((n + 1) * (n + 1 + 1))) = -1 := by
    linear_combination hzero
  rw [heq, norm_neg, norm_one] at htail
  exact (lt_irrefl (1 : ℝ)) htail

def publishedThetaFactsOfCompleteUltrametric
    {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
    (s i : Kˣ) (hi : i ^ 2 = -1) (hs : ‖(s : K)‖ < 1) :
    PublishedThetaFacts s i where
  small := hs
  summable u := thetaValue_summable s u hs
  nonzero_at_i := thetaValue_at_i_ne_zero s i hi hs

theorem norm_thetaValue_at_i
    {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (s i : Kˣ) (hi : i ^ 2 = -1) (hs : ‖(s : K)‖ < 1) :
    ‖thetaValue s i‖ = ‖(2 : K)‖ := by
  have hiNorm : ‖(i : K)‖ = 1 := by
    have heq : ‖(i : K)‖ ^ 2 = 1 := by
      have hv := congrArg (fun x : Kˣ => ‖(x : K)‖) hi
      simpa using hv
    nlinarith [norm_nonneg (i : K)]
  have hsum : Summable (fun n : ℕ => (s : K) ^ (n * (n + 1))) := by
    simpa using summable_quadratic_geometric (s : K) (1 : K) hs
  have htail : ‖∑' n : ℕ, (s : K) ^ ((n + 1) * (n + 1 + 1))‖ < 1 := by
    apply lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le ?_)
      (pow_lt_one₀ (norm_nonneg (s : K)) hs (by decide : (2 : ℕ) ≠ 0))
    intro n
    rw [norm_pow]
    apply pow_le_pow_of_le_one (norm_nonneg (s : K)) hs.le
    nlinarith
  have hseries : ‖∑' n : ℕ, (s : K) ^ (n * (n + 1))‖ = 1 := by
    rw [hsum.tsum_eq_zero_add]
    simp only [Nat.zero_mul, pow_zero]
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by simpa using htail.ne' : ‖(1 : K)‖ ≠
        ‖∑' n : ℕ, (s : K) ^ ((n + 1) * (n + 1 + 1))‖)]
    simp [max_eq_left htail.le]
  rw [thetaValue_at_i s i hi hs, norm_mul, norm_mul, hiNorm, hseries]
  simp

end Src.EtTh.ThetaValueArithmetic
