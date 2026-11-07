import Cor312LogVolume.Src.IUT3.Section1Remark122LogShellInclusions
import Cor312LogVolume.theorem311.NormalizedHaarCore
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.MetricSpace.Ultra.Basic

set_option autoImplicit false
noncomputable section
namespace CitedLV.LocalLogShellCompactness

open Metric Set MeasureTheory
open Src.IUT3.Remark122 Src.IUT3.Proposition39iv
open SrcLib.LocalFieldLogIsometry

variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]
  [CompleteSpace K] [IsUltrametricDist K] [ProperSpace K]

theorem principalUnits_eq_ball : (principalUnits : Set K) = ball 1 1 := by
  ext u
  simp [principalUnits, mem_ball, dist_eq_norm]

theorem principalUnits_compact : IsCompact (principalUnits : Set K) := by
  rw [principalUnits_eq_ball]
  exact (isCompact_closedBall (1 : K) 1).of_isClosed_subset
    (IsUltrametricDist.isClosed_ball 1 1) ball_subset_closedBall

include p in
theorem logUnit_continuousOn : ContinuousOn (logUnit : K → K) principalUnits := by
  obtain ⟨a, ha, hmax⟩ := (principalUnits_compact (K := K)).exists_isMaxOn
    ⟨1, one_mem_principalUnits (p := p)⟩
    (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
  have hr : ‖a - 1‖ < 1 := ha
  have hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) * ‖a - 1‖ ^ (n + 1)) := by
    have hgeo := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (r := ‖a - 1‖) (by simpa using hr)
    simpa [pow_one] using (summable_nat_add_iff 1).mpr hgeo
  unfold logUnit log1p
  apply continuousOn_tsum (u := fun n : ℕ => ((n : ℝ) + 1) * ‖a - 1‖ ^ (n + 1))
  · intro n
    unfold term
    fun_prop
  · exact hsum
  · intro n x hx
    have hbound := norm_log_term_le_extension (p := p) (K := K)
      (x - 1) (n + 1) (Nat.succ_ne_zero n)
    have hle : ‖x - 1‖ ≤ ‖a - 1‖ := hmax hx
    simp only [Nat.cast_add, Nat.cast_one] at hbound
    simp only [term, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    simp only [Nat.cast_add, Nat.cast_one]
    apply hbound.trans
    gcongr

include p in
theorem logImage_compact : IsCompact ((logUnit : K → K) '' principalUnits) :=
  (principalUnits_compact (K := K)).image_of_continuousOn (logUnit_continuousOn p)

theorem pStar_ne_zero : ((pStar p : ℕ) : K) ≠ 0 := by
  letI : CharZero K := charZero_of_injective_ringHom (algebraMap ℚ_[p] K).injective
  have hn : pStar p ≠ 0 := by
    unfold pStar
    split_ifs
    · decide
    · exact (Fact.out : p.Prime).ne_zero
  exact_mod_cast hn

theorem logShell_eq_scaled_image :
    logShell (K := K) p =
      (fun y : K => ((pStar p : ℕ) : K)⁻¹ * y) '' (logUnit '' principalUnits) := by
  ext x
  constructor
  · rintro ⟨u, hu, heq⟩
    refine ⟨logUnit u, ⟨u, hu, rfl⟩, ?_⟩
    change ((pStar p : ℕ) : K)⁻¹ * logUnit u = x
    rw [← heq, ← mul_assoc, inv_mul_cancel₀ (pStar_ne_zero (K := K) p), one_mul]
  · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨u, hu, ?_⟩
    rw [← mul_assoc, mul_inv_cancel₀ (pStar_ne_zero (K := K) p), one_mul]

theorem logShell_compact : IsCompact (logShell (K := K) p) := by
  rw [logShell_eq_scaled_image p]
  exact (logImage_compact p).image (continuous_const.mul continuous_id)

theorem principalUnit_norm {u : K} (hu : u ∈ principalUnits) : ‖u‖ = 1 := by
  have hlt : ‖u - 1‖ < 1 := hu
  have hne : ‖(1 : K)‖ ≠ ‖u - 1‖ := by simpa using hlt.ne'
  have heq := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  simpa only [add_sub_cancel, norm_one, max_eq_left hlt.le] using heq

theorem principalUnits_inv {u : K} (hu : u ∈ principalUnits) : u⁻¹ ∈ principalUnits := by
  have hn : ‖u‖ = 1 := principalUnit_norm hu
  have hu0 : u ≠ 0 := by intro h; simpa [h] using hn
  change ‖u⁻¹ - 1‖ < 1
  have heq : u⁻¹ - 1 = -(u - 1) / u := by field_simp; ring
  rw [heq, norm_div, norm_neg, hn, div_one]
  exact hu

include p in
theorem logUnit_one : logUnit (1 : K) = 0 := by
  simpa [logUnit] using (log1p_zero (p := p) (K := K))

include p in
theorem logUnit_inv {u : K} (hu : u ∈ principalUnits) : logUnit u⁻¹ = -logUnit u := by
  have hu0 : u ≠ 0 := by
    intro h
    have hn := principalUnit_norm hu
    simpa [h] using hn
  have heq := logUnit_mul (p := p) hu (principalUnits_inv hu)
  rw [mul_inv_cancel₀ hu0, logUnit_one p] at heq
  linear_combination -heq

def logImageAddSubgroup : AddSubgroup K where
  carrier := logUnit '' principalUnits
  zero_mem' := ⟨1, one_mem_principalUnits (p := p), logUnit_one p⟩
  add_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u * v, principalUnits_mul (p := p) hu hv, logUnit_mul (p := p) hu hv⟩
  neg_mem' := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, principalUnits_inv hu, logUnit_inv p hu⟩

def logShellAddSubgroup : AddSubgroup K where
  carrier := logShell p
  zero_mem' := by
    refine ⟨1, one_mem_principalUnits (p := p), ?_⟩
    simp [logUnit_one p]
  add_mem' := by
    rintro x y ⟨u, hu, hx⟩ ⟨v, hv, hy⟩
    exact ⟨u * v, principalUnits_mul (p := p) hu hv,
      by rw [logUnit_mul (p := p) hu hv, mul_add, hx, hy]⟩
  neg_mem' := by
    rintro x ⟨u, hu, hx⟩
    exact ⟨u⁻¹, principalUnits_inv hu, by rw [logUnit_inv p hu, mul_neg, hx]⟩

theorem logShell_open : IsOpen (logShell (K := K) p) := by
  apply (logShellAddSubgroup (K := K) p).isOpen_of_mem_nhds (g := 0)
  exact Filter.mem_of_superset (closedBall_mem_nhds (0 : K) (by norm_num : (0 : ℝ) < 1))
    (intO_subset_logShell (p := p) (K := K))

def logShellRegion : CitedLV.Theorem311.NormalizedHaarRegion K :=
  ⟨logShell p, ⟨⟨logShell_compact p, logShell_open p⟩,
    ⟨0, (logShellAddSubgroup p).zero_mem⟩⟩⟩

theorem logShell_measure_pos_lt_top [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] :
    0 < μ (logShell (K := K) p) ∧ μ (logShell (K := K) p) < ⊤ :=
  ⟨(logShell_open p).measure_pos μ ⟨0, (logShellAddSubgroup p).zero_mem⟩,
    (logShell_compact p).measure_lt_top⟩

end CitedLV.LocalLogShellCompactness
end
