import Cor312LogVolume.Src.Lib.PadicLog.LocalFieldLogIsometry
import Cor312LogVolume.Src.Lib.PadicLog.PadicLogFubini
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

namespace SrcLib.LocalFieldLogFubini

open scoped PowerSeries
open PowerSeries IsUltrametricDist
open SrcLib.PadicLogFubini SrcLib.LocalFieldLogIsometry

variable (p : ℕ) [hp : Fact p.Prime]
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]
  [CompleteSpace K] [IsUltrametricDist K]

include p hp

noncomputable def logSeries1p (x : K) : K :=
  ∑' n : ℕ, (-1 : K) ^ n * (x ^ (n + 1) / ((n + 1 : ℕ) : K))

theorem norm_div_natCast_le (a : K) (n : ℕ) (hn : n ≠ 0) :
    ‖a / (n : K)‖ ≤ (n : ℝ) * ‖a‖ := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hnorm : (1 : ℝ) / (n : ℝ) ≤ ‖(n : K)‖ :=
    norm_natCast_ge_extension (p := p) (K := K) n hn
  have hnormpos : 0 < ‖(n : K)‖ :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (n : ℝ)) hnorm
  rw [norm_div, div_le_iff₀ hnormpos]
  have hone : (1 : ℝ) ≤ (n : ℝ) * ‖(n : K)‖ := by
    simpa [mul_comm] using (div_le_iff₀ hnpos).mp hnorm
  calc
    ‖a‖ = ‖a‖ * 1 := by ring
    _ ≤ ‖a‖ * ((n : ℝ) * ‖(n : K)‖) :=
      mul_le_mul_of_nonneg_left hone (norm_nonneg _)
    _ = (n : ℝ) * ‖a‖ * ‖(n : K)‖ := by ring

noncomputable def logPathTerm (c₁ c₂ : K) (nm : ℕ × ℕ) : K :=
  (-1 : K) ^ nm.1 *
    ((pathPoly c₁ c₂ ^ (nm.1 + 1)).coeff nm.2 / ((nm.1 + 1 : ℕ) : K))

theorem norm_logPathTerm_le (c₁ c₂ : K) (n m : ℕ) :
    ‖logPathTerm c₁ c₂ (n, m)‖ ≤
      ((n : ℝ) + 1) * (max ‖c₁‖ ‖c₂‖) ^ (n + 1) := by
  rw [logPathTerm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  refine (norm_div_natCast_le (p := p) _ (n + 1) (Nat.succ_ne_zero n)).trans ?_
  simpa only [Nat.cast_add, Nat.cast_one] using
    mul_le_mul_of_nonneg_left (norm_coeff_pathPoly_pow_le c₁ c₂ (n + 1) m)
      (by positivity : 0 ≤ (n : ℝ) + 1)

theorem summable_logPathTerm (c₁ c₂ : K)
    (hsmall : max ‖c₁‖ ‖c₂‖ < 1) :
    Summable (logPathTerm c₁ c₂) := by
  let r : ℝ := max ‖c₁‖ ‖c₂‖
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ r)]
    exact hsmall
  have hmajorant : Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ (n + 1)) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := r) hr
    have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ)) : ℝ) ^ 1 * r ^ (n + 1)) :=
      (summable_nat_add_iff 1).mpr h
    simpa [pow_one] using hshift
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero,
    tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  have htail := (Metric.tendsto_atTop.mp hmajorant.tendsto_atTop_zero) ε hε
  obtain ⟨N, hN⟩ := htail
  let exceptional : Finset (ℕ × ℕ) :=
    (Finset.range N).biUnion fun n =>
      (pathPoly c₁ c₂ ^ (n + 1)).support.map
        ⟨fun m => (n, m), fun _ _ h => Prod.mk.inj h |>.2⟩
  rw [Filter.eventually_cofinite]
  refine exceptional.finite_toSet.subset ?_
  intro nm hbad
  by_cases hn : nm.1 < N
  · have hm : nm.2 ∈ (pathPoly c₁ c₂ ^ (nm.1 + 1)).support := by
      by_contra hm
      have hzero : (pathPoly c₁ c₂ ^ (nm.1 + 1)).coeff nm.2 = 0 :=
        Polynomial.notMem_support_iff.mp hm
      have hdist : dist ‖logPathTerm c₁ c₂ nm‖ 0 < ε := by
        simp [logPathTerm, hzero, hε]
      exact hbad hdist
    apply Finset.mem_biUnion.mpr
    refine ⟨nm.1, Finset.mem_range.mpr hn, ?_⟩
    simp [hm]
  · have hn' : N ≤ nm.1 := Nat.le_of_not_gt hn
    have hle := norm_logPathTerm_le (p := p) c₁ c₂ nm.1 nm.2
    have hlt : ((nm.1 : ℝ) + 1) * r ^ (nm.1 + 1) < ε := by
      have ht := hN nm.1 hn'
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
        0 ≤ ((nm.1 : ℝ) + 1) * r ^ (nm.1 + 1))] at ht
      exact ht
    have hdist : dist ‖logPathTerm c₁ c₂ nm‖ 0 < ε := by
      simpa [Real.dist_eq] using lt_of_le_of_lt hle hlt
    exact (hbad hdist).elim

theorem tsum_logPathTerm_row (c₁ c₂ : K) (n : ℕ) :
    (∑' m : ℕ, logPathTerm c₁ c₂ (n, m)) =
      (-1 : K) ^ n * ((c₁ + c₂) ^ (n + 1) / ((n + 1 : ℕ) : K)) := by
  let P : Polynomial K := pathPoly c₁ c₂ ^ (n + 1)
  rw [tsum_eq_sum (s := P.support)]
  · simp only [logPathTerm]
    rw [← Finset.mul_sum]
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    have heval : ∑ m ∈ P.support, P.coeff m = Polynomial.eval 1 P := by
      rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
      simp
    rw [heval]
    simp [P, pathPoly, Polynomial.eval_pow]
  · intro m hm
    have hz : P.coeff m = 0 := Polynomial.notMem_support_iff.mp hm
    simp [logPathTerm, P, hz]

theorem tsum_logPathTerm_eq_logSeries1p (c₁ c₂ : K)
    (hsmall : max ‖c₁‖ ‖c₂‖ < 1) :
    (∑' nm : ℕ × ℕ, logPathTerm c₁ c₂ nm) = logSeries1p (c₁ + c₂) := by
  have hs := summable_logPathTerm (p := p) c₁ c₂ hsmall
  have hrow : ∀ n : ℕ, Summable (fun m : ℕ => logPathTerm c₁ c₂ (n, m)) :=
    fun n => hs.comp_injective (fun _ _ h => Prod.mk.inj h |>.2)
  rw [hs.tsum_prod' hrow]
  simp_rw [tsum_logPathTerm_row (p := p)]
  rfl

variable [CharZero K]

theorem logPathTerm_eq_coeff_log_mul_coeff (c₁ c₂ : K) (n m : ℕ) :
    logPathTerm c₁ c₂ (n, m) =
      coeff (n + 1) (PowerSeries.log K) * coeff m ((pathSeries c₁ c₂) ^ (n + 1)) := by
  have hsign : (-1 : ℚ) ^ (n + 1 + 1) = (-1 : ℚ) ^ n := by
    rw [show n + 1 + 1 = n + 2 by omega, pow_add]
    norm_num
  have hcoeff : coeff (n + 1) (PowerSeries.log K) =
      (-1 : K) ^ n / ((n + 1 : ℕ) : K) := by
    rw [PowerSeries.coeff_log, if_neg (Nat.succ_ne_zero n), hsign]
    rw [map_div₀ (algebraMap ℚ K), map_pow]
    norm_num
  rw [hcoeff]
  simp only [logPathTerm]
  rw [← pathPoly_toPowerSeries, ← Polynomial.coe_pow, Polynomial.coeff_coe]
  ring

theorem tsum_logPathTerm_col (c₁ c₂ : K) (m : ℕ) :
    (∑' n : ℕ, logPathTerm c₁ c₂ (n, m)) =
      coeff m ((PowerSeries.log K).subst (pathSeries c₁ c₂)) := by
  let b : K⟦X⟧ := pathSeries c₁ c₂
  have hb : PowerSeries.HasSubst b :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [b, pathSeries])
  let F : ℕ → K := fun d => coeff d (PowerSeries.log K) * coeff m (b ^ d)
  have hfinite : Function.HasFiniteSupport F := by
    simpa [F, smul_eq_mul] using
      (PowerSeries.coeff_subst_finite' hb (PowerSeries.log K) m)
  have hsum : Summable F := summable_of_hasFiniteSupport hfinite
  have hzero : F 0 = 0 := by simp [F, PowerSeries.coeff_log]
  have hshift : (∑' n : ℕ, F (n + 1)) = ∑' d : ℕ, F d := by
    have h := hsum.sum_add_tsum_nat_add 1
    simpa [hzero, add_comm] using h
  calc
    (∑' n : ℕ, logPathTerm c₁ c₂ (n, m)) = ∑' n : ℕ, F (n + 1) := by
      apply tsum_congr
      intro n
      simpa [F, b] using
        logPathTerm_eq_coeff_log_mul_coeff (p := p) c₁ c₂ n m
    _ = ∑' d : ℕ, F d := hshift
    _ = ∑ᶠ d : ℕ, F d := tsum_eq_finsum hfinite
    _ = coeff m ((PowerSeries.log K).subst b) := by
      rw [PowerSeries.coeff_subst' hb]
      simp [F, smul_eq_mul]
    _ = coeff m ((PowerSeries.log K).subst (pathSeries c₁ c₂)) := rfl

theorem summable_coeff_log_subst_path (c₁ c₂ : K)
    (hsmall : max ‖c₁‖ ‖c₂‖ < 1) :
    Summable (fun m : ℕ =>
      coeff m ((PowerSeries.log K).subst (pathSeries c₁ c₂))) := by
  have hs := summable_logPathTerm (p := p) c₁ c₂ hsmall
  have hcol : ∀ m : ℕ, Summable (fun n : ℕ => logPathTerm c₁ c₂ (n, m)) :=
    fun m => hs.comp_injective (fun _ _ h => Prod.mk.inj h |>.1)
  have houter : Summable (fun m : ℕ => ∑' n : ℕ, logPathTerm c₁ c₂ (n, m)) :=
    (hs.prod_symm.hasSum.prod_fiberwise fun m => (hcol m).hasSum).summable
  simpa only [tsum_logPathTerm_col (p := p)] using houter

theorem tsum_coeff_log_subst_path_eq_rows (c₁ c₂ : K)
    (hs : Summable (logPathTerm c₁ c₂)) :
    (∑' m : ℕ, coeff m ((PowerSeries.log K).subst (pathSeries c₁ c₂))) =
      ∑' n : ℕ, ∑' m : ℕ, logPathTerm c₁ c₂ (n, m) := by
  have hcol : ∀ m : ℕ, Summable (fun n : ℕ => logPathTerm c₁ c₂ (n, m)) :=
    fun m => hs.comp_injective (fun _ _ h => Prod.mk.inj h |>.1)
  have hrow : ∀ n : ℕ, Summable (fun m : ℕ => logPathTerm c₁ c₂ (n, m)) :=
    fun n => hs.comp_injective (fun _ _ h => Prod.mk.inj h |>.2)
  calc
    (∑' m : ℕ, coeff m ((PowerSeries.log K).subst (pathSeries c₁ c₂))) =
        ∑' m : ℕ, ∑' n : ℕ, logPathTerm c₁ c₂ (n, m) := by
          apply tsum_congr
          intro m
          exact (tsum_logPathTerm_col (p := p) c₁ c₂ m).symm
    _ = ∑' q : ℕ × ℕ, logPathTerm c₁ c₂ q.swap :=
      (hs.prod_symm.tsum_prod' hcol).symm
    _ = ∑' nm : ℕ × ℕ, logPathTerm c₁ c₂ nm := by
      simpa using (Equiv.prodComm ℕ ℕ).tsum_eq (logPathTerm c₁ c₂)
    _ = ∑' n : ℕ, ∑' m : ℕ, logPathTerm c₁ c₂ (n, m) := hs.tsum_prod' hrow

theorem tsum_coeff_log_subst_path_eq_logSeries1p (c₁ c₂ : K)
    (hsmall : max ‖c₁‖ ‖c₂‖ < 1) :
    (∑' m : ℕ, coeff m ((PowerSeries.log K).subst (pathSeries c₁ c₂))) =
      logSeries1p (c₁ + c₂) := by
  have hs := summable_logPathTerm (p := p) c₁ c₂ hsmall
  have hrow : ∀ n : ℕ, Summable (fun m : ℕ => logPathTerm c₁ c₂ (n, m)) :=
    fun n => hs.comp_injective (fun _ _ h => Prod.mk.inj h |>.2)
  calc
    (∑' m : ℕ, coeff m ((PowerSeries.log K).subst (pathSeries c₁ c₂))) =
        ∑' n : ℕ, ∑' m : ℕ, logPathTerm c₁ c₂ (n, m) :=
      tsum_coeff_log_subst_path_eq_rows (p := p) c₁ c₂ hs
    _ = ∑' nm : ℕ × ℕ, logPathTerm c₁ c₂ nm := (hs.tsum_prod' hrow).symm
    _ = logSeries1p (c₁ + c₂) :=
      tsum_logPathTerm_eq_logSeries1p (p := p) c₁ c₂ hsmall

end SrcLib.LocalFieldLogFubini
