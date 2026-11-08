import Mathlib.Topology.MetricSpace.Contracting
import LogShellEdge.Reuse.Logshell.LocalFieldLogContraction

/-!
# The logarithm is a bijection of the ball of radius `1/4`

By the Banach fixed point theorem (`log1p_surjOn`, `log1p_injOn`, `log1p_bijOn`).

Adapted from an earlier, unpublished Lean development of the author: the comments were
rewritten, the namespace was renamed and a few unused summary statements were removed; the
remaining definitions and proofs are unchanged.
-/

namespace LogShellEdge.Logshell.LocalFieldLogSurjective

open LogShellEdge.Logshell.LocalFieldLogIsometry LogShellEdge.Logshell.LocalFieldLogContraction

variable {K : Type*} [NormedField K]

def B : Set K := Metric.closedBall (0 : K) (1 / 4)

theorem mem_B_iff {x : K} : x ∈ B (K := K) ↔ ‖x‖ ≤ 1 / 4 := by
  simp [B]

instance : Nonempty (B (K := K)) := ⟨⟨0, by simp [B]⟩⟩

variable [CompleteSpace K]

instance : CompleteSpace (B (K := K)) := by
  have hclosed : IsClosed (B (K := K)) := Metric.isClosed_closedBall
  exact hclosed.completeSpace_coe

variable (p : ℕ) [hp : Fact p.Prime]
variable [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]

include p hp

theorem norm_g_le (x : K) (hx : ‖x‖ ≤ 1 / 4) :
    ‖log1p x - x‖ ≤ 1 / 8 := by
  have hxlt : ‖x‖ < 1 := lt_of_le_of_lt hx (by norm_num)
  have hrw : log1p x - x = ∑' n : ℕ, term x (n + 1) := by
    rw [log_eq_head_add_tail (p := p) x hxlt]
    ring
  rw [hrw]
  have htail := norm_tail_le (p := p) x hx
  linarith

noncomputable def F (y : K) (hy : ‖y‖ ≤ 1 / 4) (x : B (K := K)) : B (K := K) :=
  ⟨y - (log1p (x : K) - (x : K)), by
    rw [mem_B_iff]
    have hx : ‖(x : K)‖ ≤ 1 / 4 := mem_B_iff.mp x.2
    have hg : ‖log1p (x : K) - (x : K)‖ ≤ 1 / 8 := norm_g_le (p := p) _ hx
    have hmax : ‖y - (log1p (x : K) - (x : K))‖
        ≤ max ‖y‖ ‖log1p (x : K) - (x : K)‖ := by
      have h := IsUltrametricDist.norm_add_le_max
        (x := y) (y := -(log1p (x : K) - (x : K)))
      rw [norm_neg] at h
      rw [sub_eq_add_neg]
      exact h
    have hle : max ‖y‖ ‖log1p (x : K) - (x : K)‖ ≤ 1 / 4 :=
      max_le hy (by linarith)
    exact hmax.trans hle⟩

theorem lipschitz_F (y : K) (hy : ‖y‖ ≤ 1 / 4) :
    LipschitzWith (1 / 2 : NNReal) (F (p := p) y hy) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have ha : ‖(a : K)‖ ≤ 1 / 4 := mem_B_iff.mp a.2
  have hb : ‖(b : K)‖ ≤ 1 / 4 := mem_B_iff.mp b.2
  have hcon := norm_tail_sub_le (p := p) (a : K) (b : K) ha hb
  have hdist : dist (F (p := p) y hy a) (F (p := p) y hy b)
      = ‖(log1p (a : K) - (a : K)) - (log1p (b : K) - (b : K))‖ := by
    rw [Subtype.dist_eq, dist_eq_norm]
    simp only [F]
    rw [show y - (log1p (a : K) - (a : K)) -
        (y - (log1p (b : K) - (b : K))) =
        -((log1p (a : K) - (a : K)) - (log1p (b : K) - (b : K))) by ring,
      norm_neg]
  rw [hdist, Subtype.dist_eq, dist_eq_norm]
  have hcast : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
  rw [hcast]
  exact hcon

theorem contracting_F (y : K) (hy : ‖y‖ ≤ 1 / 4) :
    ContractingWith (1 / 2 : NNReal) (F (p := p) y hy) :=
  ⟨by norm_num, lipschitz_F (p := p) y hy⟩

theorem log1p_surjOn (y : K) (hy : ‖y‖ ≤ 1 / 4) :
    ∃ x : K, ‖x‖ ≤ 1 / 4 ∧ log1p x = y := by
  have hc := contracting_F (p := p) y hy
  let xs : B (K := K) := hc.fixedPoint (F (p := p) y hy)
  have hfix : F (p := p) y hy xs = xs := hc.fixedPoint_isFixedPt
  refine ⟨(xs : K), mem_B_iff.mp xs.2, ?_⟩
  have hval : y - (log1p (xs : K) - (xs : K)) = (xs : K) := by
    have h := congrArg (fun z : B (K := K) => (z : K)) hfix
    simpa [F] using h
  linear_combination -hval

theorem log1p_injOn :
    Set.InjOn (log1p : K → K) {x : K | ‖x‖ ≤ 1 / 4} := by
  intro x hx y hy hlog
  have hcon := norm_tail_sub_le (p := p) x y hx hy
  have hrw : (log1p x - x) - (log1p y - y) = -(x - y) := by
    rw [hlog]
    ring
  rw [hrw, norm_neg] at hcon
  have hzero : ‖x - y‖ = 0 := by
    have hnonneg : 0 ≤ ‖x - y‖ := norm_nonneg _
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

theorem log1p_bijOn :
    Set.BijOn (log1p : K → K) {x : K | ‖x‖ ≤ 1 / 4} {y : K | ‖y‖ ≤ 1 / 4} := by
  refine ⟨?_, log1p_injOn (p := p), ?_⟩
  · intro x hx
    have hnorm : ‖log1p x‖ = ‖x‖ := norm_log1p_eq (p := p) x hx
    simpa [hnorm] using hx
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := log1p_surjOn (p := p) y hy
    exact ⟨x, hx, hxy⟩

end LogShellEdge.Logshell.LocalFieldLogSurjective
