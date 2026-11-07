import Cor312LogVolume.Src.Lib.PadicLog.PadicLogFubini
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

namespace SrcLib.PadicLogAdd

open scoped PowerSeries

namespace Formal

open PowerSeries

variable {A : Type*} [Field A] [Algebra ℚ A] [IsAddTorsionFree A]

def geometric : A⟦X⟧ :=
  PowerSeries.mk fun n => algebraMap ℚ A ((-1 : ℚ) ^ n)

theorem geometric_mul_one_add_X :
    geometric (A := A) * (1 + PowerSeries.X) = 1 := by
  ext n
  cases n with
  | zero => simp [geometric]
  | succ n =>
      rw [PowerSeries.coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_succ']
      simp only [geometric, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one,
        PowerSeries.coeff_X]
      rw [Finset.sum_eq_single (n, 0)]
      · simp [pow_succ]
      · intro b hb hne
        have hb2 : b.2 ≠ 0 := by
          intro hb20
          apply hne
          apply Prod.ext
          · have hsum := Finset.mem_antidiagonal.mp hb
            omega
          · exact hb20
        simp [hb2]
      · intro hnot
        exact (hnot (Finset.mem_antidiagonal.mpr (show n + 0 = n from rfl))).elim

theorem log_subst_exp_sub_one :
    (PowerSeries.log A).subst (PowerSeries.exp A - 1) = PowerSeries.X := by
  let e : A⟦X⟧ := PowerSeries.exp A - 1
  have he0 : PowerSeries.constantCoeff e = 0 := by
    simp [e, PowerSeries.constantCoeff_exp]
  have he : PowerSeries.HasSubst e :=
    PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have hone : (1 : A⟦X⟧).subst e = 1 := by
    rw [← PowerSeries.coe_substAlgHom he]
    exact map_one (PowerSeries.substAlgHom he)
  have hgeom_eval :
      (geometric (A := A)).subst e * PowerSeries.exp A = 1 := by
    have h := congrArg (fun f : A⟦X⟧ => f.subst e)
      (geometric_mul_one_add_X (A := A))
    change (geometric (A := A) * (1 + PowerSeries.X)).subst e =
      (1 : A⟦X⟧).subst e at h
    rw [PowerSeries.subst_mul he] at h
    rw [PowerSeries.subst_add he, PowerSeries.subst_X he, hone] at h
    simpa [e] using h
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_subst A he, PowerSeries.deriv_log]
    have hde : d⁄dX A e = PowerSeries.exp A := by
      simp [e, PowerSeries.derivative_exp]
    rw [hde, show PowerSeries.mk (fun n => algebraMap ℚ A ((-1 : ℚ) ^ n)) =
      geometric (A := A) from rfl]
    simpa using hgeom_eval
  · simpa using PowerSeries.constantCoeff_subst_eq_zero he0 (PowerSeries.log A)
      PowerSeries.constantCoeff_log

theorem derivative_logOf {f : A⟦X⟧} (hf : PowerSeries.constantCoeff f = 1) :
    d⁄dX A (PowerSeries.logOf f) = f⁻¹ * d⁄dX A f := by
  let u : A⟦X⟧ := f - 1
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    simp [u, hf]
  have hu : PowerSeries.HasSubst u :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hu0
  have hone : (1 : A⟦X⟧).subst u = 1 := by
    rw [← PowerSeries.coe_substAlgHom hu]
    exact map_one (PowerSeries.substAlgHom hu)
  have hgeom : (geometric (A := A)).subst u = f⁻¹ := by
    apply (PowerSeries.eq_inv_iff_mul_eq_one (by simpa [hf])).2
    have h := congrArg (fun g : A⟦X⟧ => g.subst u)
      (geometric_mul_one_add_X (A := A))
    change (geometric (A := A) * (1 + PowerSeries.X)).subst u =
      (1 : A⟦X⟧).subst u at h
    rw [PowerSeries.subst_mul hu, PowerSeries.subst_add hu,
      PowerSeries.subst_X hu, hone] at h
    simpa [u] using h
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst A hu, PowerSeries.deriv_log]
  rw [show PowerSeries.mk (fun n => algebraMap ℚ A ((-1 : ℚ) ^ n)) =
    geometric (A := A) from rfl, hgeom]
  congr 1
  simp [u]

theorem logOf_mul {f g : A⟦X⟧}
    (hf : PowerSeries.constantCoeff f = 1)
    (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.logOf (f * g) = PowerSeries.logOf f + PowerSeries.logOf g := by
  have hfg : PowerSeries.constantCoeff (f * g) = 1 := by simp [hf, hg]
  have hfi : f⁻¹ * f = 1 :=
    PowerSeries.inv_mul_cancel f (by rw [hf]; exact one_ne_zero)
  have hgi : g⁻¹ * g = 1 :=
    PowerSeries.inv_mul_cancel g (by rw [hg]; exact one_ne_zero)
  apply PowerSeries.derivative.ext
  · rw [derivative_logOf hfg, map_add, derivative_logOf hf, derivative_logOf hg,
      Derivation.leibniz, PowerSeries.mul_inv_rev]
    simp only [smul_eq_mul]
    calc
      (g⁻¹ * f⁻¹) * (f * d⁄dX A g + g * d⁄dX A f) =
          (f⁻¹ * f) * (g⁻¹ * d⁄dX A g) +
            (g⁻¹ * g) * (f⁻¹ * d⁄dX A f) := by ring
      _ = f⁻¹ * d⁄dX A f + g⁻¹ * d⁄dX A g := by
        rw [hfi, hgi]
        simp [add_comm]
  · simp [PowerSeries.constantCoeff_logOf, hf, hg, hfg]

theorem log_subst_mul {u v : A⟦X⟧}
    (hu0 : PowerSeries.constantCoeff u = 0)
    (hv0 : PowerSeries.constantCoeff v = 0) :
    (PowerSeries.log A).subst (u + v + u * v) =
      (PowerSeries.log A).subst u + (PowerSeries.log A).subst v := by
  have hfu : PowerSeries.constantCoeff (1 + u) = 1 := by simp [hu0]
  have hfv : PowerSeries.constantCoeff (1 + v) = 1 := by simp [hv0]
  have hmul := logOf_mul (A := A) hfu hfv
  have hinner : (1 + u) * (1 + v) - 1 = u + v + u * v := by ring
  rw [PowerSeries.logOf_eq, PowerSeries.logOf_eq, PowerSeries.logOf_eq,
    hinner, add_sub_cancel_left, add_sub_cancel_left] at hmul
  exact hmul

end Formal

namespace Padic

open SrcLib.PadicLogFubini
open SrcLib.PadicLogFubini.Padic
open PowerSeries

variable (p : ℕ) [Fact p.Prime]

theorem logSeries1p_add (x y : ℚ_[p]) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    logSeries1p p (x + y + x * y) = logSeries1p p x + logSeries1p p y := by
  let u : ℚ_[p]⟦X⟧ := pathSeries x 0
  let v : ℚ_[p]⟦X⟧ := pathSeries y 0
  have hu0 : constantCoeff u = 0 := by simp [u, pathSeries]
  have hv0 : constantCoeff v = 0 := by simp [v, pathSeries]
  have hformal := Formal.log_subst_mul (A := ℚ_[p]) hu0 hv0
  have hpath : u + v + u * v = pathSeries (x + y) (x * y) := by
    simp [u, v, pathSeries]
    ring
  rw [hpath] at hformal

  have hsum : ‖x + y‖ < 1 :=
    (IsUltrametricDist.norm_add_le_max x y).trans_lt ((max_lt_iff).2 ⟨hx, hy⟩)
  have hprod : ‖x * y‖ < 1 := by
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg x) hx hy.le
  have hxy : max ‖x + y‖ ‖x * y‖ < 1 := (max_lt_iff).2 ⟨hsum, hprod⟩
  have hx0 : max ‖x‖ ‖(0 : ℚ_[p])‖ < 1 := by simpa using hx
  have hy0 : max ‖y‖ ‖(0 : ℚ_[p])‖ < 1 := by simpa using hy

  have hsx := summable_coeff_log_subst_path p x 0 hx0
  have hsy := summable_coeff_log_subst_path p y 0 hy0
  have hcoeff (m : ℕ) :
      coeff m ((PowerSeries.log ℚ_[p]).subst (pathSeries (x + y) (x * y))) =
        coeff m ((PowerSeries.log ℚ_[p]).subst (pathSeries x 0)) +
          coeff m ((PowerSeries.log ℚ_[p]).subst (pathSeries y 0)) := by
    simpa [u, v] using congrArg (coeff m) hformal

  calc
    logSeries1p p (x + y + x * y) =
        ∑' m : ℕ, coeff m
          ((PowerSeries.log ℚ_[p]).subst (pathSeries (x + y) (x * y))) :=
      (tsum_coeff_log_subst_path_eq_logSeries1p p (x + y) (x * y) hxy).symm
    _ = ∑' m : ℕ,
        (coeff m ((PowerSeries.log ℚ_[p]).subst (pathSeries x 0)) +
          coeff m ((PowerSeries.log ℚ_[p]).subst (pathSeries y 0))) := by
      apply tsum_congr
      exact hcoeff
    _ = (∑' m : ℕ, coeff m
          ((PowerSeries.log ℚ_[p]).subst (pathSeries x 0))) +
        ∑' m : ℕ, coeff m
          ((PowerSeries.log ℚ_[p]).subst (pathSeries y 0)) := hsx.tsum_add hsy
    _ = logSeries1p p x + logSeries1p p y := by
      rw [tsum_coeff_log_subst_path_eq_logSeries1p p x 0 hx0,
        tsum_coeff_log_subst_path_eq_logSeries1p p y 0 hy0]
      simp

end Padic

end SrcLib.PadicLogAdd
