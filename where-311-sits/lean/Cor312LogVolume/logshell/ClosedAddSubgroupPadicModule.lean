import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Topology.Algebra.ContinuousMonoidHom

noncomputable section
set_option autoImplicit false

namespace CitedLV.ClosedAddSubgroupPadicModule

variable (p : ℕ) [Fact p.Prime]

section ContinuousAdditiveMaps

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [TopologicalSpace M] [TopologicalSpace N] [T2Space N]
  [Module ℤ_[p] M] [Module ℤ_[p] N]
  [ContinuousSMul ℤ_[p] M] [ContinuousSMul ℤ_[p] N]

theorem map_padicInt_smul (f : M →+ N) (hf : Continuous f)
    (a : ℤ_[p]) (x : M) : f (a • x) = a • f x := by
  refine PadicInt.denseRange_intCast.induction_on a ?_ ?_
  · exact isClosed_eq (hf.comp (continuous_id.smul continuous_const))
      (continuous_id.smul continuous_const)
  · intro n
    simp only [Int.cast_smul_eq_zsmul, map_zsmul]

def padicIntLinearEquiv (e : M ≃ₜ+ N) : M ≃ₗ[ℤ_[p]] N where
  __ := e.toAddEquiv
  map_smul' := map_padicInt_smul p e.toAddEquiv.toAddMonoidHom e.continuous

end ContinuousAdditiveMaps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]

theorem padicInt_smul_mem (H : AddSubgroup E) (hH : IsClosed (H : Set E))
    {z : E} (hz : z ∈ H) (a : ℤ_[p]) : (a : ℚ_[p]) • z ∈ H := by
  refine PadicInt.denseRange_intCast.induction_on a ?_ ?_
  · exact hH.preimage (continuous_subtype_val.smul continuous_const)
  · intro n
    simpa only [PadicInt.coe_intCast, Int.cast_smul_eq_zsmul] using H.zsmul_mem hz n

theorem inv_natCast_smul_mem (H : AddSubgroup E) (hH : IsClosed (H : Set E))
    (n : ℕ) (hn : ¬p ∣ n) {z : E} (hz : z ∈ H) : (n : ℚ_[p])⁻¹ • z ∈ H := by
  have hc : p.Coprime n := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hn
  have hnorm : ‖(n : ℚ_[p])⁻¹‖ ≤ 1 := by
    rw [norm_inv, Padic.norm_natCast_eq_one_iff.mpr hc, inv_one]
  exact padicInt_smul_mem p H hH hz ⟨(n : ℚ_[p])⁻¹, hnorm⟩

section Field

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]

theorem inv_natCast_mul_mem (H : AddSubgroup K) (hH : IsClosed (H : Set K))
    (n : ℕ) (hn : ¬p ∣ n) {z : K} (hz : z ∈ H) : (n : K)⁻¹ * z ∈ H := by
  have h := inv_natCast_smul_mem p H hH n hn hz
  simpa only [inv_natCast_smul_eq ℚ_[p] K, smul_eq_mul] using h

theorem natCast_mul_mem_iff (H : AddSubgroup K) (hH : IsClosed (H : Set K))
    (n : ℕ) (hn : ¬p ∣ n) (z : K) : (n : K) * z ∈ H ↔ z ∈ H := by
  constructor
  · intro hz
    have hn0 : n ≠ 0 := by
      intro hzero
      exact hn (hzero ▸ dvd_zero p)
    haveI : CharZero K := charZero_of_injective_ringHom (algebraMap ℚ_[p] K).injective
    have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    have h := inv_natCast_mul_mem p H hH n hn hz
    simpa only [← mul_assoc, inv_mul_cancel₀ hnK, one_mul] using h
  · intro hz
    simpa only [nsmul_eq_mul] using H.nsmul_mem hz n

end Field

end CitedLV.ClosedAddSubgroupPadicModule
