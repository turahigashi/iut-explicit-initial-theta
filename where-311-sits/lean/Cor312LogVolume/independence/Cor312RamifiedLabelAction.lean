import Cor312LogVolume.independence.Cor312RamifiedLogShell

set_option autoImplicit false
noncomputable section

namespace CitedLV.Independence.Cor312RamifiedLogShell

open CitedLV.Theorem311.TensorIntegralLattice
open CitedLV.Independence.Cor312RamifiedBadPlace
open scoped TensorProduct

section Label

variable (p : ℕ) [Fact p.Prime]
variable (L : Type) [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
  [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]

def traceMul : MultilinearMap ℚ_[p] (LL L 1) L :=
  (MultilinearMap.mkPiAlgebra ℚ_[p] (Fin 2) L).compLinearMap
    (fun i => if i = 0 then (Algebra.linearMap ℚ_[p] L).comp (Algebra.trace ℚ_[p] L)
      else LinearMap.id)

omit [CompleteSpace L] [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem traceMul_apply (v : (i : Fin 2) → LL L 1 i) :
    traceMul p L v = algebraMap ℚ_[p] L (Algebra.trace ℚ_[p] L (v 0)) * v 1 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [traceMul, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    Fin.prod_univ_two, if_pos rfl, if_neg h10]
  rfl

omit [CompleteSpace L] [IsUltrametricDist L] [ProperSpace L] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem trace_one_eq : Algebra.trace ℚ_[p] L 1 = (Module.finrank ℚ_[p] L : ℚ_[p]) := by
  have h := Algebra.trace_algebraMap (R := ℚ_[p]) (S := L) (1 : ℚ_[p])
  rw [map_one] at h
  rw [h, nsmul_eq_mul, mul_one]

omit [CompleteSpace L] [IsUltrametricDist L] [ProperSpace L] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] L] in

theorem label_swap_ne (α : L) (hα : α ∉ Set.range (algebraMap ℚ_[p] L)) :
    permLin p L 1 (Equiv.swap 0 1) (PiTensorProduct.tprod ℚ_[p] (s := LL L 1) ![1, α]) ≠
      PiTensorProduct.tprod ℚ_[p] (s := LL L 1) ![1, α] := by
  intro h
  have h1 := congrArg (PiTensorProduct.lift (traceMul p L)) h
  rw [permLin_tprod, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod, traceMul_apply,
    traceMul_apply] at h1
  simp only [Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at h1
  rw [trace_one_eq, map_natCast] at h1
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  have hn : (Module.finrank ℚ_[p] L : L) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ_[p]) (M := L)).ne'
  apply hα
  refine ⟨Algebra.trace ℚ_[p] L α / (Module.finrank ℚ_[p] L : ℚ_[p]), ?_⟩
  rw [map_div₀, h1, map_natCast, mul_div_cancel_left₀ α hn]

theorem ind1_nontrivial (h : Module.finrank ℚ_[p] L ≠ 1) :
    ∃ (σ : Equiv.Perm (Fin 2)) (z : PP p L 1),
      (logShellSystem p L).labelAct () ⟨1, by show 1 < 3 + 1; norm_num⟩ σ z ≠ z := by
  obtain ⟨α, hα⟩ : ∃ α : L, α ∉ Set.range (algebraMap ℚ_[p] L) := by
    by_contra hc
    push Not at hc
    apply h
    rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨(algebraMap ℚ_[p] L).injective, hc⟩
  exact ⟨Equiv.swap 0 1, PiTensorProduct.tprod ℚ_[p] (s := LL L 1) ![1, α], label_swap_ne p L α hα⟩

theorem ind1_strip_nontrivial :
    ∃ g : Fin (0 + 1) → ∀ v : (logShellSystem p L).Above (), (logShellSystem p L).StripAut () v,
      (logShellSystem p L).stripAct () 0 g (1 : PP p L 0) ≠ (1 : PP p L 0) := by
  obtain ⟨g, hg⟩ := ind2_nontrivial p L
  exact ⟨g () 0, hg⟩

end Label

section ConcreteLabel

open Src.Lib.P211Datum Src.Lib.P211Valuation

theorem rU_not_rational : ((rU : FBˣ) : FB) ∉ Set.range (algebraMap ℚ_[211] FB) := by
  rintro ⟨x, hx⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact Units.ne_zero _ hx.symm
  have hnorm : ‖((rU : FBˣ) : FB)‖ = ‖x‖ := by
    rw [← hx]
    exact norm_algebraMap' FB x
  have h98 : ‖((rU : FBˣ) : FB)‖ ^ 98 = (211 : ℝ)⁻¹ ^ 29 := by
    show ‖rootB‖ ^ 98 = _
    rw [show (98 : ℕ) = 14 * 7 by norm_num, pow_mul, ← norm_pow, rootB_pow, qbVal_spec.2.1, norm_pC]
  rw [hnorm, Padic.norm_eq_zpow_neg_valuation hx0] at h98
  have h211 : (1 : ℝ) < 211 := by norm_num
  have hl := congrArg Real.log h98
  rw [← zpow_natCast, ← zpow_mul, Real.log_zpow, Real.log_pow, Real.log_inv] at hl
  have hlog : 0 < Real.log (211 : ℝ) := Real.log_pos h211
  have key : ((-(x.valuation) * 98 : ℤ) : ℝ) = -29 := by
    have := hl
    push_cast at this ⊢
    nlinarith
  have hint : -(x.valuation) * 98 = -29 := by exact_mod_cast key
  omega

theorem ind1_nontrivial_FB :
    ∃ (σ : Equiv.Perm (Fin 2)) (z : PP 211 FB 1),
      (logShellSystem 211 FB).labelAct () ⟨1, by show 1 < 3 + 1; norm_num⟩ σ z ≠ z :=
  ⟨Equiv.swap 0 1, PiTensorProduct.tprod ℚ_[211] (s := LL FB 1) ![1, ((rU : FBˣ) : FB)],
    label_swap_ne 211 FB _ rU_not_rational⟩

end ConcreteLabel

end CitedLV.Independence.Cor312RamifiedLogShell
