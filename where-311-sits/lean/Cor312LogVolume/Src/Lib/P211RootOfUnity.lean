import Mathlib

open Polynomial

noncomputable section
namespace Src.Lib.P211RootOfUnity

instance fact211 : Fact (Nat.Prime 211) := ⟨by norm_num⟩

def F : Polynomial ℤ := X ^ 7 - 1

def a : ℤ_[211] := ((171 : ℤ) : ℤ_[211])

lemma F_aeval (z : ℤ_[211]) : F.aeval z = z ^ 7 - 1 := by
  simp [F]

lemma F_deriv : F.derivative = 7 * X ^ 6 := by
  simp [F, derivative_sub]

lemma F_deriv_aeval (z : ℤ_[211]) : F.derivative.aeval z = 7 * z ^ 6 := by
  rw [F_deriv, map_mul, map_pow, aeval_X, map_ofNat]

lemma dvd_num : (211 : ℤ) ∣ (171 : ℤ) ^ 7 - 1 := by
  have : (((171 : ℤ) ^ 7 - 1 : ℤ) : ZMod 211) = 0 := by
    push_cast
    decide
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 211).mp this

lemma not_dvd_deriv : ¬ (211 : ℤ) ∣ (7 : ℤ) * (171 : ℤ) ^ 6 := by
  intro h
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((7 : ℤ) * (171 : ℤ) ^ 6) 211).mpr h
  revert this
  push_cast
  decide

lemma norm_F_a : ‖F.aeval a‖ < 1 := by
  have : F.aeval a = (((171 : ℤ) ^ 7 - 1 : ℤ) : ℤ_[211]) := by
    rw [F_aeval, a]; push_cast; ring
  rw [this]
  exact (PadicInt.norm_int_lt_one_iff_dvd _).mpr dvd_num

lemma norm_deriv_a : ‖F.derivative.aeval a‖ = 1 := by
  have h : F.derivative.aeval a = (((7 : ℤ) * (171 : ℤ) ^ 6 : ℤ) : ℤ_[211]) := by
    rw [F_deriv_aeval, a]; push_cast; ring
  rw [h]
  have hle : ‖(((7 : ℤ) * (171 : ℤ) ^ 6 : ℤ) : ℤ_[211])‖ ≤ 1 := PadicInt.norm_le_one _
  have hne : ¬ ‖(((7 : ℤ) * (171 : ℤ) ^ 6 : ℤ) : ℤ_[211])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    exact not_dvd_deriv
  exact le_antisymm hle (not_lt.mp hne)

theorem exists_root : ∃ z : ℤ_[211], z ^ 7 = 1 ∧ ‖z - a‖ < 1 := by
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [norm_deriv_a]; simpa using norm_F_a
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma (F := F) (a := a) hnorm
  refine ⟨z, ?_, ?_⟩
  · have := F_aeval z
    rw [hz] at this
    linear_combination -this
  · rw [norm_deriv_a] at hza; exact hza

lemma root_ne_one {z : ℤ_[211]} (h : ‖z - a‖ < 1) : z ≠ 1 := by
  intro hz
  rw [hz] at h
  have he : (1 : ℤ_[211]) - a = (((1 - 171 : ℤ)) : ℤ_[211]) := by
    rw [a]; push_cast; ring
  rw [he, PadicInt.norm_int_lt_one_iff_dvd] at h
  have : (((1 - 171 : ℤ)) : ZMod 211) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 211).mpr h
  revert this
  push_cast
  decide

instance fact7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem exists_primitiveRoot : ∃ z : ℤ_[211], IsPrimitiveRoot z 7 := by
  obtain ⟨z, hz7, hza⟩ := exists_root
  refine ⟨z, IsPrimitiveRoot.iff_orderOf.mpr ?_⟩
  exact orderOf_eq_prime hz7 (root_ne_one hza)

noncomputable def zeta7 : ℚ_[211] :=
  ((Classical.choose exists_primitiveRoot : ℤ_[211]) : ℚ_[211])

theorem zeta7_isPrimitiveRoot : IsPrimitiveRoot zeta7 7 :=
  (Classical.choose_spec exists_primitiveRoot).map_of_injective
    (f := (PadicInt.Coe.ringHom (p := 211))) Subtype.coe_injective

theorem zeta7_ne_zero : zeta7 ≠ 0 :=
  zeta7_isPrimitiveRoot.ne_zero (by norm_num)

noncomputable def zeta7Unit : ℚ_[211]ˣ :=
  Units.mk0 zeta7 zeta7_ne_zero

theorem zeta7Unit_isPrimitiveRoot : IsPrimitiveRoot zeta7Unit 7 := by
  refine IsPrimitiveRoot.iff_orderOf.mpr ?_
  rw [← orderOf_units]
  simpa [zeta7Unit] using IsPrimitiveRoot.iff_orderOf.mp zeta7_isPrimitiveRoot

theorem padic211_isNonarchimedean :
    IsNonarchimedean (fun x : ℚ_[211] => ‖x‖) :=
  fun a b => Padic.nonarchimedean a b

noncomputable def qUnit : ℚ_[211]ˣ :=
  Units.mk0 (211 : ℚ_[211]) (by
    have : ((211 : ℕ) : ℚ_[211]) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num)
    simpa using this)

theorem qUnit_norm_lt_one : ‖((qUnit : ℚ_[211]))‖ < 1 := by
  have h : ((qUnit : ℚ_[211])) = ((211 : ℕ) : ℚ_[211]) := by
    simp [qUnit]
  rw [h, Padic.norm_p]
  norm_num

theorem tate_hypotheses_over_Q211 :
    IsNonarchimedean (fun x : ℚ_[211] => ‖x‖) ∧
      ‖((qUnit : ℚ_[211]))‖ < 1 ∧
      IsPrimitiveRoot zeta7Unit 7 :=
  ⟨padic211_isNonarchimedean, qUnit_norm_lt_one, zeta7Unit_isPrimitiveRoot⟩

end Src.Lib.P211RootOfUnity
end
