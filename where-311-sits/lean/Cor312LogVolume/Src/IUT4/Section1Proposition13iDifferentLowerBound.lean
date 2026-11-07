import Mathlib
import Cor312LogVolume.Src.IUT4.Section1Proposition12iiTensorLogUnits

namespace Src.IUT4.Proposition13

open SrcLib.PadicLog Src.IUT4.Proposition12i

variable (p : ℕ) [hp : Fact p.Prime]
variable {L B : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L] [IsUltrametricDist L]
  [FiniteDimensional ℚ_[p] L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]
  [CommRing B] [IsDomain B] [Algebra ℤ_[p] B] [Algebra B L] [IsScalarTower ℤ_[p] B L]
  [IsIntegralClosure B ℤ_[p] L] [IsDedekindDomain B] [IsFractionRing B L] [Module.IsTorsionFree ℤ_[p] B]
  [Module.Finite ℤ_[p] B]

include p B in

theorem exists_of_norm_le_one {x : L} (hx : ‖x‖ ≤ 1) : ∃ b : B, algebraMap B L b = x :=
  IsIntegralClosure.isIntegral_iff.mp ((isIntegral_iff_norm_le_one (p := p) x).mpr hx)

include p in
theorem norm_algebraMap_le_one (b : B) : ‖algebraMap B L b‖ ≤ 1 :=
  norm_le_one_of_isIntegral (p := p) ((IsIntegralClosure.isIntegral ℤ_[p] L b).map (IsScalarTower.toAlgHom ℤ_[p] B L))

omit [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [CompleteSpace L] [IsUltrametricDist L]
  [FiniteDimensional ℚ_[p] L] in
theorem norm_pi_pos_lt_one (R : RamificationData p L) : 0 < ‖R.pi‖ ∧ ‖R.pi‖ < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have he : (0 : ℝ) < R.e := by exact_mod_cast R.e_pos
  rw [R.norm_pi]
  refine ⟨Real.rpow_pos_of_pos (by linarith) _, Real.rpow_lt_one_of_one_lt_of_neg hp1 ?_⟩
  exact div_neg_of_neg_of_pos (by norm_num) he

omit [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [CompleteSpace L] [IsUltrametricDist L]
  [FiniteDimensional ℚ_[p] L] in
theorem norm_pi_pow_e (R : RamificationData p L) : ‖R.pi‖ ^ R.e = ‖(p : L)‖ := by
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have he : (R.e : ℝ) ≠ 0 := by exact_mod_cast R.e_pos.ne'
  rw [R.norm_pi, ← Real.rpow_natCast, ← Real.rpow_mul hp0, div_mul_cancel₀ _ he,
    show (p : L) = algebraMap ℚ_[p] L (p : ℚ_[p]) by simp, norm_algebraMap', Padic.norm_p]
  rw [Real.rpow_neg_one]

include B in

theorem differentIdeal_le_span_pow (R : RamificationData p L) :
    ∃ πB : B, algebraMap B L πB = R.pi ∧ differentIdeal ℤ_[p] B ≤ Ideal.span {πB ^ (R.e - 1)} := by
  obtain ⟨hπ0, hπ1⟩ := norm_pi_pos_lt_one p R
  obtain ⟨πB, hπB⟩ := exists_of_norm_le_one p (B := B) hπ1.le
  refine ⟨πB, hπB, ?_⟩
  have hpi0 : R.pi ≠ 0 := norm_pos_iff.mp hπ0
  have hdiv : ‖(p : L) / R.pi ^ R.e‖ ≤ 1 := by
    rw [norm_div, norm_pow, norm_pi_pow_e p R, div_self (by rw [← norm_pi_pow_e p R]; positivity)]
  obtain ⟨u, hu⟩ := exists_of_norm_le_one p (B := B) hdiv
  have hP : Ideal.span {πB} ^ R.e ∣ (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] B) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow,
      Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton]
    refine ⟨u, (IsIntegralClosure.algebraMap_injective B ℤ_[p] L) ?_⟩
    rw [map_mul, map_pow, hπB, hu, ← IsScalarTower.algebraMap_apply, map_natCast]
    field_simp
  have hp0 : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have h := pow_sub_one_dvd_differentIdeal_aux ℤ_[p] ℚ_[p] L (Ideal.span {πB}) R.e_pos.ne' hp0 hP
  rwa [Ideal.span_singleton_pow, Ideal.dvd_iff_le] at h

include B in

theorem prop13i_Qp (R : RamificationData p L) (δ : B) (hδ : δ ∈ differentIdeal ℤ_[p] B) (D : ℕ)
    (hD : ‖algebraMap B L δ‖ = ‖R.pi‖ ^ D) : R.e - 1 ≤ D := by
  obtain ⟨hπ0, hπ1⟩ := norm_pi_pos_lt_one p R
  obtain ⟨πB, hπB, hle⟩ := differentIdeal_le_span_pow p (B := B) R
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hle hδ)
  have hnorm : ‖R.pi‖ ^ D ≤ ‖R.pi‖ ^ (R.e - 1) := by
    rw [← hD, ← hb, map_mul, norm_mul, map_pow, hπB, norm_pow, mul_comm]
    exact mul_le_of_le_one_right (by positivity) (norm_algebraMap_le_one p b)
  exact (pow_le_pow_iff_right_of_lt_one₀ hπ0 hπ1).mp hnorm

include B in

theorem prop13i_Qp_real (R : RamificationData p L) (δ : B) (hδ : δ ∈ differentIdeal ℤ_[p] B) (D : ℕ)
    (hD : ‖algebraMap B L δ‖ = ‖R.pi‖ ^ D) : ((R.e : ℝ) - 1) / R.e ≤ (D : ℝ) / R.e := by
  have h := prop13i_Qp p R δ hδ D hD
  have he : (0 : ℝ) < R.e := by exact_mod_cast R.e_pos
  apply div_le_div_of_nonneg_right _ he.le
  have : ((R.e - 1 : ℕ) : ℝ) ≤ D := by exact_mod_cast h
  have h1 : (1 : ℝ) ≤ R.e := by exact_mod_cast R.e_pos
  rw [Nat.cast_sub (by exact_mod_cast R.e_pos : 1 ≤ R.e)] at this
  simpa using this

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

include p B in

theorem isUnit_of_norm_eq_one (b : B) (hb : ‖algebraMap B L b‖ = 1) : IsUnit b := by
  have hne : algebraMap B L b ≠ 0 := by
    intro h; rw [h, norm_zero] at hb; exact zero_ne_one hb
  obtain ⟨c, hc⟩ := exists_of_norm_le_one p (B := B) (x := (algebraMap B L b)⁻¹)
    (by rw [norm_inv, hb, inv_one])
  refine isUnit_iff_exists_inv.mpr ⟨c, IsIntegralClosure.algebraMap_injective B ℤ_[p] L ?_⟩
  rw [map_mul, hc, mul_inv_cancel₀ hne, map_one]

include p in

theorem mem_span_pi_of_not_isUnit (R : RamificationData p L) {πB : B} (hπB : algebraMap B L πB = R.pi)
    (b : B) (hb : ¬ IsUnit b) : b ∈ Ideal.span {πB} := by
  obtain ⟨hπ0, hπ1⟩ := norm_pi_pos_lt_one p R
  have hle := norm_algebraMap_le_one p (L := L) b
  have hlt : ‖algebraMap B L b‖ < 1 :=
    lt_of_le_of_ne hle fun h => hb (isUnit_of_norm_eq_one p b h)
  by_cases hb0 : algebraMap B L b = 0
  · have : b = 0 := (IsIntegralClosure.algebraMap_injective B ℤ_[p] L) (by rw [hb0, map_zero])
    rw [this]; exact Ideal.zero_mem _
  obtain ⟨n, hn⟩ := R.valueGroup _ hb0
  have hn1 : 1 ≤ n := by
    by_contra h
    have : 1 ≤ ‖R.pi‖ ^ n := one_le_zpow_of_nonpos₀ hπ0 hπ1.le (by omega)
    rw [← hn] at this; linarith
  have hdiv : ‖algebraMap B L b / R.pi‖ ≤ 1 := by
    rw [norm_div, hn, div_le_one hπ0]
    calc ‖R.pi‖ ^ n ≤ ‖R.pi‖ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hπ0 hπ1.le hn1
      _ = ‖R.pi‖ := zpow_one _
  obtain ⟨c, hc⟩ := exists_of_norm_le_one p (B := B) hdiv
  refine Ideal.mem_span_singleton'.mpr ⟨c, (IsIntegralClosure.algebraMap_injective B ℤ_[p] L) ?_⟩
  rw [map_mul, hc, hπB, div_mul_cancel₀ _ (norm_pos_iff.mp hπ0)]

include p in

theorem le_span_pi_of_ne_top (R : RamificationData p L) {πB : B} (hπB : algebraMap B L πB = R.pi)
    (I : Ideal B) (hI : I ≠ ⊤) : I ≤ Ideal.span {πB} := fun b hb =>
  mem_span_pi_of_not_isUnit p R hπB b fun hu => hI (Ideal.eq_top_of_isUnit_mem I hb hu)

theorem residue_finite : Finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) := by
  have hsurj : Function.Surjective (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := fun a =>
    ⟨(a.val : ℤ_[p]), by rw [map_natCast, ZMod.natCast_zmod_val]⟩
  have e := RingHom.quotientKerEquivOfSurjective hsurj
  exact Finite.of_equiv (ZMod p) ((Ideal.quotEquivOfEq PadicInt.ker_toZMod.symm).trans e).toEquiv.symm

include B in

theorem differentIdeal_eq_top_of_e_eq_one [Module.Free ℤ_[p] B] (R : RamificationData p L) (he : R.e = 1) :
    differentIdeal ℤ_[p] B = ⊤ := by
  classical
  haveI : CharZero (FractionRing ℤ_[p]) :=
    (algebraMap ℤ_[p] (FractionRing ℤ_[p])).charZero_iff (IsFractionRing.injective _ _) |>.mp inferInstance
  obtain ⟨hπ0, hπ1⟩ := norm_pi_pos_lt_one p R
  obtain ⟨πB, hπB⟩ := exists_of_norm_le_one p (B := B) hπ1.le

  have hmB : (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] B) = Ideal.span {πB} := by
    have hdiv : ‖(p : L) / R.pi‖ ≤ 1 := by
      rw [norm_div, ← norm_pi_pow_e p R, he, pow_one, div_self hπ0.ne']
    obtain ⟨u, hu⟩ := exists_of_norm_le_one p (B := B) hdiv
    have hunit : IsUnit u := by
      refine isUnit_of_norm_eq_one p (L := L) u ?_
      rw [hu, norm_div, ← norm_pi_pow_e p R, he, pow_one, div_self hπ0.ne']
    have hpu : algebraMap ℤ_[p] B p = πB * u := by
      refine (IsIntegralClosure.algebraMap_injective B ℤ_[p] L) ?_
      rw [map_mul, hπB, hu, ← IsScalarTower.algebraMap_apply, map_natCast,
        mul_div_cancel₀ _ (norm_pos_iff.mp hπ0)]
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, hpu,
      Ideal.span_singleton_mul_right_unit hunit]
  have hPmax : (Ideal.span {πB}).IsMaximal := by
    refine Ideal.isMaximal_iff.mpr ⟨?_, fun J b hle hb hbJ => ?_⟩
    · intro h1
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
      have := congrArg (fun y => ‖algebraMap B L y‖) hc
      simp only [map_mul, norm_mul, hπB, map_one, norm_one] at this
      have := norm_algebraMap_le_one p (L := L) c
      nlinarith
    · by_contra hJ
      have hJtop : J ≠ ⊤ := fun h => hJ (h ▸ Submodule.mem_top)
      exact hb (le_span_pi_of_ne_top p R hπB J hJtop hbJ)
  haveI : ((IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] B)).IsMaximal := hmB ▸ hPmax
  letI := Ideal.Quotient.field ((IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] B))
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal ℤ_[p])
  haveI := residue_finite p
  haveI : Module.Finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) (B ⧸ (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] B)) := inferInstance
  obtain ⟨y, hy⟩ := Algebra.trace_surjective (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) (B ⧸ (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] B)) 1
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Algebra.trace_quotient_mk] at hy
  have hx : Algebra.intTrace ℤ_[p] B x ∉ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [Algebra.intTrace_eq_trace, ← Ideal.Quotient.eq_zero_iff_mem, hy]
    exact one_ne_zero
  have hnd := not_dvd_differentIdeal_of_intTrace_not_mem (A := ℤ_[p]) (Ideal.span {πB}) ⊤
    (by rw [Ideal.mul_top, hmB]) x Submodule.mem_top hx
  by_contra hD
  exact hnd (Ideal.dvd_iff_le.mpr (le_span_pi_of_ne_top p R hπB _ hD))

end Src.IUT4.Proposition13

section Check
open Src.IUT4.Proposition13
end Check
