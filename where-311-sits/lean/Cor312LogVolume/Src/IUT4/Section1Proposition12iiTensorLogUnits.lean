import Mathlib
import Cor312LogVolume.Src.IUT4.Section1Proposition11NormalizationDifferent
import Cor312LogVolume.Src.IUT4.Section1Proposition12iLogBounds
import Cor312LogVolume.Src.Lib.PadicLog.FiniteExtensionIntegral

namespace Src.IUT4.Proposition12ii

open PiTensorProduct Metric
open scoped TensorProduct
open Src.IUT4.Proposition12i Src.IUT4.Proposition11 SrcLib.PadicLog

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable def aNum (e : ℕ) : ℤ :=
  if p = 2 then 2 * e else ⌈(e : ℝ) / ((p : ℝ) - 2)⌉

noncomputable def bNum (e : ℕ) : ℤ :=
  e * ⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ - 1

theorem aNum_eq (e : ℕ) (he : 0 < e) : (aNum p e : ℝ) = e * aExp p e := by
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  unfold aNum aExp
  split_ifs <;> push_cast <;> field_simp

theorem bNum_eq (e : ℕ) (he : 0 < e) : (bNum p e : ℝ) = e * bExp p e := by
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  unfold bNum bExp
  push_cast
  field_simp

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) {a : ℚ_[p]} (ha : a ≠ 0) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ ha]

section Factor

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [CompleteSpace K] [IsUltrametricDist K]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem norm_pi_zpow (R : RamificationData p K) (n : ℤ) :
    ‖R.pi ^ n‖ = (p : ℝ) ^ (-(n : ℝ) / R.e) := by
  have hp0 : (0 : ℝ) ≤ p := by positivity
  rw [norm_zpow, R.norm_pi, ← Real.rpow_intCast, ← Real.rpow_mul hp0]
  congr 1
  ring

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem pi_ne_zero (R : RamificationData p K) : R.pi ≠ 0 := by
  intro h
  have h1 := R.norm_pi
  rw [h, norm_zero] at h1
  have : (0 : ℝ) < (p : ℝ) ^ (-(1 : ℝ) / R.e) := Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _
  linarith

theorem zpow_mul_mem_logUnits (R : RamificationData p K) (r : K) (hr : ‖r‖ ≤ 1) :
    R.pi ^ aNum p R.e * r ∈ logUnitsSet p K := by
  apply lower_inclusion p R.e R.e_pos
  rw [mem_closedBall_zero_iff, norm_mul, norm_pi_zpow, aNum_eq p R.e R.e_pos]
  have he : (0 : ℝ) < R.e := by exact_mod_cast R.e_pos
  have hpow : (p : ℝ) ^ (-((R.e : ℝ) * aExp p R.e) / R.e) = (p : ℝ) ^ (-(aExp p R.e)) := by
    congr 1; field_simp
  rw [hpow]
  have hpos : (0 : ℝ) ≤ (p : ℝ) ^ (-(aExp p R.e)) := by positivity
  nlinarith [norm_nonneg r]

variable [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

theorem zpow_mul_isIntegral_of_mem_logUnits (R : RamificationData p K) (y : K) (hy : y ∈ logUnitsSet p K) :
    IsIntegral ℤ_[p] (R.pi ^ bNum p R.e * y) := by
  apply isIntegral_of_norm_le_one
  have hy' := upper_inclusion p R hy
  rw [mem_closedBall_zero_iff] at hy'
  rw [norm_mul, norm_pi_zpow, bNum_eq p R.e R.e_pos]
  have he : (0 : ℝ) < R.e := by exact_mod_cast R.e_pos
  have hpow : (p : ℝ) ^ (-((R.e : ℝ) * bExp p R.e) / R.e) = (p : ℝ) ^ (-(bExp p R.e)) := by
    congr 1; field_simp
  rw [hpow]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hmul : (p : ℝ) ^ (-(bExp p R.e)) * (p : ℝ) ^ (bExp p R.e) = 1 := by
    rw [← Real.rpow_add hp0]; simp
  have hpos : (0 : ℝ) ≤ (p : ℝ) ^ (-(bExp p R.e)) := by positivity
  calc (p : ℝ) ^ (-(bExp p R.e)) * ‖y‖ ≤ (p : ℝ) ^ (-(bExp p R.e)) * (p : ℝ) ^ (bExp p R.e) :=
        mul_le_mul_of_nonneg_left hy' hpos
    _ = 1 := hmul

end Factor

section Packet

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)] [∀ i, CompleteSpace (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

variable (L) in

noncomputable def logUnits : Submodule ℤ_[p] (⨂[ℚ_[p]] i, L i) :=
  Submodule.span ℤ_[p] {w | ∃ y : ∀ i, L i, (∀ i, y i ∈ logUnitsSet p (L i)) ∧ w = tprod ℚ_[p] y}

omit [∀ i, CompleteSpace (L i)] in

theorem isIntegral_zpow_smul_tprod (R : ∀ i, RamificationData p (L i)) (y : ∀ i, L i) (n : ι → ℤ)
    (hy : ∀ i, ‖y i‖ = ‖(R i).pi‖ ^ n i) (t : ℤ) (hsum : 0 ≤ (t : ℝ) + ∑ i, (n i : ℝ) / (R i).e) :
    IsIntegral ℤ_[p] (((p : ℚ_[p]) ^ t) • tprod ℚ_[p] y) := by
  classical
  set E : ℕ := ∏ i, (R i).e with hE
  have hEpos : 0 < E := Finset.prod_pos fun i _ => (R i).e_pos
  have hdvd : ∀ i, (R i).e ∣ E := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  set M : ι → ℕ := fun i => E / (R i).e with hMdef
  have hM : ∀ i, (R i).e * M i = E := fun i => Nat.mul_div_cancel' (hdvd i)
  set N : ι → ℤ := fun i => n i * M i with hNdef
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  set u : ∀ i, L i := fun i => y i ^ E * algebraMap ℚ_[p] (L i) (((p : ℚ_[p]) ^ N i)⁻¹) with hudef
  have hnormu : ∀ i, ‖u i‖ = 1 := by
    intro i
    have he : (0 : ℝ) < (R i).e := by exact_mod_cast (R i).e_pos
    simp only [hudef, norm_mul, norm_pow, norm_algebraMap', norm_inv, norm_zpow, Padic.norm_p, hy i,
      (R i).norm_pi]
    have hEcast : (E : ℝ) = (R i).e * (M i : ℝ) := by exact_mod_cast (hM i).symm
    rw [inv_zpow', zpow_neg, inv_inv]
    rw [← Real.rpow_intCast (((p : ℝ) ^ (-1 / ((R i).e : ℝ)))) (n i), ← Real.rpow_mul hpR.le,
      ← Real.rpow_natCast, ← Real.rpow_mul hpR.le, ← Real.rpow_intCast (p : ℝ) (N i), ← Real.rpow_add hpR]
    have key : -1 / ((R i).e : ℝ) * (n i : ℝ) * (E : ℝ) + ((N i : ℤ) : ℝ) = 0 := by
      simp only [hNdef]; push_cast; rw [hEcast]; field_simp; ring
    rw [key, Real.rpow_zero]
  have hyE : ∀ i, y i ^ E = ((p : ℚ_[p]) ^ N i) • u i := by
    intro i
    simp only [hudef, Algebra.smul_def]
    rw [mul_left_comm, ← map_mul, mul_inv_cancel₀ (zpow_ne_zero _ hp0), map_one, mul_one]
  have hpow : (((p : ℚ_[p]) ^ t) • tprod ℚ_[p] y) ^ E =
      ((p : ℚ_[p]) ^ (t * (E : ℤ) + ∑ i, N i)) • tprod ℚ_[p] u := by
    rw [smul_pow]
    have h1 : (tprod ℚ_[p] y) ^ E = tprod ℚ_[p] (y ^ E) :=
      (map_pow (tprodMonoidHom (R := ℚ_[p]) (A := L)) y E).symm
    have h2 : y ^ E = fun i => ((p : ℚ_[p]) ^ N i) • u i := funext fun i => by rw [Pi.pow_apply, hyE i]
    rw [h1, h2, MultilinearMap.map_smul_univ, smul_smul, prod_zpow_eq_zpow_sum p _ _ hp0, ← zpow_natCast,
      ← zpow_mul, ← zpow_add₀ hp0]
  have hnonneg : 0 ≤ t * (E : ℤ) + ∑ i, N i := by
    have hcast : ((t * (E : ℤ) + ∑ i, N i : ℤ) : ℝ) = (E : ℝ) * ((t : ℝ) + ∑ i, (n i : ℝ) / (R i).e) := by
      push_cast
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        have he : ((R i).e : ℝ) ≠ 0 := by exact_mod_cast (R i).e_pos.ne'
        have hEcast : (E : ℝ) = (R i).e * (M i : ℝ) := by exact_mod_cast (hM i).symm
        simp only [hNdef]; push_cast; rw [hEcast]; field_simp
    have : (0 : ℝ) ≤ ((t * (E : ℤ) + ∑ i, N i : ℤ) : ℝ) := by
      rw [hcast]; exact mul_nonneg (Nat.cast_nonneg E) hsum
    exact_mod_cast this
  have hint : IsIntegral ℤ_[p] ((((p : ℚ_[p]) ^ t) • tprod ℚ_[p] y) ^ E) := by
    rw [hpow]
    obtain ⟨s, hs⟩ := Int.eq_ofNat_of_zero_le hnonneg
    rw [hs, zpow_natCast]
    have hsmul : ((p : ℚ_[p]) ^ s) • tprod ℚ_[p] u = ((p : ℤ_[p]) ^ s) • tprod ℚ_[p] u := by
      rw [← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ s)]
      simp
    rw [hsmul]
    exact (isIntegral_tprod u fun i => isIntegral_of_norm_le_one (hnormu i).le).smul _
  exact IsIntegral.of_pow hEpos hint

end Packet

section Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L B : ι → Type*}
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)] [∀ i, CompleteSpace (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]
  [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, Algebra ℤ_[p] (B i)] [∀ i, Algebra (B i) (L i)]
  [∀ i, IsScalarTower ℤ_[p] (B i) (L i)] [∀ i, IsIntegralClosure (B i) ℤ_[p] (L i)]
  [∀ i, IsDedekindDomain (B i)] [∀ i, IsFractionRing (B i) (L i)] [∀ i, Module.IsTorsionFree ℤ_[p] (B i)]
  [∀ i, Module.Free ℤ_[p] (B i)] [∀ i, Module.Finite ℤ_[p] (B i)]
  [∀ i, IsLocalization (Algebra.algebraMapSubmonoid (B i) (nonZeroDivisors ℤ_[p])) (L i)]

variable (B) in

structure DifferentData (R : ∀ i, RamificationData p (L i)) where
  δ : ∀ i, B i
  mem : ∀ i, δ i ∈ differentIdeal ℤ_[p] (B i)
  D : ι → ℕ
  norm_eq : ∀ i, ‖algebraMap (B i) (L i) (δ i)‖ = ‖(R i).pi‖ ^ D i

noncomputable def dI {R : ∀ i, RamificationData p (L i)} (Δ : DifferentData p B R) : ℝ :=
  ∑ i, (Δ.D i : ℝ) / (R i).e

noncomputable def aI (R : ∀ i, RamificationData p (L i)) : ℝ := ∑ i, aExp p (R i).e

noncomputable def bI (R : ∀ i, RamificationData p (L i)) : ℝ := ∑ i, bExp p (R i).e

noncomputable def piAt (R : ∀ i, RamificationData p (L i)) (i₀ : ι) (k : ℤ) : ⨂[ℚ_[p]] i, L i :=
  tprod ℚ_[p] (Pi.mulSingle i₀ ((R i₀).pi ^ k))

noncomputable def piA (R : ∀ i, RamificationData p (L i)) : ⨂[ℚ_[p]] i, L i :=
  tprod ℚ_[p] (fun i => (R i).pi ^ aNum p (R i).e)

noncomputable def piNegB (R : ∀ i, RamificationData p (L i)) : ⨂[ℚ_[p]] i, L i :=
  tprod ℚ_[p] (fun i => (R i).pi ^ (-bNum p (R i).e))

omit [∀ i, IsDomain (B i)] [∀ i, Algebra ℤ_[p] (B i)] [∀ i, Algebra (B i) (L i)]
  [∀ i, IsScalarTower ℤ_[p] (B i) (L i)] [∀ i, IsIntegralClosure (B i) ℤ_[p] (L i)] [∀ i, IsDedekindDomain (B i)]
  [∀ i, IsFractionRing (B i) (L i)] [∀ i, Module.IsTorsionFree ℤ_[p] (B i)] [∀ i, Module.Free ℤ_[p] (B i)]
  [∀ i, Module.Finite ℤ_[p] (B i)] [∀ i, CommRing (B i)]
  [∀ i, IsLocalization (Algebra.algebraMapSubmonoid (B i) (nonZeroDivisors ℤ_[p])) (L i)] in

theorem piA_mul_mem_logUnits (R : ∀ i, RamificationData p (L i)) (v : ⨂[ℚ_[p]] i, L i)
    (hv : v ∈ packetOrder ℤ_[p] ℚ_[p] L) : piA p R * v ∈ logUnits p L := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, rfl⟩ := hw
    rw [piA, tprod_mul_tprod]
    exact Submodule.subset_span ⟨_, fun i => zpow_mul_mem_logUnits p (R i) (y i)
      (norm_le_one_of_isIntegral (hy i)), rfl⟩
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem prop12ii_first (R : ∀ i, RamificationData p (L i)) (Δ : DifferentData p B R) (i₀ : ι) (k : ℤ)
    (φ : (⨂[ℚ_[p]] i, L i) →ₗ[ℚ_[p]] (⨂[ℚ_[p]] i, L i)) (hφ : ∀ w ∈ logUnits p L, φ w ∈ logUnits p L)
    (z : ⨂[ℚ_[p]] i, L i) (hz : IsIntegral ℤ_[p] z) :
    ∃ w ∈ logUnits p L, φ (piAt p R i₀ k * z) =
      ((p : ℚ_[p]) ^ ⌊(k : ℝ) / (R i₀).e - dI p Δ - aI p R⌋) • w := by
  classical
  set m := ⌊(k : ℝ) / (R i₀).e - dI p Δ - aI p R⌋ with hm
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set c : ∀ i, L i := fun i => Pi.mulSingle i₀ ((R i₀).pi ^ k) i * (algebraMap (B i) (L i) (Δ.δ i))⁻¹ *
    (R i).pi ^ (-aNum p (R i).e) with hc
  set n : ι → ℤ := fun i => (if i = i₀ then k else 0) - Δ.D i - aNum p (R i).e with hn
  have hsingle : ∀ i, ‖Pi.mulSingle i₀ ((R i₀).pi ^ k) i‖ = ‖(R i).pi‖ ^ (if i = i₀ then k else 0) := by
    intro i
    by_cases h : i = i₀
    · subst h; simp
    · simp [h]
  have hcnorm : ∀ i, ‖c i‖ = ‖(R i).pi‖ ^ n i := by
    intro i
    have hπ : ‖(R i).pi‖ ≠ 0 := norm_ne_zero_iff.mpr (pi_ne_zero p (R i))
    simp only [hc, hn, norm_mul, norm_inv, norm_zpow, hsingle i, Δ.norm_eq i]
    rw [zpow_sub₀ hπ, zpow_sub₀ hπ, zpow_neg, zpow_natCast, div_eq_mul_inv, div_eq_mul_inv]
  have hsn : ∑ i, (n i : ℝ) / (R i).e = (k : ℝ) / (R i₀).e - dI p Δ - aI p R := by
    have hterm : ∀ i, (n i : ℝ) / (R i).e =
        (if i = i₀ then (k : ℝ) else 0) / (R i).e - (Δ.D i : ℝ) / (R i).e - aExp p (R i).e := by
      intro i
      have he : ((R i).e : ℝ) ≠ 0 := by exact_mod_cast (R i).e_pos.ne'
      have ha := aNum_eq p (R i).e (R i).e_pos
      simp only [hn]
      split_ifs <;> push_cast <;> rw [ha] <;> field_simp <;> ring
    have hk : ∑ i, (if i = i₀ then (k : ℝ) else 0) / (R i).e = (k : ℝ) / (R i₀).e := by
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ i₀) h
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib, Finset.sum_sub_distrib, hk]
    rfl
  have hsum : 0 ≤ ((-m : ℤ) : ℝ) + ∑ i, (n i : ℝ) / (R i).e := by
    have hfl := Int.floor_le ((k : ℝ) / (R i₀).e - dI p Δ - aI p R)
    rw [hsn]; push_cast; linarith
  have hcint := isIntegral_zpow_smul_tprod p R c n hcnorm (-m) hsum
  set z' := (((p : ℚ_[p]) ^ (-m)) • tprod ℚ_[p] c) * z with hz'def
  have hz' : IsIntegral ℤ_[p] z' := hcint.mul hz
  have hv := prop11_all_factors (O := ℤ_[p]) (K := ℚ_[p]) (L := L) (B := B) Δ.δ Δ.mem z' hz'
  have hw := piA_mul_mem_logUnits p R _ hv
  refine ⟨_, hφ _ hw, ?_⟩
  rw [← LinearMap.map_smul]
  congr 1
  rw [hz'def, smul_mul_assoc, mul_smul_comm, mul_smul_comm, smul_smul, ← zpow_add₀ hp0, add_neg_cancel,
    zpow_zero, one_smul, ← mul_assoc, ← mul_assoc, piA, tprod_mul_tprod, tprod_mul_tprod, piAt]
  congr 2
  funext i
  simp only [hc, Pi.mul_apply]
  have hδ : algebraMap (B i) (L i) (Δ.δ i) ≠ 0 := by
    intro h
    have h1 := Δ.norm_eq i
    rw [h, norm_zero] at h1
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (pi_ne_zero p (R i))) h1.symm
  have hπ : (R i).pi ^ aNum p (R i).e ≠ 0 := zpow_ne_zero _ (pi_ne_zero p (R i))
  rw [zpow_neg]
  have hre : (R i).pi ^ aNum p (R i).e * algebraMap (B i) (L i) (Δ.δ i) *
      (Pi.mulSingle i₀ ((R i₀).pi ^ k) i * (algebraMap (B i) (L i) (Δ.δ i))⁻¹ * ((R i).pi ^ aNum p (R i).e)⁻¹) =
      Pi.mulSingle i₀ ((R i₀).pi ^ k) i * ((R i).pi ^ aNum p (R i).e * ((R i).pi ^ aNum p (R i).e)⁻¹) *
        (algebraMap (B i) (L i) (Δ.δ i) * (algebraMap (B i) (L i) (Δ.δ i))⁻¹) := by ring
  rw [hre, mul_inv_cancel₀ hπ, mul_inv_cancel₀ hδ, mul_one, mul_one]

omit [∀ i, IsDomain (B i)] [∀ i, Algebra ℤ_[p] (B i)] [∀ i, Algebra (B i) (L i)]
  [∀ i, IsScalarTower ℤ_[p] (B i) (L i)] [∀ i, IsIntegralClosure (B i) ℤ_[p] (L i)] [∀ i, IsDedekindDomain (B i)]
  [∀ i, IsFractionRing (B i) (L i)] [∀ i, Module.IsTorsionFree ℤ_[p] (B i)] [∀ i, Module.Free ℤ_[p] (B i)]
  [∀ i, Module.Finite ℤ_[p] (B i)] [∀ i, CommRing (B i)]
  [∀ i, IsLocalization (Algebra.algebraMapSubmonoid (B i) (nonZeroDivisors ℤ_[p])) (L i)] in

theorem prop12ii_second (R : ∀ i, RamificationData p (L i)) (w : ⨂[ℚ_[p]] i, L i) (hw : w ∈ logUnits p L) :
    ∃ v, IsIntegral ℤ_[p] v ∧ w = piNegB p R * v := by
  classical
  let S : Submodule ℤ_[p] (⨂[ℚ_[p]] i, L i) :=
    (Subalgebra.toSubmodule (integralClosure ℤ_[p] (⨂[ℚ_[p]] i, L i))).map
      (LinearMap.mulLeft ℤ_[p] (piNegB p R))
  have hle : logUnits p L ≤ S := by
    rw [logUnits, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨tprod ℚ_[p] (fun i => (R i).pi ^ bNum p (R i).e * y i), ?_, ?_⟩
    · exact isIntegral_tprod _ fun i => zpow_mul_isIntegral_of_mem_logUnits p (R i) (y i) (hy i)
    · simp only [LinearMap.mulLeft_apply, piNegB, tprod_mul_tprod]
      congr 1
      funext i
      simp only [Pi.mul_apply]
      rw [← mul_assoc, ← zpow_add₀ (pi_ne_zero p (R i)), neg_add_cancel, zpow_zero, one_mul]
  obtain ⟨v, hv, rfl⟩ := hle hw
  exact ⟨v, hv, rfl⟩

theorem prop12ii (R : ∀ i, RamificationData p (L i)) (Δ : DifferentData p B R) (i₀ : ι) (k : ℤ)
    (φ : (⨂[ℚ_[p]] i, L i) →ₗ[ℚ_[p]] (⨂[ℚ_[p]] i, L i)) (hφ : ∀ w ∈ logUnits p L, φ w ∈ logUnits p L)
    (z : ⨂[ℚ_[p]] i, L i) (hz : IsIntegral ℤ_[p] z) :
    (∃ w ∈ logUnits p L, φ (piAt p R i₀ k * z) =
      ((p : ℚ_[p]) ^ ⌊(k : ℝ) / (R i₀).e - dI p Δ - aI p R⌋) • w) ∧
    ∃ v, IsIntegral ℤ_[p] v ∧ φ (piAt p R i₀ k * z) =
      ((p : ℚ_[p]) ^ ⌊(k : ℝ) / (R i₀).e - dI p Δ - aI p R⌋) • (piNegB p R * v) := by
  obtain ⟨w, hw, heq⟩ := prop12ii_first p R Δ i₀ k φ hφ z hz
  obtain ⟨v, hv, rfl⟩ := prop12ii_second p R w hw
  exact ⟨⟨_, hw, heq⟩, v, hv, heq⟩

theorem prop12ii_particular (R : ∀ i, RamificationData p (L i)) (Δ : DifferentData p B R)
    (φ : (⨂[ℚ_[p]] i, L i) →ₗ[ℚ_[p]] (⨂[ℚ_[p]] i, L i)) (hφ : ∀ w ∈ logUnits p L, φ w ∈ logUnits p L)
    [Nonempty ι] (z : ⨂[ℚ_[p]] i, L i) (hz : IsIntegral ℤ_[p] z) :
    ∃ w ∈ logUnits p L, φ z = ((p : ℚ_[p]) ^ (-⌈dI p Δ + aI p R⌉)) • w := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨w, hw, heq⟩ := prop12ii_first p R Δ i₀ 0 φ hφ z hz
  refine ⟨w, hw, ?_⟩
  have h1 : piAt p R i₀ 0 = 1 := by
    rw [piAt, zpow_zero, Pi.mulSingle_one]
    rfl
  rw [h1, one_mul] at heq
  rw [heq]
  congr 2
  rw [Int.cast_zero, zero_div, zero_sub, sub_eq_add_neg, ← neg_add, Int.floor_neg]

end Main

section Model

variable (p : ℕ) [hp : Fact p.Prime]

theorem exists_qpDifferentData :
    Nonempty (DifferentData p (fun _ : Fin 2 => ℤ_[p]) (fun _ : Fin 2 => qpRamification p)) := by
  obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (differentIdeal_ne_bot (A := ℤ_[p]) (B := ℤ_[p]))
  refine ⟨⟨fun _ => δ, fun _ => hδ, fun _ => δ.valuation, fun _ => ?_⟩⟩
  change ‖algebraMap ℤ_[p] ℚ_[p] δ‖ = ‖(p : ℚ_[p])‖ ^ δ.valuation
  rw [PadicInt.algebraMap_apply, ← PadicInt.norm_def, PadicInt.norm_eq_zpow_neg_valuation hδ0, Padic.norm_p,
    inv_pow, zpow_neg, zpow_natCast]

theorem model_prop12ii (z : ⨂[ℚ_[p]] _ : Fin 2, ℚ_[p]) (hz : IsIntegral ℤ_[p] z) (k : ℤ) :
    ∃ Δ : DifferentData p (fun _ : Fin 2 => ℤ_[p]) (fun _ : Fin 2 => qpRamification p),
      ∃ v, IsIntegral ℤ_[p] v ∧ piAt p (fun _ => qpRamification p) 0 k * z =
        ((p : ℚ_[p]) ^ ⌊(k : ℝ) / (qpRamification p).e - dI p Δ - aI p (fun _ : Fin 2 => qpRamification p)⌋) •
          (piNegB p (fun _ : Fin 2 => qpRamification p) * v) := by
  obtain ⟨Δ⟩ := exists_qpDifferentData p
  obtain ⟨_, v, hv, heq⟩ := prop12ii p (L := fun _ : Fin 2 => ℚ_[p]) (B := fun _ : Fin 2 => ℤ_[p])
    (fun _ => qpRamification p) Δ 0 k LinearMap.id (fun w hw => hw) z hz
  exact ⟨Δ, v, hv, heq⟩

theorem model_logUnits_nonzero :
    tprod ℚ_[p] (fun _ : Fin 2 => ((p : ℚ_[p]) ^ 2)) ∈ logUnits p (fun _ : Fin 2 => ℚ_[p]) ∧
      tprod ℚ_[p] (fun _ : Fin 2 => ((p : ℚ_[p]) ^ 2)) ≠ 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have ha : aExp p 1 ≤ 2 := by
    unfold aExp
    split_ifs with h2
    · exact le_refl _
    · have hp3 : (3 : ℝ) ≤ p := by
        have := hp.out.two_le
        have : 3 ≤ p := by omega
        exact_mod_cast this
      have hceil : ⌈((1 : ℕ) : ℝ) / ((p : ℝ) - 2)⌉ ≤ 1 := by
        rw [Int.ceil_le]
        push_cast
        rw [div_le_one (by linarith)]
        linarith
      have : ((⌈((1 : ℕ) : ℝ) / ((p : ℝ) - 2)⌉ : ℤ) : ℝ) ≤ 1 := by exact_mod_cast hceil
      simp only [Nat.cast_one, div_one, one_mul] at this ⊢
      linarith
  have hmem : (p : ℚ_[p]) ^ 2 ∈ logUnitsSet p ℚ_[p] := by
    apply lower_inclusion p 1 one_pos
    rw [mem_closedBall_zero_iff, norm_pow, Padic.norm_p, ← Real.rpow_natCast, Real.inv_rpow (by linarith),
      ← Real.rpow_neg (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by push_cast; linarith)
  refine ⟨Submodule.subset_span ⟨_, fun _ => hmem, rfl⟩, ?_⟩
  intro h
  have h1 := congrArg (PiTensorProduct.constantBaseRingEquiv (Fin 2) ℚ_[p]) h
  rw [PiTensorProduct.constantBaseRingEquiv_tprod, map_zero, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at h1
  exact pow_ne_zero 2 (pow_ne_zero 2 (by exact_mod_cast hp.out.ne_zero : (p : ℚ_[p]) ≠ 0)) h1

end Model

end Src.IUT4.Proposition12ii

section Check
open Src.IUT4.Proposition12ii
end Check
