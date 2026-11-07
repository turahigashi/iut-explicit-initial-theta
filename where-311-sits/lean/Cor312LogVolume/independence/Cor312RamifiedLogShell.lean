import Cor312LogVolume.independence.Cor312RamifiedBadPlace
import Cor312LogVolume.independence.Cor312CitedTheoryFamily

set_option autoImplicit false
noncomputable section

namespace CitedLV.Independence.Cor312RamifiedLogShell

open MeasureTheory Topology
open Src.IUT3.Theorem311
open CitedLV.Theorem311 CitedLV.Theorem311.TensorIntegralLattice
open CitedLV.Theorem311.TensorFactorHaarCharacter
open CitedLV.Theorem311.TensorNormalizationPrincipal
open CitedLV.Theorem311.PadicNormedRamification
open CitedLV.Theorem311.PadicNormDifferent
open CitedLV.Theorem311.PadicNormIntegerRing
open CitedLV.ActualTensorHaarBound CitedLV.ActualTensorHaarNumericalBound
open CitedLV.LogShellAmbientExtension CitedLV.LogShellTensorAction
open CitedLV.ThetaLink.GaussianThetaHorizontalVerticalHull
open CitedLV.ThetaLink.GaussianThetaVerticalShellBound
open CitedLV.ThetaLink.GaussianMonoidFromThetaValues
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Independence.Cor312Cited
open CitedLV.Independence.Cor312RamifiedBadPlace
open Src.EtTh.ThetaValueArithmetic
open Src.IUT4.Proposition12i Src.IUT4.Proposition12ii Src.IUT4.Proposition14i
open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section General

variable (p : ℕ) [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Lf : ι → Type*)
  [∀ i, NormedField (Lf i)] [∀ i, NormedAlgebra ℚ_[p] (Lf i)]
  [∀ i, IsUltrametricDist (Lf i)] [∀ i, FiniteDimensional ℚ_[p] (Lf i)]
  [∀ i, CompleteSpace (Lf i)] [∀ i, ProperSpace (Lf i)]
  [∀ i, Algebra ℤ_[p] (Lf i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (Lf i)]

abbrev T := ⨂[ℚ_[p]] i, Lf i

abbrev Adm (ψ : T p Lf ≃ₗ[ℚ_[p]] T p Lf) : Prop :=
  Src.IUT4.Theorem110.IsAdmissibleAut p Lf ψ

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℚ_[p] (Lf i)] [∀ i, ProperSpace (Lf i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (Lf i)] [(i : ι) → Algebra ℤ_[p] (Lf i)] in
theorem adm_refl : Adm p Lf (LinearEquiv.refl ℚ_[p] (T p Lf)) := fun _ => Iff.rfl

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℚ_[p] (Lf i)] [∀ i, ProperSpace (Lf i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (Lf i)] [(i : ι) → Algebra ℤ_[p] (Lf i)] in
theorem adm_trans {φ ψ : T p Lf ≃ₗ[ℚ_[p]] T p Lf} (hφ : Adm p Lf φ) (hψ : Adm p Lf ψ) :
    Adm p Lf (φ.trans ψ) := fun w => (hφ w).trans (hψ (φ w))

def shellMul (m : ℤ) : Set (T p Lf) :=
  (fun w => ((p : ℚ_[p]) ^ m) • w) '' (logUnits p Lf : Set (T p Lf))

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℚ_[p] (Lf i)] [∀ i, ProperSpace (Lf i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (Lf i)] [(i : ι) → Algebra ℤ_[p] (Lf i)] in
theorem shellMul_zero : shellMul p Lf 0 = (logUnits p Lf : Set (T p Lf)) := by
  unfold shellMul
  simp only [zpow_zero, one_smul, Set.image_id']

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℚ_[p] (Lf i)] [∀ i, ProperSpace (Lf i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (Lf i)] [(i : ι) → Algebra ℤ_[p] (Lf i)] in

theorem pow_smul_mem_logUnits (n : ℤ) (hn : 0 ≤ n) {w : T p Lf} (hw : w ∈ logUnits p Lf) :
    ((p : ℚ_[p]) ^ n) • w ∈ logUnits p Lf := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have h : ((p : ℚ_[p]) ^ (k : ℤ)) • w = ((p : ℤ_[p]) ^ k) • w := by
    rw [zpow_natCast, ← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ k) w]
    congr 1
  rw [h]
  exact Submodule.smul_mem _ _ hw

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℚ_[p] (Lf i)] [∀ i, ProperSpace (Lf i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (Lf i)] [(i : ι) → Algebra ℤ_[p] (Lf i)] in
theorem shellMul_mono {m m' : ℤ} (h : m' ≤ m) : shellMul p Lf m ⊆ shellMul p Lf m' := by
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨((p : ℚ_[p]) ^ (m - m')) • w, pow_smul_mem_logUnits p Lf _ (by omega) hw, ?_⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  show ((p : ℚ_[p]) ^ m') • (((p : ℚ_[p]) ^ (m - m')) • w) = ((p : ℚ_[p]) ^ m) • w
  rw [smul_smul, ← zpow_add₀ hp0]
  congr 2
  ring

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℚ_[p] (Lf i)] [∀ i, ProperSpace (Lf i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (Lf i)] [(i : ι) → Algebra ℤ_[p] (Lf i)] in
theorem shellMul_subset_logUnits {m : ℤ} (h : 0 ≤ m) :
    shellMul p Lf m ⊆ (logUnits p Lf : Set (T p Lf)) := by
  rw [← shellMul_zero p Lf]
  exact shellMul_mono p Lf h

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℚ_[p] (Lf i)] [∀ i, ProperSpace (Lf i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (Lf i)] [(i : ι) → Algebra ℤ_[p] (Lf i)] in

theorem adm_image_shellMul {ψ : T p Lf ≃ₗ[ℚ_[p]] T p Lf} (hψ : Adm p Lf ψ) (m : ℤ) :
    ψ '' shellMul p Lf m = shellMul p Lf m := by
  ext x
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨ψ w, (hψ w).mp hw, (ψ.map_smul _ w).symm⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨((p : ℚ_[p]) ^ m) • ψ.symm w,
      ⟨ψ.symm w, (hψ (ψ.symm w)).mpr (by rw [ψ.apply_symm_apply]; exact hw), rfl⟩, ?_⟩
    show ψ (((p : ℚ_[p]) ^ m) • ψ.symm w) = ((p : ℚ_[p]) ^ m) • w
    rw [ψ.map_smul, ψ.apply_symm_apply]

def c0 : ℤ := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (Lf i)) :=
    fun i => normIntegers_discreteValuationRing p (Lf i)
  exact ⌈bI p (fun i => finiteExtensionRamification p (Lf i))⌉ +
    ⌈dI p (actualDifferentData p Lf).val + aI p (fun i => finiteExtensionRamification p (Lf i))⌉

omit [∀ i, ProperSpace (Lf i)] in

theorem integral_mem_shellMul (i₀ : ι) {z : T p Lf} (hz : IsIntegral ℤ_[p] z) :
    letI : ∀ i, IsDiscreteValuationRing (Integers (Lf i)) :=
      fun i => normIntegers_discreteValuationRing p (Lf i)
    z ∈ shellMul p Lf (-⌈dI p (actualDifferentData p Lf).val +
      aI p (fun i => finiteExtensionRamification p (Lf i))⌉) := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (Lf i)) :=
    fun i => normIntegers_discreteValuationRing p (Lf i)
  obtain ⟨w, hw, heq⟩ := prop12ii_first p (fun i => finiteExtensionRamification p (Lf i))
    (actualDifferentData p Lf).val i₀ 0 LinearMap.id (fun w hw => hw) z hz
  have h1 : piAt p (fun i => finiteExtensionRamification p (Lf i)) i₀ 0 = 1 := by
    rw [piAt, zpow_zero, Pi.mulSingle_one]
    rfl
  rw [h1, one_mul, LinearMap.id_apply] at heq
  have hfl : ⌊((0 : ℤ) : ℝ) / ((finiteExtensionRamification p (Lf i₀)).e : ℝ) -
      dI p (actualDifferentData p Lf).val - aI p (fun i => finiteExtensionRamification p (Lf i))⌋ =
      -⌈dI p (actualDifferentData p Lf).val + aI p (fun i => finiteExtensionRamification p (Lf i))⌉ := by
    rw [← Int.floor_neg]
    congr 1
    push_cast
    ring
  refine ⟨w, hw, ?_⟩
  show ((p : ℚ_[p]) ^ _) • w = z
  rw [heq, hfl]

theorem boundRegion_subset_shellMul (i₀ : ι) (k : ℤ) :
    ((boundRegion p Lf i₀ k).val : Set (T p Lf)) ⊆
      shellMul p Lf (boundExponent p Lf i₀ k - c0 p Lf) := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (Lf i)) :=
    fun i => normIntegers_discreteValuationRing p (Lf i)
  rw [boundRegion_eq_candidate]
  rintro _ ⟨z, hz, rfl⟩
  have hz' : IsIntegral ℤ_[p] z := (mem_normalization p).mp hz
  rw [mulHom_apply]
  set R := fun i => finiteExtensionRamification p (Lf i) with hR
  set t : ℤ := ⌈bI p R⌉ with ht
  have hsum : ∑ i, (((-bNum p (R i).e : ℤ) : ℝ) / (R i).e) = -bI p R := by
    unfold bI
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have he : ((R i).e : ℝ) ≠ 0 := by exact_mod_cast (R i).e_pos.ne'
    push_cast
    rw [bNum_eq p (R i).e (R i).e_pos]
    field_simp
  have hu : IsIntegral ℤ_[p] (((p : ℚ_[p]) ^ t) • piNegB p R) := by
    unfold piNegB
    refine isIntegral_zpow_smul_tprod p R (fun i => (R i).pi ^ (-bNum p (R i).e))
      (fun i => -bNum p (R i).e) (fun i => norm_zpow _ _) _ ?_
    rw [hsum]
    have := Int.le_ceil (bI p R)
    linarith
  have hv : IsIntegral ℤ_[p] ((((p : ℚ_[p]) ^ t) • piNegB p R) * z) := hu.mul hz'
  obtain ⟨w, hw, hweq⟩ := integral_mem_shellMul p Lf i₀ hv
  refine ⟨w, hw, ?_⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hc0 : c0 p Lf = t + ⌈dI p (actualDifferentData p Lf).val + aI p R⌉ := rfl
  have hweq' : (((p : ℚ_[p]) ^ t) • piNegB p R) * z =
      ((p : ℚ_[p]) ^ (-⌈dI p (actualDifferentData p Lf).val + aI p R⌉)) • w := hweq.symm
  show ((p : ℚ_[p]) ^ (boundExponent p Lf i₀ k - c0 p Lf)) • w =
    (((p : ℚ_[p]) ^ boundExponent p Lf i₀ k) • piNegB p R) * z
  have key : (((p : ℚ_[p]) ^ boundExponent p Lf i₀ k) • piNegB p R) * z =
      ((p : ℚ_[p]) ^ (boundExponent p Lf i₀ k - t)) • ((((p : ℚ_[p]) ^ t) • piNegB p R) * z) := by
    rw [smul_mul_assoc, smul_mul_assoc, smul_smul, ← zpow_add₀ hp0]
    congr 2
    ring
  rw [key, hweq', smul_smul, ← zpow_add₀ hp0, hc0]
  congr 2
  ring

omit [∀ i, ProperSpace (Lf i)] in

theorem shellMul_subset_unit (m : ℤ) :
    shellMul p Lf m ⊆ ((normalization p Lf).map (mulHom p Lf
      (((p : ℚ_[p]) ^ m) • piNegB p (fun i => finiteExtensionRamification p (Lf i)))) :
        Set (T p Lf)) := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨v, hv, rfl⟩ := prop12ii_second p (fun i => finiteExtensionRamification p (Lf i)) w hw
  refine ⟨v, (mem_normalization p).mpr hv, ?_⟩
  rw [mulHom_apply, smul_mul_assoc]

omit [DecidableEq ι] [∀ i, CompleteSpace (Lf i)] [∀ i, ProperSpace (Lf i)] in

theorem boundExponent_shift (i₀ : ι) (k c : ℤ) :
    boundExponent p Lf i₀ (k - (finiteExtensionRamification p (Lf i₀)).e * c) =
      boundExponent p Lf i₀ k - c := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (Lf i)) :=
    fun i => normIntegers_discreteValuationRing p (Lf i)
  have he : ((finiteExtensionRamification p (Lf i₀)).e : ℝ) ≠ 0 := by
    exact_mod_cast (finiteExtensionRamification p (Lf i₀)).e_pos.ne'
  change ⌊(((k - (finiteExtensionRamification p (Lf i₀)).e * c : ℤ) : ℝ)) /
      (finiteExtensionRamification p (Lf i₀)).e - dI p (actualDifferentData p Lf).val -
        aI p (fun i => finiteExtensionRamification p (Lf i))⌋ =
    ⌊(k : ℝ) / (finiteExtensionRamification p (Lf i₀)).e - dI p (actualDifferentData p Lf).val -
        aI p (fun i => finiteExtensionRamification p (Lf i))⌋ - c
  rw [← Int.floor_sub_intCast]
  congr 1
  push_cast
  field_simp
  ring

omit [∀ i, ProperSpace (Lf i)] in

theorem pow_smul_integral_mem_logUnits (i₀ : ι) {z : T p Lf} (hz : IsIntegral ℤ_[p] z) :
    letI : ∀ i, IsDiscreteValuationRing (Integers (Lf i)) :=
      fun i => normIntegers_discreteValuationRing p (Lf i)
    ((p : ℚ_[p]) ^ ⌈dI p (actualDifferentData p Lf).val +
      aI p (fun i => finiteExtensionRamification p (Lf i))⌉) • z ∈ logUnits p Lf := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (Lf i)) :=
    fun i => normIntegers_discreteValuationRing p (Lf i)
  obtain ⟨w, hw, heq⟩ := integral_mem_shellMul p Lf i₀ hz
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have heq' : z = ((p : ℚ_[p]) ^ (-⌈dI p (actualDifferentData p Lf).val +
      aI p (fun i => finiteExtensionRamification p (Lf i))⌉)) • w := heq.symm
  rw [heq', smul_smul, ← zpow_add₀ hp0, add_neg_cancel, zpow_zero, one_smul]
  exact hw

def logUnitsP : Set (Packet p Lf) := (logUnits p Lf : Set (T p Lf))

def logUnitsAG : AddSubgroup (Packet p Lf) where
  carrier := logUnitsP p Lf
  add_mem' ha hb := (logUnits p Lf).add_mem ha hb
  zero_mem' := (logUnits p Lf).zero_mem
  neg_mem' ha := (logUnits p Lf).neg_mem ha

omit [∀ i, ProperSpace (Lf i)] in
theorem logUnits_mem_nhds (i₀ : ι) : logUnitsP p Lf ∈ 𝓝 (0 : Packet p Lf) := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (Lf i)) :=
    fun i => normIntegers_discreteValuationRing p (Lf i)
  set c : ℚ_[p] := (p : ℚ_[p]) ^ ⌈dI p (actualDifferentData p Lf).val +
      aI p (fun i => finiteExtensionRamification p (Lf i))⌉ with hc
  have hc0 : c ≠ 0 := zpow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hopen : IsOpen ((fun z : Packet p Lf => c • z) '' (integralAnchor p Lf).val) :=
    (Homeomorph.smulOfNeZero c hc0).isOpenMap _ (integralAnchor p Lf).2.1.2
  have h0 : (0 : Packet p Lf) ∈ (fun z : Packet p Lf => c • z) '' (integralAnchor p Lf).val :=
    ⟨0, (integralLattice p Lf).zero_mem, smul_zero c⟩
  refine Filter.mem_of_superset (hopen.mem_nhds h0) ?_
  rintro _ ⟨z, hz, rfl⟩
  change IsIntegral ℤ_[p] z at hz
  exact pow_smul_integral_mem_logUnits p Lf i₀ hz

omit [∀ i, ProperSpace (Lf i)] in
theorem logUnits_isOpen (i₀ : ι) : IsOpen (logUnitsP p Lf) :=
  (logUnitsAG p Lf).isOpen_of_mem_nhds (logUnits_mem_nhds p Lf i₀)

omit [∀ i, ProperSpace (Lf i)] in
theorem logUnits_subset_image :
    logUnitsP p Lf ⊆ (fun v => Mul.mul (α := Packet p Lf)
      (piNegB p (fun i => finiteExtensionRamification p (Lf i))) v) '' (integralAnchor p Lf).val := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := prop12ii_second p (fun i => finiteExtensionRamification p (Lf i)) w hw
  exact ⟨v, hv, rfl⟩

omit [∀ i, ProperSpace (Lf i)] in
theorem logUnits_isCompact (i₀ : ι) : IsCompact (logUnitsP p Lf) := by
  have hcont : Continuous (fun v => Mul.mul (α := Packet p Lf)
      (piNegB p (fun i => finiteExtensionRamification p (Lf i))) v) :=
    (LinearMap.mulLeft ℚ_[p] (show Packet p Lf from
      piNegB p (fun i => finiteExtensionRamification p (Lf i)))).continuous_of_finiteDimensional
  have hclosed : IsClosed (logUnitsP p Lf) :=
    (logUnitsAG p Lf).isClosed_of_isOpen (logUnits_isOpen p Lf i₀)
  exact ((integralAnchor p Lf).2.1.1.image hcont).of_isClosed_subset hclosed
    (logUnits_subset_image p Lf)

omit [∀ i, ProperSpace (Lf i)] in
theorem logUnits_interior_nonempty (i₀ : ι) : (interior (logUnitsP p Lf)).Nonempty := by
  rw [(logUnits_isOpen p Lf i₀).interior_eq]
  exact ⟨0, (logUnits p Lf).zero_mem⟩

private theorem principal_of_bounded {A : Type*} [CommRing A]
    (O : Subring A) [IsPrincipalIdealRing O] (H : AddSubgroup A)
    (hstable : ∀ (r : O) (x : A), x ∈ H → (r : A) * x ∈ H)
    (b : Aˣ) (hbound : ∀ x ∈ H, ∃ z : O, (b : A) * z = x)
    (a : Aˣ) (ha : (a : A) ∈ H) :
    ∃ c : Aˣ, ∀ x : A, x ∈ H ↔ ∃ z : O, (c : A) * z = x := by
  let I : Ideal O :=
    { carrier := {z | (b : A) * z ∈ H}
      zero_mem' := by change (b : A) * 0 ∈ H; simp
      add_mem' := by
        intro x y hx hy
        change (b : A) * ((x + y : O) : A) ∈ H
        simpa only [Subring.coe_add, mul_add] using H.add_mem hx hy
      smul_mem' := by
        intro r x hx
        change (b : A) * ((r : A) * (x : A)) ∈ H
        simpa only [mul_left_comm] using hstable r ((b : A) * x) hx }
  let g := Submodule.IsPrincipal.generator I
  have hg : (b : A) * (g : A) ∈ H := Submodule.IsPrincipal.generator_mem I
  have hrepr : ∀ x : A, x ∈ H ↔ ∃ z : O, ((b : A) * (g : A)) * z = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := hbound x hx
      have hzI : z ∈ I := by change (b : A) * z ∈ H; rwa [hz]
      obtain ⟨t, ht⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hzI
      refine ⟨t, ?_⟩
      rw [ht] at hz
      change (b : A) * ((t : A) * (g : A)) = x at hz
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hz
    · rintro ⟨z, rfl⟩
      simpa only [mul_comm] using hstable z ((b : A) * (g : A)) hg
  obtain ⟨z, hz⟩ := (hrepr a).mp ha
  have hc : IsUnit ((b : A) * (g : A)) :=
    isUnit_of_mul_isUnit_left (hz.symm ▸ a.isUnit)
  exact ⟨hc.unit, fun x => by simpa only [hc.unit_spec] using hrepr x⟩

omit [∀ i, CompleteSpace (Lf i)] [∀ i, ProperSpace (Lf i)] in

theorem lambdaIntersection_principal' (P : Set (Packet p Lf)) (b : Packet p Lf) (hb : IsUnit b)
    (hPb : P ⊆ ((normalization p Lf).map (mulHom p Lf b) : Set (T p Lf)))
    (a : (Packet p Lf)ˣ) (ha : (a : Packet p Lf) ∈ P) :
    ∃ c : (Packet p Lf)ˣ,
      (lambdaIntersection p Lf P : Set (Packet p Lf)) =
        (unitRegion p Lf c (integralAnchor p Lf)).val := by
  let O := (integralClosure ℤ_[p] (Packet p Lf)).toSubring
  letI : IsPrincipalIdealRing O := packet_normalization_isPrincipalIdealRing p Lf
  let H := lambdaIntersection p Lf P
  have hs : ∀ (r : O) (x : Packet p Lf), x ∈ H → (r : Packet p Lf) * x ∈ H := by
    intro r x hx
    simp only [H, lambdaIntersection, AddSubgroup.mem_iInf] at hx ⊢
    intro c hc hPc
    obtain ⟨z, hz, heq⟩ := hx c hc hPc
    refine ⟨Mul.mul (α := Packet p Lf) (r : Packet p Lf) z, ?_, ?_⟩
    · exact (integralClosure ℤ_[p] (Packet p Lf)).mul_mem r.property hz
    · have hm : ∀ (c r w : Packet p Lf), c * (r * w) = r * (c * w) :=
        fun c r w => mul_left_comm c r w
      exact (hm c r z).trans (congrArg (fun y : Packet p Lf => (r : Packet p Lf) * y) heq)
  have hB : ∀ x ∈ H, ∃ z : O, (hb.unit : Packet p Lf) * z = x := by
    intro x hx
    simp only [H, lambdaIntersection, AddSubgroup.mem_iInf] at hx
    obtain ⟨z, hz, heq⟩ := hx b hb hPb
    refine ⟨⟨z, hz⟩, ?_⟩
    simpa only [hb.unit_spec] using heq
  obtain ⟨c, hc⟩ := principal_of_bounded O H hs hb.unit hB a
    (subset_lambdaIntersection p Lf P ha)
  refine ⟨c, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (hc x).mp hx
    exact ⟨z, z.property, hz⟩
  · rintro ⟨z, hz, heq⟩
    exact (hc x).mpr ⟨⟨z, hz⟩, heq⟩

omit [Fintype ι] [DecidableEq ι] [∀ i, IsUltrametricDist (Lf i)] [∀ i, FiniteDimensional ℚ_[p] (Lf i)] [∀ i, CompleteSpace (Lf i)] [∀ i, ProperSpace (Lf i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (Lf i)] [(i : ι) → Algebra ℤ_[p] (Lf i)] in

theorem lambdaIntersection_subset (P : Set (Packet p Lf)) (d : T p Lf) (hd : IsUnit d)
    (hPd : P ⊆ ((normalization p Lf).map (mulHom p Lf d) : Set (T p Lf))) :
    (lambdaIntersection p Lf P : Set (Packet p Lf)) ⊆
      ((normalization p Lf).map (mulHom p Lf d) : Set (T p Lf)) := by
  intro x hx
  simp only [lambdaIntersection, SetLike.mem_coe, AddSubgroup.mem_iInf] at hx
  exact hx d hd hPd

end General

section Actions

variable (p : ℕ) [Fact p.Prime]
variable (L : Type) [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
  [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]

def permLin (j : ℕ) (σ : Equiv.Perm (Fin (j + 1))) : T p (LL L j) ≃ₗ[ℚ_[p]] T p (LL L j) :=
  PiTensorProduct.reindex ℚ_[p] (LL L j) σ

omit [CompleteSpace L] [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem permLin_tprod (j : ℕ) (σ : Equiv.Perm (Fin (j + 1))) (y : (i : Fin (j + 1)) → LL L j i) :
    permLin p L j σ (PiTensorProduct.tprod ℚ_[p] y) =
      PiTensorProduct.tprod ℚ_[p] (s := LL L j) (fun i => y (σ.symm i)) :=
  PiTensorProduct.reindex_tprod σ y

omit [CompleteSpace L] [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem permLin_one (j : ℕ) (x : T p (LL L j)) : permLin p L j 1 x = x := by
  show PiTensorProduct.reindex ℚ_[p] (LL L j) (Equiv.refl _) x = x
  rw [PiTensorProduct.reindex_refl]
  rfl

omit [CompleteSpace L] [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem permLin_mul (j : ℕ) (σ τ : Equiv.Perm (Fin (j + 1))) (x : T p (LL L j)) :
    permLin p L j (σ * τ) x = permLin p L j σ (permLin p L j τ x) := by
  show PiTensorProduct.reindex ℚ_[p] (LL L j) (τ.trans σ) x = _
  rw [← PiTensorProduct.reindex_reindex]
  rfl

omit [FiniteDimensional ℚ_[p] L] [ProperSpace L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem permLin_mem (j : ℕ) (σ : Equiv.Perm (Fin (j + 1))) {w : T p (LL L j)}
    (hw : w ∈ logUnits p (LL L j)) : permLin p L j σ w ∈ logUnits p (LL L j) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, rfl⟩ := hw
    rw [permLin_tprod]
    exact Submodule.subset_span ⟨_, fun i => hy (σ.symm i), rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    change (permLin p L j σ).toLinearMap (a • x) ∈ _
    rw [(permLin p L j σ).toLinearMap.map_smul_of_tower a x]
    exact Submodule.smul_mem _ _ hx

omit [FiniteDimensional ℚ_[p] L] [ProperSpace L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in

theorem adm_permLin (j : ℕ) (σ : Equiv.Perm (Fin (j + 1))) : Adm p (LL L j) (permLin p L j σ) := by
  intro w
  refine ⟨permLin_mem p L j σ, fun h => ?_⟩
  have h2 := permLin_mem p L j σ⁻¹ h
  rwa [← permLin_mul, inv_mul_cancel, permLin_one] at h2

abbrev ShellAut : Type := logShellModule (K := L) p ≃ₗ[ℤ_[p]] logShellModule (K := L) p

def shellLin (j : ℕ) (g : Fin (j + 1) → ShellAut p L) : T p (LL L j) ≃ₗ[ℚ_[p]] T p (LL L j) :=
  tensorEquiv p (L := LL L j) g

omit [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem shellLin_tprod (j : ℕ) (g : Fin (j + 1) → ShellAut p L) (y : (i : Fin (j + 1)) → LL L j i) :
    shellLin p L j g (PiTensorProduct.tprod ℚ_[p] y) =
      PiTensorProduct.tprod ℚ_[p] (s := LL L j) (fun i => ambientAction p (g i) (y i)) := by
  unfold shellLin tensorEquiv
  exact PiTensorProduct.congr_tprod _ y

theorem adm_shellLin (j : ℕ) (g : Fin (j + 1) → ShellAut p L) :
    Adm p (LL L j) (shellLin p L j g) := by
  intro w
  refine ⟨tensorEquiv_mem_logUnits p g w, fun h => ?_⟩
  have h2 := tensorEquiv_symm_mem_logUnits p g _ h
  have h3 : (tensorEquiv p (L := LL L j) g).symm (shellLin p L j g w) = w :=
    (tensorEquiv p (L := LL L j) g).symm_apply_apply w
  rwa [h3] at h2

omit [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem shellLin_one_eq (j : ℕ) : shellLin p L j 1 = LinearEquiv.refl ℚ_[p] (T p (LL L j)) := by
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro y
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, shellLin_tprod, LinearEquiv.refl_apply]
  congr 1
  funext i
  rw [Pi.one_apply, map_one]
  rfl

omit [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem shellLin_mul_eq (j : ℕ) (g h : Fin (j + 1) → ShellAut p L) :
    shellLin p L j (g * h) = (shellLin p L j h).trans (shellLin p L j g) := by
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro y
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply, shellLin_tprod, shellLin_tprod, shellLin_tprod]
  congr 1
  funext i
  rw [Pi.mul_apply, map_mul]
  rfl

def toCAE {j : ℕ} (ψ : T p (LL L j) ≃ₗ[ℚ_[p]] T p (LL L j)) : PP p L j ≃ₜ+ PP p L j :=
  (show PP p L j ≃ₗ[ℚ_[p]] PP p L j from ψ).toContinuousLinearEquiv.toContinuousAddEquiv

omit [CompleteSpace L] [IsUltrametricDist L] [ProperSpace L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem toCAE_apply {j : ℕ} (ψ : T p (LL L j) ≃ₗ[ℚ_[p]] T p (LL L j)) (x : PP p L j) :
    toCAE p L ψ x = ψ x := rfl

omit [ProperSpace L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem preimage_logUnits {j : ℕ} {ψ : T p (LL L j) ≃ₗ[ℚ_[p]] T p (LL L j)} (hψ : Adm p (LL L j) ψ) :
    toCAE p L ψ ⁻¹' logUnitsP p (LL L j) = logUnitsP p (LL L j) :=
  Set.ext fun w => (hψ w).symm

end Actions

section System

variable (p : ℕ) [Fact p.Prime]
variable (L : Type) [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
  [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]

def logShellSystem : PacketSystem where
  lstar := 3
  lstar_pos := by norm_num
  PlaceQ := Unit
  IsArch := fun _ => False
  Above := fun _ => Unit
  Packet := fun _ j => PP p L j.val
  haar := fun _ j => normalizedAddHaar (anchor p L j.val)
  integral := fun _ j => logUnitsP p (LL L j.val)
  integral_isCompact := fun _ j => logUnits_isCompact p (LL L j.val) 0
  integral_interior_nonempty := fun _ j => logUnits_interior_nonempty p (LL L j.val) 0
  weight := fun _ j => 1 / (Module.finrank ℚ_[p] (PP p L j.val) : ℝ)
  weight_pos := fun _ j => one_div_pos.mpr (finrank_pos p L j.val)
  adjustment := fun _ j => 1 / (Module.finrank ℚ_[p] (PP p L j.val) : ℝ) *
    logVolume (normalizedAddHaar (anchor p L j.val)) (anchor p L j.val).val (logUnitsP p (LL L j.val))
  StripAut := fun _ _ => ShellAut p L
  Ism := fun _ _ => ShellAut p L
  ism_arch_order_two := fun _ h => absurd h id
  labelAct := fun _ j σ => toCAE p L (permLin p L j.val σ)
  stripAct := fun _ j g => toCAE p L (shellLin p L j.val (fun t => g t ()))
  ismAct := fun _ j g => toCAE p L (shellLin p L j.val (fun t => g t ()))
  labelAct_one := fun _ j => ContinuousAddEquiv.ext fun x => permLin_one p L j.val x
  labelAct_mul := fun _ j σ τ => ContinuousAddEquiv.ext fun x => permLin_mul p L j.val σ τ x
  stripAct_one := fun _ j => ContinuousAddEquiv.ext fun x => by
    show shellLin p L j.val 1 x = x
    rw [shellLin_one_eq]
    rfl
  stripAct_mul := fun _ j g h => ContinuousAddEquiv.ext fun x => by
    show shellLin p L j.val ((fun t => g t ()) * (fun t => h t ())) x = _
    rw [shellLin_mul_eq]
    rfl
  ismAct_one := fun _ j => ContinuousAddEquiv.ext fun x => by
    show shellLin p L j.val 1 x = x
    rw [shellLin_one_eq]
    rfl
  ismAct_mul := fun _ j g h => ContinuousAddEquiv.ext fun x => by
    show shellLin p L j.val ((fun t => g t ()) * (fun t => h t ())) x = _
    rw [shellLin_mul_eq]
    rfl
  labelAct_integral := fun _ j σ => preimage_logUnits p L (adm_permLin p L j.val σ)
  stripAct_integral := fun _ j g => preimage_logUnits p L (adm_shellLin p L j.val _)
  ismAct_integral := fun _ j g => preimage_logUnits p L (adm_shellLin p L j.val _)

theorem packetLogVolume_eq (vQ : Unit) (j : Fin 4) (A : Set (PP p L j.val)) :
    (logShellSystem p L).packetLogVolume vQ j A = (rampSystem p L).packetLogVolume vQ j A := by
  show 1 / (Module.finrank ℚ_[p] (PP p L j.val) : ℝ) *
        logVolume (normalizedAddHaar (anchor p L j.val)) (logUnitsP p (LL L j.val)) A +
      1 / (Module.finrank ℚ_[p] (PP p L j.val) : ℝ) *
        logVolume (normalizedAddHaar (anchor p L j.val)) (anchor p L j.val).val (logUnitsP p (LL L j.val)) =
    1 / (Module.finrank ℚ_[p] (PP p L j.val) : ℝ) *
        logVolume (normalizedAddHaar (anchor p L j.val)) (anchor p L j.val).val A + 0
  unfold logVolume
  ring

theorem procVol_eq_ramp (x : (logShellSystem p L).Regions) :
    (logShellSystem p L).procVol x = (rampSystem p L).procVol x := by
  unfold PacketSystem.procVol
  refine Finset.sum_congr rfl fun vQ _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun j _ => packetLogVolume_eq p L vQ j.succ _

end System

section Regions

variable (p : ℕ) [Fact p.Prime]
variable {L : Type} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
  [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]
variable (D : ThetaDatum L) (N : ℕ)

theorem unionSpec (j : ℕ) :
    ∃ k : ℤ, ‖(D.ξ (labOf j) : L)‖ ^ N = ‖(finiteExtensionRamification p L).pi‖ ^ k ∧
      horizontalVerticalImages p (KU L) j (ch j) 0 D.s D.i 7 (labOf j) N ⊆
        (boundRegion p (LL L j) 0 k).val :=
  gaussian_horizontal_vertical_union_subset_boundRegion p (KU L) j (ch j) 0 D.s D.i D.hi D.facts 7
    (by norm_num) D.ξ D.hξ (labOf j) N

def kθ (j : ℕ) : ℤ := (unionSpec p D N j).choose

theorem kθ_spec (j : ℕ) :
    ‖(D.ξ (labOf j) : L)‖ ^ N = ‖(finiteExtensionRamification p L).pi‖ ^ kθ p D N j :=
  (unionSpec p D N j).choose_spec.1

theorem images_subset_bound (j : ℕ) :
    horizontalVerticalImages p (KU L) j (ch j) 0 D.s D.i 7 (labOf j) N ⊆
      (boundRegion p (LL L j) 0 (kθ p D N j)).val :=
  (unionSpec p D N j).choose_spec.2

def mExp (j : ℕ) : ℤ := boundExponent p (LL L j) 0 (kθ p D N j) - c0 p (LL L j)

def contSet (j : ℕ) : Set (PP p L j) := shellMul p (LL L j) (mExp p D N j)

theorem images_subset_cont (j : ℕ) :
    horizontalVerticalImages p (KU L) j (ch j) 0 D.s D.i 7 (labOf j) N ⊆ contSet p D N j :=
  (images_subset_bound p D N j).trans (boundRegion_subset_shellMul p (LL L j) 0 (kθ p D N j))

theorem base_subset_cont (j : ℕ) {A : Set (PP p L j)} (hA : A ∈ baseSet p D N j) :
    A ⊆ contSet p D N j :=
  (base_subset_images p D N j hA).trans (images_subset_cont p D N j)

def bUnit (j : ℕ) : PP p L j :=
  ((p : ℚ_[p]) ^ mExp p D N j) • piNegB p (fun t => finiteExtensionRamification p (LL L j t))

theorem bUnit_isUnit (j : ℕ) : IsUnit (bUnit p D N j) :=
  Src.IUT4.Theorem110.isUnit_zpow_smul_piNegB p _ _

theorem cont_subset_b (j : ℕ) :
    contSet p D N j ⊆ ((normalization p (LL L j)).map (mulHom p (LL L j) (bUnit p D N j)) :
      Set (T p (LL L j))) :=
  shellMul_subset_unit p (LL L j) (mExp p D N j)

theorem thetaUnit_mem_cont (j : ℕ) :
    ((factorUnit p (LL L j) 0 (D.ξ (labOf j) ^ N) : (PP p L j)ˣ) : PP p L j) ∈ contSet p D N j := by
  apply base_subset_cont p D N j (theta_mem_base p D N j)
  refine ⟨1, ?_, ?_⟩
  · change IsIntegral ℤ_[p] (1 : PP p L j)
    exact isIntegral_one
  · show ((factorUnit p (LL L j) 0 (D.ξ (labOf j) ^ N) : (PP p L j)ˣ) : PP p L j) * 1 = _
    exact mul_one _

theorem hullSpec (j : ℕ) :
    ∃ c : (PP p L j)ˣ, (lambdaIntersection p (LL L j) (contSet p D N j) : Set (PP p L j)) =
      (unitRegion p (LL L j) c (anchor p L j)).val :=
  lambdaIntersection_principal' p (LL L j) (contSet p D N j) (bUnit p D N j) (bUnit_isUnit p D N j)
    (cont_subset_b p D N j) _ (thetaUnit_mem_cont p D N j)

def hullC (j : ℕ) : (PP p L j)ˣ := (hullSpec p D N j).choose

def hullReg (j : ℕ) : NormalizedHaarRegion (PP p L j) :=
  unitRegion p (LL L j) (hullC p D N j) (anchor p L j)

theorem hull_eq (j : ℕ) :
    (hullReg p D N j).val = (lambdaIntersection p (LL L j) (contSet p D N j) : Set (PP p L j)) :=
  (hullSpec p D N j).choose_spec.symm

theorem cont_subset_hull (j : ℕ) : contSet p D N j ⊆ (hullReg p D N j).val := by
  rw [hull_eq]
  exact subset_lambdaIntersection p (LL L j) _

def kB (j : ℕ) : ℤ := kθ p D N j - (finiteExtensionRamification p L).e * c0 p (LL L j)

theorem bE_kB (j : ℕ) : boundExponent p (LL L j) 0 (kB p D N j) = mExp p D N j :=
  boundExponent_shift p (LL L j) 0 (kθ p D N j) (c0 p (LL L j))

theorem hull_subset_boundB (j : ℕ) :
    (hullReg p D N j).val ⊆ (boundRegion p (LL L j) 0 (kB p D N j)).val := by
  rw [hull_eq, boundRegion_eq_candidate, bE_kB]
  exact lambdaIntersection_subset p (LL L j) _ _ (bUnit_isUnit p D N j) (cont_subset_b p D N j)

omit [CompleteSpace L] [ProperSpace L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in

theorem kqSpec : ∃ k : ℤ, ‖(D.r : L)‖ ^ N = ‖(finiteExtensionRamification p L).pi‖ ^ k := by
  obtain ⟨k, hk⟩ := (finiteExtensionRamification p L).valueGroup ((D.r ^ N : Lˣ) : L) (Units.ne_zero _)
  exact ⟨k, by rw [← hk, Units.val_pow_eq_pow_val, norm_pow]⟩

def kq : ℤ := (kqSpec p D N).choose

omit [CompleteSpace L] [ProperSpace L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem kq_spec : ‖(D.r : L)‖ ^ N = ‖(finiteExtensionRamification p L).pi‖ ^ kq p D N :=
  (kqSpec p D N).choose_spec

def BigL : Prop :=
  ∀ j : ℕ, j ≤ 3 →
    c0 p (LL L j) ≤ boundExponent p (LL L j) 0 (kθ p D N j) ∧
    2 * c0 p (LL L j) ≤ boundExponent p (LL L j) 0 (kθ p D N j) ∧
    c0 p (LL L j) ≤ boundExponent p (LL L j) 0 (kq p D N)

theorem cont_le_logUnits (hbig : BigL p D N) (j : ℕ) (hj : j ≤ 3) :
    contSet p D N j ⊆ logUnitsP p (LL L j) :=
  shellMul_subset_logUnits p (LL L j) (by unfold mExp; linarith [(hbig j hj).1])

theorem hull_le_logUnits (hbig : BigL p D N) (j : ℕ) (hj : j ≤ 3) :
    (hullReg p D N j).val ⊆ logUnitsP p (LL L j) :=
  (hull_subset_boundB p D N j).trans ((boundRegion_subset_shellMul p (LL L j) 0 (kB p D N j)).trans
    (shellMul_subset_logUnits p (LL L j) (by rw [bE_kB]; unfold mExp; linarith [(hbig j hj).2.1])))

theorem q_le_logUnits (hbig : BigL p D N) (j : ℕ) (hj : j ≤ 3) :
    (factorRegion p (LL L j) 0 (D.r ^ N) (anchor p L j)).val ⊆ logUnitsP p (LL L j) := by
  have hq : ‖((D.r ^ N : Lˣ) : L)‖ = ‖(finiteExtensionRamification p L).pi‖ ^ kq p D N := by
    rw [Units.val_pow_eq_pow_val, norm_pow]
    exact kq_spec p D N
  have h1 := horizontal_factorRegion_subset_boundRegion p (LL L j) 0 (D.r ^ N) (kq p D N) hq
    (LinearEquiv.refl ℚ_[p] _) (fun _ => Iff.rfl)
  intro x hx
  exact shellMul_subset_logUnits p (LL L j) (by linarith [(hbig j hj).2.2])
    (boundRegion_subset_shellMul p (LL L j) 0 (kq p D N) (h1 ⟨x, hx, rfl⟩))

def thetaL : (logShellSystem p L).Regions := fun _ j =>
  (factorRegion p (LL L j.val) 0 (D.ξ (labOf j.val) ^ N) (anchor p L j.val)).val

def qL : (logShellSystem p L).Regions := fun _ j =>
  (factorRegion p (LL L j.val) 0 (D.r ^ N) (anchor p L j.val)).val

def contL : (logShellSystem p L).Regions := fun _ j => contSet p D N j.val

def hullL : (logShellSystem p L).Regions := fun _ j => (hullReg p D N j.val).val

def possL : Set (logShellSystem p L).Regions :=
  {y | (∃ b : (logShellSystem p L).Regions, (∀ vQ j, b vQ j ∈ baseSet p D N j.val) ∧
      RegionLE (logShellSystem p L) b y) ∧ RegionLE (logShellSystem p L) y (contL p D N)}

theorem theta_le_cont : RegionLE (logShellSystem p L) (thetaL p D N) (contL p D N) := fun _ j =>
  base_subset_cont p D N j.val (theta_mem_base p D N j.val)

theorem theta_mem_possL : thetaL p D N ∈ possL p D N :=
  ⟨⟨thetaL p D N, fun _ j => theta_mem_base p D N j.val, fun _ _ => subset_rfl⟩, theta_le_cont p D N⟩

theorem cont_mem_possL : contL p D N ∈ possL p D N :=
  ⟨⟨thetaL p D N, fun _ j => theta_mem_base p D N j.val, theta_le_cont p D N⟩, fun _ _ => subset_rfl⟩

theorem possL_hasVolume {x : (logShellSystem p L).Regions} (hx : x ∈ possL p D N) :
    (logShellSystem p L).HasVolume x := by
  obtain ⟨⟨b, hb, hbx⟩, _⟩ := hx
  intro vQ j h0
  exact base_measure_ne_zero p D N j.val (hb vQ j) (measure_mono_null (hbx vQ j) h0)

omit [ProperSpace L] in

theorem image_base {j : ℕ} (f : PP p L j → PP p L j) (ψ : T p (LL L j) ≃ₗ[ℚ_[p]] T p (LL L j))
    (hψ : Adm p (LL L j) ψ) (hf : ∀ z, f z = ψ z) {A : Set (PP p L j)} (hA : A ∈ baseSet p D N j) :
    f '' A ∈ baseSet p D N j := by
  obtain ⟨η, hη, u, φ, hφ, rfl⟩ := hA
  let ψ' : PP p L j ≃ₗ[ℚ_[p]] PP p L j := ψ
  refine ⟨η, hη, u, φ.trans ψ', adm_trans p (LL L j) hφ hψ, ?_⟩
  rw [Set.image_image]
  apply Set.image_congr
  intro z _
  exact hf (φ z)

theorem image_cont {j : ℕ} (f : PP p L j → PP p L j) (ψ : T p (LL L j) ≃ₗ[ℚ_[p]] T p (LL L j))
    (hψ : Adm p (LL L j) ψ) (hf : ∀ z, f z = ψ z) : f '' contSet p D N j = contSet p D N j := by
  have h : f '' contSet p D N j = ψ '' contSet p D N j := Set.image_congr fun z _ => hf z
  rw [h]
  exact adm_image_shellMul p (LL L j) hψ _

theorem possL_image {x : (logShellSystem p L).Regions} (hx : x ∈ possL p D N)
    (f : ∀ _vQ (j : Fin ((logShellSystem p L).lstar + 1)), PP p L j.val → PP p L j.val)
    (hf : ∀ vQ (j : Fin ((logShellSystem p L).lstar + 1)),
      ∃ ψ : T p (LL L j.val) ≃ₗ[ℚ_[p]] T p (LL L j.val),
        Adm p (LL L j.val) ψ ∧ ∀ z : PP p L j.val, f vQ j z = ψ z) :
    (fun vQ j => f vQ j '' x vQ j) ∈ possL p D N := by
  obtain ⟨⟨b, hb, hbx⟩, hxc⟩ := hx
  refine ⟨⟨fun vQ j => f vQ j '' b vQ j, fun vQ j => ?_, fun vQ j => Set.image_mono (hbx vQ j)⟩,
    fun vQ j => ?_⟩
  · obtain ⟨ψ, hψ, hfψ⟩ := hf vQ j
    exact image_base p D N (f vQ j) ψ hψ hfψ (hb vQ j)
  · obtain ⟨ψ, hψ, hfψ⟩ := hf vQ j
    have h := Set.image_mono (f := f vQ j) (hxc vQ j)
    rwa [show f vQ j '' contL p D N vQ j = contL p D N vQ j from image_cont p D N (f vQ j) ψ hψ hfψ] at h

theorem packetAut_adm (h : (logShellSystem p L).ProcessionAut) (vQ : Unit)
    (j : Fin ((logShellSystem p L).lstar + 1)) :
    ∃ ψ : T p (LL L j.val) ≃ₗ[ℚ_[p]] T p (LL L j.val),
      Adm p (LL L j.val) ψ ∧ ∀ z, h.packetAut vQ j z = ψ z :=
  ⟨(shellLin p L j.val (fun α => h.stripAut j α vQ ())).trans (permLin p L j.val (h.labelPerm j)),
    adm_trans p (LL L j.val) (adm_shellLin p L j.val _) (adm_permLin p L j.val _), fun _ => rfl⟩

theorem ismAct_adm (g : (logShellSystem p L).Ind2Element) (vQ : Unit)
    (j : Fin ((logShellSystem p L).lstar + 1)) :
    ∃ ψ : T p (LL L j.val) ≃ₗ[ℚ_[p]] T p (LL L j.val),
      Adm p (LL L j.val) ψ ∧ ∀ z, (logShellSystem p L).ismAct vQ j (g vQ j) z = ψ z :=
  ⟨shellLin p L j.val (fun t => g vQ j t ()), adm_shellLin p L j.val _, fun _ => rfl⟩

end Regions

section Volumes

variable (p : ℕ) [Fact p.Prime]
variable {L : Type} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
  [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]
variable (D : ThetaDatum L) (N : ℕ)

theorem procVol_thetaL : (logShellSystem p L).procVol (thetaL p D N) = (N : ℝ) / 3 * D.Lq :=
  (procVol_eq_ramp p L _).trans (procVol_theta p D N)

theorem procVol_qL : (logShellSystem p L).procVol (qL p D N) = (N : ℝ) / 14 * D.Lq :=
  (procVol_eq_ramp p L _).trans (procVol_q p D N)

theorem stage_hull_le (j : Fin ((rampSystem p L).lstar + 1)) :
    (rampSystem p L).packetLogVolume () j (hullL p D N () j) ≤
      (errCoeff p (LL L j.val) + c0 p (LL L j.val)) * Real.log p +
        (N : ℝ) * Real.log ‖(D.ξ (labOf j.val) : L)‖ := by
  have h1 := packetLogVolume_region p L () j (hullReg p D N j.val)
  have h2 := normalizedHaarLogVolume_mono (anchor p L j.val) (hullReg p D N j.val)
    (boundRegion p (LL L j.val) 0 (kB p D N j.val)) (hull_subset_boundB p D N j.val)
  have h3 := bound_logVolume_numerical p (LL L j.val) 0 (kB p D N j.val)
  have h4 := bI_sub_boundExponent_le p (LL L j.val) 0 (kB p D N j.val)
  have h5 := k_div_e_log p (D.ξ (labOf j.val) : L) N (kθ p D N j.val) (kθ_spec p D N j.val)
  have hd := finrank_pos p L j.val
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have he : ((finiteExtensionRamification p L).e : ℝ) ≠ 0 := by
    exact_mod_cast (finiteExtensionRamification p L).e_pos.ne'
  have hkB : ((kB p D N j.val : ℤ) : ℝ) / ((finiteExtensionRamification p (LL L j.val 0)).e : ℝ) =
      (kθ p D N j.val : ℝ) / (finiteExtensionRamification p L).e - (c0 p (LL L j.val) : ℝ) := by
    change ((kθ p D N j.val - (finiteExtensionRamification p L).e * c0 p (LL L j.val) : ℤ) : ℝ) /
      ((finiteExtensionRamification p L).e : ℝ) = _
    push_cast
    field_simp
  rw [hkB] at h4
  have h5' : (kθ p D N j.val : ℝ) / (finiteExtensionRamification p L).e * Real.log p =
      -((N : ℝ) * Real.log ‖(D.ξ (labOf j.val) : L)‖) := h5
  set V := normalizedHaarLogVolume (anchor p L j.val) (hullReg p D N j.val)
  set d : ℝ := (Module.finrank ℚ_[p] (PP p L j.val) : ℝ)
  have hstep : V / d ≤ (bI p (fun t => finiteExtensionRamification p (LL L j.val t)) -
      (boundExponent p (LL L j.val) 0 (kB p D N j.val) : ℝ)) * Real.log p := by
    rw [div_le_iff₀ hd]
    have h3' : normalizedHaarLogVolume (anchor p L j.val) (boundRegion p (LL L j.val) 0 (kB p D N j.val)) =
        d * (bI p (fun t => finiteExtensionRamification p (LL L j.val t)) -
          (boundExponent p (LL L j.val) 0 (kB p D N j.val) : ℝ)) * Real.log p := h3
    linarith
  have h6 := mul_le_mul_of_nonneg_right h4 hlogp
  show (rampSystem p L).packetLogVolume () j (hullReg p D N j.val).val ≤ _
  rw [h1]
  calc V / d ≤ _ := hstep
    _ ≤ (errCoeff p (LL L j.val) - ((kθ p D N j.val : ℝ) / (finiteExtensionRamification p L).e -
          (c0 p (LL L j.val) : ℝ))) * Real.log p := h6
    _ = _ := by linear_combination (-1 : ℝ) * h5'

def errBarL : ℝ :=
  (∑ k : Fin 3, (errCoeff p (LL L (k.val + 1)) + c0 p (LL L (k.val + 1)))) / 3 * Real.log p

theorem procVol_hullL_le :
    (logShellSystem p L).procVol (hullL p D N) ≤ errBarL p (L := L) + (N : ℝ) / 3 * D.Lq := by
  rw [procVol_eq_ramp, procVol_eq]
  have hk : ∀ k : Fin 3, (rampSystem p L).packetLogVolume () k.succ (hullL p D N () k.succ) ≤
      (errCoeff p (LL L (k.val + 1)) + c0 p (LL L (k.val + 1))) * Real.log p +
        (N : ℝ) * (((k.val : ℝ) + 1) ^ 2 / 14 * D.Lq) := by
    intro k
    have h := stage_hull_le p D N k.succ
    rw [Fin.val_succ, labOf_succ, D.log_xi] at h
    exact h
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  unfold errBarL
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  norm_num at h0 h1 h2 ⊢
  linarith

theorem enlargementL_bounded :
    (logShellSystem p L).procVol (hullL p D N) - (logShellSystem p L).procVol (thetaL p D N) ≤
      errBarL p (L := L) := by
  rw [procVol_thetaL]
  linarith [procVol_hullL_le p D N]

end Volumes

section Theory

variable (p : ℕ) [Fact p.Prime]
variable {L : Type} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
  [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]
variable (D : ThetaDatum L) (N : ℕ)

theorem stage_le' (j : Fin ((logShellSystem p L).lstar + 1)) : j.val ≤ 3 :=
  Nat.lt_succ_iff.mp j.isLt

theorem hullL_neg (hgap : errBarL p (L := L) + (N : ℝ) / 3 * D.Lq < (N : ℝ) / 14 * D.Lq)
    (hN : 0 < N) : (logShellSystem p L).procVol (hullL p D N) < 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : (N : ℝ) / 14 * D.Lq < 0 := mul_neg_of_pos_of_neg (by positivity) D.Lq_neg
  linarith [procVol_hullL_le p D N]

def logShellTheory (hbig : BigL p D N)
    (hgap : errBarL p (L := L) + (N : ℝ) / 3 * D.Lq < (N : ℝ) / 14 * D.Lq) (hN : 0 < N) :
    CitedTheory where
  S := logShellSystem p L
  thetaPilot := thetaL p D N
  qPilot := qL p D N
  container := contL p D N
  Possible := possL p D N
  IsLambdaO := fun _ j A => ∃ d : (PP p L j.val)ˣ, A = (unitRegion p (LL L j.val) d (anchor p L j.val)).val
  hull := hullL p D N
  theta_possible := theta_mem_possL p D N
  ind1_closed := by
    rintro x hx y ⟨h, rfl⟩
    exact possL_image p D N hx (fun vQ j => h.packetAut vQ j) (fun vQ j => packetAut_adm p h vQ j)
  ind2_closed := by
    rintro x hx y ⟨g, rfl⟩
    exact possL_image p D N hx (fun vQ j => (logShellSystem p L).ismAct vQ j (g vQ j))
      (fun vQ j => ismAct_adm p g vQ j)
  ind3_bound := fun _ hx => hx.2
  ind3_saturated := by
    rintro x ⟨⟨b, hb, hbx⟩, _⟩ y hxy hyc
    exact ⟨⟨b, hb, fun vQ j => (hbx vQ j).trans (hxy vQ j)⟩, hyc⟩
  container_le_integral := fun _ j => cont_le_logUnits p D N hbig j.val (stage_le' p j)
  hull_isLambdaO := fun _ j => ⟨hullC p D N j.val, rfl⟩
  hull_contains := fun _ hx vQ j => (hx.2 vQ j).trans (cont_subset_hull p D N j.val)
  hull_minimal := by
    intro T hT hc vQ j
    obtain ⟨d, hd⟩ := hT vQ j
    have hcT : contSet p D N j.val ⊆ T vQ j := hc (contL p D N) (cont_mem_possL p D N) vQ j
    rw [hd] at hcT
    show (hullReg p D N j.val).val ⊆ T vQ j
    rw [hd, hull_eq]
    exact lambdaIntersection_subset p (LL L j.val) _ (d : PP p L j.val) d.isUnit hcT
  hull_le_integral := fun _ j => hull_le_logUnits p D N hbig j.val (stage_le' p j)
  q_hasVolume := fun _ j =>
    (normalizedAddHaar_region_pos (anchor p L j.val)
      (factorRegion p (LL L j.val) 0 (D.r ^ N) (anchor p L j.val))).ne'
  q_le_integral := fun _ j => q_le_logUnits p D N hbig j.val (stage_le' p j)
  q_neg := by
    rw [procVol_qL]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    exact mul_neg_of_pos_of_neg (by positivity) D.Lq_neg
  linkScale := 3 / 14
  linkScale_pos := by norm_num
  link_degree := by
    rw [procVol_qL, procVol_thetaL]
    ring
  ipl := by
    intro x hx
    have hle : (logShellSystem p L).procVol x ≤ (logShellSystem p L).procVol (hullL p D N) :=
      PacketSystem.procVol_ind3 (fun vQ j => ⟨(hx.2 vQ j).trans (cont_subset_hull p D N j.val),
        hull_le_logUnits p D N hbig j.val (stage_le' p j)⟩) (possL_hasVolume p D N hx)
    have hxneg : (logShellSystem p L).procVol x < 0 := lt_of_le_of_lt hle (hullL_neg p D N hgap hN)
    have hqneg : (logShellSystem p L).procVol (qL p D N) < 0 := by
      rw [procVol_qL]
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      exact mul_neg_of_pos_of_neg (by positivity) D.Lq_neg
    exact ⟨(logShellSystem p L).procVol (qL p D N) / (logShellSystem p L).procVol x,
      div_pos_of_neg_of_neg hqneg hxneg, (div_mul_cancel₀ _ hxneg.ne).symm⟩

theorem logShellTheory_weakSHE (hbig) (hgap) (hN) : (logShellTheory p D N hbig hgap hN).WeakSHE :=
  ⟨fun c => {y | (∃ b : (logShellSystem p L).Regions, (∀ vQ j, b vQ j ∈ baseSet p D N j.val) ∧
      RegionLE (logShellSystem p L) b y) ∧ RegionLE (logShellSystem p L) y c}, rfl, fun _ _ hx => hx.2⟩

theorem logShellTheory_not_conclusion (hbig) (hgap) (hN) :
    ¬ (logShellTheory p D N hbig hgap hN).Conclusion := by
  intro h
  have h' : (logShellSystem p L).procVol (qL p D N) ≤ (logShellSystem p L).procVol (hullL p D N) := h
  rw [procVol_qL] at h'
  linarith [procVol_hullL_le p D N]

end Theory

section Existence

variable (p : ℕ) [Fact p.Prime]
variable {L : Type} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
  [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]
variable (D : ThetaDatum L) (N : ℕ)

omit [CompleteSpace L] [ProperSpace L] in

theorem bE_lower (j : ℕ) (x : L) (k : ℤ)
    (hk : ‖x‖ ^ N = ‖(finiteExtensionRamification p L).pi‖ ^ k) :
    bI p (fun t => finiteExtensionRamification p (LL L j t)) - errCoeff p (LL L j) +
      (-((N : ℝ) * Real.log ‖x‖)) / Real.log p ≤ (boundExponent p (LL L j) 0 k : ℝ) := by
  have hp : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have h3 := bI_sub_boundExponent_le p (LL L j) 0 k
  have h4 := k_div_e_log p x N k hk
  have h4' : (k : ℝ) / (finiteExtensionRamification p (LL L j 0)).e =
      (-((N : ℝ) * Real.log ‖x‖)) / Real.log p := by
    rw [eq_div_iff hp.ne']
    exact h4
  rw [h4'] at h3
  linarith

theorem bigL_of_large
    (hN : ∀ j : ℕ, j ≤ 3 → (2 * |(c0 p (LL L j) : ℝ)| + |errCoeff p (LL L j)| +
      |bI p (fun t => finiteExtensionRamification p (LL L j t))| + 1) * Real.log p ≤
        (N : ℝ) * (-D.Lq) / 14) : BigL p D N := by
  intro j hj
  have hp : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have key : ∀ (x : L) (k : ℤ), ‖x‖ ^ N = ‖(finiteExtensionRamification p L).pi‖ ^ k →
      Real.log ‖x‖ ≤ D.Lq / 14 → 2 * |(c0 p (LL L j) : ℝ)| < (boundExponent p (LL L j) 0 k : ℝ) := by
    intro x k hk hx
    have hb := bE_lower p N j x k hk
    have h1 : (N : ℝ) * (-D.Lq) / 14 ≤ -((N : ℝ) * Real.log ‖x‖) := by nlinarith
    have h2 : 2 * |(c0 p (LL L j) : ℝ)| + |errCoeff p (LL L j)| +
        |bI p (fun t => finiteExtensionRamification p (LL L j t))| + 1 ≤
        (-((N : ℝ) * Real.log ‖x‖)) / Real.log p := by
      rw [le_div_iff₀ hp]
      linarith [hN j hj]
    have h3 := le_abs_self (errCoeff p (LL L j))
    have h4 := neg_abs_le (bI p (fun t => finiteExtensionRamification p (LL L j t)))
    linarith
  have hξ : Real.log ‖(D.ξ (labOf j) : L)‖ ≤ D.Lq / 14 := by
    rw [D.log_xi]
    have hsq : (1 : ℝ) ≤ (((labOf j).val : ℝ) + 1) ^ 2 := by
      have : (0 : ℝ) ≤ ((labOf j).val : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hL := D.Lq_neg
    nlinarith
  have hr : Real.log ‖(D.r : L)‖ ≤ D.Lq / 14 := by rw [D.log_r]
  have hθ := key _ _ (kθ_spec p D N j) hξ
  have hq := key _ _ (kq_spec p D N) hr
  have ha := le_abs_self (c0 p (LL L j) : ℝ)
  have hb := abs_nonneg (c0 p (LL L j) : ℝ)
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast (show (c0 p (LL L j) : ℝ) ≤ (boundExponent p (LL L j) 0 (kθ p D N j) : ℝ) by linarith)
  · exact_mod_cast
      (show ((2 * c0 p (LL L j) : ℤ) : ℝ) ≤ (boundExponent p (LL L j) 0 (kθ p D N j) : ℝ) by
        push_cast; linarith)
  · exact_mod_cast (show (c0 p (LL L j) : ℝ) ≤ (boundExponent p (LL L j) 0 (kq p D N) : ℝ) by linarith)

theorem exists_logShell_counterexample :
    ∃ (N : ℕ) (hbig : BigL p D N)
      (hgap : errBarL p (L := L) + (N : ℝ) / 3 * D.Lq < (N : ℝ) / 14 * D.Lq) (hN : 0 < N),
      (logShellTheory p D N hbig hgap hN).WeakSHE ∧ ¬ (logShellTheory p D N hbig hgap hN).Conclusion := by
  have hA : 0 < -D.Lq := by linarith [D.Lq_neg]
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  set Mf : ℕ → ℝ := fun j => 2 * |(c0 p (LL L j) : ℝ)| + |errCoeff p (LL L j)| +
    |bI p (fun t => finiteExtensionRamification p (LL L j t))| + 1 with hMf
  have hMf0 : ∀ j, 0 ≤ Mf j := fun j => by simp only [hMf]; positivity
  set M : ℝ := Mf 0 + Mf 1 + Mf 2 + Mf 3 with hM
  set E : ℝ := errBarL p (L := L) with hE
  obtain ⟨N, hNgt⟩ := exists_nat_gt ((14 * M * Real.log p + 42 * |E| + 1) / (-D.Lq))
  have hkey : 14 * M * Real.log p + 42 * |E| + 1 < (N : ℝ) * (-D.Lq) := by
    rwa [div_lt_iff₀ hA] at hNgt
  have hM0 : 0 ≤ M := by simp only [hM]; linarith [hMf0 0, hMf0 1, hMf0 2, hMf0 3]
  have hML : 0 ≤ M * Real.log p := mul_nonneg hM0 hlogp.le
  have hE0 : 0 ≤ |E| := abs_nonneg E
  have hNpos : 0 < N := by
    have : (0 : ℝ) < (N : ℝ) * (-D.Lq) := by linarith
    have h' : (0 : ℝ) < N := lt_of_not_ge fun hc => by nlinarith
    exact_mod_cast h'
  have hbig : BigL p D N := by
    apply bigL_of_large
    intro j hj
    have hj' : Mf j ≤ M := by
      interval_cases j <;> simp only [hM] <;> linarith [hMf0 0, hMf0 1, hMf0 2, hMf0 3]
    have h1 : Mf j * Real.log p ≤ M * Real.log p := mul_le_mul_of_nonneg_right hj' hlogp.le
    show Mf j * Real.log p ≤ _
    linarith
  have hgap : E + (N : ℝ) / 3 * D.Lq < (N : ℝ) / 14 * D.Lq := by
    have hE' : E ≤ |E| := le_abs_self E
    nlinarith
  exact ⟨N, hbig, hgap, hNpos, logShellTheory_weakSHE p D N hbig hgap hNpos,
    logShellTheory_not_conclusion p D N hbig hgap hNpos⟩

end Existence

section Nontrivial

variable (p : ℕ) [Fact p.Prime]
variable (L : Type) [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
  [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]

def negAut : ShellAut p L := LinearEquiv.neg ℤ_[p]

omit [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem ambientAction_negAut (y : L) : ambientAction p (negAut p L) y = -y := by
  have h := extend_unique p (negAut p L) (-LinearMap.id) (fun x => by
    show -(x : L) = ((negAut p L) x : L)
    rfl)
  have hy := congrArg (fun f : L →ₗ[ℚ_[p]] L => f y) h
  simp only [LinearMap.neg_apply, LinearMap.id_apply] at hy
  exact hy.symm

theorem ind2_nontrivial :
    ∃ g : (logShellSystem p L).Ind2Element,
      (logShellSystem p L).ismAct () 0 (g () 0) (1 : PP p L 0) ≠ (1 : PP p L 0) := by
  refine ⟨fun _ _ _ _ => negAut p L, ?_⟩
  have hone : (1 : T p (LL L 0)) = PiTensorProduct.tprod ℚ_[p] (s := LL L 0) (fun _ => (1 : L)) := rfl
  have hact : (logShellSystem p L).ismAct () 0 (fun _ _ => negAut p L) (1 : PP p L 0) =
      -(1 : PP p L 0) := by
    show shellLin p L 0 (fun _ => negAut p L) 1 = -1
    rw [hone, shellLin_tprod]
    simp only [ambientAction_negAut]
    have h := (PiTensorProduct.tprod ℚ_[p] (s := LL L 0)).map_smul_univ (fun _ => (-1 : ℚ_[p]))
      (fun _ => (1 : L))
    simp only [neg_one_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    rw [h]
    exact neg_one_smul ℚ_[p] _
  rw [hact]
  intro h
  haveI : Nontrivial (PP p L 0) := Module.nontrivial_of_finrank_pos
    (by exact_mod_cast finrank_pos p L 0)
  have h2 : (2 : PP p L 0) = 0 := by
    have : (1 : PP p L 0) + 1 = 0 := by
      calc (1 : PP p L 0) + 1 = -1 + 1 := by rw [h]
        _ = 0 := neg_add_cancel 1
    rw [← this]
    norm_num
  have h3 : algebraMap ℚ_[p] (PP p L 0) 2 = algebraMap ℚ_[p] (PP p L 0) 0 := by
    rw [map_ofNat, map_zero, h2]
  have h4 := (algebraMap ℚ_[p] (PP p L 0)).injective h3
  norm_num at h4

end Nontrivial

section Concrete

theorem concrete_logShell :
    98 ∣ (finiteExtensionRamification 211 FB).e ∧
      ∃ (N : ℕ) (hbig : BigL 211 D0 N)
        (hgap : errBarL 211 (L := FB) + (N : ℝ) / 3 * D0.Lq < (N : ℝ) / 14 * D0.Lq) (hN : 0 < N),
        (logShellTheory 211 D0 N hbig hgap hN).WeakSHE ∧
          ¬ (logShellTheory 211 D0 N hbig hgap hN).Conclusion :=
  ⟨FB_ramified, exists_logShell_counterexample 211 D0⟩

end Concrete

section PowDatum

variable (p : ℕ) [Fact p.Prime]
variable {L : Type} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L] [IsUltrametricDist L]

omit [CompleteSpace L] [IsUltrametricDist L] in
theorem datum_norm_s_lt (D : ThetaDatum L) : ‖(D.s : L)‖ < 1 := by
  have h : ‖(D.s : L)‖ ^ 2 < 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val]
    exact D.hq
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h

def powDatum (D : ThetaDatum L) (N : ℕ) (hN : 0 < N) : ThetaDatum L :=
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  have hsN : ‖((D.s ^ N : Lˣ) : L)‖ < 1 := by
    rw [Units.val_pow_eq_pow_val, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (datum_norm_s_lt D) hN.ne'
  let F := publishedThetaFactsOfCompleteUltrametric (D.s ^ N) D.i D.hi hsN
  { s := D.s ^ N
    i := D.i
    hi := D.hi
    facts := F
    ξ := fun j => D.ξ j ^ N
    hξ := fun j => by
      rw [mem_normalizedRootValues_iff_power (D.s ^ N) D.i D.hi F 7 (j.val + 1)]
      have h := (mem_normalizedRootValues_iff_power D.s D.i D.hi D.facts 7 (j.val + 1) (D.ξ j)).mp
        (D.hξ j)
      rw [← pow_mul, Nat.mul_comm N, pow_mul, h, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      ring
    r := D.r ^ N
    hr := by rw [← pow_mul, Nat.mul_comm, pow_mul, D.hr, ← pow_mul, ← pow_mul, Nat.mul_comm]
    hq := by
      rw [← pow_mul, Units.val_pow_eq_pow_val, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) (datum_norm_s_lt D) (by positivity) }

theorem Lq_powDatum (D : ThetaDatum L) (N : ℕ) (hN : 0 < N) :
    (powDatum p D N hN).Lq = N * D.Lq := by
  unfold ThetaDatum.Lq powDatum
  simp only
  rw [← pow_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, norm_pow, norm_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

variable [FiniteDimensional ℚ_[p] L] [ProperSpace L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]

theorem thetaL_pow (D : ThetaDatum L) (N : ℕ) (hN : 0 < N) :
    thetaL p D N = thetaL p (powDatum p D N hN) 1 := by
  funext vQ j
  simp only [thetaL, powDatum, pow_one]

theorem qL_pow (D : ThetaDatum L) (N : ℕ) (hN : 0 < N) :
    qL p D N = qL p (powDatum p D N hN) 1 := by
  funext vQ j
  simp only [qL, powDatum, pow_one]

end PowDatum

section Family

open CitedLV.Independence.Cor312CitedFamily

variable (p : ℕ) [Fact p.Prime]
variable (L : Type) [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
  [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]
variable {κ : Type} [Fintype κ] (E : κ → ExtraPlace)

def famSL : Option κ → PacketSystem
  | none => logShellSystem p L
  | some k => (E k).S

omit [Fintype κ] in
theorem famSL_lstar : ∀ i, (famSL p L E i).lstar = 3
  | none => rfl
  | some k => (E k).lstar_eq

variable {L} (D : ThetaDatum L) (N : ℕ)

def famThetaL : ∀ i, (famSL p L E i).Regions
  | none => thetaL p D N
  | some k => (E k).S.integralRegions

def famQL : ∀ i, (famSL p L E i).Regions
  | none => qL p D N
  | some k => (E k).q

def famContL : ∀ i, (famSL p L E i).Regions
  | none => contL p D N
  | some k => (E k).S.integralRegions

def famHullL : ∀ i, (famSL p L E i).Regions
  | none => hullL p D N
  | some k => (E k).S.integralRegions

def famLamL : ∀ i, ∀ vQ (j : Fin ((famSL p L E i).lstar + 1)), Set ((famSL p L E i).Packet vQ j) → Prop
  | none => fun _ j A => ∃ d : (PP p L j.val)ˣ, A = (unitRegion p (LL L j.val) d (anchor p L j.val)).val
  | some k => fun vQ j A => A = (E k).S.integral vQ j

def famPossL : Set (∀ i, (famSL p L E i).Regions) :=
  {x | x none ∈ possL p D N ∧ ∀ k, RegionLE (E k).S (E k).S.integralRegions (x (some k)) ∧
    RegionLE (E k).S (x (some k)) (E k).S.integralRegions}

theorem tot_famThetaL :
    ∑ i, (famSL p L E i).procVol (famThetaL p E D N i) = (N : ℝ) / 3 * D.Lq + extraTheta E := by
  rw [Fintype.sum_option]
  exact congrArg₂ (· + ·) (procVol_thetaL p D N) rfl

theorem tot_famQL :
    ∑ i, (famSL p L E i).procVol (famQL p E D N i) = (N : ℝ) / 14 * D.Lq + extraQ E := by
  rw [Fintype.sum_option]
  exact congrArg₂ (· + ·) (procVol_qL p D N) rfl

theorem tot_famHullL_le :
    ∑ i, (famSL p L E i).procVol (famHullL p E D N i) ≤
      errBarL p (L := L) + (N : ℝ) / 3 * D.Lq + extraTheta E := by
  rw [Fintype.sum_option]
  have h := procVol_hullL_le p D N
  change (logShellSystem p L).procVol (hullL p D N) + extraTheta E ≤ _
  linarith

theorem theta_le_hull_vol (hbig : BigL p D N) :
    (logShellSystem p L).procVol (thetaL p D N) ≤ (logShellSystem p L).procVol (hullL p D N) :=
  PacketSystem.procVol_ind3 (fun vQ j => ⟨(theta_le_cont p D N vQ j).trans (cont_subset_hull p D N j.val),
    hull_le_logUnits p D N hbig j.val (stage_le' p j)⟩) (possL_hasVolume p D N (theta_mem_possL p D N))

theorem famThetaL_neg (hbig : BigL p D N) (hq : (N : ℝ) / 14 * D.Lq + extraQ E < 0)
    (hgap : errBarL p (L := L) + (N : ℝ) / 3 * D.Lq + extraTheta E < (N : ℝ) / 14 * D.Lq + extraQ E) :
    (N : ℝ) / 3 * D.Lq + extraTheta E < 0 := by
  have h1 := theta_le_hull_vol p D N hbig
  have h2 := procVol_hullL_le p D N
  rw [procVol_thetaL] at h1
  linarith

set_option maxHeartbeats 1000000 in

def famModelL (hbig : BigL p D N) (hq : (N : ℝ) / 14 * D.Lq + extraQ E < 0)
    (hgap : errBarL p (L := L) + (N : ℝ) / 3 * D.Lq + extraTheta E < (N : ℝ) / 14 * D.Lq + extraQ E) :
    CitedTheoryFam where
  ι := Option κ
  S := famSL p L E
  lstar_common := fun i k => (famSL_lstar p L E i).trans (famSL_lstar p L E k).symm
  thetaPilot := famThetaL p E D N
  qPilot := famQL p E D N
  container := famContL p E D N
  Possible := famPossL p E D N
  IsLambdaO := famLamL p E
  hull := famHullL p E D N
  theta_possible := ⟨theta_mem_possL p D N, fun _ => ⟨fun _ _ => subset_rfl, fun _ _ => subset_rfl⟩⟩
  ind1_closed := by
    rintro x ⟨hx0, hxk⟩ y hy
    refine ⟨?_, fun k => ?_⟩
    · obtain ⟨h, hh⟩ := hy none
      change (logShellSystem p L).ProcessionAut at h
      change y none = h.act (x none) at hh
      rw [hh]
      exact possL_image p D N hx0 (fun vQ j => h.packetAut vQ j) (fun vQ j => packetAut_adm p h vQ j)
    · obtain ⟨h, hh⟩ := hy (some k)
      change (E k).S.ProcessionAut at h
      change y (some k) = h.act (x (some k)) at hh
      have hx : x (some k) = (E k).S.integralRegions :=
        funext fun vQ => funext fun j => Set.Subset.antisymm ((hxk k).2 vQ j) ((hxk k).1 vQ j)
      rw [hh, hx, act_integralRegions (E k).S h]
      exact ⟨fun _ _ => subset_rfl, fun _ _ => subset_rfl⟩
  ind2_closed := by
    rintro x ⟨hx0, hxk⟩ y hy
    refine ⟨?_, fun k => ?_⟩
    · obtain ⟨g, hg⟩ := hy none
      change (logShellSystem p L).Ind2Element at g
      change y none = (logShellSystem p L).ind2Act g (x none) at hg
      rw [hg]
      exact possL_image p D N hx0 (fun vQ j => (logShellSystem p L).ismAct vQ j (g vQ j))
        (fun vQ j => ismAct_adm p g vQ j)
    · obtain ⟨g, hg⟩ := hy (some k)
      change (E k).S.Ind2Element at g
      change y (some k) = (E k).S.ind2Act g (x (some k)) at hg
      have hx : x (some k) = (E k).S.integralRegions :=
        funext fun vQ => funext fun j => Set.Subset.antisymm ((hxk k).2 vQ j) ((hxk k).1 vQ j)
      rw [hg, hx, ind2Act_integralRegions (E k).S g]
      exact ⟨fun _ _ => subset_rfl, fun _ _ => subset_rfl⟩
  ind3_bound := by
    rintro x ⟨hx0, hxk⟩ i
    cases i with
    | none => exact hx0.2
    | some k => exact (hxk k).2
  ind3_saturated := by
    rintro x ⟨hx0, hxk⟩ y hxy hyc
    refine ⟨?_, fun k => ⟨fun vQ j => ((hxk k).1 vQ j).trans (hxy (some k) vQ j), hyc (some k)⟩⟩
    obtain ⟨⟨b, hb, hbx⟩, _⟩ := hx0
    exact ⟨⟨b, hb, fun vQ j => (hbx vQ j).trans (hxy none vQ j)⟩, hyc none⟩
  container_le_integral := by
    intro i
    cases i with
    | none => exact fun _ j => cont_le_logUnits p D N hbig j.val (stage_le' p j)
    | some k => exact fun _ _ => subset_rfl
  hull_isLambdaO := by
    intro i
    cases i with
    | none => exact fun _ j => ⟨hullC p D N j.val, rfl⟩
    | some k => exact fun _ _ => rfl
  hull_contains := by
    rintro x ⟨hx0, hxk⟩ i
    cases i with
    | none => exact fun vQ j => (hx0.2 vQ j).trans (cont_subset_hull p D N j.val)
    | some k => exact (hxk k).2
  hull_minimal := by
    intro T hT hc i
    have hmem : famContL p E D N ∈ famPossL p E D N :=
      ⟨cont_mem_possL p D N, fun _ => ⟨fun _ _ => subset_rfl, fun _ _ => subset_rfl⟩⟩
    cases i with
    | none =>
      intro vQ j
      obtain ⟨d, hd⟩ := hT none vQ j
      have hcT : contSet p D N j.val ⊆ T none vQ j := hc _ hmem none vQ j
      rw [hd] at hcT
      show (hullReg p D N j.val).val ⊆ T none vQ j
      rw [hd, hull_eq]
      exact lambdaIntersection_subset p (LL L j.val) _ (d : PP p L j.val) d.isUnit hcT
    | some k =>
      intro vQ j
      have hd : T (some k) vQ j = (E k).S.integral vQ j := hT (some k) vQ j
      show (E k).S.integral vQ j ⊆ T (some k) vQ j
      rw [hd]
  hull_le_integral := by
    intro i
    cases i with
    | none => exact fun _ j => hull_le_logUnits p D N hbig j.val (stage_le' p j)
    | some k => exact fun _ _ => subset_rfl
  q_hasVolume := by
    intro i
    cases i with
    | none =>
      exact fun _ j => (normalizedAddHaar_region_pos (anchor p L j.val)
        (factorRegion p (LL L j.val) 0 (D.r ^ N) (anchor p L j.val))).ne'
    | some k => exact (E k).q_hasVolume
  q_le_integral := by
    intro i
    cases i with
    | none => exact fun _ j => q_le_logUnits p D N hbig j.val (stage_le' p j)
    | some k => exact (E k).q_le_integral
  q_neg := by
    rw [tot_famQL]
    exact hq
  linkScale := ((N : ℝ) / 14 * D.Lq + extraQ E) / ((N : ℝ) / 3 * D.Lq + extraTheta E)
  linkScale_pos := div_pos_of_neg_of_neg hq (famThetaL_neg p E D N hbig hq hgap)
  link_degree := by
    rw [tot_famQL, tot_famThetaL]
    exact (div_mul_cancel₀ _ (famThetaL_neg p E D N hbig hq hgap).ne).symm
  ipl := by
    rintro x ⟨hx0, hxk⟩
    have hx : ∀ k, x (some k) = (E k).S.integralRegions := fun k =>
      funext fun vQ => funext fun j => Set.Subset.antisymm ((hxk k).2 vQ j) ((hxk k).1 vQ j)
    have hsum : ∑ i, (famSL p L E i).procVol (x i) =
        (logShellSystem p L).procVol (x none) + extraTheta E := by
      rw [Fintype.sum_option]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by
        show (E k).S.procVol (x (some k)) = (E k).S.procVol (E k).S.integralRegions
        rw [hx k]
    have hle : (logShellSystem p L).procVol (x none) ≤ (logShellSystem p L).procVol (hullL p D N) :=
      PacketSystem.procVol_ind3 (fun vQ j => ⟨(hx0.2 vQ j).trans (cont_subset_hull p D N j.val),
        hull_le_logUnits p D N hbig j.val (stage_le' p j)⟩) (possL_hasVolume p D N hx0)
    have hH := procVol_hullL_le p D N
    have hxneg : ∑ i, (famSL p L E i).procVol (x i) < 0 := by rw [hsum]; linarith
    refine ⟨(∑ i, (famSL p L E i).procVol (famQL p E D N i)) / ∑ i, (famSL p L E i).procVol (x i),
      div_pos_of_neg_of_neg (by rw [tot_famQL]; exact hq) hxneg, ?_⟩
    exact (div_mul_cancel₀ _ hxneg.ne).symm

theorem famModelL_weakSHE (hbig) (hq) (hgap) : (famModelL p E D N hbig hq hgap).WeakSHE :=
  ⟨fun c => {x | ((∃ b : (logShellSystem p L).Regions, (∀ vQ j, b vQ j ∈ baseSet p D N j.val) ∧
      RegionLE (logShellSystem p L) b (x none)) ∧ RegionLE (logShellSystem p L) (x none) (c none)) ∧
      ∀ k, RegionLE (E k).S (E k).S.integralRegions (x (some k)) ∧ RegionLE (E k).S (x (some k)) (c (some k))},
    rfl, fun _ x hx i => by
      cases i with
      | none => exact hx.1.2
      | some k => exact (hx.2 k).2⟩

theorem famModelL_not_conclusion (hbig) (hq) (hgap) :
    ¬ (famModelL p E D N hbig hq hgap).Conclusion := by
  intro h
  have h' : ∑ i, (famSL p L E i).procVol (famQL p E D N i) ≤
      ∑ i, (famSL p L E i).procVol (famHullL p E D N i) := h
  rw [tot_famQL] at h'
  linarith [tot_famHullL_le p E D N]

theorem robust_logShell :
    ∃ (N : ℕ) (hbig : BigL p D N) (_ : 0 < N) (hq : (N : ℝ) / 14 * D.Lq + extraQ E < 0)
      (hgap : errBarL p (L := L) + (N : ℝ) / 3 * D.Lq + extraTheta E < (N : ℝ) / 14 * D.Lq + extraQ E),
      (famModelL p E D N hbig hq hgap).WeakSHE ∧ ¬ (famModelL p E D N hbig hq hgap).Conclusion := by
  have hA : 0 < -D.Lq := by linarith [D.Lq_neg]
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  set Mf : ℕ → ℝ := fun j => 2 * |(c0 p (LL L j) : ℝ)| + |errCoeff p (LL L j)| +
    |bI p (fun t => finiteExtensionRamification p (LL L j t))| + 1 with hMf
  have hMf0 : ∀ j, 0 ≤ Mf j := fun j => by simp only [hMf]; positivity
  set M : ℝ := Mf 0 + Mf 1 + Mf 2 + Mf 3 with hM
  set Eb : ℝ := errBarL p (L := L) with hEb
  set At : ℝ := extraTheta E with hAt
  set Bq : ℝ := extraQ E with hBq
  obtain ⟨N, hNgt⟩ := exists_nat_gt ((14 * M * Real.log p + 42 * (|Eb| + |At| + |Bq|) + 1) / (-D.Lq))
  have hkey : 14 * M * Real.log p + 42 * (|Eb| + |At| + |Bq|) + 1 < (N : ℝ) * (-D.Lq) := by
    rwa [div_lt_iff₀ hA] at hNgt
  have hM0 : 0 ≤ M := by simp only [hM]; linarith [hMf0 0, hMf0 1, hMf0 2, hMf0 3]
  have hML : 0 ≤ M * Real.log p := mul_nonneg hM0 hlogp.le
  have hE0 := abs_nonneg Eb
  have hA0 := abs_nonneg At
  have hB0 := abs_nonneg Bq
  have hNpos : 0 < N := by
    have : (0 : ℝ) < (N : ℝ) * (-D.Lq) := by linarith
    have h' : (0 : ℝ) < N := lt_of_not_ge fun hc => by nlinarith
    exact_mod_cast h'
  have hbig : BigL p D N := by
    apply bigL_of_large
    intro j hj
    have hj' : Mf j ≤ M := by
      interval_cases j <;> simp only [hM] <;> linarith [hMf0 0, hMf0 1, hMf0 2, hMf0 3]
    have h1 : Mf j * Real.log p ≤ M * Real.log p := mul_le_mul_of_nonneg_right hj' hlogp.le
    show Mf j * Real.log p ≤ _
    linarith
  have hq : (N : ℝ) / 14 * D.Lq + Bq < 0 := by
    have := neg_abs_le Bq
    have := le_abs_self Bq
    nlinarith
  have hgap : Eb + (N : ℝ) / 3 * D.Lq + At < (N : ℝ) / 14 * D.Lq + Bq := by
    have := le_abs_self Eb
    have := le_abs_self At
    have := neg_abs_le Bq
    nlinarith
  exact ⟨N, hbig, hNpos, hq, hgap, famModelL_weakSHE p E D N hbig hq hgap,
    famModelL_not_conclusion p E D N hbig hq hgap⟩

theorem concrete_family :
    98 ∣ (finiteExtensionRamification 211 FB).e ∧
      ∃ (N : ℕ) (hbig : BigL 211 D0 N) (_ : 0 < N)
        (hq : (N : ℝ) / 14 * D0.Lq + extraQ ![goodPlace5, archPlace] < 0)
        (hgap : errBarL 211 (L := FB) + (N : ℝ) / 3 * D0.Lq + extraTheta ![goodPlace5, archPlace] <
          (N : ℝ) / 14 * D0.Lq + extraQ ![goodPlace5, archPlace]),
        (famModelL 211 ![goodPlace5, archPlace] D0 N hbig hq hgap).WeakSHE ∧
          ¬ (famModelL 211 ![goodPlace5, archPlace] D0 N hbig hq hgap).Conclusion :=
  ⟨FB_ramified, robust_logShell 211 ![goodPlace5, archPlace] D0⟩

end Family

end CitedLV.Independence.Cor312RamifiedLogShell
