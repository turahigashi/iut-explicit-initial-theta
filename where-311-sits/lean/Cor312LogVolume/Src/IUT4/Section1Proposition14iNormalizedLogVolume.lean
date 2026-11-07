import Mathlib
import Cor312LogVolume.Src.IUT4.Section1Proposition12iiTensorLogUnits
import Cor312LogVolume.Src.Lib.LatticeLogIndex
import Cor312LogVolume.Src.CoreLayer.LogVolumeBoundProp14

namespace Src.IUT4.Proposition14i

open PiTensorProduct
open scoped TensorProduct Pointwise
open SrcLib.LatticeLogIndex Src.IUT4.Proposition11 Src.IUT4.Proposition12i
  Src.IUT4.Proposition12ii SrcLib.PadicLog

variable (p : ℕ) [hp : Fact p.Prime]

theorem finite_quotient_span_p : Finite (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
  have h : Finite (ℤ_[p] ⧸ RingHom.ker (PadicInt.toZMod (p := p))) :=
    Finite.of_injective _ (RingHom.kerLift_injective _)
  rwa [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p] at h

section Packet

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L B : ι → Type*}
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)] [∀ i, CompleteSpace (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]
  [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, Algebra ℤ_[p] (B i)] [∀ i, Algebra (B i) (L i)]
  [∀ i, IsScalarTower ℤ_[p] (B i) (L i)] [∀ i, IsIntegralClosure (B i) ℤ_[p] (L i)]
  [∀ i, IsDedekindDomain (B i)] [∀ i, IsFractionRing (B i) (L i)] [∀ i, Module.IsTorsionFree ℤ_[p] (B i)]
  [∀ i, Module.Free ℤ_[p] (B i)] [∀ i, Module.Finite ℤ_[p] (B i)]
  [∀ i, IsLocalization (Algebra.algebraMapSubmonoid (B i) (nonZeroDivisors ℤ_[p])) (L i)]

variable (L) in

noncomputable def normalizationSubmodule : Submodule ℤ_[p] (⨂[ℚ_[p]] i, L i) :=
  Subalgebra.toSubmodule (integralClosure ℤ_[p] (⨂[ℚ_[p]] i, L i))

variable (L) in

noncomputable def normalization : AddSubgroup (⨂[ℚ_[p]] i, L i) :=
  (normalizationSubmodule p L).toAddSubgroup

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in
theorem mem_normalization {x : ⨂[ℚ_[p]] i, L i} : x ∈ normalization p L ↔ IsIntegral ℤ_[p] x := by
  change x ∈ integralClosure ℤ_[p] (⨂[ℚ_[p]] i, L i) ↔ _
  exact mem_integralClosure_iff ℤ_[p] _

variable (L) in

noncomputable def smulHom (c : ℚ_[p]) : (⨂[ℚ_[p]] i, L i) →+ (⨂[ℚ_[p]] i, L i) :=
  DistribSMul.toAddMonoidHom _ c

variable (L) in

noncomputable def pNormalization : AddSubgroup (⨂[ℚ_[p]] i, L i) :=
  (normalization p L).map (smulHom p L (p : ℚ_[p]))

include B in
theorem normalizationSubmodule_fg : (normalizationSubmodule p L).FG := by
  classical
  refine Submodule.FG.of_le (Submodule.fg_span (Set.finite_range
    (packetDualBasis ℤ_[p] ℚ_[p] L B))) ?_
  intro z hz
  exact mem_span_packetDual_of_isIntegral (B := B) z ((mem_normalization p).mp hz)

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in
theorem pNormalization_eq :
    pNormalization p L = ((Ideal.span {(p : ℤ_[p])}) • normalizationSubmodule p L).toAddSubgroup := by
  ext x
  rw [Submodule.ideal_span_singleton_smul]
  simp only [pNormalization, normalization, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup,
    Submodule.mem_smul_pointwise_iff_exists, smulHom, DistribSMul.toAddMonoidHom_apply]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, by rw [← algebraMap_smul ℚ_[p] (p : ℤ_[p]) m, map_natCast]⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, by rw [← algebraMap_smul ℚ_[p] (p : ℤ_[p]) m, map_natCast]⟩

include B in

theorem relIndex_pNormalization_ne_zero :
    (pNormalization p L).relIndex (normalization p L) ≠ 0 := by
  have hfg := normalizationSubmodule_fg p (L := L) (B := B)
  have hfin := finite_quotient_span_p p
  set N := normalizationSubmodule p L
  set I : Ideal ℤ_[p] := Ideal.span {(p : ℤ_[p])}
  rw [pNormalization_eq]
  change Nat.card (N ⧸ (I • N).comap N.subtype) ≠ 0
  let e : (N ⧸ (I • N).comap N.subtype) ≃ₗ[ℤ_[p]] (ℤ_[p] ⧸ I) ⊗[ℤ_[p]] N :=
    Submodule.quotEquivOfEq _ (I • (⊤ : Submodule ℤ_[p] N)) (Submodule.map_injective_of_injective
      N.injective_subtype (by simp [Submodule.smul_le_right])) ≪≫ₗ
        (TensorProduct.quotTensorEquivQuotSMul N I).symm
  rw [Nat.card_congr e.toEquiv]
  have : Module.Finite ℤ_[p] N := .of_fg hfg
  have : Finite ((ℤ_[p] ⧸ I) ⊗[ℤ_[p]] N) := Module.finite_of_finite (ℤ_[p] ⧸ I)
  exact Nat.card_pos.ne'

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in
theorem smulHom_apply (c : ℚ_[p]) (x : ⨂[ℚ_[p]] i, L i) : smulHom p L c x = c • x := rfl

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in
theorem smulHom_injective {c : ℚ_[p]} (hc : c ≠ 0) : Function.Injective (smulHom p L c) :=
  smul_right_injective _ hc

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in
theorem map_smulHom_map_smulHom (H : AddSubgroup (⨂[ℚ_[p]] i, L i)) (a b : ℚ_[p]) :
    (H.map (smulHom p L a)).map (smulHom p L b) = H.map (smulHom p L (b * a)) := by
  rw [AddSubgroup.map_map]
  congr 1
  ext x
  simp [smulHom_apply, mul_smul]

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in
theorem map_smulHom_one (H : AddSubgroup (⨂[ℚ_[p]] i, L i)) : H.map (smulHom p L 1) = H := by
  have : smulHom p L 1 = AddMonoidHom.id _ := by ext x; simp [smulHom_apply]
  rw [this, AddSubgroup.map_id]

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in
theorem pNormalization_le : pNormalization p L ≤ normalization p L := by
  rintro _ ⟨m, hm, rfl⟩
  rw [SetLike.mem_coe, mem_normalization] at hm
  rw [mem_normalization, smulHom_apply, ← map_natCast (algebraMap ℤ_[p] ℚ_[p]) p, algebraMap_smul]
  exact hm.smul _

include B in
theorem nontrivial_packet : Nontrivial (⨂[ℚ_[p]] i, L i) := by
  classical
  have hne : ∀ i, Nonempty (Module.Free.ChooseBasisIndex ℤ_[p] (B i)) :=
    fun i => (Module.Free.chooseBasis ℤ_[p] (B i)).index_nonempty
  exact nontrivial_of_ne _ _ ((packetBasis ℤ_[p] ℚ_[p] L B).ne_zero fun i => (hne i).some)

include B in

theorem relIndex_pNormalization_ne_one : (pNormalization p L).relIndex (normalization p L) ≠ 1 := by
  haveI := nontrivial_packet p (L := L) (B := B)
  rw [Ne, AddSubgroup.relIndex_eq_one]
  intro hle
  have h1 : (1 : ⨂[ℚ_[p]] i, L i) ∈ normalization p L := (mem_normalization p).mpr isIntegral_one
  obtain ⟨m, hm, hpm⟩ := hle h1
  rw [SetLike.mem_coe, mem_normalization] at hm
  rw [smulHom_apply] at hpm
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hmeq : m = algebraMap ℚ_[p] _ (p : ℚ_[p])⁻¹ := by
    rw [Algebra.algebraMap_eq_smul_one, ← hpm, smul_smul, inv_mul_cancel₀ hp0, one_smul]
  rw [hmeq, isIntegral_algebraMap_iff (algebraMap ℚ_[p] (⨂[ℚ_[p]] i, L i)).injective] at hm
  have h2 := norm_le_one_of_isIntegral hm
  rw [norm_inv, Padic.norm_p, inv_inv] at h2
  have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  linarith

variable (L) in

def IsLattice (H : AddSubgroup (⨂[ℚ_[p]] i, L i)) : Prop := Comm H (normalization p L)

variable (L) in

noncomputable def logVol (H : AddSubgroup (⨂[ℚ_[p]] i, L i)) : ℝ :=
  Real.log p * lidx H (normalization p L) / Real.log ((pNormalization p L).relIndex (normalization p L))

include B in
theorem log_index_pos : 0 < Real.log ((pNormalization p L).relIndex (normalization p L)) := by
  apply Real.log_pos
  have h0 := relIndex_pNormalization_ne_zero p (L := L) (B := B)
  have h1 := relIndex_pNormalization_ne_one p (L := L) (B := B)
  have : 1 < (pNormalization p L).relIndex (normalization p L) := by omega
  exact_mod_cast this

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in
theorem isLattice_normalization : IsLattice p L (normalization p L) := comm_refl _

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in

theorem logVol_normalization : logVol p L (normalization p L) = 0 := by
  simp [logVol, lidx_self]

include B in

theorem logVol_pNormalization : logVol p L (pNormalization p L) = -Real.log p := by
  have hX := log_index_pos p (L := L) (B := B)
  rw [logVol, lidx_of_le (pNormalization_le p)]
  field_simp

include B in
theorem isLattice_pNormalization : IsLattice p L (pNormalization p L) :=
  comm_of_le (pNormalization_le p) (relIndex_pNormalization_ne_zero p (B := B))

include B in

theorem logVol_mono {H K : AddSubgroup (⨂[ℚ_[p]] i, L i)} (hH : IsLattice p L H) (hK : IsLattice p L K)
    (hHK : H ≤ K) : logVol p L H ≤ logVol p L K := by
  have hX := log_index_pos p (L := L) (B := B)
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  unfold logVol
  apply div_le_div_of_nonneg_right _ hX.le
  exact mul_le_mul_of_nonneg_left (lidx_mono hH hK hHK) hlp.le

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in

theorem logVol_map (φ : (⨂[ℚ_[p]] i, L i) →+ (⨂[ℚ_[p]] i, L i)) (hφ : Function.Injective φ)
    (hφM : IsLattice p L ((normalization p L).map φ)) {H : AddSubgroup (⨂[ℚ_[p]] i, L i)}
    (hH : IsLattice p L H) :
    IsLattice p L (H.map φ) ∧ logVol p L (H.map φ) = logVol p L H + logVol p L ((normalization p L).map φ) := by
  have h1 : Comm (H.map φ) ((normalization p L).map φ) := hH.map φ hφ
  refine ⟨h1.trans hφM, ?_⟩
  unfold logVol
  rw [lidx_trans h1 hφM, lidx_map φ hφ]
  ring

include B in

theorem logVol_zpow_normalization (k : ℤ) :
    IsLattice p L ((normalization p L).map (smulHom p L ((p : ℚ_[p]) ^ k))) ∧
      logVol p L ((normalization p L).map (smulHom p L ((p : ℚ_[p]) ^ k))) = -k * Real.log p := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hnat : ∀ n : ℕ, IsLattice p L ((normalization p L).map (smulHom p L ((p : ℚ_[p]) ^ n))) ∧
      logVol p L ((normalization p L).map (smulHom p L ((p : ℚ_[p]) ^ n))) = -n * Real.log p := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, map_smulHom_one, CharP.cast_eq_zero, neg_zero, zero_mul]
      exact ⟨isLattice_normalization p, logVol_normalization p⟩
    | succ n ih =>
      have heq : (normalization p L).map (smulHom p L ((p : ℚ_[p]) ^ (n + 1))) =
          ((normalization p L).map (smulHom p L ((p : ℚ_[p]) ^ n))).map (smulHom p L (p : ℚ_[p])) := by
        rw [map_smulHom_map_smulHom, pow_succ, mul_comm]
      rw [heq]
      obtain ⟨hl, hv⟩ := logVol_map p (smulHom p L (p : ℚ_[p])) (smulHom_injective p hp0)
        (isLattice_pNormalization p (B := B)) ih.1
      refine ⟨hl, ?_⟩
      rw [hv, ih.2]
      change _ + logVol p L (pNormalization p L) = _
      rw [logVol_pNormalization p (B := B)]
      push_cast; ring
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · simpa using hnat n
  ·
    set H := (normalization p L).map (smulHom p L ((p : ℚ_[p]) ^ (-(n : ℤ))))
    have hback : H.map (smulHom p L ((p : ℚ_[p]) ^ n)) = normalization p L := by
      rw [map_smulHom_map_smulHom, ← zpow_natCast, ← zpow_add₀ hp0, add_neg_cancel, zpow_zero,
        map_smulHom_one]
    have hinj : Function.Injective (smulHom p L ((p : ℚ_[p]) ^ (-(n : ℤ)))) :=
      smulHom_injective p (zpow_ne_zero _ hp0)
    have hHlat : IsLattice p L H := by
      have hc := (hnat n).1.map _ hinj
      rw [map_smulHom_map_smulHom, ← zpow_natCast, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero,
        map_smulHom_one] at hc
      exact hc.symm
    obtain ⟨_, hv⟩ := logVol_map p (smulHom p L ((p : ℚ_[p]) ^ n))
      (smulHom_injective p (pow_ne_zero _ hp0)) (hnat n).1 hHlat
    rw [hback, logVol_normalization, (hnat n).2] at hv
    refine ⟨hHlat, ?_⟩
    push_cast
    linarith

include B in

theorem logVol_smul_zpow {H : AddSubgroup (⨂[ℚ_[p]] i, L i)} (hH : IsLattice p L H) (k : ℤ) :
    IsLattice p L (H.map (smulHom p L ((p : ℚ_[p]) ^ k))) ∧
      logVol p L (H.map (smulHom p L ((p : ℚ_[p]) ^ k))) = logVol p L H - k * Real.log p := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨hl, hv⟩ := logVol_zpow_normalization p (L := L) (B := B) k
  obtain ⟨hl', hv'⟩ := logVol_map p _ (smulHom_injective p (zpow_ne_zero k hp0)) hl hH
  exact ⟨hl', by rw [hv', hv]; ring⟩

variable (L) in

noncomputable def mulHom (x : ⨂[ℚ_[p]] i, L i) : (⨂[ℚ_[p]] i, L i) →+ (⨂[ℚ_[p]] i, L i) :=
  AddMonoidHom.mulLeft x

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in
theorem mulHom_apply (x y : ⨂[ℚ_[p]] i, L i) : mulHom p L x y = x * y := rfl

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in
theorem map_mulHom_map_mulHom (H : AddSubgroup (⨂[ℚ_[p]] i, L i)) (x y : ⨂[ℚ_[p]] i, L i) :
    (H.map (mulHom p L x)).map (mulHom p L y) = H.map (mulHom p L (y * x)) := by
  rw [AddSubgroup.map_map]
  congr 1
  ext z
  simp [mulHom_apply, mul_assoc]

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in
theorem map_mulHom_smul (H : AddSubgroup (⨂[ℚ_[p]] i, L i)) (c : ℚ_[p]) (x : ⨂[ℚ_[p]] i, L i) :
    H.map (mulHom p L (c • x)) = (H.map (mulHom p L x)).map (smulHom p L c) := by
  rw [AddSubgroup.map_map]
  congr 1
  ext z
  simp [mulHom_apply, smulHom_apply, smul_mul_assoc]

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in
theorem tprod_mul_tprod_inv (y : ∀ i, L i) (hy : ∀ i, y i ≠ 0) :
    tprod ℚ_[p] y * tprod ℚ_[p] (fun i => (y i)⁻¹) = 1 := by
  rw [tprod_mul_tprod]
  have : (y * fun i => (y i)⁻¹) = 1 := funext fun i => by simp [hy i]
  rw [this]
  rfl

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in
theorem mulHom_tprod_injective (y : ∀ i, L i) (hy : ∀ i, y i ≠ 0) :
    Function.Injective (mulHom p L (tprod ℚ_[p] y)) := by
  intro a b h
  simp only [mulHom_apply] at h
  have hinv := tprod_mul_tprod_inv p y hy
  calc a = (tprod ℚ_[p] fun i => (y i)⁻¹) * (tprod ℚ_[p] y * a) := by
        rw [← mul_assoc, mul_comm (tprod ℚ_[p] fun i => (y i)⁻¹) (tprod ℚ_[p] y), hinv, one_mul]
    _ = (tprod ℚ_[p] fun i => (y i)⁻¹) * (tprod ℚ_[p] y * b) := by rw [h]
    _ = b := by rw [← mul_assoc, mul_comm (tprod ℚ_[p] fun i => (y i)⁻¹) (tprod ℚ_[p] y), hinv, one_mul]

omit [∀ i, CompleteSpace (L i)] [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)] in

theorem map_mulHom_unit (u v : ⨂[ℚ_[p]] i, L i) (huv : u * v = 1) (hu : IsIntegral ℤ_[p] u)
    (hv : IsIntegral ℤ_[p] v) : (normalization p L).map (mulHom p L u) = normalization p L := by
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    rw [SetLike.mem_coe, mem_normalization] at hm
    rw [mem_normalization, mulHom_apply]
    exact hu.mul hm
  · intro m hm
    rw [mem_normalization] at hm
    refine ⟨v * m, (mem_normalization p).mpr (hv.mul hm), ?_⟩
    rw [mulHom_apply, ← mul_assoc, huv, one_mul]

omit [∀ i, CompleteSpace (L i)] in

theorem tprod_pow_decomp (R : ∀ i, RamificationData p (L i)) (y : ∀ i, L i) (n : ι → ℤ)
    (hy : ∀ i, ‖y i‖ = ‖(R i).pi‖ ^ n i) :
    ∃ E : ℕ, 0 < E ∧ ∃ s : ℤ, (s : ℝ) = E * ∑ i, (n i : ℝ) / (R i).e ∧
      ∃ u : ∀ i, L i, (∀ i, ‖u i‖ = 1) ∧ (tprod ℚ_[p] y) ^ E = ((p : ℚ_[p]) ^ s) • tprod ℚ_[p] u := by
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
  refine ⟨E, hEpos, ∑ i, N i, ?_, u, ?_, ?_⟩
  · push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have he : ((R i).e : ℝ) ≠ 0 := by exact_mod_cast (R i).e_pos.ne'
    have hEcast : (E : ℝ) = (R i).e * (M i : ℝ) := by exact_mod_cast (hM i).symm
    simp only [hNdef]; push_cast; rw [hEcast]; field_simp
  · intro i
    have he : ((R i).e : ℝ) ≠ 0 := by exact_mod_cast (R i).e_pos.ne'
    have hEcast : (E : ℝ) = (R i).e * (M i : ℝ) := by exact_mod_cast (hM i).symm
    simp only [hudef, norm_mul, norm_pow, norm_algebraMap', norm_inv, norm_zpow, Padic.norm_p, hy i,
      (R i).norm_pi]
    rw [inv_zpow', zpow_neg, inv_inv]
    rw [← Real.rpow_intCast (((p : ℝ) ^ (-1 / ((R i).e : ℝ)))) (n i), ← Real.rpow_mul hpR.le,
      ← Real.rpow_natCast, ← Real.rpow_mul hpR.le, ← Real.rpow_intCast (p : ℝ) (N i), ← Real.rpow_add hpR]
    have key : -1 / ((R i).e : ℝ) * (n i : ℝ) * (E : ℝ) + ((N i : ℤ) : ℝ) = 0 := by
      simp only [hNdef]; push_cast; rw [hEcast]; field_simp; ring
    rw [key, Real.rpow_zero]
  · have hyE : ∀ i, y i ^ E = ((p : ℚ_[p]) ^ N i) • u i := by
      intro i
      simp only [hudef, Algebra.smul_def]
      rw [mul_left_comm, ← map_mul, mul_inv_cancel₀ (zpow_ne_zero _ hp0), map_one, mul_one]
    have h1 : (tprod ℚ_[p] y) ^ E = tprod ℚ_[p] (y ^ E) :=
      (map_pow (tprodMonoidHom (R := ℚ_[p]) (A := L)) y E).symm
    have h2 : y ^ E = fun i => ((p : ℚ_[p]) ^ N i) • u i := funext fun i => by rw [Pi.pow_apply, hyE i]
    rw [h1, h2, MultilinearMap.map_smul_univ, prod_zpow_eq_zpow_sum p _ _ hp0]

include B in

theorem logVol_tprod_normalization (R : ∀ i, RamificationData p (L i)) (y : ∀ i, L i) (n : ι → ℤ)
    (hy : ∀ i, ‖y i‖ = ‖(R i).pi‖ ^ n i) :
    IsLattice p L ((normalization p L).map (mulHom p L (tprod ℚ_[p] y))) ∧
      logVol p L ((normalization p L).map (mulHom p L (tprod ℚ_[p] y))) =
        -(∑ i, (n i : ℝ) / (R i).e) * Real.log p := by
  classical
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hy0 : ∀ i, y i ≠ 0 := fun i h => by
    have h1 := hy i
    rw [h, norm_zero] at h1
    exact zpow_ne_zero _ (norm_ne_zero_iff.mpr (pi_ne_zero p (R i))) h1.symm
  set t := tprod ℚ_[p] y with ht
  set S := ∑ i, (n i : ℝ) / (R i).e with hS
  set T := (normalization p L).map (mulHom p L t) with hT
  have hinj := mulHom_tprod_injective p y hy0

  obtain ⟨a, ha⟩ := exists_nat_ge (|S|)
  have hsum1 : 0 ≤ ((a : ℤ) : ℝ) + S := by push_cast; linarith [neg_abs_le S]
  have hyinv : ∀ i, ‖(y i)⁻¹‖ = ‖(R i).pi‖ ^ (-n i) := fun i => by rw [norm_inv, hy i, zpow_neg]
  have hsum2 : 0 ≤ ((a : ℤ) : ℝ) + ∑ i, ((-n i : ℤ) : ℝ) / (R i).e := by
    push_cast
    have : ∑ i, -(n i : ℝ) / (R i).e = -S := by
      rw [hS, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]; linarith [le_abs_self S]
  have hint1 := isIntegral_zpow_smul_tprod p R y n hy a hsum1
  have hint2 := isIntegral_zpow_smul_tprod p R (fun i => (y i)⁻¹) (fun i => -n i) hyinv a hsum2
  set Mlo := (normalization p L).map (smulHom p L ((p : ℚ_[p]) ^ (a : ℤ)))
  set Mhi := (normalization p L).map (smulHom p L ((p : ℚ_[p]) ^ (-(a : ℤ))))
  have hlo := (logVol_zpow_normalization p (L := L) (B := B) (a : ℤ)).1
  have hhi := (logVol_zpow_normalization p (L := L) (B := B) (-(a : ℤ))).1
  have hloT : Mlo ≤ T := by
    rintro _ ⟨m, hm, rfl⟩
    rw [SetLike.mem_coe, mem_normalization] at hm
    refine ⟨(((p : ℚ_[p]) ^ (a : ℤ)) • tprod ℚ_[p] (fun i => (y i)⁻¹)) * m,
      (mem_normalization p).mpr (hint2.mul hm), ?_⟩
    rw [mulHom_apply, smulHom_apply, ← mul_assoc, mul_smul_comm, tprod_mul_tprod_inv p y hy0, smul_mul_assoc,
      one_mul]
  have hThi : T ≤ Mhi := by
    rintro _ ⟨m, hm, rfl⟩
    rw [SetLike.mem_coe, mem_normalization] at hm
    refine ⟨(((p : ℚ_[p]) ^ (a : ℤ)) • t) * m, (mem_normalization p).mpr (hint1.mul hm), ?_⟩
    rw [mulHom_apply, smulHom_apply, smul_mul_assoc, smul_smul, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero,
      one_smul]
  have hlohi : Comm Mlo Mhi := hlo.trans hhi.symm
  have hcomm : Comm Mlo T := comm_of_le hloT (mt (AddSubgroup.relIndex_eq_zero_of_le_right hThi) hlohi.2)
  have hTlat : IsLattice p L T := hcomm.symm.trans hlo
  refine ⟨hTlat, ?_⟩

  obtain ⟨E, hEpos, s, hs, u, hu, hpow⟩ := tprod_pow_decomp p R y n hy
  have hu0 : ∀ i, u i ≠ 0 := fun i h => by have := hu i; rw [h, norm_zero] at this; exact zero_ne_one this
  have hpowvol : ∀ j : ℕ, IsLattice p L ((normalization p L).map (mulHom p L (t ^ j))) ∧
      logVol p L ((normalization p L).map (mulHom p L (t ^ j))) = j * logVol p L T := by
    intro j
    induction j with
    | zero =>
      have : mulHom p L ((t : ⨂[ℚ_[p]] i, L i) ^ 0) = AddMonoidHom.id _ := by ext z; simp [mulHom_apply]
      rw [this, AddSubgroup.map_id]
      simp [isLattice_normalization, logVol_normalization]
    | succ j ih =>
      have heq : (normalization p L).map (mulHom p L (t ^ (j + 1))) =
          ((normalization p L).map (mulHom p L (t ^ j))).map (mulHom p L t) := by
        rw [map_mulHom_map_mulHom, pow_succ, mul_comm]
      rw [heq]
      obtain ⟨hl, hv⟩ := logVol_map p (mulHom p L t) hinj hTlat ih.1
      exact ⟨hl, by rw [hv, ih.2]; push_cast; ring⟩
  have hEvol := (hpowvol E).2
  have hunit : (normalization p L).map (mulHom p L (tprod ℚ_[p] u)) = normalization p L :=
    map_mulHom_unit p _ _ (tprod_mul_tprod_inv p u hu0)
      (isIntegral_tprod u fun i => isIntegral_of_norm_le_one (hu i).le)
      (isIntegral_tprod _ fun i => isIntegral_of_norm_le_one (by rw [norm_inv, hu i, inv_one]))
  rw [hpow, map_mulHom_smul, hunit, (logVol_zpow_normalization p (L := L) (B := B) s).2, hs] at hEvol
  have hEr : (0 : ℝ) < E := by exact_mod_cast hEpos
  have : (E : ℝ) * logVol p L T = (E : ℝ) * (-S * Real.log p) := by rw [← hEvol]; ring
  exact mul_left_cancel₀ hEr.ne' this

include B in

theorem logVol_mul_tprod (R : ∀ i, RamificationData p (L i)) (y : ∀ i, L i) (n : ι → ℤ)
    (hy : ∀ i, ‖y i‖ = ‖(R i).pi‖ ^ n i) {H : AddSubgroup (⨂[ℚ_[p]] i, L i)} (hH : IsLattice p L H) :
    IsLattice p L (H.map (mulHom p L (tprod ℚ_[p] y))) ∧
      logVol p L (H.map (mulHom p L (tprod ℚ_[p] y))) = logVol p L H - (∑ i, (n i : ℝ) / (R i).e) * Real.log p := by
  have hy0 : ∀ i, y i ≠ 0 := fun i h => by
    have h1 := hy i
    rw [h, norm_zero] at h1
    exact zpow_ne_zero _ (norm_ne_zero_iff.mpr (pi_ne_zero p (R i))) h1.symm
  obtain ⟨hl, hv⟩ := logVol_tprod_normalization p (B := B) R y n hy
  obtain ⟨hl', hv'⟩ := logVol_map p _ (mulHom_tprod_injective p y hy0) hl hH
  exact ⟨hl', by rw [hv', hv]; ring⟩

omit hp in
theorem aExp_sub_le [hp : Fact p.Prime] (e : ℕ) (he : 0 < e) : aExp p e - 1 / (e : ℝ) ≤ 4 / p := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  unfold aExp
  split_ifs with h
  · subst h
    have : 0 < 1 / (e : ℝ) := by positivity
    norm_num
  · have hp3 : (3 : ℝ) ≤ p := by
      have := hp.out.two_le
      have : 3 ≤ p := by omega
      exact_mod_cast this
    have hceil : ((⌈(e : ℝ) / ((p : ℝ) - 2)⌉ : ℤ) : ℝ) ≤ (e : ℝ) / ((p : ℝ) - 2) + 1 :=
      (Int.ceil_lt_add_one _).le
    have h1 : 1 / (e : ℝ) * ((⌈(e : ℝ) / ((p : ℝ) - 2)⌉ : ℤ) : ℝ) ≤ 1 / (e : ℝ) * ((e : ℝ) / ((p : ℝ) - 2) + 1) :=
      mul_le_mul_of_nonneg_left hceil (by positivity)
    have h2 : 1 / (e : ℝ) * ((e : ℝ) / ((p : ℝ) - 2) + 1) = 1 / ((p : ℝ) - 2) + 1 / (e : ℝ) := by
      have hpm : (p : ℝ) - 2 ≠ 0 := by linarith
      field_simp
    have h3 := Src.CoreLayer.LogVol.one_div_sub_two_le_four_div (p : ℝ) hp3
    linarith

omit hp in
theorem bExp_add_mul_log_le [hp : Fact p.Prime] (e : ℕ) (he : 0 < e) :
    (bExp p e + 1 / (e : ℝ)) * Real.log p ≤ Real.log (2 * e) := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hl : 0 < Real.log p := Real.log_pos (by linarith)
  have hb : bExp p e + 1 / (e : ℝ) = (⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ : ℝ) := by
    unfold bExp; ring
  rw [hb]
  have hfl := Int.floor_le (Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p)
  have h1 : (⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ : ℝ) * Real.log p ≤
      Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) := by
    have := mul_le_mul_of_nonneg_right hfl hl.le
    rwa [div_mul_cancel₀ _ hl.ne'] at this
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h2 : (p : ℝ) * e / ((p : ℝ) - 1) ≤ 2 * e := by
    have := Src.CoreLayer.LogVol.p_div_sub_one_le_two (p : ℝ) hp2
    calc (p : ℝ) * e / ((p : ℝ) - 1) = (p / ((p : ℝ) - 1)) * e := by ring
      _ ≤ 2 * e := mul_le_mul_of_nonneg_right this he'.le
  have h3 : Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) ≤ Real.log (2 * e) :=
    Real.log_le_log (by positivity) h2
  linarith

omit hp in
theorem aExp_add_bExp_of_small [hp : Fact p.Prime] (e : ℕ) (he : 0 < e) (hep : e + 2 ≤ p) :
    aExp p e + bExp p e = 0 := by
  have hp2 : p ≠ 2 := by omega
  rw [aExp_eq_of_small p e he hp2 hep, bExp_eq_of_small p e he hep]
  ring

variable (L) in

noncomputable def container (R : ∀ i, RamificationData p (L i)) (m : ℤ) : AddSubgroup (⨂[ℚ_[p]] i, L i) :=
  ((normalization p L).map (mulHom p L (piNegB p R))).map (smulHom p L ((p : ℚ_[p]) ^ m))

include B in

theorem logVol_container (R : ∀ i, RamificationData p (L i)) (m : ℤ) :
    IsLattice p L (container p L R m) ∧ logVol p L (container p L R m) = -((m : ℝ) - bI p R) * Real.log p := by
  obtain ⟨h1, v1⟩ := logVol_tprod_normalization p (B := B) R (fun i => (R i).pi ^ (-bNum p (R i).e))
    (fun i => -bNum p (R i).e) (fun i => norm_zpow _ _)
  obtain ⟨h2, v2⟩ := logVol_smul_zpow p (B := B) h1 m
  refine ⟨h2, ?_⟩
  change logVol p L (((normalization p L).map (mulHom p L (tprod ℚ_[p] fun i => (R i).pi ^ (-bNum p (R i).e)))).map
    (smulHom p L ((p : ℚ_[p]) ^ m))) = _
  rw [v2, v1]
  have hsum : ∑ i, ((-bNum p (R i).e : ℤ) : ℝ) / (R i).e = -bI p R := by
    simp only [bI]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have he : ((R i).e : ℝ) ≠ 0 := by exact_mod_cast (R i).e_pos.ne'
    push_cast
    rw [bNum_eq p (R i).e (R i).e_pos]
    field_simp
  rw [hsum]
  ring

theorem prop14iii_inclusion (R : ∀ i, RamificationData p (L i)) (Δ : DifferentData p B R) (i₀ : ι) (k : ℤ)
    (φ : (⨂[ℚ_[p]] i, L i) →ₗ[ℚ_[p]] (⨂[ℚ_[p]] i, L i)) (hφ : ∀ w ∈ logUnits p L, φ w ∈ logUnits p L)
    (z : ⨂[ℚ_[p]] i, L i) (hz : IsIntegral ℤ_[p] z) :
    φ (piAt p R i₀ k * z) ∈ container p L R ⌊(k : ℝ) / (R i₀).e - dI p Δ - aI p R⌋ := by
  obtain ⟨_, v, hv, heq⟩ := prop12ii p R Δ i₀ k φ hφ z hz
  rw [heq]
  exact ⟨piNegB p R * v, ⟨v, (mem_normalization p).mpr hv, rfl⟩, rfl⟩

include B in

theorem prop14iii_second (R : ∀ i, RamificationData p (L i)) (Δ : DifferentData p B R) (i₀ : ι) (k : ℤ)
    (Istar : Finset ι) (hIstar : ∀ i ∉ Istar, (R i).e + 2 ≤ p) :
    logVol p L (container p L R ⌊(k : ℝ) / (R i₀).e - dI p Δ - aI p R⌋) ≤
      (-((k : ℝ) / (R i₀).e) + dI p Δ + 1) * Real.log p + ∑ i ∈ Istar, (3 + Real.log (R i).e) := by
  rw [(logVol_container p (B := B) R _).2]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have h := Src.CoreLayer.LogVol.second_inequality Istar (p : ℝ) hp2 (fun i => ((R i).e : ℝ))
    (fun i => aExp p (R i).e) (fun i => bExp p (R i).e) (fun i => (Δ.D i : ℝ) / (R i).e)
    ((k : ℝ) / (R i₀).e) (fun i => show (0 : ℝ) < (R i).e by exact_mod_cast (R i).e_pos)
    (fun i _ => aExp_sub_le p (R i).e (R i).e_pos) (fun i _ => bExp_add_mul_log_le p (R i).e (R i).e_pos)
    (fun i hi => aExp_add_bExp_of_small p (R i).e (R i).e_pos (hIstar i hi))
  simpa only [dI, aI, bI] using h

end Packet

section Model

variable (p : ℕ) [hp : Fact p.Prime]

theorem model_logVol_nondegenerate :
    logVol p (fun _ : Fin 2 => ℚ_[p]) (normalization p (fun _ : Fin 2 => ℚ_[p])) = 0 ∧
      logVol p (fun _ : Fin 2 => ℚ_[p]) (pNormalization p (fun _ : Fin 2 => ℚ_[p])) = -Real.log p ∧
      -Real.log p < 0 := by
  refine ⟨logVol_normalization p, logVol_pNormalization p (B := fun _ : Fin 2 => ℤ_[p]), ?_⟩
  have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  linarith [Real.log_pos this]

theorem model_prop14iii_second (hp2 : p ≠ 2) (k : ℤ) :
    ∃ Δ : DifferentData p (fun _ : Fin 2 => ℤ_[p]) (fun _ : Fin 2 => qpRamification p),
      logVol p (fun _ : Fin 2 => ℚ_[p]) (container p (fun _ : Fin 2 => ℚ_[p]) (fun _ => qpRamification p)
        ⌊(k : ℝ) / (qpRamification p).e - dI p Δ - aI p (fun _ : Fin 2 => qpRamification p)⌋) ≤
        (-((k : ℝ) / (qpRamification p).e) + dI p Δ + 1) * Real.log p := by
  obtain ⟨Δ⟩ := exists_qpDifferentData p
  refine ⟨Δ, ?_⟩
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have h := prop14iii_second p (L := fun _ : Fin 2 => ℚ_[p]) (B := fun _ : Fin 2 => ℤ_[p])
    (fun _ => qpRamification p) Δ 0 k ∅ (fun i _ => by change 1 + 2 ≤ p; omega)
  simpa using h

end Model

end Src.IUT4.Proposition14i

section Check
open Src.IUT4.Proposition14i
end Check
