import Cor312LogVolume.thetalink.GaussianThetaTensorReadout
import Cor312LogVolume.logshell.ActualTensorHaarBound
import Cor312LogVolume.Src.IUT4.Section1Proposition13iDifferentLowerBound

noncomputable section
set_option autoImplicit false

namespace CitedLV.ThetaLink.GaussianThetaInd3ShellBound

open Src.IUT3.Remark122 Src.IUT3.Proposition35ii
open Src.IUT4.Proposition12i Src.IUT4.Proposition12ii
open CitedLV.Theorem311.PadicNormedRamification
open CitedLV.Theorem311.PadicNormIntegerRing CitedLV.Theorem311.PadicNormDifferent
open CitedLV.Theorem311.TensorIntegralLattice
open CitedLV.LogShellTensorAction CitedLV.ActualTensorHaarBound
open CitedLV.ThetaLink.GaussianThetaTensorReadout
open scoped BigOperators TensorProduct

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (p : ℕ) [Fact p.Prime]

def shellExponent : ℕ := if p = 2 then 2 else 1

theorem pStar_eq_pow : (pStar p : ℚ_[p]) = (p : ℚ_[p]) ^ shellExponent p := by
  by_cases hp : p = 2
  · subst p
    norm_num [pStar, shellExponent]
  · simp [pStar, shellExponent, hp]

theorem source_shell_factor (r : ℕ) :
    ∃ u : ℤ_[p]ˣ,
      (p : ℚ_[p]) ^ (-(r : ℤ)) * (2 : ℚ_[p]) ^ (-(r : ℤ)) *
          (((u : ℤ_[p]) : ℚ_[p]) ^ r) = (pStar p : ℚ_[p]) ^ (-(r : ℤ)) := by
  by_cases hp : p = 2
  · subst p
    refine ⟨1, ?_⟩
    simp only [Units.val_one, PadicInt.coe_one, one_pow, mul_one, pStar,
      Nat.cast_ofNat, zpow_neg, zpow_natCast, ← mul_inv, ← mul_pow]
    norm_num
  · have h2 : IsUnit (2 : ℤ_[p]) := by
      apply PadicInt.isUnit_iff.mpr
      exact PadicInt.norm_natCast_eq_one_iff.mpr
        ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp)
    refine ⟨h2.unit, ?_⟩
    have hu : ((h2.unit : ℤ_[p]) : ℚ_[p]) = 2 := by rw [IsUnit.unit_spec]; norm_cast
    rw [hu]
    simp [pStar, hp, zpow_neg, zpow_natCast]

section Bounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Type*)
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, CompleteSpace (L i)] [∀ i, ProperSpace (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

omit [Fintype ι] [DecidableEq ι] [∀ i, ProperSpace (L i)] in
private theorem different_add_a_ge_shellExponent (i : ι) :
    letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
      fun i => normIntegers_discreteValuationRing p (L i)
    let R := fun i => finiteExtensionRamification p (L i)
    let Δ := (actualDifferentData p L).val
    (shellExponent p : ℝ) ≤ (Δ.D i : ℝ) / (R i).e + aExp p (R i).e := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
    fun i => normIntegers_discreteValuationRing p (L i)
  let R := fun i => finiteExtensionRamification p (L i)
  let Δ := (actualDifferentData p L).val
  change (shellExponent p : ℝ) ≤ (Δ.D i : ℝ) / (R i).e + aExp p (R i).e
  by_cases hp : p = 2
  · simp only [shellExponent, aExp, hp, if_pos]
    have hd : (0 : ℝ) ≤ (Δ.D i : ℝ) / (R i).e := by positivity
    norm_num only [Nat.cast_ofNat]
    linarith
  · have he : (0 : ℝ) < (R i).e := by exact_mod_cast (R i).e_pos
    have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
    have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hceil : (1 : ℝ) ≤ (⌈((R i).e : ℝ) / ((p : ℝ) - 2)⌉ : ℤ) := by
      exact_mod_cast (Int.one_le_ceil_iff.mpr (div_pos he (by linarith : (0 : ℝ) < p - 2)))
    have ha : 1 / ((R i).e : ℝ) ≤ aExp p (R i).e := by
      simp only [aExp, hp, if_false]
      nlinarith [mul_le_mul_of_nonneg_left hceil (le_of_lt (one_div_pos.mpr he))]
    have hd := Src.IUT4.Proposition13.prop13i_Qp_real p (R i)
      (Δ.δ i) (Δ.mem i) (Δ.D i) (Δ.norm_eq i)
    have heq : (((R i).e : ℝ) - 1) / (R i).e + 1 / (R i).e = 1 := by
      field_simp
      ring
    simp only [shellExponent, hp, if_false, Nat.cast_one]
    linarith

omit [DecidableEq ι] [∀ i, ProperSpace (L i)] in
theorem boundExponent_le_shellExponent (slot : ι) (k : ℤ) :
    boundExponent p L slot k ≤
      ⌊(k : ℝ) / (finiteExtensionRamification p (L slot)).e⌋ -
        (Fintype.card ι * shellExponent p : ℕ) := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
    fun i => normIntegers_discreteValuationRing p (L i)
  let R := fun i => finiteExtensionRamification p (L i)
  let Δ := (actualDifferentData p L).val
  have hs : (Fintype.card ι * shellExponent p : ℕ) ≤ dI p Δ + aI p R := by
    simpa only [dI, aI, ← Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Nat.cast_mul] using
      Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
        different_add_a_ge_shellExponent p L i)
  have hf := Int.floor_mono (sub_le_sub_left hs ((k : ℝ) / (R slot).e))
  simpa only [boundExponent, sub_add_eq_sub_sub, Int.floor_sub_natCast] using hf

end Bounds

section Packet

variable {V : Type*} [DecidableEq V] (K : V → Type*)
  [∀ v, NormedField (K v)] [∀ v, NormedAlgebra ℚ_[p] (K v)]
  [∀ v, CompleteSpace (K v)] [∀ v, IsUltrametricDist (K v)]
  [∀ v, FiniteDimensional ℚ_[p] (K v)] [∀ v, ProperSpace (K v)]
  [∀ v, Algebra ℤ_[p] (K v)] [∀ v, IsScalarTower ℤ_[p] ℚ_[p] (K v)]

omit [DecidableEq V] [∀ v, FiniteDimensional ℚ_[p] (K v)]
  [∀ v, IsScalarTower ℤ_[p] ℚ_[p] (K v)] [∀ v, Algebra ℤ_[p] (K v)] in
theorem pStar_smul_choiceProjection_mem_logUnits (stage : ℕ)
    (choice : Fin (stage + 1) → V) {z : Src.IUT3.Proposition35ii.Packet p K stage}
    (hz : z ∈ packetShell p K stage) :
    ((pStar p : ℚ_[p]) ^ (stage + 1)) • choiceProjection p K stage choice z ∈
      logUnits p (fun a => K (choice a)) := by
  let T : AddSubgroup (Src.IUT3.Proposition35ii.Packet p K stage) :=
    (logUnits p (fun a => K (choice a))).toAddSubgroup.comap
      (((pStar p : ℚ_[p]) ^ (stage + 1)) •
        choiceProjection p K stage choice).toAddMonoidHom
  have hle : packetShell p K stage ≤ T := by
    rw [packetShell, AddSubgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    change ((pStar p : ℚ_[p]) ^ (stage + 1)) •
      choiceProjection p K stage choice (PiTensorProduct.tprod ℚ_[p] y) ∈
        logUnits p (fun a => K (choice a))
    rw [choiceProjection_tprod]
    have heq : ((pStar p : ℚ_[p]) ^ (stage + 1)) •
        (PiTensorProduct.tprod ℚ_[p] (fun a => y a (choice a)) :
          ⨂[ℚ_[p]] a : Fin (stage + 1), K (choice a)) =
        PiTensorProduct.tprod ℚ_[p] (fun a => (pStar p : ℚ_[p]) • y a (choice a)) := by
      rw [MultilinearMap.map_smul_univ]
      simp
    have hgen : (PiTensorProduct.tprod ℚ_[p]
        (fun a => (pStar p : ℚ_[p]) • y a (choice a))) ∈
        logUnits p (fun a => K (choice a)) := by
      apply Submodule.subset_span
      refine ⟨_, fun a => ?_, rfl⟩
      apply (mem_logUnitsSet_iff_inv_smul_shell p _).mpr
      have hp0 : (pStar p : ℚ_[p]) ≠ 0 := CitedLV.LocalLogShellCompactness.pStar_ne_zero p
      simpa only [smul_smul, inv_mul_cancel₀ hp0, one_smul] using hy a (choice a)
    exact heq.symm ▸ hgen
  exact hle hz

omit [DecidableEq V] in

theorem floor_smul_choiceProjection_mem_boundRegion (stage : ℕ)
    (choice : Fin (stage + 1) → V) (slot : Fin (stage + 1)) (k : ℤ)
    {z : Src.IUT3.Proposition35ii.Packet p K stage} (hz : z ∈ packetShell p K stage) :
    ((p : ℚ_[p]) ^ ⌊(k : ℝ) / (finiteExtensionRamification p (K (choice slot))).e⌋) •
      choiceProjection p K stage choice z ∈
        (boundRegion p (fun a => K (choice a)) slot k).val := by
  let L := fun a => K (choice a)
  let R := fun a => finiteExtensionRamification p (L a)
  let f : ℤ := ⌊(k : ℝ) / (R slot).e⌋
  let b : ℤ := boundExponent p L slot k
  let r : ℕ := (stage + 1) * shellExponent p
  have hbr : b ≤ f - (r : ℤ) := by
    simpa only [L, R, Fintype.card_fin] using boundExponent_le_shellExponent p L slot k
  let w := ((pStar p : ℚ_[p]) ^ (stage + 1)) • choiceProjection p K stage choice z
  have hw : w ∈ logUnits p L := pStar_smul_choiceProjection_mem_logUnits p K stage choice hz
  obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ f - r - b by omega)
  have hw' : ((p : ℚ_[p]) ^ N) • w ∈ logUnits p L := by
    simpa only [← map_pow, map_natCast, algebraMap_smul] using
      (logUnits p L).smul_mem ((p : ℤ_[p]) ^ N) hw
  obtain ⟨v, hv, heq⟩ := prop12ii_second p R _ hw'
  refine ⟨v, hv, ?_⟩
  change boundEquiv p L slot k v = (p : ℚ_[p]) ^ f • choiceProjection p K stage choice z
  rw [boundEquiv_apply]
  change (p : ℚ_[p]) ^ b • (piNegB p R * v) = _
  rw [← heq]
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hw_eq : w = ((p : ℚ_[p]) ^ (r : ℤ)) • choiceProjection p K stage choice z := by
    dsimp only [w]
    rw [pStar_eq_pow, ← pow_mul]
    simp only [r, Nat.mul_comm, zpow_natCast]
  have hexp : b + (N : ℤ) + r = f := by omega
  rw [hw_eq, ← hexp]
  simp only [zpow_add₀ hp0, zpow_natCast, smul_smul, mul_assoc]
  exact smul_smul _ _ _

theorem floor_smul_kummer_logIter_mem_boundRegion (stage : ℕ)
    (choice : Fin (stage + 1) → V) (slot : Fin (stage + 1)) (k : ℤ)
    (κ : Fin (stage + 1) → (v : V) → K v ≃ₐ[ℚ_[p]] K v)
    (hκ : ∀ t v x, ‖κ t v x‖ = ‖x‖) {m' : ℕ} (hm' : 1 ≤ m')
    (vs : Fin (stage + 1) → V) (u x : (t : Fin (stage + 1)) → K (vs t))
    (hux : ∀ t, LogIter p m' (u t) (x t)) :
    ((p : ℚ_[p]) ^ ⌊(k : ℝ) / (finiteExtensionRamification p (K (choice slot))).e⌋) •
      choiceProjection p K stage choice
        (packetMap p stage κ (PiTensorProduct.tprod ℚ_[p]
          (fun t => (Pi.single (vs t) (x t) : PlaceSum K)))) ∈
      (boundRegion p (fun a => K (choice a)) slot k).val :=
  floor_smul_choiceProjection_mem_boundRegion p K stage choice slot k
    (kummer_logIter_mem κ hκ hm' vs u x hux)

end Packet
end CitedLV.ThetaLink.GaussianThetaInd3ShellBound
