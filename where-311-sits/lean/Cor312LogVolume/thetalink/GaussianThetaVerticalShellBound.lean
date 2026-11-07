import Cor312LogVolume.thetalink.GaussianThetaInd3ShellBound
import Cor312LogVolume.thetalink.GaussianThetaShellBound

noncomputable section
set_option autoImplicit false

namespace CitedLV.ThetaLink.GaussianThetaVerticalShellBound

open Src.IUT3.Proposition35ii
open Src.IUT4.Proposition12i Src.IUT4.Proposition12ii
open CitedLV.Theorem311 CitedLV.Theorem311.TensorIntegralLattice
open CitedLV.Theorem311.TensorFactorHaarCharacter
open CitedLV.Theorem311.PadicNormedRamification
open CitedLV.ActualTensorHaarBound
open CitedLV.ThetaLink.GaussianThetaTensorReadout
open CitedLV.ThetaLink.GaussianThetaInd3ShellBound
open CitedLV.ThetaLink.GaussianThetaShellBound
open CitedLV.ThetaLink.GaussianMonoidFromThetaValues
open CitedLV.ThetaLink.GaussianThetaLogReadout
open Src.EtTh.ThetaValueArithmetic
open scoped BigOperators TensorProduct

variable (p : ℕ) [Fact p.Prime]

section Scalar

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]

theorem normalized_factor_norm_le_one (R : RamificationData p K) (a : K) (k : ℤ)
    (ha : ‖a‖ = ‖R.pi‖ ^ k) :
    ‖((p : ℚ_[p]) ^ (-⌊(k : ℝ) / R.e⌋)) • a‖ ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have han : ‖a‖ = (p : ℝ) ^ (-(k : ℝ) / R.e) := by
    rw [ha, ← norm_zpow, norm_pi_zpow]
  rw [norm_smul, norm_zpow, Padic.norm_p, inv_zpow', neg_neg,
    han, ← Real.rpow_intCast, ← Real.rpow_add hp0]
  apply Real.rpow_le_one_of_one_le_of_nonpos hp1
  rw [neg_div]
  exact sub_nonpos.mpr (Int.floor_le ((k : ℝ) / R.e))

end Scalar

section IntegralStability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Type*)
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, CompleteSpace (L i)] [∀ i, ProperSpace (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

theorem integral_mul_mem_boundRegion (slot : ι) (k : ℤ)
    {b x : TensorIntegralLattice.Packet p L} (hb : IsIntegral ℤ_[p] b)
    (hx : x ∈ (boundRegion p L slot k).val) :
    b * x ∈ (boundRegion p L slot k).val := by
  obtain ⟨v, hv, rfl⟩ := hx
  refine ⟨b * v, hb.mul hv, ?_⟩
  change boundEquiv p L slot k (b * v) = b * boundEquiv p L slot k v
  rw [boundEquiv_apply, boundEquiv_apply, mul_smul_comm]
  exact congrArg (fun z : TensorIntegralLattice.Packet p L =>
    ((p : ℚ_[p]) ^ boundExponent p L slot k) • z) (mul_left_comm _ _ _)

theorem horizontal_factorRegion_subset_boundRegion
    (slot : ι) (a : (L slot)ˣ) (k : ℤ)
    (ha : ‖(a : L slot)‖ = ‖(finiteExtensionRamification p (L slot)).pi‖ ^ k)
    (φ : TensorIntegralLattice.Packet p L ≃ₗ[ℚ_[p]] TensorIntegralLattice.Packet p L)
    (hφ : Src.IUT4.Theorem110.IsAdmissibleAut p L φ) :
    φ '' (factorRegion p L slot a (integralAnchor p L)).val ⊆
      (boundRegion p L slot k).val := by
  let R := fun i => finiteExtensionRamification p (L i)
  let b : (L slot)ˣ := Units.mk0 ((R slot).pi ^ k)
    (zpow_ne_zero k (pi_ne_zero p (R slot)))
  have hab : ‖(a : L slot)‖ = ‖(b : L slot)‖ := by
    simpa only [b, Units.val_mk0, norm_zpow] using ha
  rw [factorRegion_integralAnchor_eq_of_norm_eq p L slot a b hab]
  rintro _ ⟨x, ⟨z, hz, rfl⟩, rfl⟩
  apply possibleImageHull_subset_boundRegion p L slot k
  apply Src.IUT4.Theorem110.possibleImages_subset_hull p R slot k
  exact ⟨φ, hφ, z, hz, rfl⟩

end IntegralStability

section Packet

variable {V : Type*} [DecidableEq V] (K : V → Type*)
  [∀ v, NormedField (K v)] [∀ v, NormedAlgebra ℚ_[p] (K v)]
  [∀ v, CompleteSpace (K v)] [∀ v, IsUltrametricDist (K v)]
  [∀ v, FiniteDimensional ℚ_[p] (K v)] [∀ v, ProperSpace (K v)]
  [∀ v, Algebra ℤ_[p] (K v)] [∀ v, IsScalarTower ℤ_[p] ℚ_[p] (K v)]

omit [DecidableEq V] in

theorem factor_mul_choiceProjection_mem_boundRegion (stage : ℕ)
    (choice : Fin (stage + 1) → V) (slot : Fin (stage + 1))
    (a : K (choice slot)) (k : ℤ)
    (ha : ‖a‖ = ‖(finiteExtensionRamification p (K (choice slot))).pi‖ ^ k)
    {z : Src.IUT3.Proposition35ii.Packet p K stage} (hz : z ∈ packetShell p K stage) :
    factorHom p (fun t => K (choice t)) slot a * choiceProjection p K stage choice z ∈
      (boundRegion p (fun t => K (choice t)) slot k).val := by
  let L := fun t => K (choice t)
  let f : ℤ := ⌊(k : ℝ) / (finiteExtensionRamification p (L slot)).e⌋
  let u : L slot := ((p : ℚ_[p]) ^ (-f)) • a
  have huNorm : ‖u‖ ≤ 1 := normalized_factor_norm_le_one p
    (finiteExtensionRamification p (L slot)) a k ha
  have hu : IsIntegral ℤ_[p] (factorHom p L slot u) :=
    (SrcLib.PadicLog.isIntegral_of_norm_le_one huNorm).map
      ((factorHom p L slot).restrictScalars ℤ_[p])
  have hb := integral_mul_mem_boundRegion p L slot k hu
    (floor_smul_choiceProjection_mem_boundRegion p K stage choice slot k hz)
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have heq : factorHom p L slot u *
      (((p : ℚ_[p]) ^ f) • choiceProjection p K stage choice z) =
        factorHom p L slot a * choiceProjection p K stage choice z := by
    dsimp only [u]
    rw [map_smul, smul_mul_assoc, mul_smul_comm, smul_smul, ← zpow_add₀ hp0]
    simp
  exact heq ▸ hb

theorem factor_mul_kummer_logIter_mem_boundRegion (stage : ℕ)
    (choice : Fin (stage + 1) → V) (slot : Fin (stage + 1))
    (a : K (choice slot)) (k : ℤ)
    (ha : ‖a‖ = ‖(finiteExtensionRamification p (K (choice slot))).pi‖ ^ k)
    (κ : Fin (stage + 1) → (v : V) → K v ≃ₐ[ℚ_[p]] K v)
    (hκ : ∀ t v x, ‖κ t v x‖ = ‖x‖) {m' : ℕ} (hm' : 1 ≤ m')
    (vs : Fin (stage + 1) → V) (u x : (t : Fin (stage + 1)) → K (vs t))
    (hux : ∀ t, LogIter p m' (u t) (x t)) :
    factorHom p (fun t => K (choice t)) slot a *
      choiceProjection p K stage choice
        (packetMap p stage κ (PiTensorProduct.tprod ℚ_[p]
          (fun t => (Pi.single (vs t) (x t) : PlaceSum K)))) ∈
      (boundRegion p (fun t => K (choice t)) slot k).val :=
  factor_mul_choiceProjection_mem_boundRegion p K stage choice slot a k ha
    (kummer_logIter_mem κ hκ hm' vs u x hux)

omit [DecidableEq V] in

theorem gaussian_horizontal_vertical_union_subset_boundRegion (stage : ℕ)
    (choice : Fin (stage + 1) → V) (slot : Fin (stage + 1))
    (s i : (K (choice slot))ˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell : ℕ) (hell : 0 < ell)
    (ξ : Labels ell → (K (choice slot))ˣ) (hξ : ξ ∈ actualProfiles s i ell)
    (label : Labels ell) (n : ℕ) :
    ∃ k : ℤ,
      ‖(ξ label : K (choice slot))‖ ^ n =
        ‖(finiteExtensionRamification p (K (choice slot))).pi‖ ^ k ∧
      (⋃ η ∈ actualProfiles s i ell, ⋃ u : normOneUnits (K (choice slot)),
        ((⋃ φ : TensorIntegralLattice.Packet p (fun t => K (choice t)) ≃ₗ[ℚ_[p]]
              TensorIntegralLattice.Packet p (fun t => K (choice t)),
          ⋃ (_ : Src.IUT4.Theorem110.IsAdmissibleAut p (fun t => K (choice t)) φ),
            φ '' (factorRegion p (fun t => K (choice t)) slot
              ((u : (K (choice slot))ˣ) * η label ^ n)
              (integralAnchor p (fun t => K (choice t)))).val) ∪
          (fun z : Src.IUT3.Proposition35ii.Packet p K stage =>
            factorHom p (fun t => K (choice t)) slot
              (((u : (K (choice slot))ˣ) * η label ^ n : (K (choice slot))ˣ) : K (choice slot)) *
                choiceProjection p K stage choice z) ''
            (packetShell p K stage : Set (Src.IUT3.Proposition35ii.Packet p K stage)))) ⊆
        (boundRegion p (fun t => K (choice t)) slot k).val := by
  let L := fun t => K (choice t)
  obtain ⟨k, hkn, _, _⟩ := gaussian_shell_union_subset_common_hull p L slot
    s i hi h ell hell ξ hξ label n
  refine ⟨k, hkn, ?_⟩
  refine Set.iUnion_subset fun η => Set.iUnion_subset fun hη =>
    Set.iUnion_subset fun u => ?_
  have hnorm : ‖(((u : (L slot)ˣ) * η label ^ n : (L slot)ˣ) : L slot)‖ =
      ‖(finiteExtensionRamification p (L slot)).pi‖ ^ k := by
    have hu : ‖((u : (L slot)ˣ) : L slot)‖ = 1 := u.property
    rw [Units.val_mul, norm_mul, hu, one_mul, Units.val_pow_eq_pow_val, norm_pow,
      actualProfile_norm_independent s i hi h ell hell η ξ hη hξ label]
    exact hkn
  apply Set.union_subset
  · refine Set.iUnion_subset fun φ => Set.iUnion_subset fun hφ => ?_
    exact horizontal_factorRegion_subset_boundRegion p L slot _ k hnorm φ hφ
  · rintro _ ⟨z, hz, rfl⟩
    exact factor_mul_choiceProjection_mem_boundRegion p K stage choice slot _ k hnorm hz

end Packet
end CitedLV.ThetaLink.GaussianThetaVerticalShellBound
