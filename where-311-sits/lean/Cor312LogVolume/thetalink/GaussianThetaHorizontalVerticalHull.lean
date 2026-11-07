import Cor312LogVolume.thetalink.GaussianThetaVerticalShellBound

noncomputable section
set_option autoImplicit false

namespace CitedLV.ThetaLink.GaussianThetaHorizontalVerticalHull

open Src.IUT4.Proposition14i
open Src.IUT4.Proposition12i Src.IUT4.Proposition12ii
open CitedLV.Theorem311 CitedLV.Theorem311.TensorIntegralLattice
open CitedLV.Theorem311.TensorFactorHaarCharacter
open CitedLV.Theorem311.PadicNormedRamification
open CitedLV.ActualTensorHaarBound CitedLV.ActualTensorHaarNumericalBound
open CitedLV.ThetaLink.GaussianThetaTensorReadout
open CitedLV.ThetaLink.GaussianThetaVerticalShellBound
open CitedLV.ThetaLink.GaussianMonoidFromThetaValues
open CitedLV.ThetaLink.GaussianThetaLogReadout
open Src.EtTh.ThetaValueArithmetic
open scoped TensorProduct Topology

variable (p : ℕ) [Fact p.Prime]

section Intersection
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Type*)
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, CompleteSpace (L i)] [∀ i, ProperSpace (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

def lambdaIntersection (P : Set (Packet p L)) : AddSubgroup (Packet p L) :=
  ⨅ (c : Packet p L) (_ : IsUnit c)
    (_ : P ⊆ ((normalization p L).map (mulHom p L c) : Set (⨂[ℚ_[p]] i, L i))),
      (normalization p L).map (mulHom p L c)

omit [Fintype ι] [DecidableEq ι]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, CompleteSpace (L i)] [∀ i, ProperSpace (L i)]
  [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)] [∀ i, Algebra ℤ_[p] (L i)] in
theorem subset_lambdaIntersection (P : Set (Packet p L)) :
    P ⊆ (lambdaIntersection p L P : Set (Packet p L)) := by
  intro x hx
  simp only [lambdaIntersection, SetLike.mem_coe, AddSubgroup.mem_iInf]
  exact fun _ _ h => h hx

theorem boundRegion_eq_candidate (slot : ι) (k : ℤ) :
    (boundRegion p L slot k).val =
      ((normalization p L).map (mulHom p L
        (((p : ℚ_[p]) ^ boundExponent p L slot k) •
          piNegB p (fun i => finiteExtensionRamification p (L i)))) : Set (⨂[ℚ_[p]] i, L i)) := by
  ext x
  constructor <;> rintro ⟨z, hz, heq⟩ <;> refine ⟨z, hz, ?_⟩
  · have hm : ∀ (r : ℚ_[p]) (y w : ⨂[ℚ_[p]] i, L i),
        (r • y) * w = r • (y * w) := fun r y w => smul_mul_assoc r y w
    exact (hm _ _ z).trans ((boundEquiv_apply p L slot k z).symm.trans heq)
  · change boundEquiv p L slot k z = x
    rw [boundEquiv_apply]
    exact (smul_mul_assoc _ _ _).symm.trans heq

private theorem lambdaIntersection_subset_bound (P : Set (Packet p L))
    (slot : ι) (k : ℤ) (hP : P ⊆ (boundRegion p L slot k).val) :
    (lambdaIntersection p L P : Set (Packet p L)) ⊆ (boundRegion p L slot k).val := by
  rw [boundRegion_eq_candidate] at hP ⊢
  intro x hx
  simp only [lambdaIntersection, SetLike.mem_coe, AddSubgroup.mem_iInf] at hx
  exact hx _ (Src.IUT4.Theorem110.isUnit_zpow_smul_piNegB p
    (fun i => finiteExtensionRamification p (L i)) (boundExponent p L slot k)) hP
end Intersection

variable {V : Type*} (K : V → Type*)
  [∀ v, NormedField (K v)] [∀ v, NormedAlgebra ℚ_[p] (K v)]
  [∀ v, CompleteSpace (K v)] [∀ v, IsUltrametricDist (K v)]
  [∀ v, FiniteDimensional ℚ_[p] (K v)] [∀ v, ProperSpace (K v)]
  [∀ v, Algebra ℤ_[p] (K v)] [∀ v, IsScalarTower ℤ_[p] ℚ_[p] (K v)]

def horizontalVerticalImages (stage : ℕ)
    (choice : Fin (stage + 1) → V) (slot : Fin (stage + 1))
    (s i : (K (choice slot))ˣ) (ell : ℕ) (label : Labels ell) (n : ℕ) :
    Set (Packet p (fun t => K (choice t))) :=
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
            (Src.IUT3.Proposition35ii.packetShell p K stage : Set (Src.IUT3.Proposition35ii.Packet p K stage))))

theorem gaussian_horizontal_vertical_actualHaar_hull (stage : ℕ)
    (choice : Fin (stage + 1) → V) (slot : Fin (stage + 1))
    (s i : (K (choice slot))ˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell : ℕ) (hell : 0 < ell)
    (ξ : Labels ell → (K (choice slot))ˣ) (hξ : ξ ∈ actualProfiles s i ell)
    (label : Labels ell) (n : ℕ) :
    let L := fun t => K (choice t)
    let U := horizontalVerticalImages p K stage choice slot s i ell label n
    ∃ (k : ℤ) (H : NormalizedHaarRegion (Packet p L)),
      ‖(ξ label : K (choice slot))‖ ^ n =
        ‖(finiteExtensionRamification p (K (choice slot))).pi‖ ^ k ∧
      H.val = (lambdaIntersection p L U : Set (Packet p L)) ∧
      U ⊆ H.val ∧ H.val ⊆ (boundRegion p L slot k).val ∧
      normalizedHaarLogVolume (integralAnchor p L) H /
          (Module.finrank ℚ_[p] (Packet p L) : ℝ) ≤
        (bI p (fun t => finiteExtensionRamification p (L t)) -
          (boundExponent p L slot k : ℝ)) * Real.log (p : ℝ) := by
  let L := fun t => K (choice t)
  let U := horizontalVerticalImages p K stage choice slot s i ell label n
  obtain ⟨k, hk, hUB⟩ := gaussian_horizontal_vertical_union_subset_boundRegion
    p K stage choice slot s i hi h ell hell ξ hξ label n
  change U ⊆ (boundRegion p L slot k).val at hUB
  let H := lambdaIntersection p L U
  have hUH : U ⊆ (H : Set (Packet p L)) := subset_lambdaIntersection p L U
  have hHB : (H : Set (Packet p L)) ⊆ (boundRegion p L slot k).val :=
    lambdaIntersection_subset_bound p L U slot k hUB
  let A := factorRegion p L slot (ξ label ^ n) (integralAnchor p L)
  have hAU : A.val ⊆ U := by
    intro x hx
    apply Set.mem_iUnion_of_mem ξ
    apply Set.mem_iUnion_of_mem hξ
    apply Set.mem_iUnion_of_mem (1 : normOneUnits (K (choice slot)))
    apply Or.inl
    apply Set.mem_iUnion_of_mem (LinearEquiv.refl ℚ_[p] (Packet p L))
    apply Set.mem_iUnion_of_mem (fun _ => Iff.rfl)
    refine ⟨x, ?_, rfl⟩
    simpa only [OneMemClass.coe_one, one_mul] using hx
  have hzero : (0 : Packet p L) ∈ A.val := by
    refine ⟨0, (integralLattice p L).zero_mem, ?_⟩
    exact map_zero ((factorUnit p L slot (ξ label ^ n)).mulLeftLinearEquiv
      ℚ_[p] (Packet p L))
  have hOpen : IsOpen (H : Set (Packet p L)) :=
    H.isOpen_of_mem_nhds (Filter.mem_of_superset
      (A.property.1.2.mem_nhds hzero) (hAU.trans hUH))
  let region : NormalizedHaarRegion (Packet p L) :=
    ⟨H, ⟨(boundRegion p L slot k).property.1.1.of_isClosed_subset
      (H.isClosed_of_isOpen hOpen) hHB, hOpen⟩, ⟨0, H.zero_mem⟩⟩
  refine ⟨k, region, hk, rfl, hUH, hHB, ?_⟩
  have hd : (0 : ℝ) < Module.finrank ℚ_[p] (Packet p L) := by
    exact_mod_cast packet_finrank_pos p L
  have hm := normalizedHaarLogVolume_mono (integralAnchor p L) region
    (boundRegion p L slot k) hHB
  rw [bound_logVolume_numerical] at hm
  apply (div_le_iff₀ hd).mpr
  convert hm using 1
  ring

end CitedLV.ThetaLink.GaussianThetaHorizontalVerticalHull
