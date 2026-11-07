import Cor312LogVolume.thetalink.GaussianThetaHorizontalVerticalHull
import Cor312LogVolume.theorem311.TensorNormalizationPrincipal

noncomputable section
set_option autoImplicit false

namespace CitedLV.ThetaLink.GaussianThetaHorizontalVerticalPrincipalHull

open Src.IUT4.Proposition14i
open Src.IUT4.Proposition12i Src.IUT4.Proposition12ii
open CitedLV.Theorem311 CitedLV.Theorem311.TensorIntegralLattice
open CitedLV.Theorem311.TensorFactorHaarCharacter
open CitedLV.Theorem311.TensorNormalizationPrincipal
open CitedLV.Theorem311.PadicNormedRamification
open CitedLV.ActualTensorHaarBound CitedLV.ActualTensorHaarNumericalBound
open CitedLV.ThetaLink.GaussianThetaHorizontalVerticalHull
open CitedLV.ThetaLink.GaussianThetaTensorReadout
open CitedLV.ThetaLink.GaussianThetaVerticalShellBound
open CitedLV.ThetaLink.GaussianMonoidFromThetaValues
open CitedLV.ThetaLink.GaussianThetaLogReadout
open Src.EtTh.ThetaValueArithmetic
open scoped TensorProduct

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

variable (p : ℕ) [Fact p.Prime]

section Intersection
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Type*)
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, CompleteSpace (L i)] [∀ i, ProperSpace (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

private theorem lambdaIntersection_principal (P : Set (Packet p L))
    (slot : ι) (k : ℤ) (hPB : P ⊆ (boundRegion p L slot k).val)
    (a : (Packet p L)ˣ) (ha : (a : Packet p L) ∈ P) :
    ∃ c : (Packet p L)ˣ,
      (lambdaIntersection p L P : Set (Packet p L)) =
        (unitRegion p L c (integralAnchor p L)).val := by
  let O := (integralClosure ℤ_[p] (Packet p L)).toSubring
  letI : IsPrincipalIdealRing O := packet_normalization_isPrincipalIdealRing p L
  let H := lambdaIntersection p L P
  have hs : ∀ (r : O) (x : Packet p L), x ∈ H → (r : Packet p L) * x ∈ H := by
    intro r x hx
    simp only [H, lambdaIntersection, AddSubgroup.mem_iInf] at hx ⊢
    intro c hc hPc
    obtain ⟨z, hz, heq⟩ := hx c hc hPc
    refine ⟨Mul.mul (α := Packet p L) (r : Packet p L) z, ?_, ?_⟩
    · exact (integralClosure ℤ_[p] (Packet p L)).mul_mem r.property hz
    · have hm : ∀ (c r w : Packet p L), c * (r * w) = r * (c * w) :=
        fun c r w => mul_left_comm c r w
      exact (hm c r z).trans (congrArg (fun y : Packet p L => (r : Packet p L) * y) heq)
  let b₀ : Packet p L := ((p : ℚ_[p]) ^ boundExponent p L slot k) •
    piNegB p (fun i => finiteExtensionRamification p (L i))
  have hb : IsUnit b₀ := Src.IUT4.Theorem110.isUnit_zpow_smul_piNegB p
    (fun i => finiteExtensionRamification p (L i)) (boundExponent p L slot k)
  have hPc : P ⊆ ((normalization p L).map (mulHom p L b₀) :
      Set (⨂[ℚ_[p]] i, L i)) := by
    simpa only [boundRegion_eq_candidate] using hPB
  have hB : ∀ x ∈ H, ∃ z : O, (hb.unit : Packet p L) * z = x := by
    intro x hx
    simp only [H, lambdaIntersection, AddSubgroup.mem_iInf] at hx
    obtain ⟨z, hz, heq⟩ := hx b₀ hb hPc
    refine ⟨⟨z, hz⟩, ?_⟩
    simpa only [hb.unit_spec] using heq
  obtain ⟨c, hc⟩ := principal_of_bounded O H hs hb.unit hB a
    (subset_lambdaIntersection p L P ha)
  refine ⟨c, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (hc x).mp hx
    exact ⟨z, z.property, hz⟩
  · rintro ⟨z, hz, heq⟩
    exact (hc x).mpr ⟨⟨z, hz⟩, heq⟩
end Intersection

variable {V : Type*} (K : V → Type*)
  [∀ v, NormedField (K v)] [∀ v, NormedAlgebra ℚ_[p] (K v)]
  [∀ v, CompleteSpace (K v)] [∀ v, IsUltrametricDist (K v)]
  [∀ v, FiniteDimensional ℚ_[p] (K v)] [∀ v, ProperSpace (K v)]
  [∀ v, Algebra ℤ_[p] (K v)] [∀ v, IsScalarTower ℤ_[p] ℚ_[p] (K v)]

theorem gaussian_horizontal_vertical_principal_hull (stage : ℕ)
    (choice : Fin (stage + 1) → V) (slot : Fin (stage + 1))
    (s i : (K (choice slot))ˣ) (hi : i ^ 2 = -1)
    (h : PublishedThetaFacts s i) (ell : ℕ) (hell : 0 < ell)
    (ξ : Labels ell → (K (choice slot))ˣ) (hξ : ξ ∈ actualProfiles s i ell)
    (label : Labels ell) (n : ℕ) :
    let L := fun t => K (choice t)
    let U := horizontalVerticalImages p K stage choice slot s i ell label n
    ∃ (k : ℤ) (c : (Packet p L)ˣ),
      ‖(ξ label : K (choice slot))‖ ^ n =
        ‖(finiteExtensionRamification p (K (choice slot))).pi‖ ^ k ∧
      (unitRegion p L c (integralAnchor p L)).val =
        (lambdaIntersection p L U : Set (Packet p L)) ∧
      U ⊆ (unitRegion p L c (integralAnchor p L)).val ∧
      (unitRegion p L c (integralAnchor p L)).val ⊆ (boundRegion p L slot k).val ∧
      (∀ d : (Packet p L)ˣ,
        U ⊆ (unitRegion p L d (integralAnchor p L)).val →
        (unitRegion p L c (integralAnchor p L)).val ⊆
          (unitRegion p L d (integralAnchor p L)).val) ∧
      normalizedHaarLogVolume (integralAnchor p L)
          (unitRegion p L c (integralAnchor p L)) /
          (Module.finrank ℚ_[p] (Packet p L) : ℝ) ≤
        (bI p (fun t => finiteExtensionRamification p (L t)) -
          (boundExponent p L slot k : ℝ)) * Real.log (p : ℝ) := by
  let L := fun t => K (choice t)
  let U := horizontalVerticalImages p K stage choice slot s i ell label n
  obtain ⟨k, H, hk, hH, hUH, hHB, hvol⟩ :=
    gaussian_horizontal_vertical_actualHaar_hull
      p K stage choice slot s i hi h ell hell ξ hξ label n
  let a := factorUnit p L slot (ξ label ^ n)
  have ha : (a : Packet p L) ∈ U := by
    apply Set.mem_iUnion_of_mem ξ
    apply Set.mem_iUnion_of_mem hξ
    apply Set.mem_iUnion_of_mem (1 : normOneUnits (K (choice slot)))
    apply Or.inl
    apply Set.mem_iUnion_of_mem (LinearEquiv.refl ℚ_[p] (Packet p L))
    apply Set.mem_iUnion_of_mem (fun _ => Iff.rfl)
    refine ⟨a, ?_, rfl⟩
    simp only [OneMemClass.coe_one, one_mul]
    exact ⟨1, isIntegral_one, mul_one (a : Packet p L)⟩
  obtain ⟨c, hc⟩ := lambdaIntersection_principal p L U slot k (hUH.trans hHB) a ha
  have hHr : H = unitRegion p L c (integralAnchor p L) := Subtype.ext (hH.trans hc)
  rw [hHr] at hUH hHB hvol
  refine ⟨k, c, hk, hc.symm, hUH, hHB, ?_, hvol⟩
  intro d hd x hx
  rw [← hc] at hx
  simp only [lambdaIntersection, SetLike.mem_coe, AddSubgroup.mem_iInf] at hx
  exact hx d d.isUnit hd

end CitedLV.ThetaLink.GaussianThetaHorizontalVerticalPrincipalHull
