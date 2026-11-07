import Mathlib
import Cor312LogVolume.Src.IUT4.Section1Proposition14iNormalizedLogVolume

namespace Src.IUT4.Theorem110

open PiTensorProduct
open scoped TensorProduct
open SrcLib.LatticeLogIndex Src.IUT4.Proposition11 Src.IUT4.Proposition12i
  Src.IUT4.Proposition12ii Src.IUT4.Proposition14i SrcLib.PadicLog

variable (p : ℕ) [hp : Fact p.Prime]

section Component

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

def IsAdmissibleAut (φ : (⨂[ℚ_[p]] i, L i) ≃ₗ[ℚ_[p]] (⨂[ℚ_[p]] i, L i)) : Prop :=
  ∀ w, w ∈ logUnits p L ↔ φ w ∈ logUnits p L

variable (L) in

def possibleImages (R : ∀ i, RamificationData p (L i)) (i₀ : ι) (k : ℤ) : Set (⨂[ℚ_[p]] i, L i) :=
  {x | ∃ φ : (⨂[ℚ_[p]] i, L i) ≃ₗ[ℚ_[p]] (⨂[ℚ_[p]] i, L i), IsAdmissibleAut p L φ ∧
    ∃ z, IsIntegral ℤ_[p] z ∧ x = φ (piAt p R i₀ k * z)}

variable (L) in

noncomputable def possibleImageHull (R : ∀ i, RamificationData p (L i)) (i₀ : ι) (k : ℤ) :
    AddSubgroup (⨂[ℚ_[p]] i, L i) :=
  ⨅ (c : ⨂[ℚ_[p]] i, L i) (_ : IsUnit c)
    (_ : possibleImages p L R i₀ k ⊆ ((normalization p L).map (mulHom p L c) : Set (⨂[ℚ_[p]] i, L i))),
    (normalization p L).map (mulHom p L c)

theorem possibleImages_subset_hull (R : ∀ i, RamificationData p (L i)) (i₀ : ι) (k : ℤ) :
    possibleImages p L R i₀ k ⊆ (possibleImageHull p L R i₀ k : Set (⨂[ℚ_[p]] i, L i)) := by
  intro x hx
  simp only [possibleImageHull, SetLike.mem_coe, AddSubgroup.mem_iInf]
  intro c _ hsub
  exact hsub hx

theorem isUnit_zpow_smul_piNegB (R : ∀ i, RamificationData p (L i)) (m : ℤ) :
    IsUnit (((p : ℚ_[p]) ^ m) • piNegB p R) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  refine isUnit_iff_exists_inv.mpr ⟨((p : ℚ_[p]) ^ (-m)) •
    tprod ℚ_[p] (fun i => ((R i).pi ^ (-bNum p (R i).e))⁻¹), ?_⟩
  rw [smul_mul_smul_comm, ← zpow_add₀ hp0, add_neg_cancel, zpow_zero, one_smul, piNegB,
    tprod_mul_tprod_inv p _ fun i => zpow_ne_zero _ (pi_ne_zero p (R i))]

theorem possibleImageHull_le_container (R : ∀ i, RamificationData p (L i)) (Δ : DifferentData p B R)
    (i₀ : ι) (k : ℤ) :
    possibleImageHull p L R i₀ k ≤ container p L R ⌊(k : ℝ) / (R i₀).e - dI p Δ - aI p R⌋ := by
  set m := ⌊(k : ℝ) / (R i₀).e - dI p Δ - aI p R⌋
  have hc : container p L R m =
      (normalization p L).map (mulHom p L (((p : ℚ_[p]) ^ m) • piNegB p R)) := by
    rw [container, map_mulHom_smul]
  have hsub : possibleImages p L R i₀ k ⊆
      ((normalization p L).map (mulHom p L (((p : ℚ_[p]) ^ m) • piNegB p R)) : Set (⨂[ℚ_[p]] i, L i)) := by
    rintro _ ⟨φ, hφ, z, hz, rfl⟩
    rw [← hc]
    exact prop14iii_inclusion p R Δ i₀ k φ.toLinearMap (fun w hw => (hφ w).mp hw) z hz
  rw [hc]
  exact iInf_le_of_le (((p : ℚ_[p]) ^ m) • piNegB p R)
    (iInf_le_of_le (isUnit_zpow_smul_piNegB p R m) (iInf_le_of_le hsub le_rfl))

theorem le_possibleImageHull (R : ∀ i, RamificationData p (L i)) (i₀ : ι) (k : ℤ) :
    (normalization p L).map (mulHom p L (piAt p R i₀ k)) ≤ possibleImageHull p L R i₀ k := by
  rintro _ ⟨z, hz, rfl⟩
  rw [SetLike.mem_coe, mem_normalization] at hz
  exact possibleImages_subset_hull p R i₀ k ⟨LinearEquiv.refl ℚ_[p] _, fun w => Iff.rfl, z, hz, rfl⟩

theorem isLattice_of_le_of_le {T H C : AddSubgroup (⨂[ℚ_[p]] i, L i)} (hT : IsLattice p L T)
    (hC : IsLattice p L C) (h1 : T ≤ H) (h2 : H ≤ C) : IsLattice p L H := by
  have hTC : Comm T C := hT.trans hC.symm
  have hTH : Comm T H := comm_of_le h1 (mt (AddSubgroup.relIndex_eq_zero_of_le_right h2) hTC.2)
  exact hTH.symm.trans hT

theorem norm_piAt_factor (R : ∀ i, RamificationData p (L i)) (i₀ : ι) (k : ℤ) (i : ι) :
    ‖Pi.mulSingle i₀ ((R i₀).pi ^ k) i‖ = ‖(R i).pi‖ ^ (if i = i₀ then k else 0) := by
  by_cases h : i = i₀
  · subst h; simp
  · simp [h]

include B in
theorem isLattice_possibleImageHull (R : ∀ i, RamificationData p (L i)) (Δ : DifferentData p B R)
    (i₀ : ι) (k : ℤ) : IsLattice p L (possibleImageHull p L R i₀ k) := by
  have hT := (logVol_tprod_normalization p (B := B) R (Pi.mulSingle i₀ ((R i₀).pi ^ k))
    (fun i => if i = i₀ then k else 0) (norm_piAt_factor p R i₀ k)).1
  exact isLattice_of_le_of_le p hT (logVol_container p (B := B) R _).1 (le_possibleImageHull p R i₀ k)
    (possibleImageHull_le_container p R Δ i₀ k)

include B in

theorem logVol_possibleImageHull_le (R : ∀ i, RamificationData p (L i)) (Δ : DifferentData p B R)
    (i₀ : ι) (k : ℤ) (Istar : Finset ι) (hIstar : ∀ i ∉ Istar, (R i).e + 2 ≤ p) :
    logVol p L (possibleImageHull p L R i₀ k) ≤
      (-((k : ℝ) / (R i₀).e) + dI p Δ + 1) * Real.log p + ∑ i ∈ Istar, (3 + Real.log (R i).e) :=
  (logVol_mono p (B := B) (isLattice_possibleImageHull p R Δ i₀ k) (logVol_container p (B := B) R _).1
    (possibleImageHull_le_container p R Δ i₀ k)).trans (prop14iii_second p R Δ i₀ k Istar hIstar)

end Component

section Model

variable (p : ℕ) [hp : Fact p.Prime]

theorem model_component (hp2 : p ≠ 2) (k : ℤ) :
    ∃ Δ : DifferentData p (fun _ : Fin 2 => ℤ_[p]) (fun _ : Fin 2 => qpRamification p),
      logVol p (fun _ : Fin 2 => ℚ_[p]) (possibleImageHull p (fun _ : Fin 2 => ℚ_[p]) (fun _ => qpRamification p) 0 k) ≤
        (-((k : ℝ) / (qpRamification p).e) + dI p Δ + 1) * Real.log p ∧
      piAt p (fun _ : Fin 2 => qpRamification p) 0 k ∈
        possibleImageHull p (fun _ : Fin 2 => ℚ_[p]) (fun _ => qpRamification p) 0 k := by
  obtain ⟨Δ⟩ := exists_qpDifferentData p
  refine ⟨Δ, ?_, ?_⟩
  · have h := logVol_possibleImageHull_le p (L := fun _ : Fin 2 => ℚ_[p]) (B := fun _ : Fin 2 => ℤ_[p])
      (fun _ => qpRamification p) Δ 0 k ∅ (fun i _ => by change 1 + 2 ≤ p; have := hp.out.two_le; omega)
    simpa using h
  · have h := le_possibleImageHull p (L := fun _ : Fin 2 => ℚ_[p]) (fun _ => qpRamification p) 0 k
    exact h ⟨1, (mem_normalization p).mpr isIntegral_one, by simp [mulHom_apply]⟩

end Model

end Src.IUT4.Theorem110

section Check
open Src.IUT4.Theorem110
end Check
