import Cor312LogVolume.theorem311.assembly.AssembledConditions
import Cor312LogVolume.IUT1.Section1ResidueRegistry
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace CitedLV.Theorem311

open CitedLV.Theorem311.Assembly in

structure Theta311ConstructionPackage (V : Type*) where

  base : Assembly.Assembly V ℝ

  l : ℕ
  hl5 : 5 ≤ l

  thetaVal : Fin ((l - 1) / 2) → V

  thetaVal_mem : ∀ j, thetaVal j ∈ base.thetaSet

  unitVol : ℝ
  unitVol_neg : unitVol < 0

  readout_spec : ∀ j, base.readout (thetaVal j) = ((j.val : ℝ) + 1) ^ 2 * unitVol

  algorithm : V → (Fin ((l - 1) / 2) → V)
  algorithm_spec : algorithm base.qValue = thetaVal

  qVol : ℝ
  qVol_spec : base.readout base.qValue = qVol

  Primes : Type
  primes_nonempty : Nonempty Primes
  holAt : Primes → Type
  hol_plural : ∀ v, ∃ a b : holAt v, a ≠ b

  LogLinks : Type
  logLinks_plural : ∃ a b : LogLinks, a ≠ b

  ThetaLinks : Type
  thetaLinks_plural : ∃ a b : ThetaLinks, a ≠ b

  Deformations : Type
  deformations_plural : ∃ a b : Deformations, a ≠ b

namespace Theta311ConstructionPackage

variable {V : Type*}

def lstar (P : Theta311ConstructionPackage V) : ℕ := (P.l - 1) / 2

theorem two_le_lstar (P : Theta311ConstructionPackage V) : 2 ≤ P.lstar := by
  have h := P.hl5
  unfold lstar
  omega

def jZero (P : Theta311ConstructionPackage V) : Fin ((P.l - 1) / 2) :=
  ⟨0, by have := P.two_le_lstar; unfold lstar at this; omega⟩

def jOne (P : Theta311ConstructionPackage V) : Fin ((P.l - 1) / 2) :=
  ⟨1, by have := P.two_le_lstar; unfold lstar at this; omega⟩

theorem values_nonconstant (P : Theta311ConstructionPackage V) :
    P.base.readout (P.thetaVal P.jZero) ≠ P.base.readout (P.thetaVal P.jOne) := by
  rw [P.readout_spec, P.readout_spec]
  have hu := P.unitVol_neg
  simp only [jZero, jOne]
  push_cast
  intro h
  nlinarith

theorem alpha_collapse_refuted (P : Theta311ConstructionPackage V) :
    ¬ ∀ j k : Fin ((P.l - 1) / 2),
        P.base.readout (P.thetaVal j) = P.base.readout (P.thetaVal k) :=
  fun h => P.values_nonconstant (h P.jZero P.jOne)

theorem readouts_bounded (P : Theta311ConstructionPackage V) :
    ∀ j, P.base.readout (P.thetaVal j) ≤ P.base.bound :=
  fun j => P.base.thetaSet_bounded _ (P.thetaVal_mem j)

theorem package_discharges_mirrored_pair (P : Theta311ConstructionPackage V) :
    (∀ j, P.thetaVal j ∈ P.base.thetaSet) ∧
    (∃ j k : Fin ((P.l - 1) / 2),
        P.base.readout (P.thetaVal j) ≠ P.base.readout (P.thetaVal k)) :=
  ⟨P.thetaVal_mem, ⟨P.jZero, P.jOne, P.values_nonconstant⟩⟩

theorem implication_form_was_too_weak (P : Theta311ConstructionPackage V) (A : Prop) :
    (A → ∀ j, P.thetaVal j ∈ P.base.thetaSet) ∧
    ((∀ j, P.thetaVal j ∈ P.base.thetaSet) →
      ∃ j k : Fin ((P.l - 1) / 2),
        P.base.readout (P.thetaVal j) ≠ P.base.readout (P.thetaVal k)) :=
  ⟨fun _ => P.thetaVal_mem, fun _ => ⟨P.jZero, P.jOne, P.values_nonconstant⟩⟩

end Theta311ConstructionPackage

def Theta311AcceptanceOn (V : Type*) : Prop :=
  Nonempty (Theta311ConstructionPackage V)

namespace UnderSpecification

open CitedLV.Theorem311.Assembly

noncomputable def arithmeticToy : Theta311ConstructionPackage ℝ where
  base :=
    { thetaSet := Set.Iic 0
      qValue := -1
      unitAction := id
      readout := id
      readout_invariant := fun _ => rfl
      thetaSet_stable := fun _ hv => hv
      bound := 0
      thetaSet_bounded := fun _ hv => hv }
  l := 5
  hl5 := le_refl 5
  thetaVal := fun j => ((j.val : ℝ) + 1) ^ 2 * (-1)
  thetaVal_mem := fun j => by
    have h : ((j.val : ℝ) + 1) ^ 2 * (-1) ≤ 0 := by nlinarith [sq_nonneg ((j.val : ℝ) + 1)]
    exact Set.mem_Iic.mpr h
  unitVol := -1
  unitVol_neg := by norm_num
  readout_spec := fun _ => rfl
  algorithm := fun _ => fun j => ((j.val : ℝ) + 1) ^ 2 * (-1)
  algorithm_spec := rfl
  qVol := -1
  qVol_spec := rfl
  Primes := Unit
  primes_nonempty := ⟨()⟩
  holAt := fun _ => Bool
  hol_plural := fun _ => ⟨true, false, by simp⟩
  LogLinks := Bool
  logLinks_plural := ⟨true, false, by simp⟩
  ThetaLinks := Bool
  thetaLinks_plural := ⟨true, false, by simp⟩
  Deformations := Bool
  deformations_plural := ⟨true, false, by simp⟩

theorem abstract_altitude_is_underspecified : Theta311AcceptanceOn ℝ :=
  ⟨arithmeticToy⟩

end UnderSpecification

open Src.IUT1.Residue in

theorem residues_registered_and_open :
    ¬ Open_Thm311_SHE_compatibility ∧
    ¬ Open_Thm311_symmetry_establishment :=
  ⟨unresolved_is_false, unresolved_is_false⟩

end CitedLV.Theorem311
