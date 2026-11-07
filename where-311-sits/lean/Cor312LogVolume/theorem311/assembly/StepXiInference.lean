import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Image
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

namespace CitedLV.Theorem311.StepXi

structure TwoReadings (Ω Val : Type*) where

  thetaPossible : Set Ω

  vol : Ω → Val

  qObject : Ω

variable {Ω Val : Type*}

def thetaVolumes (T : TwoReadings Ω Val) : Set Val := T.vol '' T.thetaPossible

def qVolume (T : TwoReadings Ω Val) : Val := T.vol T.qObject

def SameConstruction (T : TwoReadings Ω Val) : Prop := T.qObject ∈ T.thetaPossible

theorem xi_f_inference_is_valid (T : TwoReadings Ω Val) (h : SameConstruction T) :
    qVolume T ∈ thetaVolumes T :=
  ⟨T.qObject, h, rfl⟩

theorem inequality_from_membership {Val : Type*} [Preorder Val]
    (T : TwoReadings Ω Val) (b : Val)
    (hb : ∀ x ∈ thetaVolumes T, x ≤ b)
    (h : SameConstruction T) :
    qVolume T ≤ b :=
  hb _ (xi_f_inference_is_valid T h)

def noSameConstruction : TwoReadings ℕ ℕ where
  thetaPossible := {0}
  vol := id
  qObject := 5

theorem premise_is_not_automatic :
    ¬ SameConstruction noSameConstruction := by
  intro h
  have h0 : (5 : ℕ) = 0 := Set.mem_singleton_iff.mp h
  exact absurd h0 (by decide)

theorem conclusion_fails_without_premise :
    qVolume noSameConstruction ∉ thetaVolumes noSameConstruction := by
  rintro ⟨x, hx, hxv⟩
  have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
  subst hx0
  have : (0 : ℕ) = 5 := hxv
  exact absurd this (by decide)

def volumeAgreesButObjectsDiffer : TwoReadings ℕ ℕ where
  thetaPossible := {0}
  vol := fun _ => 0
  qObject := 5

theorem volume_membership_holds :
    qVolume volumeAgreesButObjectsDiffer ∈ thetaVolumes volumeAgreesButObjectsDiffer :=
  ⟨0, rfl, rfl⟩

theorem same_construction_fails :
    ¬ SameConstruction volumeAgreesButObjectsDiffer := by
  intro h
  have h0 : (5 : ℕ) = 0 := Set.mem_singleton_iff.mp h
  exact absurd h0 (by decide)

theorem premise_is_strictly_stronger_than_conclusion :
    (qVolume volumeAgreesButObjectsDiffer ∈ thetaVolumes volumeAgreesButObjectsDiffer)
    ∧ ¬ SameConstruction volumeAgreesButObjectsDiffer :=
  ⟨volume_membership_holds, same_construction_fails⟩

theorem bridge_becomes_theorem {Val : Type*} [Preorder Val]
    (T : TwoReadings Ω Val) (b : Val)
    (hb : ∀ x ∈ thetaVolumes T, x ≤ b) :
    SameConstruction T → (qVolume T ∈ thetaVolumes T ∧ qVolume T ≤ b) :=
  fun h => ⟨xi_f_inference_is_valid T h, inequality_from_membership T b hb h⟩

theorem phaseG_summary {Val : Type*} [Preorder Val]
    (T : TwoReadings Ω Val) (b : Val) (hb : ∀ x ∈ thetaVolumes T, x ≤ b) :
    (SameConstruction T → qVolume T ∈ thetaVolumes T)
    ∧ (SameConstruction T → qVolume T ≤ b)
    ∧ (¬ SameConstruction noSameConstruction)
    ∧ (qVolume noSameConstruction ∉ thetaVolumes noSameConstruction)
    ∧ ((qVolume volumeAgreesButObjectsDiffer ∈ thetaVolumes volumeAgreesButObjectsDiffer)
       ∧ ¬ SameConstruction volumeAgreesButObjectsDiffer) :=
  ⟨xi_f_inference_is_valid T,
   inequality_from_membership T b hb,
   premise_is_not_automatic,
   conclusion_fails_without_premise,
   premise_is_strictly_stronger_than_conclusion⟩

end CitedLV.Theorem311.StepXi
