import Cor312LogVolume.relative.LanaStep6CyclotomicSourceIdentification
import Cor312LogVolume.Src.EtTh.Section5NonzeroIntegralRootLanding
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Algebra.Tower

noncomputable section

namespace Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier

open Src.EtTh.NonzeroIntegral
open Src.CoreLayer.LanaStep6.FiniteKummerRatio
open Src.CoreLayer.LanaStep6.FiniteContinuousKummer
open Src.CoreLayer.LanaStep6.GenericKummerMap
open Src.CoreLayer.LanaStep6.GenericKummerMap.AlgClosureCarrier
open Src.CoreLayer.LanaStep6.CyclotomicSourceIdentification

universe u v

variable {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
variable (K : Type u) [Field K] (v : Valuation K Γ₀)

abbrev LocalIntegralMonoid :=
  nonzeroIntegral v.valuationSubring (Closure K)

local instance valuationSubringClosureAlgebra :
    Algebra v.valuationSubring (Closure K) :=
  inferInstance

local instance valuationSubringClosureTower :
    IsScalarTower v.valuationSubring K (Closure K) :=
  inferInstance

local instance valuationSubringClosureIsAlgebraic :
    Algebra.IsAlgebraic v.valuationSubring (Closure K) :=
  IsFractionRing.comap_isAlgebraic_iff.mpr
    (AlgebraicClosure.isAlgebraic K)

def localIntegralInclusion :
    LocalIntegralMonoid K v →* (Closure K)ˣ :=
  (nonzeroIntegral v.valuationSubring (Closure K)).subtype

noncomputable def localIntegralGrothendieckHom :
    Algebra.GrothendieckGroup (LocalIntegralMonoid K v) →*
      (Closure K)ˣ :=
  Algebra.GrothendieckGroup.lift (localIntegralInclusion K v)

theorem localIntegralGrothendieckHom_injective :
    Function.Injective (localIntegralGrothendieckHom K v) := by
  change Function.Injective
    ((Localization.monoidOf
        (⊤ : Submonoid (LocalIntegralMonoid K v))).lift
      (g := localIntegralInclusion K v)
      (fun _ => Group.isUnit _))
  rw [Submonoid.LocalizationMap.lift_injective_iff]
  intro x y
  constructor
  · intro h
    have hxy : x = y :=
      Algebra.GrothendieckGroup.of_injective h
    exact congrArg (localIntegralInclusion K v) hxy
  · intro h
    have hxy : x = y := by
      apply Subtype.ext
      exact h
    exact congrArg Algebra.GrothendieckGroup.of hxy

theorem localIntegralGrothendieckHom_surjective :
    Function.Surjective (localIntegralGrothendieckHom K v) := by
  intro z
  obtain ⟨a, ha0, haInt⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic
      (R := v.valuationSubring) (z : Closure K)).exists_integral_multiple
  have haMap0 :
      algebraMap v.valuationSubring (Closure K) a ≠ 0 := by
    have hinj : Function.Injective
        (algebraMap v.valuationSubring (Closure K)) := by
      rw [IsScalarTower.algebraMap_eq v.valuationSubring K (Closure K),
        RingHom.coe_comp]
      exact (algebraMap K (Closure K)).injective.comp Subtype.val_injective
    simpa using hinj.ne ha0
  have hnum0 :
      a • (z : Closure K) ≠ 0 := by
    rw [Algebra.smul_def]
    exact mul_ne_zero haMap0 (Units.ne_zero z)
  let numU : (Closure K)ˣ :=
    Units.mk0 (a • (z : Closure K)) hnum0
  let denU : (Closure K)ˣ :=
    Units.mk0 (algebraMap v.valuationSubring (Closure K) a) haMap0
  let numM : LocalIntegralMonoid K v :=
    ⟨numU, by
      change IsIntegral v.valuationSubring (a • (z : Closure K))
      exact haInt⟩
  let denM : LocalIntegralMonoid K v :=
    ⟨denU, by
      change IsIntegral v.valuationSubring
        (algebraMap v.valuationSubring (Closure K) a)
      exact isIntegral_algebraMap⟩
  refine
    ⟨Algebra.GrothendieckGroup.of numM /
      Algebra.GrothendieckGroup.of denM, ?_⟩
  have hnum :
      localIntegralGrothendieckHom K v
          (Algebra.GrothendieckGroup.of numM) = numU :=
    (Localization.monoidOf
      (⊤ : Submonoid (LocalIntegralMonoid K v))).lift_eq
        (fun _ => Group.isUnit _) numM
  have hden :
      localIntegralGrothendieckHom K v
          (Algebra.GrothendieckGroup.of denM) = denU :=
    (Localization.monoidOf
      (⊤ : Submonoid (LocalIntegralMonoid K v))).lift_eq
        (fun _ => Group.isUnit _) denM
  rw [map_div, hnum, hden]
  apply Units.ext
  change
    (a • (z : Closure K)) /
        algebraMap v.valuationSubring (Closure K) a =
      (z : Closure K)
  rw [Algebra.smul_def]
  field_simp

noncomputable def localIntegralGroupification :
    Algebra.GrothendieckGroup (LocalIntegralMonoid K v) ≃*
      (Closure K)ˣ :=
  MulEquiv.ofBijective (localIntegralGrothendieckHom K v)
    ⟨localIntegralGrothendieckHom_injective K v,
      localIntegralGrothendieckHom_surjective K v⟩

noncomputable def localIntegralCoefficientInput :
    KummerCoefficientInput
      (LocalIntegralMonoid K v) (Closure K)ˣ where
  groupification := localIntegralGroupification K v
  divisible := closureUnits_divisible K
  finiteTors := closureUnits_finiteTors K

@[simp] theorem localIntegralCoefficientInput_toGp
    (m : LocalIntegralMonoid K v) :
    KummerCoefficientInput.toGp (localIntegralCoefficientInput K v) m =
      (m : (Closure K)ˣ) := by
  change
    localIntegralGrothendieckHom K v
      (Algebra.GrothendieckGroup.of m) = (m : (Closure K)ˣ)
  exact
    (Localization.monoidOf
      (⊤ : Submonoid (LocalIntegralMonoid K v))).lift_eq
        (fun _ => Group.isUnit _) m

def galoisOnLocalIntegral
    (sigma : AbsGal K) (m : LocalIntegralMonoid K v) :
    LocalIntegralMonoid K v :=
  ⟨galoisOnClosureUnits K sigma m.1, by
    change IsIntegral v.valuationSubring
      (toAlgEquiv K sigma (m.1 : Closure K))
    exact
      (isIntegral_algEquiv
        ((toAlgEquiv K sigma).restrictScalars v.valuationSubring)).2 m.2⟩

@[simp] theorem galoisOnLocalIntegral_coe
    (sigma : AbsGal K) (m : LocalIntegralMonoid K v) :
    ((galoisOnLocalIntegral K v sigma m :
        LocalIntegralMonoid K v) : (Closure K)ˣ) =
      galoisOnClosureUnits K sigma m.1 :=
  rfl

local instance closureActionForLocalIntegral :
    MulAction (AbsGal K) (Closure K) where
  smul sigma x := galoisOnClosure K sigma x
  one_smul x := by
    simp [galoisOnClosure, toAlgEquiv_one]
  mul_smul sigma tau x := by
    simp [galoisOnClosure, toAlgEquiv_mul, AlgEquiv.mul_apply]

local instance closureUnitsTopologyForLocalIntegral :
    TopologicalSpace (Closure K)ˣ := ⊥

local instance closureUnitsDiscreteForLocalIntegral :
    DiscreteTopology (Closure K)ˣ :=
  discreteTopology_bot _

local instance closureUnitsTopologicalGroupForLocalIntegral :
    IsTopologicalGroup (Closure K)ˣ := {}

local instance closureUnitsActionForLocalIntegral :
    MulDistribMulAction (AbsGal K) (Closure K)ˣ where
  smul sigma u := galoisOnClosureUnits K sigma u
  one_smul u := by
    apply Units.ext
    simp [galoisOnClosureUnits, toAlgEquiv_one]
  mul_smul sigma tau u := by
    apply Units.ext
    simp [galoisOnClosureUnits, toAlgEquiv_mul, AlgEquiv.mul_apply]
  smul_one sigma := by
    apply Units.ext
    simp [galoisOnClosureUnits]
  smul_mul sigma x y := by
    apply Units.ext
    simp [galoisOnClosureUnits]

theorem closureUnits_stabilizer_eq_forLocalIntegral
    (u : (Closure K)ˣ) :
    (MulAction.stabilizer (AbsGal K) u : Set (AbsGal K)) =
      {sigma : AbsGal K |
        toAlgEquiv K sigma (u : Closure K) = (u : Closure K)} := by
  ext sigma
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff,
    Set.mem_setOf_eq]
  constructor
  · intro h
    have h' := congrArg (fun w : (Closure K)ˣ => (w : Closure K)) h
    exact h'
  · intro h
    apply Units.ext
    exact h

local instance closureUnitsContinuousSMulForLocalIntegral :
    ContinuousSMul (AbsGal K) (Closure K)ˣ :=
  (continuousSMul_iff_stabilizer_isOpen).2 fun u => by
    rw [closureUnits_stabilizer_eq_forLocalIntegral K u]
    exact isOpen_fixingValue K (u : Closure K)

local instance localIntegralTopology :
    TopologicalSpace (LocalIntegralMonoid K v) := ⊥

local instance localIntegralDiscreteTopology :
    DiscreteTopology (LocalIntegralMonoid K v) :=
  discreteTopology_bot _

local instance localIntegralContinuousMul :
    ContinuousMul (LocalIntegralMonoid K v) where
  continuous_mul := continuous_of_discreteTopology

local instance localIntegralAction :
    MulDistribMulAction (AbsGal K) (LocalIntegralMonoid K v) where
  smul sigma m := galoisOnLocalIntegral K v sigma m
  one_smul m := by
    apply Subtype.ext
    apply Units.ext
    show toAlgEquiv K 1 ((m : (Closure K)ˣ) : Closure K)
        = ((m : (Closure K)ˣ) : Closure K)
    rw [toAlgEquiv_one]; rfl
  mul_smul sigma tau m := by
    apply Subtype.ext
    apply Units.ext
    show toAlgEquiv K (sigma * tau) ((m : (Closure K)ˣ) : Closure K)
        = toAlgEquiv K sigma (toAlgEquiv K tau ((m : (Closure K)ˣ) : Closure K))
    rw [toAlgEquiv_mul, AlgEquiv.mul_apply]
  smul_one sigma := by
    apply Subtype.ext
    apply Units.ext
    show toAlgEquiv K sigma (1 : Closure K) = 1
    simp
  smul_mul sigma x y := by
    apply Subtype.ext
    apply Units.ext
    show toAlgEquiv K sigma
        ((x : (Closure K)ˣ) * (y : (Closure K)ˣ) : (Closure K)ˣ)
      = toAlgEquiv K sigma ((x : (Closure K)ˣ) : Closure K)
        * toAlgEquiv K sigma ((y : (Closure K)ˣ) : Closure K)
    simp

@[simp] theorem localIntegral_smul_coe
    (sigma : AbsGal K) (m : LocalIntegralMonoid K v) :
    ((sigma • m : LocalIntegralMonoid K v) : (Closure K)ˣ) =
      sigma • (m : (Closure K)ˣ) :=
  rfl

theorem localIntegral_stabilizer_eq
    (m : LocalIntegralMonoid K v) :
    (MulAction.stabilizer (AbsGal K) m : Set (AbsGal K)) =
      {sigma : AbsGal K |
        toAlgEquiv K sigma (m.1 : Closure K) = (m.1 : Closure K)} := by
  ext sigma
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff,
    Set.mem_setOf_eq]
  constructor
  · intro h
    have h' := congrArg
      (fun w : LocalIntegralMonoid K v => (w.1 : Closure K)) h
    exact h'
  · intro h
    apply Subtype.ext
    apply Units.ext
    exact h

local instance localIntegralContinuousSMul :
    ContinuousSMul (AbsGal K) (LocalIntegralMonoid K v) :=
  (continuousSMul_iff_stabilizer_isOpen).2 fun m => by
    rw [localIntegral_stabilizer_eq K v m]
    exact isOpen_fixingValue K (m.1 : Closure K)

noncomputable def localIntegralSubgroupInput :
    KummerSubgroupInput
      (AbsGal K) (LocalIntegralMonoid K v) (Closure K)ˣ where
  coeff := localIntegralCoefficientInput K v
  equivariant_toGp := by
    intro sigma m
    simp only [localIntegralCoefficientInput_toGp]
    rfl

noncomputable def localIntegralFixingFiniteOpen
    (m : LocalIntegralMonoid K v) :
    FiniteOpen (AbsGal K) :=
  closureFixingFiniteOpen K (m.1 : Closure K)

theorem localIntegralFixingFiniteOpen_fixes
    (m : LocalIntegralMonoid K v) :
    ∀ h :
      (restrictedOpen (localIntegralFixingFiniteOpen K v m)).toSubgroup,
      h • m = m := by
  intro h
  apply Subtype.ext
  apply Units.ext
  change toAlgEquiv K h.1 (m.1 : Closure K) = (m.1 : Closure K)
  have hh :
      h.1 ∈
        MulAction.stabilizer (AbsGal K) (m.1 : Closure K) := by
    simpa [localIntegralFixingFiniteOpen, restrictedOpen,
      closureFixingFiniteOpen,
      Src.Lib.ContinuousH1RestrictionColimit.restrictedOpen]
      using h.2
  exact hh

@[reducible] noncomputable def localIntegralColimitInput :
    KummerColimitInput
      (AbsGal K) (LocalIntegralMonoid K v) (Closure K)ˣ where
  toKummerSubgroupInput := localIntegralSubgroupInput K v
  unionFixed := by
    intro m
    exact
      ⟨localIntegralFixingFiniteOpen K v m,
        localIntegralFixingFiniteOpen_fixes K v m⟩

noncomputable def localIntegralKummerMap :
    LocalIntegralMonoid K v →
      (localIntegralColimitInput K v).infinityH1 :=
  (localIntegralColimitInput K v).genericKummerMap

theorem localIntegralLambda_eq_closureLambda :
    (localIntegralCoefficientInput K v).Lambda =
      (closureCoefficientInput K).Lambda :=
  rfl

noncomputable def localIntegralLambdaEquivLanaCyclotomicLimit :
    (localIntegralCoefficientInput K v).Lambda ≃*
      (CategoryTheory.Limits.limit
        (Src.CoreLayer.LanaStep6.FactorialCofinalLimit.fullCyclotomicDiagram K)).carrier :=
  closureLambdaEquivLanaCyclotomicLimit K

end Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier

end
