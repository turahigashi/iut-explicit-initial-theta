import Cor312LogVolume.relative.LanaStep6PrimeStripAttachmentWitness
import Cor312LogVolume.relative.LanaStep6KummerEquivariance
import Cor312LogVolume.relative.LanaStep6AlgebraicClosureKummerBoundary

set_option autoImplicit false

noncomputable section

namespace Src.CoreLayer.LanaStep6.PrimeStripDecompositionGroupAttachment

open Src.CoreLayer.LanaStep6.FiniteKummerRatio
open Src.CoreLayer.LanaStep6.GenericKummerMap
open Src.CoreLayer.LanaStep6.KummerEquivariance
open Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier
open Src.CoreLayer.LanaStep6.PrimeStripLocalMonoidAttachment
open Src.CoreLayer.LanaStep6.PrimeStripAttachmentWitness
open Src.CoreLayer.LanaStep6.AlgebraicClosureKummerBoundary
open CitedLV.ThetaLink.Cor410iAssembly

attribute [local instance]
  Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier.closureUnitsTopologyForLocalIntegral
  Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier.closureUnitsDiscreteForLocalIntegral
  Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier.closureUnitsTopologicalGroupForLocalIntegral
  Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier.closureUnitsActionForLocalIntegral
  Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier.closureUnitsContinuousSMulForLocalIntegral
  Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier.localIntegralTopology
  Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier.localIntegralDiscreteTopology
  Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier.localIntegralContinuousMul
  Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier.localIntegralAction
  Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier.localIntegralContinuousSMul

universe uT uV uGlobal uPrime uLocal uGLoc uLRlf uK uD uG

variable
    {T : Type uT}
    {V : Type uV}
    {Global : Type uGlobal}
    {Prime : Global -> Type uPrime}
    {Local : V -> Type uLocal}
    {GlobalLoc : (C : Global) -> Prime C -> Type uGLoc}
    {LocalRlf : (place : V) -> Local place -> Type uLRlf}
    [forall C p, TopologicalSpace (GlobalLoc C p)]
    [forall C p, CommMonoid (GlobalLoc C p)]
    [forall place L, TopologicalSpace (LocalRlf place L)]
    [forall place L, CommMonoid (LocalRlf place L)]

structure DecompositionGroupAttachment
    {D : Cor410iGlobalizationOutput
      T V Global Prime Local GlobalLoc LocalRlf}
    {t : T} {place : V}
    {K : Type uK} [Field K]
    {Gamma0 : Type uG} [LinearOrderedCommGroupWithZero Gamma0]
    {valuation : Valuation K Gamma0}
    (carrier :
      LocalMonoidCarrierAttachment D t place K valuation)
    (Dt : Type uD)
    [Group Dt] [TopologicalSpace Dt] [IsTopologicalGroup Dt]
    [MulDistribMulAction Dt (PrimeStripLocalMonoid D t place)]
    [ContinuousSMul Dt (PrimeStripLocalMonoid D t place)] where

  groupEquiv : Dt ≃ₜ* AbsGal K

  compat : ∀ d : Dt, ∀ m : PrimeStripLocalMonoid D t place,
    carrier.carrierEquiv (d • m) =
      groupEquiv d • carrier.carrierEquiv m

namespace DecompositionGroupAttachment

variable
    {D : Cor410iGlobalizationOutput
      T V Global Prime Local GlobalLoc LocalRlf}
    {t : T} {place : V}
    {K : Type uK} [Field K]
    {Gamma0 : Type uG} [LinearOrderedCommGroupWithZero Gamma0]
    {valuation : Valuation K Gamma0}
    {carrier :
      LocalMonoidCarrierAttachment D t place K valuation}
    {Dt : Type uD}
    [Group Dt] [TopologicalSpace Dt] [IsTopologicalGroup Dt]
    [MulDistribMulAction Dt (PrimeStripLocalMonoid D t place)]
    [ContinuousSMul Dt (PrimeStripLocalMonoid D t place)]

theorem carrierEquiv_smul
    (A : DecompositionGroupAttachment carrier Dt)
    (d : Dt) (m : PrimeStripLocalMonoid D t place) :
    carrier.carrierEquiv (d • m) =
      A.groupEquiv d • carrier.carrierEquiv m :=
  A.compat d m

theorem arithmeticKummerFunction_equivariant
    (A : DecompositionGroupAttachment carrier Dt)
    (d : Dt) (m : PrimeStripLocalMonoid D t place) :
    carrier.arithmeticKummerFunction (d • m) =
      A.groupEquiv d • carrier.arithmeticKummerFunction m := by
  change
    (localIntegralColimitInput K valuation).genericKummerMap
        (carrier.carrierEquiv (d • m)) =
      A.groupEquiv d •
        (localIntegralColimitInput K valuation).genericKummerMap
          (carrier.carrierEquiv m)
  rw [A.compat d m]
  exact
    genericKummerMap_equivariant
      (localIntegralColimitInput K valuation)
      (A.groupEquiv d) (carrier.carrierEquiv m)

end DecompositionGroupAttachment

section Witness

variable
    {Gamma0 : Type uG} [LinearOrderedCommGroupWithZero Gamma0]
    (K : Type uK) [Field K] (valuation : Valuation K Gamma0)

local instance witnessPrimeStripAbsGalAction :
    MulDistribMulAction (AbsGal K)
      (PrimeStripLocalMonoid (witnessOutput K valuation) () ()) := by
  change MulDistribMulAction (AbsGal K) (LocalIntegralMonoid K valuation)
  exact localIntegralAction K valuation

local instance witnessPrimeStripAbsGalContinuousSMul :
    ContinuousSMul (AbsGal K)
      (PrimeStripLocalMonoid (witnessOutput K valuation) () ()) := by
  change ContinuousSMul (AbsGal K) (LocalIntegralMonoid K valuation)
  exact localIntegralContinuousSMul K valuation

def witnessDecompositionGroupAttachment :
    DecompositionGroupAttachment
      (witnessAttachment K valuation) (AbsGal K) where
  groupEquiv := ContinuousMulEquiv.refl (AbsGal K)
  compat := by
    intro d m
    rfl

theorem witnessDecompositionGroupAttachment_nonempty :
    Nonempty
      (DecompositionGroupAttachment
        (witnessAttachment K valuation) (AbsGal K)) :=
  ⟨witnessDecompositionGroupAttachment K valuation⟩

end Witness

section TrivialGroupNoGo

variable
    {Gamma0 : Type uG} [LinearOrderedCommGroupWithZero Gamma0]
    (valuation : Valuation ℚ Gamma0)

local instance witnessRatPrimeStripUnitAction :
    MulDistribMulAction Unit
      (PrimeStripLocalMonoid (witnessOutput ℚ valuation) () ()) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

local instance witnessRatPrimeStripUnitContinuousSMul :
    ContinuousSMul Unit
      (PrimeStripLocalMonoid (witnessOutput ℚ valuation) () ()) where
  continuous_smul := by
    change Continuous
      (fun p :
        Unit × PrimeStripLocalMonoid (witnessOutput ℚ valuation) () () =>
          p.2)
    exact continuous_snd

theorem rat_absGal_nontrivial :
    ∃ sigma : AbsGal ℚ, sigma ≠ 1 := by
  obtain ⟨a, sigma, hmove⟩ := rat_sqrtTwo_moved_witness
  refine ⟨sigma, ?_⟩
  intro hsigma
  subst hsigma
  apply hmove
  rw [toAlgEquiv_one]
  rfl

theorem trivialDecompositionGroup_no_attachment :
    ¬ Nonempty
      (DecompositionGroupAttachment
        (witnessAttachment ℚ valuation) Unit) := by
  rintro ⟨A⟩
  obtain ⟨sigma, hsigma⟩ := rat_absGal_nontrivial
  obtain ⟨d, hd⟩ := A.groupEquiv.surjective sigma
  apply hsigma
  calc
    sigma = A.groupEquiv d := hd.symm
    _ = A.groupEquiv (1 : Unit) := by
      exact congrArg A.groupEquiv (Subsingleton.elim d 1)
    _ = 1 := map_one A.groupEquiv

theorem decompositionGroupAttachment_is_extra_data :
    Nonempty
        (DecompositionGroupAttachment
          (witnessAttachment ℚ valuation) (AbsGal ℚ)) ∧
      ¬ Nonempty
        (DecompositionGroupAttachment
          (witnessAttachment ℚ valuation) Unit) :=
  ⟨witnessDecompositionGroupAttachment_nonempty ℚ valuation,
    trivialDecompositionGroup_no_attachment valuation⟩

end TrivialGroupNoGo

end Src.CoreLayer.LanaStep6.PrimeStripDecompositionGroupAttachment

end
