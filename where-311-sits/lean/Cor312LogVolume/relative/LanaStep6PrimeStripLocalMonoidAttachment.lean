import Cor312LogVolume.thetalink.Cor410iConstantPrimeStripAssembly
import Cor312LogVolume.relative.LanaStep6LocalIntegralMonoidSupplier

set_option autoImplicit false

noncomputable section

namespace Src.CoreLayer.LanaStep6.PrimeStripLocalMonoidAttachment

open CitedLV.ThetaLink.Cor410iAssembly
open Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier

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

universe uT uV uGlobal uPrime uLocal uGLoc uLRlf uK uG

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

abbrev PrimeStripLocalMonoid
    (D : Cor410iGlobalizationOutput
      T V Global Prime Local GlobalLoc LocalRlf)
    (t : T) (place : V) : Type uLRlf :=
  step6LocalMonoid LocalRlf D.localData t place

structure LocalMonoidCarrierAttachment
    (D : Cor410iGlobalizationOutput
      T V Global Prime Local GlobalLoc LocalRlf)
    (t : T) (place : V)
    (K : Type uK) [Field K]
    {Gamma0 : Type uG} [LinearOrderedCommGroupWithZero Gamma0]
    (valuation : Valuation K Gamma0) where
  carrierEquiv :
    PrimeStripLocalMonoid D t place ≃*
      LocalIntegralMonoid K valuation

namespace LocalMonoidCarrierAttachment

variable
    {D : Cor410iGlobalizationOutput
      T V Global Prime Local GlobalLoc LocalRlf}
    {t : T} {place : V}
    {K : Type uK} [Field K]
    {Gamma0 : Type uG} [LinearOrderedCommGroupWithZero Gamma0]
    {valuation : Valuation K Gamma0}

noncomputable def arithmeticKummerFunction
    (A : LocalMonoidCarrierAttachment D t place K valuation) :
    PrimeStripLocalMonoid D t place ->
      (localIntegralColimitInput K valuation).infinityH1 :=
  fun m => localIntegralKummerMap K valuation (A.carrierEquiv m)

@[simp] theorem arithmeticKummerFunction_apply
    (A : LocalMonoidCarrierAttachment D t place K valuation)
    (m : PrimeStripLocalMonoid D t place) :
    A.arithmeticKummerFunction m =
      localIntegralKummerMap K valuation (A.carrierEquiv m) :=
  rfl

theorem arithmeticKummerFunction_injective
    (A : LocalMonoidCarrierAttachment D t place K valuation)
    (hKummer : Function.Injective (localIntegralKummerMap K valuation)) :
    Function.Injective A.arithmeticKummerFunction := by
  intro x y hxy
  apply A.carrierEquiv.injective
  apply hKummer
  exact hxy

end LocalMonoidCarrierAttachment

abbrev ClosedPrime (_ : Unit) := Unit
abbrev ClosedLocal (_ : Unit) := Unit
abbrev ClosedGlobalLoc (_ : Unit) (_ : Unit) := Unit
abbrev ClosedLocalRlf (_ : Unit) (_ : Unit) := Unit

def closedCor46LocalOutput :
    Cor46ConstantLocalOutput Unit Unit ClosedLocal where
  localObj := fun _ _ => ()

def closedCor410iOutput :
    Cor410iGlobalizationOutput
      Unit Unit Unit ClosedPrime ClosedLocal
        ClosedGlobalLoc ClosedLocalRlf where
  localData := closedCor46LocalOutput
  global := fun _ => ()
  primeEquiv := fun _ => Equiv.refl Unit
  rho := fun _ _ => ContinuousMulEquiv.refl Unit

theorem closed_primeStripLocalMonoid_subsingleton :
    Subsingleton
      (PrimeStripLocalMonoid closedCor410iOutput () ()) :=
  inferInstance

theorem closed_output_rejects_visible_arithmetic_carrier
    (K : Type uK) [Field K]
    {Gamma0 : Type uG} [LinearOrderedCommGroupWithZero Gamma0]
    (valuation : Valuation K Gamma0)
    (x y : LocalIntegralMonoid K valuation)
    (hxy : x ≠ y) :
    ¬ Nonempty
      (LocalMonoidCarrierAttachment
        closedCor410iOutput () () K valuation) := by
  rintro ⟨A⟩
  obtain ⟨x0, hx0⟩ := A.carrierEquiv.surjective x
  obtain ⟨y0, hy0⟩ := A.carrierEquiv.surjective y
  apply hxy
  calc
    x = A.carrierEquiv x0 := hx0.symm
    _ = A.carrierEquiv y0 := by
      exact congrArg A.carrierEquiv (Subsingleton.elim x0 y0)
    _ = y := hy0

end Src.CoreLayer.LanaStep6.PrimeStripLocalMonoidAttachment

end
