import Cor312LogVolume.theorem311.InnerArithmeticArrowTransport
import Cor312LogVolume.theorem311.ArithmeticCanonicalSplittingCoherence

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211InnerComponentB

open CitedLV.Theorem311
open CitedLV.Theorem311.InnerArithmeticArrowTransport
open CitedLV.Theorem311.ArithmeticCanonicalSplittingCoherence
open CitedLV.Theorem311.CompletePolyComponentAction
open Src.CoreLayer.LanaStep6.FiniteKummerRatio
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

local instance fact211 : Fact (Nat.Prime 211) := ⟨by norm_num⟩

theorem coherent
    (Bad : Type) (Label : Type) :
    ComponentCoherent
      (polyFunctor
        (galoisProcessionIsoRaw (K := ℚ_[211]))
        (fun _ : Unit => ℚ_[211])
        (WithZero (Multiplicative ℤ))
        (fun _ => v211)
        p211Transport)
      (RetainedMonoidSplittingAdapter.action
        (polyFunctor
          (galoisProcessionIsoRaw (K := ℚ_[211]))
          (fun _ : Unit => ℚ_[211])
          (WithZero (Multiplicative ℤ))
          (fun _ => v211)
          p211Transport)
        Bad Label)
      (splittingBuild
        (galoisProcessionIsoRaw (K := ℚ_[211]))
        (fun _ : Unit => ℚ_[211])
        (WithZero (Multiplicative ℤ))
        (fun _ => v211)
        p211Transport
        Bad Label) :=
  componentB_coherent
    (galoisProcessionIsoRaw (K := ℚ_[211]))
    (fun _ : Unit => ℚ_[211])
    (WithZero (Multiplicative ℤ))
    (fun _ => v211)
    p211Transport
    Bad Label
    p211Transport_preservesIdentity
    p211Transport_preservesComposition

example :
    (polyFunctor
      (galoisProcessionIsoRaw (K := ℚ_[211]))
      (fun _ : Unit => ℚ_[211])
      (WithZero (Multiplicative ℤ))
      (fun _ => v211)
      p211Transport).side () =
        ArithmeticRetainedThetaSide.p211Side := rfl

theorem arrow_nondegenerate_of_moves
    (a : AbsGal ℚ_[211])
    (x : Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier.LocalIntegralMonoid
      ℚ_[211] v211)
    (hmove : a • x ≠ x) :
    (p211Transport.map (p := ()) (q := ()) a).monoidEquiv ≠
      ContinuousMulEquiv.refl _ :=
  monoidEquiv_ne_refl_of_moves v211 a x hmove

end CitedLV.Theorem311.P211InnerComponentB
end
