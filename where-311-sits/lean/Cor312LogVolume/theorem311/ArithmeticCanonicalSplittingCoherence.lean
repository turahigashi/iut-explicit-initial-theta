import Cor312LogVolume.theorem311.ArithmeticRetainedThetaIso
import Cor312LogVolume.theorem311.CanonicalTorsionSplitting

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.ArithmeticCanonicalSplittingCoherence

open CitedLV.Theorem311.ProcessionPolyFunctorBoundary
open CitedLV.Theorem311.ArithmeticRetainedThetaIso
open CitedLV.Theorem311.RetainedMonoidSplittingAdapter
open CitedLV.Theorem311.CanonicalTorsionSplitting
open CitedLV.Theorem311.CompletePolyComponentAction

universe uObj uK uGamma uBad uLabel

variable {Obj : Type uObj} (G : ProcessionIsoRaw Obj)
variable (KObj : Obj -> Type uK) [∀ p, Field (KObj p)]
variable (Gamma : Type uGamma) [LinearOrderedCommGroupWithZero Gamma]
variable (valuation : (p : Obj) -> Valuation (KObj p) Gamma)
variable (T : ArithmeticArrowTransport G KObj Gamma valuation)
variable (Bad : Type uBad) (Label : Type uLabel)

abbrev polyFunctor :=
  toProcessionPolyFunctor G KObj Gamma valuation T

abbrev splittingBuild :
    (p : Obj) ->
      CitedLV.Theorem311.CompletePolySplittingTransport.Output
        (Psi (polyFunctor G KObj Gamma valuation T) Bad)
        (Packet (polyFunctor G KObj Gamma valuation T) Bad Label) p :=
  buildL7 (polyFunctor G KObj Gamma valuation T) Bad Label

theorem componentB_coherent
    (hId : PreservesArithmeticIdentity G KObj Gamma valuation T)
    (hComp : PreservesArithmeticComposition G KObj Gamma valuation T) :
    ComponentCoherent
      (polyFunctor G KObj Gamma valuation T)
      (action (polyFunctor G KObj Gamma valuation T) Bad Label)
      (splittingBuild G KObj Gamma valuation T Bad Label) := by
  apply componentCoherent_of_buildNaturality
  · exact poly_preservesIdentity G KObj Gamma valuation T hId
  · exact poly_preservesComposition G KObj Gamma valuation T hComp
  · exact buildL7_natural
      (polyFunctor G KObj Gamma valuation T) Bad Label

theorem componentB_needs_only_arithmetic_arrow_laws :
    SourceBuildNaturality
      (polyFunctor G KObj Gamma valuation T) Bad Label
      (splittingBuild G KObj Gamma valuation T Bad Label) :=
  buildL7_natural (polyFunctor G KObj Gamma valuation T) Bad Label

end CitedLV.Theorem311.ArithmeticCanonicalSplittingCoherence
end
