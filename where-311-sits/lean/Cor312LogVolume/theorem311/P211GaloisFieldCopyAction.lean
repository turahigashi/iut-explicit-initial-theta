import Cor312LogVolume.theorem311.InnerArithmeticArrowTransport
import Cor312LogVolume.theorem311.P211RLGPRawComponents
import Cor312LogVolume.theorem311.CompletePolyFieldCopyTransport
import Cor312LogVolume.theorem311.FVdashSelectedFieldCopyBridge
import Cor312LogVolume.theorem311.ArithmeticCanonicalSplittingCoherence

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211GaloisFieldCopyAction

open CitedLV.Theorem311
open CitedLV.Theorem311.P211RLGPRaw
open CitedLV.Theorem311.ArithmeticRetainedThetaIso
open CitedLV.Theorem311.ArithmeticCanonicalSplittingCoherence
open CitedLV.Theorem311.InnerArithmeticArrowTransport
open CitedLV.Theorem311.ProcessionPolyFunctorBoundary
open CitedLV.Theorem311.CompletePolyComponentAction
open CitedLV.Theorem311.CompletePolyFieldCopyTransport
open CitedLV.Theorem311.FVdashSelectedFieldCopyBridge
open Src.CoreLayer.LanaStep6.FiniteKummerRatio

abbrev F :=
  ArithmeticCanonicalSplittingCoherence.polyFunctor
    (galoisProcessionIsoRaw (K := ℚ_[211]))
    (fun _ : Unit => ℚ_[211])
    (WithZero (Multiplicative ℤ))
    (fun _ => v211)
    p211Transport

abbrev Copy (_p : Unit) (j : P211RLGPRaw.Label) :=
  P211RLGPRaw.Global.GlobalCopy j

abbrev LocalPacket (_p : Unit) (j : P211RLGPRaw.Label)
    (w : P211RLGPRaw.Global.Place) :=
  P211RLGPRaw.Global.GlobalLocalPacket j w

theorem absGal_fixes_rat (a : AbsGal ℚ_[211]) (q : ℚ) :
    toAlgEquiv ℚ_[211] a
        (algebraMap ℚ_[211] (Closure ℚ_[211]) ((q : ℚ_[211]))) =
      algebraMap ℚ_[211] (Closure ℚ_[211]) ((q : ℚ_[211])) :=
  AlgEquiv.commutes (toAlgEquiv ℚ_[211] a) ((q : ℚ_[211]))

def globalCopyAction :
    GlobalCopyActionRaw F Copy where
  copyEquiv := fun _e _j => Equiv.refl _

theorem globalCopyAction_identity :
    GlobalCopyIdentityLaw F Copy globalCopyAction := by
  intro p j
  rfl

theorem globalCopyAction_composition :
    GlobalCopyCompositionLaw F Copy globalCopyAction := by
  intro p q r e f j
  rfl

theorem globalCopy_nontrivial :
    ∀ p : Unit, ∀ j : P211RLGPRaw.Label,
      ∃ x y : Copy p j, x ≠ y := by
  intro p j
  exact ⟨1, -1, by norm_num⟩

def carrierAction :
    CarrierActionRaw F Copy LocalPacket where
  copyEquiv := fun _e _j => Equiv.refl _
  localEquiv := fun _e _j _w => Equiv.refl _

theorem carrierAction_identity :
    CarrierIdentityLaw F Copy LocalPacket carrierAction := by
  constructor
  · intro p j
    rfl
  · intro p j w
    rfl

theorem carrierAction_composition :
    CarrierCompositionLaw F Copy LocalPacket carrierAction := by
  constructor
  · intro p q r e f j
    rfl
  · intro p q r e f j w
    rfl

def build :
    (p : Unit) -> Output Copy LocalPacket p :=
  fun _ => P211RLGPRaw.Global.fieldCopy

theorem embedNaturality :
    EmbedNaturalitySquare F Copy LocalPacket carrierAction build := by
  intro p q e j x w
  rfl

theorem poly_identity :
    ProcessionPolyFunctorBoundary.PreservesIdentity F :=
  ArithmeticRetainedThetaIso.poly_preservesIdentity
    (galoisProcessionIsoRaw (K := ℚ_[211]))
    (fun _ : Unit => ℚ_[211])
    (WithZero (Multiplicative ℤ))
    (fun _ => v211)
    p211Transport
    p211Transport_preservesIdentity

theorem poly_composition :
    ProcessionPolyFunctorBoundary.PreservesComposition F :=
  ArithmeticRetainedThetaIso.poly_preservesComposition
    (galoisProcessionIsoRaw (K := ℚ_[211]))
    (fun _ : Unit => ℚ_[211])
    (WithZero (Multiplicative ℤ))
    (fun _ => v211)
    p211Transport
    p211Transport_preservesComposition

theorem componentC_coherent :
    ComponentCoherent F
      (polyAction F Copy LocalPacket carrierAction)
      build := by
  exact componentCoherent_of_carriers
    F Copy LocalPacket carrierAction build
    poly_identity poly_composition
    carrierAction_identity carrierAction_composition
    embedNaturality

theorem build_checked :
    CheckedLabeledGlobalInclusion (build ()) :=
  P211RLGPRaw.Global.fieldCopy_checked

end CitedLV.Theorem311.P211GaloisFieldCopyAction
end
