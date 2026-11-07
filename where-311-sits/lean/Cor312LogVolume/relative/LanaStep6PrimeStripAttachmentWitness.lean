import Cor312LogVolume.relative.LanaStep6PrimeStripLocalMonoidAttachment
import Cor312LogVolume.relative.LanaStep6KummerEquivariance

set_option autoImplicit false

noncomputable section

namespace Src.CoreLayer.LanaStep6.PrimeStripAttachmentWitness

open Src.EtTh.NonzeroIntegral
open Src.CoreLayer.LanaStep6.FiniteKummerRatio
open Src.CoreLayer.LanaStep6.KummerEquivariance
open Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier
open Src.CoreLayer.LanaStep6.PrimeStripLocalMonoidAttachment
open CitedLV.ThetaLink.Cor410iAssembly

universe uK uG

variable
    {Gamma0 : Type uG} [LinearOrderedCommGroupWithZero Gamma0]
    (K : Type uK) [Field K] (v : Valuation K Gamma0)

local instance witnessLocalIntegralTopology :
    TopologicalSpace (LocalIntegralMonoid K v) :=
  localIntegralTopology K v

local instance witnessLocalIntegralContinuousMul :
    ContinuousMul (LocalIntegralMonoid K v) :=
  localIntegralContinuousMul K v

local instance witnessClosureUnitsTopology :
    TopologicalSpace (Closure K)ˣ :=
  closureUnitsTopologyForLocalIntegral K

local instance witnessClosureUnitsDiscrete :
    DiscreteTopology (Closure K)ˣ :=
  closureUnitsDiscreteForLocalIntegral K

local instance witnessClosureUnitsTopologicalGroup :
    IsTopologicalGroup (Closure K)ˣ :=
  closureUnitsTopologicalGroupForLocalIntegral K

local instance witnessClosureUnitsAction :
    MulDistribMulAction (AbsGal K) (Closure K)ˣ :=
  closureUnitsActionForLocalIntegral K

local instance witnessClosureUnitsContinuousSMul :
    ContinuousSMul (AbsGal K) (Closure K)ˣ :=
  closureUnitsContinuousSMulForLocalIntegral K

local instance witnessLocalIntegralDiscreteTopology :
    DiscreteTopology (LocalIntegralMonoid K v) :=
  localIntegralDiscreteTopology K v

local instance witnessLocalIntegralAction :
    MulDistribMulAction (AbsGal K) (LocalIntegralMonoid K v) :=
  localIntegralAction K v

local instance witnessLocalIntegralContinuousSMul :
    ContinuousSMul (AbsGal K) (LocalIntegralMonoid K v) :=
  localIntegralContinuousSMul K v

noncomputable instance localIntegralInfinityH1MulAction :
    MulAction (AbsGal K) (localIntegralColimitInput K v).infinityH1 :=
  infinityH1MulAction (localIntegralColimitInput K v)

abbrev WitnessLocal (_ : Unit) := Unit
abbrev WitnessPrime (_ : Unit) := Unit
abbrev WitnessGlobalLoc (_ : Unit) (_ : Unit) : Type uK :=
  (LocalIntegralMonoid K v : Type uK)
abbrev WitnessLocalRlf (_ : Unit) (_ : Unit) : Type uK :=
  (LocalIntegralMonoid K v : Type uK)

def witnessLocalOutput :
    Cor46ConstantLocalOutput Unit Unit WitnessLocal where
  localObj := fun _ _ => ()

def witnessOutput :
    Cor410iGlobalizationOutput
      Unit Unit Unit WitnessPrime WitnessLocal
        (WitnessGlobalLoc K v) (WitnessLocalRlf K v) where
  localData := witnessLocalOutput
  global := fun _ => ()
  primeEquiv := fun _ => Equiv.refl Unit
  rho := fun _ _ => ContinuousMulEquiv.refl (LocalIntegralMonoid K v)

def witnessAttachment :
    LocalMonoidCarrierAttachment (witnessOutput K v) () () K v where
  carrierEquiv := MulEquiv.refl (LocalIntegralMonoid K v)

theorem witnessAttachment_nonempty :
    Nonempty
      (LocalMonoidCarrierAttachment (witnessOutput K v) () () K v) :=
  ⟨witnessAttachment K v⟩

theorem localIntegralMonoid_one_ne_neg_one
    (h2 : (2 : Closure K) ≠ 0) :
    (1 : LocalIntegralMonoid K v) ≠
      ⟨-1, by
        change IsIntegral v.valuationSubring ((-1 : (Closure K)ˣ) : Closure K)
        simpa using (isIntegral_one (R := v.valuationSubring)
          (B := Closure K)).neg⟩ := by
  intro h
  apply h2
  have h1 := congrArg
    (fun z : LocalIntegralMonoid K v => ((z : (Closure K)ˣ) : Closure K)) h
  simp only at h1
  have : (1 : Closure K) = -1 := h1
  linear_combination this

end Src.CoreLayer.LanaStep6.PrimeStripAttachmentWitness

end
