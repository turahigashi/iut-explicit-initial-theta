import Cor312LogVolume.thetalink.CompletePolyIso
import Cor312LogVolume.relative.LanaStep6PrimeStripDecompositionGroupAttachment
import Cor312LogVolume.relative.LanaStep6FiniteKummerRatio
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.ArithmeticRetainedThetaSide

open CitedLV.ThetaLink
open Src.CoreLayer.LanaStep6.LocalIntegralMonoidSupplier
open Src.CoreLayer.LanaStep6.FiniteKummerRatio

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

universe u v

variable {Gamma0 : Type v} [LinearOrderedCommGroupWithZero Gamma0]
variable (K : Type u) [Field K] (valuation : Valuation K Gamma0)

def fixedSubmonoid (H : OpenSubgroup (AbsGal K)) :
    Submonoid (LocalIntegralMonoid K valuation) where
  carrier := {m | forall h : H, (h.1 : AbsGal K) • m = m}
  one_mem' := by
    intro h
    exact smul_one _
  mul_mem' := by
    intro a b ha hb h
    rw [smul_mul', ha h, hb h]

def arithmeticRetainedDatum :
    RetainedThetaDatum (AbsGal K) (LocalIntegralMonoid K valuation) where
  lattice := fixedSubmonoid K valuation

def arithmeticSide : RetainedThetaSide where
  G := AbsGal K
  O := LocalIntegralMonoid K valuation
  datum := arithmeticRetainedDatum K valuation

theorem mem_lattice_iff
    (H : OpenSubgroup (AbsGal K))
    (m : LocalIntegralMonoid K valuation) :
    m ∈ (arithmeticSide K valuation).datum.lattice H ↔
      forall h : H, (h.1 : AbsGal K) • m = m :=
  Iff.rfl

theorem one_mem_every_lattice
    (H : OpenSubgroup (AbsGal K)) :
    (1 : LocalIntegralMonoid K valuation) ∈
      (arithmeticSide K valuation).datum.lattice H := by
  intro h
  exact smul_one _

theorem mul_mem_lattice
    (H : OpenSubgroup (AbsGal K))
    {a b : LocalIntegralMonoid K valuation}
    (ha : a ∈ (arithmeticSide K valuation).datum.lattice H)
    (hb : b ∈ (arithmeticSide K valuation).datum.lattice H) :
    a * b ∈ (arithmeticSide K valuation).datum.lattice H := by
  exact ((arithmeticSide K valuation).datum.lattice H).mul_mem ha hb

local instance fact211 : Fact (Nat.Prime 211) := ⟨by norm_num⟩

noncomputable abbrev p211Valuation :=
  Padic.mulValuation (p := 211)

noncomputable def p211Side : RetainedThetaSide :=
  arithmeticSide ℚ_[211] p211Valuation

example : (p211Side).O =
    LocalIntegralMonoid ℚ_[211] p211Valuation := rfl

example : (p211Side).G = AbsGal ℚ_[211] := rfl

theorem p211_mem_lattice_iff
    (H : OpenSubgroup (AbsGal ℚ_[211]))
    (m : LocalIntegralMonoid ℚ_[211] p211Valuation) :
    m ∈ p211Side.datum.lattice H ↔
      ∀ h : H, (h.1 : AbsGal ℚ_[211]) • m = m :=
  Iff.rfl

end CitedLV.Theorem311.ArithmeticRetainedThetaSide
end
