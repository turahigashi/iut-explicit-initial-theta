import Cor312LogVolume.theorem311.ArithmeticRetainedThetaSide
import Cor312LogVolume.theorem311.ProcessionPolyFunctorBoundary

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.ArithmeticRetainedThetaIso

open CitedLV.ThetaLink
open CitedLV.Theorem311.ArithmeticRetainedThetaSide
open CitedLV.Theorem311.ProcessionPolyFunctorBoundary
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

universe uK uL uGammaK uGammaL uObj

variable
  {GammaK : Type uGammaK} [LinearOrderedCommGroupWithZero GammaK]
  {GammaL : Type uGammaL} [LinearOrderedCommGroupWithZero GammaL]
  {K : Type uK} [Field K]
  {L : Type uL} [Field L]
  (vK : Valuation K GammaK)
  (vL : Valuation L GammaL)

structure EquivariantArithmeticEquiv where
  groupEquiv : AbsGal K ≃ₜ* AbsGal L
  monoidEquiv :
    LocalIntegralMonoid K vK ≃ₜ*
      LocalIntegralMonoid L vL
  equivariant :
    ∀ g x,
      monoidEquiv (g • x) =
        groupEquiv g • monoidEquiv x

theorem fixedSubmonoid_preserved
    (e : EquivariantArithmeticEquiv vK vL)
    (H : OpenSubgroup (AbsGal K))
    (x : LocalIntegralMonoid K vK) :
    x ∈ fixedSubmonoid K vK H ↔
      e.monoidEquiv x ∈
        fixedSubmonoid L vL
          (transportOpen e.groupEquiv H) := by
  constructor
  · intro hx
    intro h'
    let h : H :=
      ⟨e.groupEquiv.symm h'.1, h'.2⟩
    have hfixed : (h.1 : AbsGal K) • x = x := hx h
    have heq := e.equivariant (h.1 : AbsGal K) x
    rw [hfixed] at heq
    have hback : e.groupEquiv (e.groupEquiv.symm h'.1) = h'.1 :=
      e.groupEquiv.apply_symm_apply h'.1
    rw [hback] at heq
    exact heq.symm
  · intro hx
    intro h
    let h' : transportOpen e.groupEquiv H :=
      ⟨e.groupEquiv h.1, by
        change e.groupEquiv.symm (e.groupEquiv h.1) ∈ H
        simpa using h.2⟩
    have hfixed :
        (h'.1 : AbsGal L) • e.monoidEquiv x =
          e.monoidEquiv x :=
      hx h'
    have heq := e.equivariant (h.1 : AbsGal K) x
    apply e.monoidEquiv.injective
    calc
      e.monoidEquiv ((h.1 : AbsGal K) • x)
          = e.groupEquiv h.1 • e.monoidEquiv x := heq
      _ = e.monoidEquiv x := by
        simpa [h'] using hfixed

def EquivariantArithmeticEquiv.toAdmissibleIso
    (e : EquivariantArithmeticEquiv vK vL) :
    AdmissibleIso
      (arithmeticSide K vK)
      (arithmeticSide L vL) where
  groupEquiv := e.groupEquiv
  monoidEquiv := e.monoidEquiv
  equivariant := e.equivariant
  preservesLattices := by
    intro H x
    exact fixedSubmonoid_preserved vK vL e H x

section Procession

variable {Obj : Type uObj} (G : ProcessionIsoRaw Obj)
variable (KObj : Obj -> Type uK) [∀ p, Field (KObj p)]
variable (Gamma : Type uGammaK) [LinearOrderedCommGroupWithZero Gamma]
variable (valuation : (p : Obj) -> Valuation (KObj p) Gamma)

structure ArithmeticArrowTransport where
  map :
    {p q : Obj} -> G.Hom p q ->
      EquivariantArithmeticEquiv (valuation p) (valuation q)

def toProcessionPolyFunctor
    (T : ArithmeticArrowTransport G KObj Gamma valuation) :
    ProcessionPolyFunctorRaw G where
  side := fun p => arithmeticSide (KObj p) (valuation p)
  map := fun e => (T.map e).toAdmissibleIso

def PreservesArithmeticIdentity
    (T : ArithmeticArrowTransport G KObj Gamma valuation) : Prop :=
  (∀ p,
    (T.map (G.idHom p)).groupEquiv = ContinuousMulEquiv.refl _) ∧
  (∀ p,
    (T.map (G.idHom p)).monoidEquiv = ContinuousMulEquiv.refl _)

def PreservesArithmeticComposition
    (T : ArithmeticArrowTransport G KObj Gamma valuation) : Prop :=
  (∀ {p q r} (e : G.Hom p q) (f : G.Hom q r),
    (T.map (G.comp e f)).groupEquiv =
      (T.map e).groupEquiv.trans (T.map f).groupEquiv) ∧
  (∀ {p q r} (e : G.Hom p q) (f : G.Hom q r),
    (T.map (G.comp e f)).monoidEquiv =
      (T.map e).monoidEquiv.trans (T.map f).monoidEquiv)

theorem poly_preservesIdentity
    (T : ArithmeticArrowTransport G KObj Gamma valuation)
    (h : PreservesArithmeticIdentity G KObj Gamma valuation T) :
    ProcessionPolyFunctorBoundary.PreservesIdentity
      (toProcessionPolyFunctor G KObj Gamma valuation T) := by
  intro p
  apply CitedLV.Theorem311.CompletePolyProcession.admissibleIso_ext
  · intro x

    simp only [toProcessionPolyFunctor, EquivariantArithmeticEquiv.toAdmissibleIso]
    rw [show (T.map (G.idHom p)).groupEquiv =
      ContinuousMulEquiv.refl _ from h.1 p]
    rfl
  · intro x
    simp only [toProcessionPolyFunctor, EquivariantArithmeticEquiv.toAdmissibleIso]
    rw [show (T.map (G.idHom p)).monoidEquiv =
      ContinuousMulEquiv.refl _ from h.2 p]
    rfl

theorem poly_preservesComposition
    (T : ArithmeticArrowTransport G KObj Gamma valuation)
    (h : PreservesArithmeticComposition G KObj Gamma valuation T) :
    ProcessionPolyFunctorBoundary.PreservesComposition
      (toProcessionPolyFunctor G KObj Gamma valuation T) := by
  intro p q r e f
  apply CitedLV.Theorem311.CompletePolyProcession.admissibleIso_ext
  · intro x
    simp only [toProcessionPolyFunctor, EquivariantArithmeticEquiv.toAdmissibleIso]
    rw [show (T.map (G.comp e f)).groupEquiv =
      (T.map e).groupEquiv.trans (T.map f).groupEquiv from h.1 e f]
    rfl
  · intro x
    simp only [toProcessionPolyFunctor, EquivariantArithmeticEquiv.toAdmissibleIso]
    rw [show (T.map (G.comp e f)).monoidEquiv =
      (T.map e).monoidEquiv.trans (T.map f).monoidEquiv from h.2 e f]
    rfl

end Procession

end CitedLV.Theorem311.ArithmeticRetainedThetaIso
end
