import Cor312LogVolume.theorem311.ArithmeticRetainedThetaIso
import Cor312LogVolume.theorem311.ArithmeticRetainedThetaSide

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.InnerArithmeticArrowTransport

open CitedLV.Theorem311
open CitedLV.Theorem311.ArithmeticRetainedThetaIso
open CitedLV.Theorem311.ArithmeticRetainedThetaSide
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

universe uK uGamma

variable {K : Type uK} [Field K]
variable {Gamma : Type uGamma} [LinearOrderedCommGroupWithZero Gamma]
variable (v : Valuation K Gamma)

def innerGroupEquiv (a : AbsGal K) : AbsGal K ≃ₜ* AbsGal K where
  toFun g := a * g * a⁻¹
  invFun g := a⁻¹ * g * a
  left_inv g := by simp [mul_assoc]
  right_inv g := by simp [mul_assoc]
  map_mul' g h := by simp [mul_assoc]
  continuous_toFun :=
    (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun :=
    (continuous_const.mul continuous_id).mul continuous_const

def innerMonoidEquiv (a : AbsGal K) :
    LocalIntegralMonoid K v ≃ₜ* LocalIntegralMonoid K v where
  toFun x := a • x
  invFun x := a⁻¹ • x
  left_inv x := by

    show a⁻¹ • a • x = x
    simp [smul_smul]
  right_inv x := by
    show a • a⁻¹ • x = x
    simp [smul_smul]
  map_mul' x y := smul_mul' a x y
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

def innerEquivariantArithmeticEquiv (a : AbsGal K) :
    EquivariantArithmeticEquiv v v where
  groupEquiv := innerGroupEquiv a
  monoidEquiv := innerMonoidEquiv v a
  equivariant := by
    intro g x
    change a • (g • x) =
      (a * g * a⁻¹) • (a • x)
    simp [smul_smul, mul_assoc]

def galoisProcessionIsoRaw : ProcessionIsoRaw Unit where
  Hom _ _ := AbsGal K
  idHom _ := 1
  comp e f := f * e
  inv e := e⁻¹

theorem galoisProcession_groupoidLaws :
    ProcessionGroupoidLaws (galoisProcessionIsoRaw (K := K)) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro p q e
      simp [galoisProcessionIsoRaw]
    · intro p q e
      simp [galoisProcessionIsoRaw]
  · intro p q r s e f g
    simp [galoisProcessionIsoRaw, mul_assoc]
  · constructor
    · intro p q e
      simp [galoisProcessionIsoRaw]
    · intro p q e
      simp [galoisProcessionIsoRaw]

def transport :
    ArithmeticArrowTransport
      (galoisProcessionIsoRaw (K := K))
      (fun _ : Unit => K) Gamma (fun _ => v) where
  map := fun a => innerEquivariantArithmeticEquiv v a

theorem transport_preservesIdentity :
    PreservesArithmeticIdentity
      (galoisProcessionIsoRaw (K := K))
      (fun _ : Unit => K) Gamma (fun _ => v) (transport v) := by
  constructor
  · intro p
    exact ContinuousMulEquiv.ext fun g => by
      simp [transport, innerEquivariantArithmeticEquiv, innerGroupEquiv,
        galoisProcessionIsoRaw]
  · intro p
    exact ContinuousMulEquiv.ext fun x => by
      simp [transport, innerEquivariantArithmeticEquiv, innerMonoidEquiv,
        galoisProcessionIsoRaw]

theorem transport_preservesComposition :
    PreservesArithmeticComposition
      (galoisProcessionIsoRaw (K := K))
      (fun _ : Unit => K) Gamma (fun _ => v) (transport v) := by
  constructor
  · intro p q r e f
    exact ContinuousMulEquiv.ext fun g => by
      simp [transport, innerEquivariantArithmeticEquiv, innerGroupEquiv,
        galoisProcessionIsoRaw, mul_assoc]
  · intro p q r e f
    exact ContinuousMulEquiv.ext fun x => by
      simp [transport, innerEquivariantArithmeticEquiv, innerMonoidEquiv,
        galoisProcessionIsoRaw, smul_smul]

theorem monoidEquiv_ne_refl_of_moves
    (a : AbsGal K) (x : LocalIntegralMonoid K v)
    (hmove : a • x ≠ x) :
    (innerEquivariantArithmeticEquiv v a).monoidEquiv ≠
      ContinuousMulEquiv.refl _ := by
  intro h
  have hx := congrArg
    (fun e : LocalIntegralMonoid K v ≃ₜ* LocalIntegralMonoid K v => e x) h
  exact hmove (by
    simpa [innerEquivariantArithmeticEquiv, innerMonoidEquiv] using hx)

theorem groupEquiv_ne_refl_of_conj_moves
    (a g : AbsGal K)
    (hmove : a * g * a⁻¹ ≠ g) :
    (innerEquivariantArithmeticEquiv v a).groupEquiv ≠
      ContinuousMulEquiv.refl _ := by
  intro h
  have hg := congrArg
    (fun e : AbsGal K ≃ₜ* AbsGal K => e g) h
  exact hmove (by
    simpa [innerEquivariantArithmeticEquiv, innerGroupEquiv] using hg)

theorem transport_arrow_nondegenerate_of_moves
    (a : AbsGal K) (x : LocalIntegralMonoid K v)
    (hmove : a • x ≠ x) :
    (transport v).map (p := ()) (q := ()) a ≠
      (transport v).map (p := ()) (q := ()) (1 : AbsGal K) := by
  intro h
  have hm := congrArg
    (fun e : EquivariantArithmeticEquiv v v => e.monoidEquiv) h
  apply monoidEquiv_ne_refl_of_moves v a x hmove
  calc
    (innerEquivariantArithmeticEquiv v a).monoidEquiv
        = ((transport v).map (p := ()) (q := ()) a).monoidEquiv := rfl
    _ = ((transport v).map (p := ()) (q := ())
          (1 : AbsGal K)).monoidEquiv := hm
    _ = ContinuousMulEquiv.refl _ := by
      exact (transport_preservesIdentity v).2 ()

local instance fact211 : Fact (Nat.Prime 211) := ⟨by norm_num⟩

noncomputable abbrev v211 :
    Valuation ℚ_[211] (WithZero (Multiplicative ℤ)) :=
  Padic.mulValuation (p := 211)

noncomputable abbrev p211Transport :=
  transport v211

theorem p211Transport_preservesIdentity :
    PreservesArithmeticIdentity
      (galoisProcessionIsoRaw (K := ℚ_[211]))
      (fun _ : Unit => ℚ_[211])
      (WithZero (Multiplicative ℤ))
      (fun _ => v211)
      p211Transport :=
  transport_preservesIdentity v211

theorem p211Transport_preservesComposition :
    PreservesArithmeticComposition
      (galoisProcessionIsoRaw (K := ℚ_[211]))
      (fun _ : Unit => ℚ_[211])
      (WithZero (Multiplicative ℤ))
      (fun _ => v211)
      p211Transport :=
  transport_preservesComposition v211

end CitedLV.Theorem311.InnerArithmeticArrowTransport
end
