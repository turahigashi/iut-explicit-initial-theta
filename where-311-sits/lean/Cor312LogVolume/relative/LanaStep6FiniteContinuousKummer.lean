import Cor312LogVolume.relative.LanaStep6FiniteKummerRatio
import Cor312LogVolume.Src.Lib.ContinuousH1
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section

namespace Src.CoreLayer.LanaStep6.FiniteContinuousKummer

open SrcContinuous.ContinuousH1
open Src.CoreLayer.LanaStep6.FiniteKummerRatio

universe u

variable (K : Type u) [Field K]

local instance unitsTopology :
    TopologicalSpace (Closure K)ˣ :=
  ⊥

local instance unitsDiscreteTopology :
    DiscreteTopology (Closure K)ˣ :=
  discreteTopology_bot (Closure K)ˣ

local instance coefficientTopology (n : ℕ) [NeZero n] :
    TopologicalSpace (Additive (Mu K n)) :=
  inferInstance

local instance coefficientDiscreteTopology (n : ℕ) [NeZero n] :
    DiscreteTopology (Additive (Mu K n)) :=
  inferInstance

def rootsMulDistribAction (n : ℕ) [NeZero n] :
    MulDistribMulAction (AbsGal K) (Mu K n) where
  smul sigma z := galoisOnRoots K n sigma z
  one_smul z := by
    show galoisOnRoots K n 1 z = z
    apply rootsOfUnity.coe_injective
    simp [galoisOnRoots, toAlgEquiv_one]
  mul_smul sigma tau z := by
    show galoisOnRoots K n (sigma * tau) z
        = galoisOnRoots K n sigma (galoisOnRoots K n tau z)
    apply rootsOfUnity.coe_injective
    simp [galoisOnRoots, toAlgEquiv_mul, AlgEquiv.mul_apply]
  smul_one sigma := by
    show galoisOnRoots K n sigma 1 = 1
    apply rootsOfUnity.coe_injective
    simp [galoisOnRoots]
  smul_mul sigma x y := by
    show galoisOnRoots K n sigma (x * y)
        = galoisOnRoots K n sigma x * galoisOnRoots K n sigma y
    apply rootsOfUnity.coe_injective
    simp [galoisOnRoots]

def additiveRootsAction (n : ℕ) [NeZero n] :
    DistribMulAction (AbsGal K) (Additive (Mu K n)) where
  smul sigma z := Additive.ofMul (galoisOnRoots K n sigma z.toMul)
  one_smul z := by
    show Additive.ofMul (galoisOnRoots K n 1 z.toMul) = z
    apply Additive.toMul.injective
    apply rootsOfUnity.coe_injective
    simp [galoisOnRoots, toAlgEquiv_one]
  mul_smul sigma tau z := by
    show Additive.ofMul (galoisOnRoots K n (sigma * tau) z.toMul)
        = Additive.ofMul (galoisOnRoots K n sigma
            (galoisOnRoots K n tau z.toMul))
    apply Additive.toMul.injective
    apply rootsOfUnity.coe_injective
    simp [galoisOnRoots, toAlgEquiv_mul, AlgEquiv.mul_apply]
  smul_zero sigma := by
    show Additive.ofMul (galoisOnRoots K n sigma (1 : Mu K n)) = 0
    apply Additive.toMul.injective
    apply rootsOfUnity.coe_injective
    simp [galoisOnRoots]
  smul_add sigma x y := by
    show Additive.ofMul (galoisOnRoots K n sigma (x.toMul * y.toMul))
        = Additive.ofMul (galoisOnRoots K n sigma x.toMul)
          + Additive.ofMul (galoisOnRoots K n sigma y.toMul)
    apply Additive.toMul.injective
    apply rootsOfUnity.coe_injective
    simp [galoisOnRoots]

local instance coefficientAction (n : ℕ) [NeZero n] :
    DistribMulAction (AbsGal K) (Additive (Mu K n)) :=
  additiveRootsAction K n

def coefficientValue (n : ℕ) [NeZero n]
    (z : Additive (Mu K n)) : Closure K :=
  (((z.toMul : Mu K n) : (Closure K)ˣ) : Closure K)

theorem isOpen_fixingValue (x : Closure K) :
    IsOpen {sigma : AbsGal K | toAlgEquiv K sigma x = x} := by
  letI : Algebra.IsIntegral K (Closure K) :=
    Algebra.isAlgebraic_iff_isIntegral.mp (AlgebraicClosure.isAlgebraic K)
  change
    IsOpen
      {sigma : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) |
        sigma x = x}
  simpa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] using
    (stabilizer_isOpen_of_isIntegral (K := K) (L := Closure K) x)

theorem coefficient_stabilizer_eq (n : ℕ) [NeZero n]
    (z : Additive (Mu K n)) :
    (MulAction.stabilizer (AbsGal K) z : Set (AbsGal K)) =
      {sigma : AbsGal K |
        toAlgEquiv K sigma (coefficientValue K n z) =
          coefficientValue K n z} := by
  ext sigma
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_setOf_eq]
  constructor
  · intro h
    have h' := congrArg
      (fun w : Additive (Mu K n) => coefficientValue K n w) h
    simpa [coefficientValue, additiveRootsAction, galoisOnRoots_coe] using h'
  · intro h
    apply Additive.toMul.injective
    apply rootsOfUnity.coe_injective
    simpa [coefficientValue, additiveRootsAction, galoisOnRoots_coe] using h

local instance coefficientContinuousSMul (n : ℕ) [NeZero n] :
    ContinuousSMul (AbsGal K) (Additive (Mu K n)) :=
  (continuousSMul_iff_stabilizer_isOpen).2 fun z => by
    rw [coefficient_stabilizer_eq K n z]
    exact isOpen_fixingValue K (coefficientValue K n z)

theorem ratioValue_continuous (n : ℕ) [NeZero n] (a : Kˣ) :
    Continuous
      (fun sigma : AbsGal K =>
        Additive.ofMul (ratioRoot K n a sigma)) := by
  rw [← IsLocallyConstant.iff_continuous]
  apply (IsLocallyConstant.iff_exists_open _).2
  intro sigma
  let r : Closure K := chosenRoot K n a
  let U : Set (AbsGal K) :=
    {tau | toAlgEquiv K (sigma⁻¹ * tau) r = r}
  refine ⟨U, ?_, ?_, ?_⟩
  · have hfix :
        IsOpen {g : AbsGal K | toAlgEquiv K g r = r} :=
      isOpen_fixingValue K r
    have htranslate :
        Continuous (fun tau : AbsGal K => sigma⁻¹ * tau) :=
      continuous_const.mul continuous_id
    simpa [U] using hfix.preimage htranslate
  · show toAlgEquiv K (sigma⁻¹ * sigma) r = r
    rw [inv_mul_cancel, toAlgEquiv_one]
    rfl
  · intro tau ht
    change toAlgEquiv K (sigma⁻¹ * tau) r = r at ht
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    change
      toAlgEquiv K tau r / r =
        toAlgEquiv K sigma r / r
    have key : toAlgEquiv K tau r = toAlgEquiv K sigma r := by
      have h := congrArg (toAlgEquiv K sigma) ht
      rwa [← AlgEquiv.mul_apply, ← toAlgEquiv_mul, mul_inv_cancel_left] at h
    rw [key]

theorem additiveRatio_continuous (n : ℕ) [NeZero n] (a : Kˣ) :
    Continuous (fun sigma : AbsGal K =>
      Additive.ofMul (ratioRoot K n a sigma)) :=
  ratioValue_continuous K n a

def finiteContinuousCocycle (n : ℕ) [NeZero n] (a : Kˣ) :
    Cocycle (AbsGal K) (Additive (Mu K n)) where
  toContinuousMap :=
    ⟨fun sigma => Additive.ofMul (ratioRoot K n a sigma),
      additiveRatio_continuous K n a⟩
  cocycle' sigma tau := by
    apply Additive.toMul.injective
    exact ratioRoot_mul K n a sigma tau

def finiteKummerClass (n : ℕ) [NeZero n] (a : Kˣ) :
    H1 (AbsGal K) (Additive (Mu K n)) :=
  Quotient.mk _ (finiteContinuousCocycle K n a)

@[simp] theorem finiteContinuousCocycle_apply
    (n : ℕ) [NeZero n] (a : Kˣ) (sigma : AbsGal K) :
    finiteContinuousCocycle K n a sigma =
      Additive.ofMul (ratioRoot K n a sigma) := rfl

end Src.CoreLayer.LanaStep6.FiniteContinuousKummer

end
