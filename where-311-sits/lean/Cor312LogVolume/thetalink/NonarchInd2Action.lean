import Cor312LogVolume.thetalink.CompletePolyIso
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Pi.Lemmas

namespace CitedLV.ThetaLink

noncomputable section

universe uG uO uP uF uS

def NonarchLocalIsm
    (D : RetainedThetaSide.{uG, uO}) : Subgroup (MulAut D.O) where
  carrier e :=
    Continuous e ∧ Continuous e.symm ∧
      (∀ g x, e (g • x) = g • e x) ∧
      (∀ H x, x ∈ D.datum.lattice H ↔ e x ∈ D.datum.lattice H)
  one_mem' := by
    refine ⟨continuous_id, continuous_id, ?_, ?_⟩
    · intro g x
      rfl
    · intro H x
      rfl
  mul_mem' := by
    rintro e f ⟨he, hei, heq, hel⟩ ⟨hf, hfi, hfq, hfl⟩
    refine ⟨he.comp hf, hfi.comp hei, ?_, ?_⟩
    · intro (g : D.G) (x : D.O)
      change e (f (g • x)) = g • e (f x)
      rw [hfq, heq]
    · intro (H : OpenSubgroup D.G) (x : D.O)
      exact (hfl H x).trans (hel H (f x))
  inv_mem' := by
    rintro e ⟨he, hei, heq, hel⟩
    refine ⟨hei, he, ?_, ?_⟩
    · intro (g : D.G) (x : D.O)
      apply e.injective
      simpa using (heq g (e.symm x)).symm
    · intro (H : OpenSubgroup D.G) (x : D.O)
      simpa using (hel H (e.symm x)).symm

def NonarchLocalIsm.toAdmissible
    (D : RetainedThetaSide.{uG, uO})
    (e : NonarchLocalIsm D) : AdmissibleIso D D where
  groupEquiv := ContinuousMulEquiv.refl D.G
  monoidEquiv :=
    { e.1 with
      continuous_toFun := e.2.1
      continuous_invFun := e.2.2.1 }
  equivariant := e.2.2.2.1
  preservesLattices := by
    intro H x
    simpa using e.2.2.2.2 H x

theorem NonarchLocalIsm.toAdmissible_mem_complete
    (D : RetainedThetaSide.{uG, uO}) (e : NonarchLocalIsm D) :
    NonarchLocalIsm.toAdmissible D e ∈ CompletePolyIso D D :=
  mem_completePolyIso _

structure FixedJFactorSet (j : ℕ) where
  Carrier : Type uF
  [fintypeCarrier : Fintype Carrier]
  card_eq : Fintype.card Carrier = j + 1

attribute [instance] FixedJFactorSet.fintypeCarrier

abbrev NonarchInd2Coordinate
    {j : ℕ} (Place : Type uP)
    (Factor : FixedJFactorSet j)
    (Above : Place → Type uS) :=
  Σ v, Factor.Carrier × Above v

abbrev IndependentNonarchIsm
    {I : Type*} (D : I → RetainedThetaSide.{uG, uO}) :=
  (i : I) → NonarchLocalIsm (D i)

abbrev NonarchComponentPacket
    {I : Type*} (D : I → RetainedThetaSide.{uG, uO}) :=
  (i : I) → (D i).O

theorem independentNonarchIsm_smul_apply
    {I : Type*} (D : I → RetainedThetaSide.{uG, uO})
    (a : IndependentNonarchIsm D)
    (x : NonarchComponentPacket D) (i : I) :
    (a • x) i = (a i : MulAut (D i).O) (x i) :=
  rfl

def singleNonarchIsm
    {I : Type*} [DecidableEq I]
    (D : I → RetainedThetaSide.{uG, uO})
    (i : I) (e : NonarchLocalIsm (D i)) : IndependentNonarchIsm D :=
  Pi.mulSingle i e

theorem singleNonarchIsm_same
    {I : Type*} [DecidableEq I]
    (D : I → RetainedThetaSide.{uG, uO})
    (i : I) (e : NonarchLocalIsm (D i))
    (x : NonarchComponentPacket D) :
    (singleNonarchIsm D i e • x) i = (e : MulAut (D i).O) (x i) := by
  rw [independentNonarchIsm_smul_apply]
  simp [singleNonarchIsm]

theorem singleNonarchIsm_other
    {I : Type*} [DecidableEq I]
    (D : I → RetainedThetaSide.{uG, uO})
    {i k : I} (h : k ≠ i)
    (e : NonarchLocalIsm (D i))
    (x : NonarchComponentPacket D) :
    (singleNonarchIsm D i e • x) k = x k := by
  simp [singleNonarchIsm, h]

theorem independentNonarchIsm_supported
    {I : Type*} (D : I → RetainedThetaSide.{uG, uO})
    (a : IndependentNonarchIsm D) :
    ∀ i, NonarchLocalIsm.toAdmissible (D i) (a i) ∈
      CompletePolyIso (D i) (D i) := by
  intro i
  exact NonarchLocalIsm.toAdmissible_mem_complete (D i) (a i)

theorem fixedRegularEquivariantMulAut_eq_one
    {M : Type*} [Group M] (e : MulAut M)
    (h : ∀ g x : M, e (g * x) = g * e x) : e = 1 := by
  ext g
  simpa using h g 1

abbrev TrivialC3Group := Multiplicative (ZMod 1)

local instance : MulAction TrivialC3Group C3Square where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

local instance : ContinuousSMul TrivialC3Group C3Square :=
  ⟨continuous_snd⟩

abbrev c3TrivialAll : RetainedThetaSide where
  G := TrivialC3Group
  O := C3Square
  datum := { lattice := fun _ ↦ ⊤ }

abbrev c3TrivialMarked : RetainedThetaSide where
  G := TrivialC3Group
  O := C3Square
  datum := { lattice := fun _ ↦ c3FirstAxis }

def c3SwapNonarchIsm : NonarchLocalIsm c3TrivialAll := by
  refine ⟨c3SquareSwap.toMulEquiv, ?_⟩
  refine ⟨c3SquareSwap.continuous_toFun,
    c3SquareSwap.continuous_invFun, ?_, ?_⟩
  · intro g x
    rfl
  · intro H x
    simp [c3TrivialAll]

theorem c3SquareSwap_not_local_for_marked :
    c3SquareSwap.toMulEquiv ∉ NonarchLocalIsm c3TrivialMarked := by
  intro h
  have hw : c3AxisWitness ∈
      c3TrivialMarked.datum.lattice
        (⊤ : OpenSubgroup c3TrivialMarked.G) := by
    simp [c3TrivialMarked, c3AxisWitness, c3FirstAxis]
  have himage := (h.2.2.2
    (⊤ : OpenSubgroup c3TrivialMarked.G) c3AxisWitness).mp hw
  exact c3SquareSwap_moves_axis_witness (by
    simpa [c3TrivialMarked] using himage)

def toyFactorSet : FixedJFactorSet 1 where
  Carrier := Bool
  card_eq := by decide

abbrev ToyAbove (_v : Bool) := Bool
abbrev ToyNonarchCoordinate :=
  NonarchInd2Coordinate Bool toyFactorSet ToyAbove
abbrev toyNonarchSides : ToyNonarchCoordinate → RetainedThetaSide :=
  fun _ ↦ c3TrivialAll

local instance : DecidableEq ToyNonarchCoordinate := Classical.decEq _

def toyTargetCoordinate : ToyNonarchCoordinate :=
  ⟨true, true, true⟩

def toyOtherCoordinate : ToyNonarchCoordinate :=
  ⟨false, true, true⟩

def toyOtherFactorCoordinate : ToyNonarchCoordinate :=
  ⟨true, false, true⟩

def toyOtherSummandCoordinate : ToyNonarchCoordinate :=
  ⟨true, true, false⟩

def toySingleSwap : IndependentNonarchIsm toyNonarchSides :=
  singleNonarchIsm toyNonarchSides toyTargetCoordinate c3SwapNonarchIsm

def toyAxisPacket : NonarchComponentPacket toyNonarchSides :=
  fun _ ↦ c3AxisWitness

theorem toySingleSwap_changes_target :
    (toySingleSwap • toyAxisPacket) toyTargetCoordinate ≠
      toyAxisPacket toyTargetCoordinate := by
  change
    (singleNonarchIsm toyNonarchSides toyTargetCoordinate c3SwapNonarchIsm •
      toyAxisPacket) toyTargetCoordinate ≠
        toyAxisPacket toyTargetCoordinate
  rw [singleNonarchIsm_same]
  intro h
  have hfst := congrArg Prod.fst h
  exact c3Generator_ne_one (by
    simpa [c3SquareSwap, c3AxisWitness] using hfst.symm)

theorem toySingleSwap_fixes_other :
    (toySingleSwap • toyAxisPacket) toyOtherCoordinate =
      toyAxisPacket toyOtherCoordinate := by
  simpa [toySingleSwap] using
    (singleNonarchIsm_other toyNonarchSides
      (i := toyTargetCoordinate) (k := toyOtherCoordinate)
      (by
        intro h
        have hv := congrArg (fun c : ToyNonarchCoordinate ↦ c.1) h
        simpa [toyOtherCoordinate, toyTargetCoordinate] using hv)
      c3SwapNonarchIsm toyAxisPacket)

theorem toySingleSwap_fixes_other_factor :
    (toySingleSwap • toyAxisPacket) toyOtherFactorCoordinate =
      toyAxisPacket toyOtherFactorCoordinate := by
  simpa [toySingleSwap] using
    (singleNonarchIsm_other toyNonarchSides
      (i := toyTargetCoordinate) (k := toyOtherFactorCoordinate)
      (by
        intro h
        have ha := congrArg (fun c : ToyNonarchCoordinate ↦ c.2.1) h
        simpa [toyOtherFactorCoordinate, toyTargetCoordinate] using ha)
      c3SwapNonarchIsm toyAxisPacket)

theorem toySingleSwap_fixes_other_summand :
    (toySingleSwap • toyAxisPacket) toyOtherSummandCoordinate =
      toyAxisPacket toyOtherSummandCoordinate := by
  simpa [toySingleSwap] using
    (singleNonarchIsm_other toyNonarchSides
      (i := toyTargetCoordinate) (k := toyOtherSummandCoordinate)
      (by
        intro h
        have hs := congrArg (fun c : ToyNonarchCoordinate ↦ c.2.2) h
        simpa [toyOtherSummandCoordinate, toyTargetCoordinate] using hs)
      c3SwapNonarchIsm toyAxisPacket)

theorem identityIndependentNonarchIsm_moves_nothing
    {I : Type*} (D : I → RetainedThetaSide.{uG, uO})
    (x : NonarchComponentPacket D) :
    (1 : IndependentNonarchIsm D) • x = x :=
  one_smul _ _

end

end CitedLV.ThetaLink
