import Cor312LogVolume.theorem311.HDDPolyMorphismToDominatedIncidence
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.GlobalMultiplierDegreeMonotonicity

open CitedLV.Theorem311.HDDPolyMorphismToDominatedIncidence

universe uO uF

structure DegreeSystem where
  Obj : Type uO
  Multiplier : Type uF

  act : Multiplier -> Obj -> Obj
  LE : Obj -> Obj -> Prop
  degree : Obj -> Real

  degree_act :
    forall (f : Multiplier) (J : Obj),
      degree (act f J) = degree J

  degree_mono :
    forall {J1 J2 : Obj},
      LE J1 J2 -> degree J1 <= degree J2

variable (D : DegreeSystem.{uO,uF})

structure LinearMorphism (J1 J2 : D.Obj) where
  multiplier : D.Multiplier
  integral : D.LE (D.act multiplier J1) J2

theorem LinearMorphism.degree_le
    {J1 J2 : D.Obj}
    (f : LinearMorphism D J1 J2) :
    D.degree J1 <= D.degree J2 := by
  rw [<- D.degree_act f.multiplier J1]
  exact D.degree_mono f.integral

def toDirectedDegreeSystem : DirectedDegreeSystem where
  Source := D.Obj
  Target := D.Obj
  Hom := LinearMorphism D
  sourceDegree := D.degree
  targetDegree := D.degree
  degree_mono := fun f => f.degree_le

theorem orbit_degree_le
    {J1 J2 : D.Obj}
    (A : Set (LinearMorphism D J1 J2))
    (hA : A.Nonempty) :
    D.degree J1 <= D.degree J2 := by
  obtain ⟨f, hf⟩ := hA
  exact f.degree_le

structure TensorDegreeSystem extends DegreeSystem where
  tensorUnit : Obj
  tensorPower : Nat -> Obj -> Obj
  tensor_zero : forall J : Obj, tensorPower 0 J = tensorUnit
  tensor_one : forall J : Obj, tensorPower 1 J = J
  degree_tensor :
    forall (M : Nat) (J : Obj),
      degree (tensorPower M J) = (M : Real) * degree J

variable (T : TensorDegreeSystem.{uO,uF})

theorem degree_tensor_unit : T.degree T.tensorUnit = 0 := by
  simpa only [T.tensor_zero, Nat.cast_zero, zero_mul] using
    T.degree_tensor 0 T.tensorUnit

theorem tensor_linear_morphism_degree
    (M : Nat) {J target : T.Obj}
    (f : LinearMorphism T.toDegreeSystem (T.tensorPower M J) target) :
    (M : Real) * T.degree J <= T.degree target := by
  rw [<- T.degree_tensor M J]
  exact f.degree_le

theorem cancel_positive_tensor_degree
    (M : Nat) (hM : 0 < M)
    (qDegree thetaDegree : Real)
    (h : (M : Real) * qDegree <= (M : Real) * thetaDegree) :
    qDegree <= thetaDegree := by
  exact le_of_mul_le_mul_left h (Nat.cast_pos.mpr hM)

theorem normalized_degree_le_of_tensor_morphism
    (M : Nat) (hM : 0 < M)
    {J target : T.Obj}
    (thetaDegree : Real)
    (f : LinearMorphism T.toDegreeSystem (T.tensorPower M J) target)
    (htarget : T.degree target = (M : Real) * thetaDegree) :
    T.degree J <= thetaDegree := by
  apply cancel_positive_tensor_degree M hM
  rw [<- htarget]
  exact tensor_linear_morphism_degree T M f

def strictSystem : DegreeSystem where
  Obj := Bool
  Multiplier := Unit
  act := fun _ J => J
  LE := fun J1 J2 => J1 = false ∨ J2 = true
  degree := fun J => if J then 1 else 0
  degree_act := by
    intro f J
    rfl
  degree_mono := by
    intro J1 J2 h
    rcases h with hfalse | htrue
    · subst J1
      cases J2 <;> norm_num
    · subst J2
      cases J1 <;> simp

def strictArrow : LinearMorphism strictSystem false true where
  multiplier := ()
  integral := Or.inl rfl

theorem linear_morphism_need_not_preserve_degree :
    strictSystem.degree false < strictSystem.degree true ∧
      strictSystem.degree false <= strictSystem.degree true := by
  constructor
  · change (0 : Real) < 1
    norm_num
  · exact strictArrow.degree_le

end CitedLV.Theorem311.GlobalMultiplierDegreeMonotonicity
end
