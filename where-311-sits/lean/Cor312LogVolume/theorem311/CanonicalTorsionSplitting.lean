import Cor312LogVolume.theorem311.RetainedMonoidSplittingAdapter
import Cor312LogVolume.theorem311.ArithmeticRetainedThetaSide

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.CanonicalTorsionSplitting

open CitedLV.ThetaLink
open CitedLV.Theorem311.ProcessionPolyFunctorBoundary
open CitedLV.Theorem311.CompletePolySplittingTransport
open CitedLV.Theorem311.RetainedMonoidSplittingAdapter

universe uObj uG uO uBad uLabel

def torsionSubmonoid
    (D : RetainedThetaSide.{uG,uO}) (n : Nat) : Submonoid D.O where
  carrier := {x | x ^ n = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_pow, ha, hb, one_mul]

def splitting
    (Bad : Type uBad) (Label : Type uLabel)
    (D : RetainedThetaSide.{uG,uO}) (n : Nat) :
    BadPlaceLGPSplittingRaw Bad Label
      (fun _ => D.O) (fun _ _ => D.O) where
  split := fun _ => torsionSubmonoid D n
  profile := fun _ x _ => x.1
  act := fun _ x y j => x.1 * y j

theorem splitting_ext
    {Bad : Type uBad} {Label : Type uLabel}
    {D : RetainedThetaSide.{uG,uO}}
    {a b : BadPlaceLGPSplittingRaw Bad Label
      (fun _ => D.O) (fun _ _ => D.O)}
    (hs : a.split = b.split)
    (hp : HEq a.profile b.profile)
    (ha : HEq a.act b.act) : a = b := by
  cases a
  cases b
  simp_all

theorem torsion_transport
    {D E : RetainedThetaSide.{uG,uO}}
    (e : AdmissibleIso D E) (n : Nat) :
    (torsionSubmonoid D n).map e.monoidEquiv.toMulEquiv.toMonoidHom =
      torsionSubmonoid E n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ^ n = 1 := hx
    change (e.monoidEquiv x) ^ n = 1

    rw [← map_pow, hx']
    exact map_one e.monoidEquiv.toMonoidHom
  · intro hy
    have hy' : y ^ n = 1 := hy
    refine ⟨e.monoidEquiv.symm y, ?_, e.monoidEquiv.apply_symm_apply y⟩
    change (e.monoidEquiv.symm y) ^ n = 1
    apply e.monoidEquiv.injective

    rw [map_pow, e.monoidEquiv.apply_symm_apply, hy', map_one]

theorem transportedSplit_eq
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    {Bad : Type uBad} {Label : Type uLabel}
    {p q : Obj}
    (e : AdmissibleIso (F.side p) (F.side q))
    (n : Nat) (v : Bad) :
    transportedSplit F (Psi F Bad) (Packet F Bad Label) (carrierAction F Bad Label) e
      (splitting Bad Label (F.side p) n) v =
      torsionSubmonoid (F.side q) n := by
  ext y
  change ((e.monoidEquiv.symm y) ^ n = 1) ↔ (y ^ n = 1)
  constructor
  · intro h
    have h' := congrArg e.monoidEquiv h
    simpa using h'
  · intro h
    have h' := congrArg e.monoidEquiv.symm h
    simpa using h'

def build
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    (Bad : Type uBad) (Label : Type uLabel) (n : Nat)
    (p : Obj) :
    CompletePolySplittingTransport.Output (Psi F Bad) (Packet F Bad Label) p :=
  splitting Bad Label (F.side p) n

theorem build_natural
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    (Bad : Type uBad) (Label : Type uLabel) (n : Nat) :
    RetainedMonoidSplittingAdapter.SourceBuildNaturality F Bad Label
      (build F Bad Label n) := by
  intro p q e
  let A := F.map e
  let R := build F Bad Label n p
  let S := build F Bad Label n q

  have hs :
      (transport F (Psi F Bad) (Packet F Bad Label) (carrierAction F Bad Label) A R).split =
        S.split := by
    funext v
    exact transportedSplit_eq F A n v

  refine CompletePolySplittingTransport.splittingExt hs ?_ ?_
  · intro v x hR hS
    funext j
    simp [transport, build, splitting, sourceSplitElement, forwardPacket,
      carrierAction, Psi, Packet]
  · intro v x hR hS y
    funext j
    simp [transport, build, splitting, sourceSplitElement, forwardPacket,
      backwardPacket, carrierAction, Psi, Packet]

abbrev buildL7
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    (Bad : Type uBad) (Label : Type uLabel) :
    (p : Obj) -> CompletePolySplittingTransport.Output (Psi F Bad) (Packet F Bad Label) p :=
  build F Bad Label 14

theorem buildL7_natural
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    (Bad : Type uBad) (Label : Type uLabel) :
    RetainedMonoidSplittingAdapter.SourceBuildNaturality F Bad Label
      (buildL7 F Bad Label) :=
  build_natural F Bad Label 14

end CitedLV.Theorem311.CanonicalTorsionSplitting
end
