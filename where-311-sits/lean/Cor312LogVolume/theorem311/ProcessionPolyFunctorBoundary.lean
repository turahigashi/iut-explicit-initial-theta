import Cor312LogVolume.theorem311.CompletePolyProcessionGroupoid
import Cor312LogVolume.thetalink.CompletePolyIsoIndeterminacy

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.ProcessionPolyFunctorBoundary

open CitedLV.ThetaLink
open CitedLV.Theorem311.CompletePolyProcession

universe uObj uG uO

structure ProcessionPolyFunctorRaw
    {Obj : Type uObj} (G : ProcessionIsoRaw Obj) where
  side : Obj -> RetainedThetaSide.{uG,uO}
  map :
    {p q : Obj} -> G.Hom p q ->
      AdmissibleIso (side p) (side q)

def PreservesIdentity
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G) : Prop :=
  ∀ p, F.map (G.idHom p) = AdmissibleIso.refl (F.side p)

def PreservesComposition
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G) : Prop :=
  ∀ {p q r} (e : G.Hom p q) (f : G.Hom q r),
    F.map (G.comp e f) = (F.map e).trans (F.map f)

theorem map_mem_complete
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    {p q : Obj} (e : G.Hom p q) :
    F.map e ∈ CompletePolyIso (F.side p) (F.side q) :=
  mem_completePolyIso _

theorem complete_nonempty_on_image
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    (hconn : EveryObjectPairConnected G)
    (p q : Obj) :
    (CompletePolyIso (F.side p) (F.side q)).Nonempty := by
  obtain ⟨e⟩ := hconn p q
  exact ⟨F.map e, map_mem_complete F e⟩

theorem map_inv
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    (hid : PreservesIdentity F)
    (hcomp : PreservesComposition F)
    (hinv : ProcessionInverseLaws G)
    {p q : Obj} (e : G.Hom p q) :
    F.map (G.inv e) = (F.map e).symm := by

  have hcomp2 : (F.map e).trans (F.map (G.inv e)) = AdmissibleIso.refl (F.side p) := by
    calc
      (F.map e).trans (F.map (G.inv e))
          = F.map (G.comp e (G.inv e)) := (hcomp e (G.inv e)).symm
      _ = F.map (G.idHom p) := by rw [hinv.1 e]
      _ = AdmissibleIso.refl (F.side p) := hid p
  apply admissibleIso_ext
  · intro x
    have key : ∀ y : (F.side p).G,
        (F.map (G.inv e)).groupEquiv ((F.map e).groupEquiv y) = y := by
      intro y
      have h := congrArg
        (fun a : AdmissibleIso (F.side p) (F.side p) => a.groupEquiv y) hcomp2
      simpa [AdmissibleIso.trans, AdmissibleIso.refl] using h
    have h2 := key ((F.map e).groupEquiv.symm x)
    simp only [ContinuousMulEquiv.apply_symm_apply] at h2
    simpa [AdmissibleIso.symm] using h2
  · intro x
    have key : ∀ y : (F.side p).O,
        (F.map (G.inv e)).monoidEquiv ((F.map e).monoidEquiv y) = y := by
      intro y
      have h := congrArg
        (fun a : AdmissibleIso (F.side p) (F.side p) => a.monoidEquiv y) hcomp2
      simpa [AdmissibleIso.trans, AdmissibleIso.refl] using h
    have h2 := key ((F.map e).monoidEquiv.symm x)
    simp only [ContinuousMulEquiv.apply_symm_apply] at h2
    simpa [AdmissibleIso.symm] using h2

def CoherentArrowLift
    {Obj : Type uObj} (G : ProcessionIsoRaw Obj)
    (F : ProcessionPolyFunctorRaw G) : Prop :=
  ProcessionGroupoidLaws G /\
  PreservesIdentity F /\
  PreservesComposition F

end CitedLV.Theorem311.ProcessionPolyFunctorBoundary
end
