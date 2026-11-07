import Cor312LogVolume.theorem311.ProcessionPolyFunctorBoundary
import Cor312LogVolume.theorem311.RLGPSimultaneousBuild

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.CompletePolyComponentAction

open CitedLV.ThetaLink
open CitedLV.Theorem311.ProcessionPolyFunctorBoundary

universe uObj uOut uG uO

structure CompletePolyActionRaw
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    (Output : Obj -> Type uOut) where
  map :
    {p q : Obj} ->
      AdmissibleIso (F.side p) (F.side q) ->
        Output p -> Output q

def ActionPreservesIdentity
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {F : ProcessionPolyFunctorRaw G}
    {Output : Obj -> Type uOut}
    (A : CompletePolyActionRaw F Output) : Prop :=
  ∀ p x, A.map (AdmissibleIso.refl (F.side p)) x = x

def ActionPreservesComposition
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {F : ProcessionPolyFunctorRaw G}
    {Output : Obj -> Type uOut}
    (A : CompletePolyActionRaw F Output) : Prop :=
  ∀ {p q r}
    (e : AdmissibleIso (F.side p) (F.side q))
    (f : AdmissibleIso (F.side q) (F.side r))
    (x : Output p),
      A.map (e.trans f) x = A.map f (A.map e x)

def EveryPolyTransportInjective
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {F : ProcessionPolyFunctorRaw G}
    {Output : Obj -> Type uOut}
    (A : CompletePolyActionRaw F Output) : Prop :=
  ∀ {p q} (e : AdmissibleIso (F.side p) (F.side q)),
    Function.Injective (A.map e)

def BuildNatural
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {F : ProcessionPolyFunctorRaw G}
    {Output : Obj -> Type uOut}
    (A : CompletePolyActionRaw F Output)
    (build : (p : Obj) -> Output p) : Prop :=
  ∀ {p q} (e : G.Hom p q),
    A.map (F.map e) (build p) = build q

def toProcessionAlgorithmRaw
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    {Output : Obj -> Type uOut}
    (A : CompletePolyActionRaw F Output)
    (build : (p : Obj) -> Output p) :
    ProcessionAlgorithmRaw G Output where
  build := build
  transport := fun e => A.map (F.map e)

theorem transportIdentity
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    {Output : Obj -> Type uOut}
    (A : CompletePolyActionRaw F Output)
    (build : (p : Obj) -> Output p)
    (hF : PreservesIdentity F)
    (hA : ActionPreservesIdentity A) :
    TransportIdentityLaw (toProcessionAlgorithmRaw F A build) := by
  intro p x
  change A.map (F.map (G.idHom p)) x = x
  rw [hF p]
  exact hA p x

theorem transportComposition
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    {Output : Obj -> Type uOut}
    (A : CompletePolyActionRaw F Output)
    (build : (p : Obj) -> Output p)
    (hF : PreservesComposition F)
    (hA : ActionPreservesComposition A) :
    TransportCompositionLaw (toProcessionAlgorithmRaw F A build) := by
  intro p q r e f x
  change A.map (F.map (G.comp e f)) x =
    A.map (F.map f) (A.map (F.map e) x)
  rw [hF e f]
  exact hA (F.map e) (F.map f) x

theorem constructionCommutes
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    {Output : Obj -> Type uOut}
    (A : CompletePolyActionRaw F Output)
    (build : (p : Obj) -> Output p)
    (h : BuildNatural A build) :
    ConstructionCommutes (toProcessionAlgorithmRaw F A build) := by
  intro p q e
  exact h e

theorem everyTransportInjective
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    {Output : Obj -> Type uOut}
    (A : CompletePolyActionRaw F Output)
    (build : (p : Obj) -> Output p)
    (h : EveryPolyTransportInjective A) :
    EveryTransportInjective (toProcessionAlgorithmRaw F A build) := by
  intro p q e
  exact h (F.map e)

def ComponentCoherent
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    {Output : Obj -> Type uOut}
    (A : CompletePolyActionRaw F Output)
    (build : (p : Obj) -> Output p) : Prop :=
  PreservesIdentity F /\
  PreservesComposition F /\
  ActionPreservesIdentity A /\
  ActionPreservesComposition A /\
  EveryPolyTransportInjective A /\
  BuildNatural A build

theorem componentCoherent_gives_algorithm_laws
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    (F : ProcessionPolyFunctorRaw G)
    {Output : Obj -> Type uOut}
    (A : CompletePolyActionRaw F Output)
    (build : (p : Obj) -> Output p)
    (h : ComponentCoherent F A build) :
    TransportIdentityLaw (toProcessionAlgorithmRaw F A build) /\
    TransportCompositionLaw (toProcessionAlgorithmRaw F A build) /\
    ConstructionCommutes (toProcessionAlgorithmRaw F A build) /\
    EveryTransportInjective (toProcessionAlgorithmRaw F A build) := by
  rcases h with ⟨hFid, hFcomp, hAid, hAcomp, hAinj, hbuild⟩
  exact
    ⟨transportIdentity F A build hFid hAid,
     transportComposition F A build hFcomp hAcomp,
     constructionCommutes F A build hbuild,
     everyTransportInjective F A build hAinj⟩

end CitedLV.Theorem311.CompletePolyComponentAction
end
