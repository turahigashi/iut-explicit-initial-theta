import Cor312LogVolume.theorem311.CompletePolyComponentAction
import Cor312LogVolume.theorem311.BadPlaceLGPSplittingAction

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.CompletePolySplittingTransport

open CitedLV.ThetaLink
open CitedLV.Theorem311.ProcessionPolyFunctorBoundary
open CitedLV.Theorem311.CompletePolyComponentAction

universe uObj uG uO uBad uLabel uPsi uPacket

variable
  {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
  (F : ProcessionPolyFunctorRaw G)
  {Bad : Type uBad} {Label : Type uLabel}
  (Psi : Obj -> Bad -> Type uPsi)
  (Packet : Obj -> Bad -> Label -> Type uPacket)
  [forall p v, Monoid (Psi p v)]

structure CarrierActionRaw where
  psiEquiv :
    {p q : Obj} ->
      AdmissibleIso (F.side p) (F.side q) ->
        (v : Bad) -> Psi p v ≃* Psi q v
  packetEquiv :
    {p q : Obj} ->
      AdmissibleIso (F.side p) (F.side q) ->
        (v : Bad) -> (j : Label) ->
          Packet p v j ≃ Packet q v j

abbrev Output (p : Obj) :=
  BadPlaceLGPSplittingRaw Bad Label (Psi p) (Packet p)

def transportedSplit
    (C : CarrierActionRaw F Psi Packet)
    {p q : Obj}
    (e : AdmissibleIso (F.side p) (F.side q))
    (R : Output Psi Packet p)
    (v : Bad) :
    Submonoid (Psi q v) :=
  (R.split v).comap (C.psiEquiv e v).symm.toMonoidHom

def sourceSplitElement
    (C : CarrierActionRaw F Psi Packet)
    {p q : Obj}
    (e : AdmissibleIso (F.side p) (F.side q))
    (R : Output Psi Packet p)
    (v : Bad)
    (x : transportedSplit F Psi Packet C e R v) :
    R.split v :=
  ⟨(C.psiEquiv e v).symm x.1, x.2⟩

def forwardPacket
    (C : CarrierActionRaw F Psi Packet)
    {p q : Obj}
    (e : AdmissibleIso (F.side p) (F.side q))
    (v : Bad) :
    SelectedPacketProduct Label (Packet p) v ->
      SelectedPacketProduct Label (Packet q) v :=
  fun x j => C.packetEquiv e v j (x j)

def backwardPacket
    (C : CarrierActionRaw F Psi Packet)
    {p q : Obj}
    (e : AdmissibleIso (F.side p) (F.side q))
    (v : Bad) :
    SelectedPacketProduct Label (Packet q) v ->
      SelectedPacketProduct Label (Packet p) v :=
  fun x j => (C.packetEquiv e v j).symm (x j)

def transport
    (C : CarrierActionRaw F Psi Packet)
    {p q : Obj}
    (e : AdmissibleIso (F.side p) (F.side q))
    (R : Output Psi Packet p) :
    Output Psi Packet q where
  split := transportedSplit F Psi Packet C e R
  profile := fun v x =>
    forwardPacket F Psi Packet C e v
      (R.profile v (sourceSplitElement F Psi Packet C e R v x))
  act := fun v x y =>
    forwardPacket F Psi Packet C e v
      (R.act v
        (sourceSplitElement F Psi Packet C e R v x)
        (backwardPacket F Psi Packet C e v y))

def polyAction
    (C : CarrierActionRaw F Psi Packet) :
    CompletePolyActionRaw F (Output Psi Packet) where
  map := fun e => transport F Psi Packet C e

theorem forward_backward
    (C : CarrierActionRaw F Psi Packet)
    {p q : Obj}
    (e : AdmissibleIso (F.side p) (F.side q))
    (v : Bad)
    (x : SelectedPacketProduct Label (Packet q) v) :
    forwardPacket F Psi Packet C e v
      (backwardPacket F Psi Packet C e v x) = x := by
  funext j
  exact (C.packetEquiv e v j).apply_symm_apply (x j)

theorem backward_forward
    (C : CarrierActionRaw F Psi Packet)
    {p q : Obj}
    (e : AdmissibleIso (F.side p) (F.side q))
    (v : Bad)
    (x : SelectedPacketProduct Label (Packet p) v) :
    backwardPacket F Psi Packet C e v
      (forwardPacket F Psi Packet C e v x) = x := by
  funext j
  exact (C.packetEquiv e v j).symm_apply_apply (x j)

theorem mem_transportedSplit_iff
    (C : CarrierActionRaw F Psi Packet)
    {p q : Obj}
    (e : AdmissibleIso (F.side p) (F.side q))
    (R : Output Psi Packet p)
    (v : Bad) (x : Psi q v) :
    x ∈ transportedSplit F Psi Packet C e R v ↔
      (C.psiEquiv e v).symm x ∈ R.split v :=
  Iff.rfl

def targetSplitElement
    (C : CarrierActionRaw F Psi Packet)
    {p q : Obj}
    (e : AdmissibleIso (F.side p) (F.side q))
    (R : Output Psi Packet p)
    (v : Bad) (x : R.split v) :
    transportedSplit F Psi Packet C e R v :=
  ⟨C.psiEquiv e v x.1, by
    change (C.psiEquiv e v).symm (C.psiEquiv e v x.1) ∈ R.split v
    rw [(C.psiEquiv e v).symm_apply_apply]
    exact x.2⟩

@[simp] theorem source_target_split
    (C : CarrierActionRaw F Psi Packet)
    {p q : Obj}
    (e : AdmissibleIso (F.side p) (F.side q))
    (R : Output Psi Packet p)
    (v : Bad) (x : R.split v) :
    sourceSplitElement F Psi Packet C e R v
      (targetSplitElement F Psi Packet C e R v x) = x := by
  apply Subtype.ext
  exact (C.psiEquiv e v).symm_apply_apply x.1

theorem profile_targetSplitElement
    (C : CarrierActionRaw F Psi Packet)
    {p q : Obj}
    (e : AdmissibleIso (F.side p) (F.side q))
    (R : Output Psi Packet p)
    (v : Bad) (x : R.split v) :
    (transport F Psi Packet C e R).profile v
        (targetSplitElement F Psi Packet C e R v x) =
      forwardPacket F Psi Packet C e v (R.profile v x) := by

  simp only [transport]
  rw [source_target_split F Psi Packet C e R v x]

theorem act_targetSplitElement
    (C : CarrierActionRaw F Psi Packet)
    {p q : Obj}
    (e : AdmissibleIso (F.side p) (F.side q))
    (R : Output Psi Packet p)
    (v : Bad) (x : R.split v)
    (y : SelectedPacketProduct Label (Packet p) v) :
    (transport F Psi Packet C e R).act v
        (targetSplitElement F Psi Packet C e R v x)
        (forwardPacket F Psi Packet C e v y) =
      forwardPacket F Psi Packet C e v (R.act v x y) := by
  simp only [transport]
  rw [show
      sourceSplitElement F Psi Packet C e R v
        (targetSplitElement F Psi Packet C e R v x) = x
    from source_target_split F Psi Packet C e R v x]
  rw [backward_forward F Psi Packet C e v y]

def CarrierIdentityLaw
    (C : CarrierActionRaw F Psi Packet) : Prop :=
  (forall p v,
      C.psiEquiv (AdmissibleIso.refl (F.side p)) v = MulEquiv.refl _) /\
  (forall p v j,
      C.packetEquiv (AdmissibleIso.refl (F.side p)) v j = Equiv.refl _)

def CarrierCompositionLaw
    (C : CarrierActionRaw F Psi Packet) : Prop :=
  (forall {p q r}
      (e : AdmissibleIso (F.side p) (F.side q))
      (f : AdmissibleIso (F.side q) (F.side r)) v,
      C.psiEquiv (e.trans f) v =
        (C.psiEquiv e v).trans (C.psiEquiv f v)) /\
  (forall {p q r}
      (e : AdmissibleIso (F.side p) (F.side q))
      (f : AdmissibleIso (F.side q) (F.side r)) v j,
      C.packetEquiv (e.trans f) v j =
        (C.packetEquiv e v j).trans (C.packetEquiv f v j))

def BuildNaturality
    (C : CarrierActionRaw F Psi Packet)
    (build : (p : Obj) -> Output Psi Packet p) : Prop :=
  forall {p q} (e : G.Hom p q),
    transport F Psi Packet C (F.map e) (build p) = build q

theorem buildNaturality_iff
    (C : CarrierActionRaw F Psi Packet)
    (build : (p : Obj) -> Output Psi Packet p) :
    BuildNaturality F Psi Packet C build ↔
      BuildNatural (polyAction F Psi Packet C) build :=
  Iff.rfl

theorem splittingExt
    {Ps : Bad -> Type uPsi} {Pk : Bad -> Label -> Type uPacket}
    [forall v, Monoid (Ps v)]
    {R S : BadPlaceLGPSplittingRaw Bad Label Ps Pk}
    (hsplit : R.split = S.split)
    (hprofile : forall v (x : Ps v) (hR : x ∈ R.split v) (hS : x ∈ S.split v),
        R.profile v ⟨x, hR⟩ = S.profile v ⟨x, hS⟩)
    (hact : forall v (x : Ps v) (hR : x ∈ R.split v) (hS : x ∈ S.split v) y,
        R.act v ⟨x, hR⟩ y = S.act v ⟨x, hS⟩ y) :
    R = S := by
  cases R with
  | mk split profile act =>
    cases S with
    | mk split' profile' act' =>
      simp only at hsplit
      subst hsplit
      simp only [BadPlaceLGPSplittingRaw.mk.injEq, heq_eq_eq, true_and]
      constructor
      · funext v x
        exact hprofile v x.1 x.2 x.2
      · funext v x y
        exact hact v x.1 x.2 x.2 y

theorem forwardPacket_injective
    (C : CarrierActionRaw F Psi Packet)
    {p q : Obj} (e : AdmissibleIso (F.side p) (F.side q)) (v : Bad) :
    Function.Injective (forwardPacket F Psi Packet C e v) := by
  intro x y hxy
  funext j
  exact (C.packetEquiv e v j).injective (congrFun hxy j)

theorem splitEq_of_transportEq
    (C : CarrierActionRaw F Psi Packet)
    {p q : Obj} (e : AdmissibleIso (F.side p) (F.side q))
    {R S : Output Psi Packet p}
    (hRS : transport F Psi Packet C e R = transport F Psi Packet C e S) :
    R.split = S.split := by
  funext v
  have h : transportedSplit F Psi Packet C e R v
         = transportedSplit F Psi Packet C e S v :=
    congrArg (fun T : Output Psi Packet q => T.split v) hRS
  apply SetLike.ext
  intro x
  have hx : ((C.psiEquiv e v) x ∈ transportedSplit F Psi Packet C e R v) ↔
            ((C.psiEquiv e v) x ∈ transportedSplit F Psi Packet C e S v) := by
    rw [h]
  have e1 : ((C.psiEquiv e v) x ∈ transportedSplit F Psi Packet C e R v)
          ↔ x ∈ R.split v := by
    show (C.psiEquiv e v).symm ((C.psiEquiv e v) x) ∈ R.split v ↔ x ∈ R.split v
    rw [MulEquiv.symm_apply_apply]
  have e2 : ((C.psiEquiv e v) x ∈ transportedSplit F Psi Packet C e S v)
          ↔ x ∈ S.split v := by
    show (C.psiEquiv e v).symm ((C.psiEquiv e v) x) ∈ S.split v ↔ x ∈ S.split v
    rw [MulEquiv.symm_apply_apply]
  exact e1.symm.trans (hx.trans e2)

theorem everyPolyTransportInjective
    (C : CarrierActionRaw F Psi Packet) :
    EveryPolyTransportInjective (polyAction F Psi Packet C) := by
  intro p q e R S hRS
  have hRS' : transport F Psi Packet C e R = transport F Psi Packet C e S := hRS
  have hsplit := splitEq_of_transportEq F Psi Packet C e hRS'
  obtain ⟨Rsplit, Rprofile, Ract⟩ := R
  obtain ⟨Ssplit, Sprofile, Sact⟩ := S
  simp only at hsplit
  subst hsplit
  simp only [transport, transportedSplit, BadPlaceLGPSplittingRaw.mk.injEq,
    heq_eq_eq] at hRS'
  obtain ⟨-, hprofile, hact⟩ := hRS'
  refine splittingExt rfl ?_ ?_
  · intro v x hR hS
    apply forwardPacket_injective F Psi Packet C e v
    have hkey :
        sourceSplitElement F Psi Packet C e
            ⟨Rsplit, Sprofile, Sact⟩ v
            (targetSplitElement F Psi Packet C e ⟨Rsplit, Rprofile, Ract⟩ v ⟨x, hR⟩)
          = ⟨x, hS⟩ := by
      apply Subtype.ext
      exact (C.psiEquiv e v).symm_apply_apply x
    have h := congrFun (congrFun hprofile v)
      (targetSplitElement F Psi Packet C e ⟨Rsplit, Rprofile, Ract⟩ v ⟨x, hR⟩)
    simp only [source_target_split, hkey] at h
    exact h
  · intro v x hR hS y
    apply forwardPacket_injective F Psi Packet C e v
    have hkey :
        sourceSplitElement F Psi Packet C e
            ⟨Rsplit, Sprofile, Sact⟩ v
            (targetSplitElement F Psi Packet C e ⟨Rsplit, Rprofile, Ract⟩ v ⟨x, hR⟩)
          = ⟨x, hS⟩ := by
      apply Subtype.ext
      exact (C.psiEquiv e v).symm_apply_apply x
    have h := congrFun (congrFun (congrFun hact v)
      (targetSplitElement F Psi Packet C e ⟨Rsplit, Rprofile, Ract⟩ v ⟨x, hR⟩))
      (forwardPacket F Psi Packet C e v y)
    simp only [source_target_split, hkey, backward_forward] at h
    exact h

theorem action_preservesIdentity
    (C : CarrierActionRaw F Psi Packet)
    (h : CarrierIdentityLaw F Psi Packet C) :
    ActionPreservesIdentity (polyAction F Psi Packet C) := by
  rcases h with ⟨hPsi, hPacket⟩
  intro p R
  have hsplitv : forall v,
      transportedSplit F Psi Packet C (AdmissibleIso.refl (F.side p)) R v
        = R.split v := by
    intro v
    apply SetLike.ext
    intro x
    show (C.psiEquiv (AdmissibleIso.refl (F.side p)) v).symm x ∈ R.split v
      ↔ x ∈ R.split v
    rw [hPsi p v]
    rfl
  refine splittingExt (funext hsplitv) ?_ ?_
  · intro v x hR hS
    show forwardPacket F Psi Packet C (AdmissibleIso.refl (F.side p)) v
        (R.profile v
          (sourceSplitElement F Psi Packet C (AdmissibleIso.refl (F.side p)) R v ⟨x, hR⟩))
      = R.profile v ⟨x, hS⟩
    have hsrc :
        sourceSplitElement F Psi Packet C (AdmissibleIso.refl (F.side p)) R v ⟨x, hR⟩
          = ⟨x, hS⟩ := by
      apply Subtype.ext
      show (C.psiEquiv (AdmissibleIso.refl (F.side p)) v).symm x = x
      rw [hPsi p v]
      rfl
    rw [hsrc]
    funext j
    show C.packetEquiv (AdmissibleIso.refl (F.side p)) v j _ = _
    rw [hPacket p v j]
    rfl
  · intro v x hR hS y
    show forwardPacket F Psi Packet C (AdmissibleIso.refl (F.side p)) v
        (R.act v
          (sourceSplitElement F Psi Packet C (AdmissibleIso.refl (F.side p)) R v ⟨x, hR⟩)
          (backwardPacket F Psi Packet C (AdmissibleIso.refl (F.side p)) v y))
      = R.act v ⟨x, hS⟩ y
    have hsrc :
        sourceSplitElement F Psi Packet C (AdmissibleIso.refl (F.side p)) R v ⟨x, hR⟩
          = ⟨x, hS⟩ := by
      apply Subtype.ext
      show (C.psiEquiv (AdmissibleIso.refl (F.side p)) v).symm x = x
      rw [hPsi p v]
      rfl
    have hback :
        backwardPacket F Psi Packet C (AdmissibleIso.refl (F.side p)) v y = y := by
      funext j
      show (C.packetEquiv (AdmissibleIso.refl (F.side p)) v j).symm _ = _
      rw [hPacket p v j]
      rfl
    rw [hsrc, hback]
    funext j
    show C.packetEquiv (AdmissibleIso.refl (F.side p)) v j _ = _
    rw [hPacket p v j]
    rfl

theorem action_preservesComposition
    (C : CarrierActionRaw F Psi Packet)
    (h : CarrierCompositionLaw F Psi Packet C) :
    ActionPreservesComposition (polyAction F Psi Packet C) := by
  rcases h with ⟨hPsi, hPacket⟩
  intro p q r e f R
  have hfwd : forall (v : Bad) (z : SelectedPacketProduct Label (Packet p) v),
      forwardPacket F Psi Packet C (e.trans f) v z
        = forwardPacket F Psi Packet C f v (forwardPacket F Psi Packet C e v z) := by
    intro v z
    funext j
    show C.packetEquiv (e.trans f) v j (z j) = _
    rw [hPacket e f v j]
    rfl
  have hback : forall (v : Bad) (y : SelectedPacketProduct Label (Packet r) v),
      backwardPacket F Psi Packet C (e.trans f) v y
        = backwardPacket F Psi Packet C e v (backwardPacket F Psi Packet C f v y) := by
    intro v y
    funext j
    show (C.packetEquiv (e.trans f) v j).symm (y j) = _
    rw [hPacket e f v j]
    rfl
  have hsplitv : forall v,
      transportedSplit F Psi Packet C (e.trans f) R v
        = transportedSplit F Psi Packet C f
            (transport F Psi Packet C e R) v := by
    intro v
    apply SetLike.ext
    intro x
    show (C.psiEquiv (e.trans f) v).symm x ∈ R.split v
      ↔ (C.psiEquiv e v).symm ((C.psiEquiv f v).symm x) ∈ R.split v
    rw [hPsi e f v]
    rfl
  refine splittingExt (funext hsplitv) ?_ ?_
  · intro v x hR hS
    show forwardPacket F Psi Packet C (e.trans f) v
        (R.profile v (sourceSplitElement F Psi Packet C (e.trans f) R v ⟨x, hR⟩))
      = forwardPacket F Psi Packet C f v
          (forwardPacket F Psi Packet C e v
            (R.profile v
              (sourceSplitElement F Psi Packet C e R v
                (sourceSplitElement F Psi Packet C f
                  (transport F Psi Packet C e R) v ⟨x, hS⟩))))
    have hsrc :
        sourceSplitElement F Psi Packet C (e.trans f) R v ⟨x, hR⟩
          = sourceSplitElement F Psi Packet C e R v
              (sourceSplitElement F Psi Packet C f
                (transport F Psi Packet C e R) v ⟨x, hS⟩) := by
      apply Subtype.ext
      show (C.psiEquiv (e.trans f) v).symm x
        = (C.psiEquiv e v).symm ((C.psiEquiv f v).symm x)
      rw [hPsi e f v]
      rfl
    rw [hsrc, hfwd]
  · intro v x hR hS y
    show forwardPacket F Psi Packet C (e.trans f) v
        (R.act v (sourceSplitElement F Psi Packet C (e.trans f) R v ⟨x, hR⟩)
          (backwardPacket F Psi Packet C (e.trans f) v y))
      = forwardPacket F Psi Packet C f v
          (forwardPacket F Psi Packet C e v
            (R.act v
              (sourceSplitElement F Psi Packet C e R v
                (sourceSplitElement F Psi Packet C f
                  (transport F Psi Packet C e R) v ⟨x, hS⟩))
              (backwardPacket F Psi Packet C e v
                (backwardPacket F Psi Packet C f v y))))
    have hsrc :
        sourceSplitElement F Psi Packet C (e.trans f) R v ⟨x, hR⟩
          = sourceSplitElement F Psi Packet C e R v
              (sourceSplitElement F Psi Packet C f
                (transport F Psi Packet C e R) v ⟨x, hS⟩) := by
      apply Subtype.ext
      show (C.psiEquiv (e.trans f) v).symm x
        = (C.psiEquiv e v).symm ((C.psiEquiv f v).symm x)
      rw [hPsi e f v]
      rfl
    rw [hsrc, hback, hfwd]

end CitedLV.Theorem311.CompletePolySplittingTransport
end
