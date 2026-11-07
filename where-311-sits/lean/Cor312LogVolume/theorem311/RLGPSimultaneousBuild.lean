import Cor312LogVolume.theorem311.ProcessionFunctorialPolyTransport
import Cor312LogVolume.theorem311.BadPlaceLGPSplittingAction
import Cor312LogVolume.theorem311.LabeledGlobalNumberFieldInclusion

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.RLGPSimultaneousBuild

theorem rlgpExt {P : Type*} {S : Type*} {F : Type*}
    {a b : RLGPRawComponents P S F}
    (hp : a.packet = b.packet) (hs : a.splitting = b.splitting)
    (hf : a.fieldCopy = b.fieldCopy) : a = b := by
  cases a
  cases b
  simp_all

universe uObj uHom uPacket uSplit uField

structure BuildRaw
    (Obj : Type uObj)
    (Packet : Obj -> Type uPacket)
    (Splitting : Obj -> Type uSplit)
    (FieldCopy : Obj -> Type uField) where
  packet : (p : Obj) -> Packet p
  splitting : (p : Obj) -> Splitting p
  fieldCopy : (p : Obj) -> FieldCopy p

def BuildRaw.build
    {Obj : Type uObj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (A : BuildRaw Obj Packet Splitting FieldCopy)
    (p : Obj) :
    RLGPRawComponents (Packet p) (Splitting p) (FieldCopy p) where
  packet := A.packet p
  splitting := A.splitting p
  fieldCopy := A.fieldCopy p

@[simp] theorem BuildRaw.build_packet
    {Obj : Type uObj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (A : BuildRaw Obj Packet Splitting FieldCopy) (p : Obj) :
    (A.build p).packet = A.packet p := rfl

@[simp] theorem BuildRaw.build_splitting
    {Obj : Type uObj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (A : BuildRaw Obj Packet Splitting FieldCopy) (p : Obj) :
    (A.build p).splitting = A.splitting p := rfl

@[simp] theorem BuildRaw.build_fieldCopy
    {Obj : Type uObj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (A : BuildRaw Obj Packet Splitting FieldCopy) (p : Obj) :
    (A.build p).fieldCopy = A.fieldCopy p := rfl

structure TransportRaw
    {Obj : Type uObj}
    (G : ProcessionIsoRaw Obj)
    (Packet : Obj -> Type uPacket)
    (Splitting : Obj -> Type uSplit)
    (FieldCopy : Obj -> Type uField) where
  packet :
    {p q : Obj} -> G.Hom p q -> Packet p -> Packet q
  splitting :
    {p q : Obj} -> G.Hom p q -> Splitting p -> Splitting q
  fieldCopy :
    {p q : Obj} -> G.Hom p q -> FieldCopy p -> FieldCopy q

def TransportRaw.map
    {Obj : Type uObj}
    {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (T : TransportRaw G Packet Splitting FieldCopy)
    {p q : Obj} (e : G.Hom p q) :
    RLGPRawComponents (Packet p) (Splitting p) (FieldCopy p) ->
      RLGPRawComponents (Packet q) (Splitting q) (FieldCopy q)
  | x =>
    { packet := T.packet e x.packet
      splitting := T.splitting e x.splitting
      fieldCopy := T.fieldCopy e x.fieldCopy }

def toProcessionAlgorithmRaw
    {Obj : Type uObj}
    (G : ProcessionIsoRaw Obj)
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (A : BuildRaw Obj Packet Splitting FieldCopy)
    (T : TransportRaw G Packet Splitting FieldCopy) :
    ProcessionAlgorithmRaw G
      (fun p => RLGPRawComponents (Packet p) (Splitting p) (FieldCopy p)) where
  build := A.build
  transport := T.map

def PacketTransportIdentityLaw
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (T : TransportRaw G Packet Splitting FieldCopy) : Prop :=
  ∀ p x, T.packet (G.idHom p) x = x

def SplittingTransportIdentityLaw
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (T : TransportRaw G Packet Splitting FieldCopy) : Prop :=
  ∀ p x, T.splitting (G.idHom p) x = x

def FieldTransportIdentityLaw
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (T : TransportRaw G Packet Splitting FieldCopy) : Prop :=
  ∀ p x, T.fieldCopy (G.idHom p) x = x

theorem transportIdentity_of_components
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (A : BuildRaw Obj Packet Splitting FieldCopy)
    (T : TransportRaw G Packet Splitting FieldCopy)
    (hp : PacketTransportIdentityLaw T)
    (hs : SplittingTransportIdentityLaw T)
    (hf : FieldTransportIdentityLaw T) :
    TransportIdentityLaw (toProcessionAlgorithmRaw G A T) := by
  intro p x
  cases x with
  | mk packet splitting fieldCopy =>
      simp [toProcessionAlgorithmRaw, TransportRaw.map, hp p packet,
        hs p splitting, hf p fieldCopy]

def PacketTransportCompositionLaw
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (T : TransportRaw G Packet Splitting FieldCopy) : Prop :=
  ∀ {p q r} (e : G.Hom p q) (f : G.Hom q r) x,
    T.packet (G.comp e f) x = T.packet f (T.packet e x)

def SplittingTransportCompositionLaw
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (T : TransportRaw G Packet Splitting FieldCopy) : Prop :=
  ∀ {p q r} (e : G.Hom p q) (f : G.Hom q r) x,
    T.splitting (G.comp e f) x = T.splitting f (T.splitting e x)

def FieldTransportCompositionLaw
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (T : TransportRaw G Packet Splitting FieldCopy) : Prop :=
  ∀ {p q r} (e : G.Hom p q) (f : G.Hom q r) x,
    T.fieldCopy (G.comp e f) x = T.fieldCopy f (T.fieldCopy e x)

theorem transportComposition_of_components
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (A : BuildRaw Obj Packet Splitting FieldCopy)
    (T : TransportRaw G Packet Splitting FieldCopy)
    (hp : PacketTransportCompositionLaw T)
    (hs : SplittingTransportCompositionLaw T)
    (hf : FieldTransportCompositionLaw T) :
    TransportCompositionLaw (toProcessionAlgorithmRaw G A T) := by
  intro p q r e f x
  cases x with
  | mk packet splitting fieldCopy =>
      simp [toProcessionAlgorithmRaw, TransportRaw.map,
        hp e f packet, hs e f splitting, hf e f fieldCopy]

def PacketConstructionCommutes
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (A : BuildRaw Obj Packet Splitting FieldCopy)
    (T : TransportRaw G Packet Splitting FieldCopy) : Prop :=
  ∀ {p q} (e : G.Hom p q), T.packet e (A.packet p) = A.packet q

def SplittingConstructionCommutes
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (A : BuildRaw Obj Packet Splitting FieldCopy)
    (T : TransportRaw G Packet Splitting FieldCopy) : Prop :=
  ∀ {p q} (e : G.Hom p q), T.splitting e (A.splitting p) = A.splitting q

def FieldConstructionCommutes
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (A : BuildRaw Obj Packet Splitting FieldCopy)
    (T : TransportRaw G Packet Splitting FieldCopy) : Prop :=
  ∀ {p q} (e : G.Hom p q), T.fieldCopy e (A.fieldCopy p) = A.fieldCopy q

theorem constructionCommutes_of_components
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (A : BuildRaw Obj Packet Splitting FieldCopy)
    (T : TransportRaw G Packet Splitting FieldCopy)
    (hp : PacketConstructionCommutes A T)
    (hs : SplittingConstructionCommutes A T)
    (hf : FieldConstructionCommutes A T) :
    ConstructionCommutes (toProcessionAlgorithmRaw G A T) := by
  intro p q e
  apply rlgpExt
  · exact hp e
  · exact hs e
  · exact hf e

def BuildRaw.ofAlgorithms
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (AP : ProcessionAlgorithmRaw G Packet)
    (AS : ProcessionAlgorithmRaw G Splitting)
    (AF : ProcessionAlgorithmRaw G FieldCopy) :
    BuildRaw Obj Packet Splitting FieldCopy where
  packet := AP.build
  splitting := AS.build
  fieldCopy := AF.build

def TransportRaw.ofAlgorithms
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (AP : ProcessionAlgorithmRaw G Packet)
    (AS : ProcessionAlgorithmRaw G Splitting)
    (AF : ProcessionAlgorithmRaw G FieldCopy) :
    TransportRaw G Packet Splitting FieldCopy where
  packet := AP.transport
  splitting := AS.transport
  fieldCopy := AF.transport

def algorithmOfComponents
    {Obj : Type uObj} (G : ProcessionIsoRaw Obj)
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (AP : ProcessionAlgorithmRaw G Packet)
    (AS : ProcessionAlgorithmRaw G Splitting)
    (AF : ProcessionAlgorithmRaw G FieldCopy) :
    ProcessionAlgorithmRaw G
      (fun p => RLGPRawComponents (Packet p) (Splitting p) (FieldCopy p)) :=
  toProcessionAlgorithmRaw G
    (BuildRaw.ofAlgorithms AP AS AF)
    (TransportRaw.ofAlgorithms AP AS AF)

theorem algorithmOfComponents_identity
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (AP : ProcessionAlgorithmRaw G Packet)
    (AS : ProcessionAlgorithmRaw G Splitting)
    (AF : ProcessionAlgorithmRaw G FieldCopy)
    (hP : TransportIdentityLaw AP)
    (hS : TransportIdentityLaw AS)
    (hF : TransportIdentityLaw AF) :
    TransportIdentityLaw (algorithmOfComponents G AP AS AF) := by
  apply transportIdentity_of_components
  · intro p x
    exact hP p x
  · intro p x
    exact hS p x
  · intro p x
    exact hF p x

theorem algorithmOfComponents_composition
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (AP : ProcessionAlgorithmRaw G Packet)
    (AS : ProcessionAlgorithmRaw G Splitting)
    (AF : ProcessionAlgorithmRaw G FieldCopy)
    (hP : TransportCompositionLaw AP)
    (hS : TransportCompositionLaw AS)
    (hF : TransportCompositionLaw AF) :
    TransportCompositionLaw (algorithmOfComponents G AP AS AF) := by
  apply transportComposition_of_components
  · intro p q r e f x
    exact hP e f x
  · intro p q r e f x
    exact hS e f x
  · intro p q r e f x
    exact hF e f x

theorem algorithmOfComponents_construction
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (AP : ProcessionAlgorithmRaw G Packet)
    (AS : ProcessionAlgorithmRaw G Splitting)
    (AF : ProcessionAlgorithmRaw G FieldCopy)
    (hP : ConstructionCommutes AP)
    (hS : ConstructionCommutes AS)
    (hF : ConstructionCommutes AF) :
    ConstructionCommutes (algorithmOfComponents G AP AS AF) := by
  apply constructionCommutes_of_components
  · intro p q e
    exact hP e
  · intro p q e
    exact hS e
  · intro p q e
    exact hF e

def PacketTransportInjective
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (T : TransportRaw G Packet Splitting FieldCopy) : Prop :=
  ∀ {p q} (e : G.Hom p q), Function.Injective (T.packet e)

def SplittingTransportInjective
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (T : TransportRaw G Packet Splitting FieldCopy) : Prop :=
  ∀ {p q} (e : G.Hom p q), Function.Injective (T.splitting e)

def FieldTransportInjective
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (T : TransportRaw G Packet Splitting FieldCopy) : Prop :=
  ∀ {p q} (e : G.Hom p q), Function.Injective (T.fieldCopy e)

theorem everyTransportInjective_of_components
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (A : BuildRaw Obj Packet Splitting FieldCopy)
    (T : TransportRaw G Packet Splitting FieldCopy)
    (hP : PacketTransportInjective T)
    (hS : SplittingTransportInjective T)
    (hF : FieldTransportInjective T) :
    EveryTransportInjective (toProcessionAlgorithmRaw G A T) := by
  intro p q e x y hxy
  apply rlgpExt
  · apply hP e
    exact congrArg (fun z => z.packet) hxy
  · apply hS e
    exact congrArg (fun z => z.splitting) hxy
  · apply hF e
    exact congrArg (fun z => z.fieldCopy) hxy

def EveryPacketFiberNontrivial
    {Obj : Type uObj} (Packet : Obj -> Type uPacket) : Prop :=
  ∀ p, ∃ x y : Packet p, x ≠ y

theorem everyOutputNontrivial_of_packet
    {Obj : Type uObj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (A : BuildRaw Obj Packet Splitting FieldCopy)
    (hP : EveryPacketFiberNontrivial Packet) :
    EveryOutputNontrivial
      (fun p => RLGPRawComponents (Packet p) (Splitting p) (FieldCopy p)) := by
  intro p
  obtain ⟨x, y, hxy⟩ := hP p
  refine
    ⟨{ packet := x, splitting := A.splitting p, fieldCopy := A.fieldCopy p },
     { packet := y, splitting := A.splitting p, fieldCopy := A.fieldCopy p }, ?_⟩
  intro h
  exact hxy (congrArg (fun z => z.packet) h)

theorem checked_algorithmOfComponents
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Packet : Obj -> Type uPacket}
    {Splitting : Obj -> Type uSplit}
    {FieldCopy : Obj -> Type uField}
    (AP : ProcessionAlgorithmRaw G Packet)
    (AS : ProcessionAlgorithmRaw G Splitting)
    (AF : ProcessionAlgorithmRaw G FieldCopy)
    (hObj : Nonempty Obj)
    (hConn : EveryObjectPairConnected G)
    (hPacketNontrivial : EveryPacketFiberNontrivial Packet)
    (hGroupoid : ProcessionGroupoidLaws G)
    (hPid : TransportIdentityLaw AP)
    (hSid : TransportIdentityLaw AS)
    (hFid : TransportIdentityLaw AF)
    (hPcomp : TransportCompositionLaw AP)
    (hScomp : TransportCompositionLaw AS)
    (hFcomp : TransportCompositionLaw AF)
    (hPbuild : ConstructionCommutes AP)
    (hSbuild : ConstructionCommutes AS)
    (hFbuild : ConstructionCommutes AF)
    (hPinj : EveryTransportInjective AP)
    (hSinj : EveryTransportInjective AS)
    (hFinj : EveryTransportInjective AF) :
    CheckedProcessionFunctorialAlgorithm
      (algorithmOfComponents G AP AS AF) := by
  let A := BuildRaw.ofAlgorithms AP AS AF
  let T := TransportRaw.ofAlgorithms AP AS AF
  refine ⟨hObj, hConn, ?_, hGroupoid, ?_, ?_, ?_, ?_⟩
  · exact everyOutputNontrivial_of_packet A hPacketNontrivial
  · exact algorithmOfComponents_identity AP AS AF hPid hSid hFid
  · exact algorithmOfComponents_composition AP AS AF hPcomp hScomp hFcomp
  · exact algorithmOfComponents_construction AP AS AF hPbuild hSbuild hFbuild
  · apply everyTransportInjective_of_components A T
    · intro p q e
      exact hPinj e
    · intro p q e
      exact hSinj e
    · intro p q e
      exact hFinj e

end CitedLV.Theorem311.RLGPSimultaneousBuild
end
