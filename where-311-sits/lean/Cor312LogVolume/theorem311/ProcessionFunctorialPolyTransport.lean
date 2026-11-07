import Cor312LogVolume.theorem311.DPrimeStripProcessionCapsule
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Equiv.Defs

namespace CitedLV.Theorem311

universe uObj uHom uOut uBoundary uPacket uSplit uField uStrip

structure RLGPRawComponents
    (Packet : Type uPacket) (Splitting : Type uSplit)
    (FieldCopy : Type uField) where
  packet : Packet
  splitting : Splitting
  fieldCopy : FieldCopy

abbrev RLGPAmbiguityQuotient
    {Obj : Type uObj} (Raw : Obj -> Type uOut)
    (indeterminacy : (p : Obj) -> Setoid (Raw p)) (p : Obj) :=
  Quotient (indeterminacy p)

abbrev FixedLengthDPrimeStripProcessionFamily
    (Obj : Type uObj) (DStrip : Obj -> Type uStrip) (length : Nat)
    (p : Obj) :=
  DPrimeStripProcessionCandidate (DStrip p) length

structure ProcessionIsoRaw (Obj : Type uObj) where
  Hom : Obj -> Obj -> Type uHom
  idHom : (p : Obj) -> Hom p p
  comp : {p q r : Obj} -> Hom p q -> Hom q r -> Hom p r
  inv : {p q : Obj} -> Hom p q -> Hom q p

def ProcessionIdentityLaws
    {Obj : Type uObj} (G : ProcessionIsoRaw Obj) : Prop :=
  (forall {p q} (e : G.Hom p q), G.comp (G.idHom p) e = e) /\
  (forall {p q} (e : G.Hom p q), G.comp e (G.idHom q) = e)

def ProcessionCompositionAssociative
    {Obj : Type uObj} (G : ProcessionIsoRaw Obj) : Prop :=
  forall {p q r s} (e : G.Hom p q) (f : G.Hom q r) (g : G.Hom r s),
    G.comp (G.comp e f) g = G.comp e (G.comp f g)

def ProcessionInverseLaws
    {Obj : Type uObj} (G : ProcessionIsoRaw Obj) : Prop :=
  (forall {p q} (e : G.Hom p q), G.comp e (G.inv e) = G.idHom p) /\
  (forall {p q} (e : G.Hom p q), G.comp (G.inv e) e = G.idHom q)

def ProcessionGroupoidLaws
    {Obj : Type uObj} (G : ProcessionIsoRaw Obj) : Prop :=
  ProcessionIdentityLaws G /\ ProcessionCompositionAssociative G /\
    ProcessionInverseLaws G

structure ProcessionAlgorithmRaw
    {Obj : Type uObj} (G : ProcessionIsoRaw Obj)
    (Output : Obj -> Type uOut) where
  build : (p : Obj) -> Output p
  transport : {p q : Obj} -> G.Hom p q -> Output p -> Output q

def TransportIdentityLaw
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Output : Obj -> Type uOut} (A : ProcessionAlgorithmRaw G Output) : Prop :=
  forall p x, A.transport (G.idHom p) x = x

def TransportCompositionLaw
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Output : Obj -> Type uOut} (A : ProcessionAlgorithmRaw G Output) : Prop :=
  forall {p q r} (e : G.Hom p q) (f : G.Hom q r) (x : Output p),
    A.transport (G.comp e f) x = A.transport f (A.transport e x)

def ConstructionCommutes
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Output : Obj -> Type uOut} (A : ProcessionAlgorithmRaw G Output) : Prop :=
  forall {p q} (e : G.Hom p q), A.transport e (A.build p) = A.build q

def EveryTransportInjective
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Output : Obj -> Type uOut} (A : ProcessionAlgorithmRaw G Output) : Prop :=
  forall {p q} (e : G.Hom p q), Function.Injective (A.transport e)

def EveryOutputNontrivial
    {Obj : Type uObj} (Output : Obj -> Type uOut) : Prop :=
  forall p, exists x y : Output p, x ≠ y

def EveryObjectPairConnected
    {Obj : Type uObj} (G : ProcessionIsoRaw Obj) : Prop :=
  forall p q, Nonempty (G.Hom p q)

def CheckedProcessionFunctorialAlgorithm
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Output : Obj -> Type uOut} (A : ProcessionAlgorithmRaw G Output) : Prop :=
  Nonempty Obj /\ EveryObjectPairConnected G /\
    EveryOutputNontrivial Output /\ ProcessionGroupoidLaws G /\
    TransportIdentityLaw A /\ TransportCompositionLaw A /\
    ConstructionCommutes A /\ EveryTransportInjective A

def transportEquiv
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Output : Obj -> Type uOut} (A : ProcessionAlgorithmRaw G Output)
    (hid : TransportIdentityLaw A) (hcomp : TransportCompositionLaw A)
    (hinv : ProcessionInverseLaws G)
    {p q : Obj} (e : G.Hom p q) : Output p ≃ Output q where
  toFun := A.transport e
  invFun := A.transport (G.inv e)
  left_inv := by
    intro x
    calc
      A.transport (G.inv e) (A.transport e x) =
          A.transport (G.comp e (G.inv e)) x :=
        (hcomp e (G.inv e) x).symm
      _ = A.transport (G.idHom p) x := by rw [hinv.1 e]
      _ = x := hid p x
  right_inv := by
    intro y
    calc
      A.transport e (A.transport (G.inv e) y) =
          A.transport (G.comp (G.inv e) e) y :=
        (hcomp (G.inv e) e y).symm
      _ = A.transport (G.idHom q) y := by rw [hinv.2 e]
      _ = y := hid q y

def transportPolyIsoSet
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Output : Obj -> Type uOut} (A : ProcessionAlgorithmRaw G Output)
    (hid : TransportIdentityLaw A) (hcomp : TransportCompositionLaw A)
    (hinv : ProcessionInverseLaws G) (p q : Obj) :
    Set (Output p ≃ Output q) :=
  Set.range (fun e : G.Hom p q => transportEquiv A hid hcomp hinv e)

theorem transport_poly_iso_set_nonempty
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Output : Obj -> Type uOut} (A : ProcessionAlgorithmRaw G Output)
    (hid : TransportIdentityLaw A) (hcomp : TransportCompositionLaw A)
    (hinv : ProcessionInverseLaws G) {p q : Obj}
    (hconnected : Nonempty (G.Hom p q)) :
    (transportPolyIsoSet A hid hcomp hinv p q).Nonempty := by
  obtain ⟨e⟩ := hconnected
  exact ⟨transportEquiv A hid hcomp hinv e, e, rfl⟩

theorem construction_commutes_through_checked_equiv
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Output : Obj -> Type uOut} (A : ProcessionAlgorithmRaw G Output)
    (hid : TransportIdentityLaw A) (hcomp : TransportCompositionLaw A)
    (hinv : ProcessionInverseLaws G) (hnatural : ConstructionCommutes A)
    {p q : Obj} (e : G.Hom p q) :
    transportEquiv A hid hcomp hinv e (A.build p) = A.build q :=
  hnatural e

structure BoundaryComparisonRaw
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Output : Obj -> Type uOut} (A : ProcessionAlgorithmRaw G Output)
    (Boundary : Obj -> Type uBoundary) where
  project : (p : Obj) -> Output p -> Boundary p
  boundaryTransport : {p q : Obj} -> G.Hom p q -> Boundary p -> Boundary q

def BoundarySquareCommutes
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Output : Obj -> Type uOut} {A : ProcessionAlgorithmRaw G Output}
    {Boundary : Obj -> Type uBoundary}
    (B : BoundaryComparisonRaw A Boundary) : Prop :=
  forall {p q} (e : G.Hom p q) (x : Output p),
    B.boundaryTransport e (B.project p x) =
      B.project q (A.transport e x)

def boolProcessionIsoRaw : ProcessionIsoRaw Bool where
  Hom := fun _ _ => Unit
  idHom := fun _ => ()
  comp := fun _ _ => ()
  inv := fun _ => ()

theorem bool_procession_groupoid_laws :
    ProcessionGroupoidLaws boolProcessionIsoRaw := by
  constructor
  · constructor
    · intro p q e
      cases e
      rfl
    · intro p q e
      cases e
      rfl
  · constructor
    · intro p q r s e f g
      cases e
      cases f
      cases g
      rfl
    · constructor
      · intro p q e
        cases e
        rfl
      · intro p q e
        cases e
        rfl

abbrev BoolProcessionOutput (_ : Bool) := Bool -> Bool

def boolProcessionBuild (p : Bool) : BoolProcessionOutput p :=
  fun j => Bool.xor p j

def boolProcessionTransport
    (p q : Bool) (x : Bool -> Bool) : Bool -> Bool :=
  fun j => Bool.xor (Bool.xor (x j) p) q

def goodProcessionAlgorithm :
    ProcessionAlgorithmRaw boolProcessionIsoRaw BoolProcessionOutput where
  build := boolProcessionBuild
  transport := fun {p q} _ x => boolProcessionTransport p q x

theorem good_procession_transport_identity :
    TransportIdentityLaw goodProcessionAlgorithm := by
  intro p x
  funext j
  cases p <;> simp [goodProcessionAlgorithm, boolProcessionTransport]

theorem good_procession_transport_composition :
    TransportCompositionLaw goodProcessionAlgorithm := by
  intro p q r e f x
  funext j
  cases p <;> cases q <;> cases r <;>
    simp [goodProcessionAlgorithm, boolProcessionTransport]

theorem good_procession_construction_commutes :
    ConstructionCommutes goodProcessionAlgorithm := by
  intro p q e
  funext j
  cases p <;> cases q <;> cases j <;> rfl

theorem good_procession_transport_injective :
    EveryTransportInjective goodProcessionAlgorithm := by
  intro p q e x y h
  funext j
  have hj := congrFun h j
  cases p <;> cases q <;>
    simpa [goodProcessionAlgorithm, boolProcessionTransport] using hj

theorem bool_output_nontrivial :
    EveryOutputNontrivial BoolProcessionOutput := by
  intro p
  refine ⟨(fun _ => false), (fun _ => true), ?_⟩
  intro h
  have hf := congrFun h false
  exact Bool.noConfusion hf

theorem bool_every_pair_connected :
    EveryObjectPairConnected boolProcessionIsoRaw := by
  intro p q
  exact ⟨()⟩

theorem good_procession_algorithm_checked :
    CheckedProcessionFunctorialAlgorithm goodProcessionAlgorithm :=
  ⟨⟨false⟩, bool_every_pair_connected, bool_output_nontrivial,
    bool_procession_groupoid_laws, good_procession_transport_identity,
    good_procession_transport_composition,
    good_procession_construction_commutes,
    good_procession_transport_injective⟩

def goodProcessionBoundary :
    BoundaryComparisonRaw goodProcessionAlgorithm BoolProcessionOutput where
  project := fun _ x => x
  boundaryTransport :=
    fun {p q} _ x => boolProcessionTransport p q x

theorem good_procession_boundary_square :
    BoundarySquareCommutes goodProcessionBoundary := by
  intro p q e x
  rfl

def constantProcessionTransportAlgorithm :
    ProcessionAlgorithmRaw boolProcessionIsoRaw BoolProcessionOutput where
  build := boolProcessionBuild
  transport := fun {_ q} _ _ => boolProcessionBuild q

theorem constant_procession_construction_commutes :
    ConstructionCommutes constantProcessionTransportAlgorithm := by
  intro p q e
  rfl

theorem constant_procession_transport_composition :
    TransportCompositionLaw constantProcessionTransportAlgorithm := by
  intro p q r e f x
  rfl

theorem constant_procession_transport_not_identity :
    ¬ TransportIdentityLaw constantProcessionTransportAlgorithm := by
  intro h
  have hx := congrFun (h false (fun _ => false)) true
  simp [constantProcessionTransportAlgorithm, boolProcessionBuild] at hx

theorem constant_procession_transport_not_injective :
    ¬ EveryTransportInjective constantProcessionTransportAlgorithm := by
  intro h
  have hi := h (p := false) (q := false) ()
  have heq : (fun _ : Bool => false) = (fun _ : Bool => true) := hi rfl
  have hx := congrFun heq false
  exact Bool.noConfusion hx

theorem constant_procession_transport_not_checked :
    ¬ CheckedProcessionFunctorialAlgorithm
        constantProcessionTransportAlgorithm := by
  intro h
  exact constant_procession_transport_not_identity h.2.2.2.2.1

def constantProcessionBoundary :
    BoundaryComparisonRaw goodProcessionAlgorithm BoolProcessionOutput where
  project := fun _ x => x
  boundaryTransport := fun {_ q} _ _ => boolProcessionBuild q

theorem constant_procession_boundary_not_commuting :
    ¬ BoundarySquareCommutes constantProcessionBoundary := by
  intro h
  have hx := congrFun
    (h (p := false) (q := false) () (fun _ => true)) false
  simp [constantProcessionBoundary, boolProcessionBuild,
    goodProcessionAlgorithm, boolProcessionTransport] at hx

abbrev UnitProcessionOutput (_ : Bool) := Unit

def unitProcessionAlgorithm :
    ProcessionAlgorithmRaw boolProcessionIsoRaw UnitProcessionOutput where
  build := fun _ => ()
  transport := fun _ _ => ()

theorem unit_procession_weak_laws :
    TransportIdentityLaw unitProcessionAlgorithm /\
      TransportCompositionLaw unitProcessionAlgorithm /\
      ConstructionCommutes unitProcessionAlgorithm /\
      EveryTransportInjective unitProcessionAlgorithm := by
  repeat' apply And.intro
  · intro p x
    rfl
  · intro p q r e f x
    rfl
  · intro p q e
    rfl
  · intro p q e x y h
    exact Subsingleton.elim _ _

theorem unit_procession_output_not_nontrivial :
    ¬ EveryOutputNontrivial UnitProcessionOutput := by
  intro h
  obtain ⟨x, y, hxy⟩ := h false
  exact hxy (Subsingleton.elim _ _)

theorem unit_procession_not_checked :
    ¬ CheckedProcessionFunctorialAlgorithm unitProcessionAlgorithm := by
  intro h
  exact unit_procession_output_not_nontrivial h.2.2.1

def twoArrowProcessionIsoRaw : ProcessionIsoRaw Unit where
  Hom := fun _ _ => Bool
  idHom := fun _ => false
  comp := Bool.xor
  inv := fun e => e

def labelReindex (e : Bool) (x : Bool -> Bool) : Bool -> Bool :=
  fun j => x (Bool.xor e j)

def twoArrowAlgorithm :
    ProcessionAlgorithmRaw twoArrowProcessionIsoRaw (fun _ => Bool -> Bool) where
  build := fun _ _ => false
  transport := fun e x => labelReindex e x

theorem two_arrow_groupoid_laws :
    ProcessionGroupoidLaws twoArrowProcessionIsoRaw := by
  constructor
  · constructor <;> intro p q e <;> cases e <;> rfl
  · constructor
    · intro p q r s e f g
      cases e <;> cases f <;> cases g <;> rfl
    · constructor <;> intro p q e <;> cases e <;> rfl

theorem two_arrow_transport_identity :
    TransportIdentityLaw twoArrowAlgorithm := by
  intro p x
  cases p
  funext j
  simp [twoArrowAlgorithm, twoArrowProcessionIsoRaw, labelReindex]

theorem two_arrow_transport_composition :
    TransportCompositionLaw twoArrowAlgorithm := by
  intro p q r e f x
  funext j
  cases e <;> cases f <;> cases j <;> rfl

theorem two_arrow_construction_commutes :
    ConstructionCommutes twoArrowAlgorithm := by
  intro p q e
  funext j
  rfl

theorem two_arrow_transport_injective :
    EveryTransportInjective twoArrowAlgorithm := by
  intro p q e x y h
  funext j
  have hj := congrFun h (Bool.xor e j)
  cases e <;> cases j <;>
    simpa [twoArrowAlgorithm, labelReindex] using hj

def twoArrowPolySet : Set ((Bool -> Bool) ≃ (Bool -> Bool)) :=
  transportPolyIsoSet twoArrowAlgorithm two_arrow_transport_identity
    two_arrow_transport_composition two_arrow_groupoid_laws.2.2 () ()

theorem two_arrow_poly_set_contains_distinct_equivalences :
    ∃ e f : (Bool -> Bool) ≃ (Bool -> Bool),
      e ∈ twoArrowPolySet /\ f ∈ twoArrowPolySet /\ e ≠ f := by
  let e := transportEquiv twoArrowAlgorithm two_arrow_transport_identity
    two_arrow_transport_composition two_arrow_groupoid_laws.2.2
      (p := ()) (q := ()) false
  let f := transportEquiv twoArrowAlgorithm two_arrow_transport_identity
    two_arrow_transport_composition two_arrow_groupoid_laws.2.2
      (p := ()) (q := ()) true
  refine ⟨e, f, ⟨false, rfl⟩, ⟨true, rfl⟩, ?_⟩
  intro hef
  have hfun := congrFun (congrArg Equiv.toFun hef) (fun j => j)
  have hpoint := congrFun hfun false
  exact Bool.noConfusion hpoint

end CitedLV.Theorem311
