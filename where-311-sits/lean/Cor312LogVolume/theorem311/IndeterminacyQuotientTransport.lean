import Cor312LogVolume.theorem311.ProcessionFunctorialPolyTransport
import Mathlib.Logic.Relation

namespace CitedLV.Theorem311

universe uObj uHom uRaw uObs

structure AmbiguityGenerators
    {Obj : Type uObj} (Raw : Obj -> Type uRaw) where
  ind1Step : (p : Obj) -> Raw p -> Raw p -> Prop
  ind2Step : (p : Obj) -> Raw p -> Raw p -> Prop

def ambiguityStep
    {Obj : Type uObj} {Raw : Obj -> Type uRaw}
    (I : AmbiguityGenerators Raw) (p : Obj) : Raw p -> Raw p -> Prop :=
  fun x y => I.ind1Step p x y \/ I.ind2Step p x y

abbrev ambiguitySetoid
    {Obj : Type uObj} {Raw : Obj -> Type uRaw}
    (I : AmbiguityGenerators Raw) (p : Obj) : Setoid (Raw p) :=
  Relation.EqvGen.setoid (ambiguityStep I p)

abbrev RLGPAmbiguityQuotientV2
    {Obj : Type uObj} {Raw : Obj -> Type uRaw}
    (I : AmbiguityGenerators Raw) (p : Obj) :=
  Quotient (ambiguitySetoid I p)

theorem ind1_step_enters_ambiguity
    {Obj : Type uObj} {Raw : Obj -> Type uRaw}
    (I : AmbiguityGenerators Raw) {p : Obj} {x y : Raw p}
    (h : I.ind1Step p x y) :
    Relation.EqvGen (ambiguityStep I p) x y :=
  Relation.EqvGen.rel _ _ (Or.inl h)

theorem ind2_step_enters_ambiguity
    {Obj : Type uObj} {Raw : Obj -> Type uRaw}
    (I : AmbiguityGenerators Raw) {p : Obj} {x y : Raw p}
    (h : I.ind2Step p x y) :
    Relation.EqvGen (ambiguityStep I p) x y :=
  Relation.EqvGen.rel _ _ (Or.inr h)

def RawTransportRespectsGenerators
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} (I : AmbiguityGenerators Raw)
    (A : ProcessionAlgorithmRaw G Raw) : Prop :=
  forall {p q} (e : G.Hom p q) {x y : Raw p},
    ambiguityStep I p x y ->
      Relation.EqvGen (ambiguityStep I q)
        (A.transport e x) (A.transport e y)

theorem raw_transport_respects_ambiguity
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} (I : AmbiguityGenerators Raw)
    (A : ProcessionAlgorithmRaw G Raw)
    (hrespect : RawTransportRespectsGenerators I A)
    {p q : Obj} (e : G.Hom p q) {x y : Raw p}
    (hxy : Relation.EqvGen (ambiguityStep I p) x y) :
    Relation.EqvGen (ambiguityStep I q)
      (A.transport e x) (A.transport e y) := by
  induction hxy with
  | rel x y h => exact hrespect e h
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ hxy hyz =>
      exact Relation.EqvGen.trans _ _ _ hxy hyz

def RawTransportIdentityModulo
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} (I : AmbiguityGenerators Raw)
    (A : ProcessionAlgorithmRaw G Raw) : Prop :=
  forall p (x : Raw p),
    Relation.EqvGen (ambiguityStep I p)
      (A.transport (G.idHom p) x) x

def RawTransportCompositionModulo
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} (I : AmbiguityGenerators Raw)
    (A : ProcessionAlgorithmRaw G Raw) : Prop :=
  forall {p q r} (e : G.Hom p q) (f : G.Hom q r) (x : Raw p),
    Relation.EqvGen (ambiguityStep I r)
      (A.transport (G.comp e f) x)
      (A.transport f (A.transport e x))

def RawConstructionCommutesModulo
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} (I : AmbiguityGenerators Raw)
    (A : ProcessionAlgorithmRaw G Raw) : Prop :=
  forall {p q} (e : G.Hom p q),
    Relation.EqvGen (ambiguityStep I q)
      (A.transport e (A.build p)) (A.build q)

def quotientProcessionAlgorithm
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} (I : AmbiguityGenerators Raw)
    (A : ProcessionAlgorithmRaw G Raw)
    (hrespect : RawTransportRespectsGenerators I A) :
    ProcessionAlgorithmRaw G (RLGPAmbiguityQuotientV2 I) where
  build := fun p => Quotient.mk _ (A.build p)
  transport := fun e =>
    Quotient.map (A.transport e)
      (fun {_ _} h => raw_transport_respects_ambiguity I A hrespect e h)

theorem quotient_transport_identity
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} (I : AmbiguityGenerators Raw)
    (A : ProcessionAlgorithmRaw G Raw)
    (hrespect : RawTransportRespectsGenerators I A)
    (hid : RawTransportIdentityModulo I A) :
    TransportIdentityLaw (quotientProcessionAlgorithm I A hrespect) := by
  intro p x
  refine Quotient.inductionOn x ?_
  intro a
  exact Quotient.sound (hid p a)

theorem quotient_transport_composition
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} (I : AmbiguityGenerators Raw)
    (A : ProcessionAlgorithmRaw G Raw)
    (hrespect : RawTransportRespectsGenerators I A)
    (hcomp : RawTransportCompositionModulo I A) :
    TransportCompositionLaw (quotientProcessionAlgorithm I A hrespect) := by
  intro p q r e f x
  refine Quotient.inductionOn x ?_
  intro a
  exact Quotient.sound (hcomp e f a)

theorem quotient_construction_commutes
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} (I : AmbiguityGenerators Raw)
    (A : ProcessionAlgorithmRaw G Raw)
    (hrespect : RawTransportRespectsGenerators I A)
    (hbuild : RawConstructionCommutesModulo I A) :
    ConstructionCommutes (quotientProcessionAlgorithm I A hrespect) := by
  intro p q e
  exact Quotient.sound (hbuild e)

theorem strict_identity_implies_modulo
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} (I : AmbiguityGenerators Raw)
    (A : ProcessionAlgorithmRaw G Raw) (h : TransportIdentityLaw A) :
    RawTransportIdentityModulo I A := by
  intro p x
  rw [h p x]
  exact Relation.EqvGen.refl _

theorem strict_composition_implies_modulo
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} (I : AmbiguityGenerators Raw)
    (A : ProcessionAlgorithmRaw G Raw) (h : TransportCompositionLaw A) :
    RawTransportCompositionModulo I A := by
  intro p q r e f x
  rw [h e f x]
  exact Relation.EqvGen.refl _

theorem strict_construction_implies_modulo
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} (I : AmbiguityGenerators Raw)
    (A : ProcessionAlgorithmRaw G Raw) (h : ConstructionCommutes A) :
    RawConstructionCommutesModulo I A := by
  intro p q e
  rw [h e]
  exact Relation.EqvGen.refl _

def descendedTransportEquiv
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} (I : AmbiguityGenerators Raw)
    (A : ProcessionAlgorithmRaw G Raw)
    (hrespect : RawTransportRespectsGenerators I A)
    (hid : RawTransportIdentityModulo I A)
    (hcomp : RawTransportCompositionModulo I A)
    (hinv : ProcessionInverseLaws G) {p q : Obj} (e : G.Hom p q) :
    RLGPAmbiguityQuotientV2 I p ≃ RLGPAmbiguityQuotientV2 I q :=
  transportEquiv (quotientProcessionAlgorithm I A hrespect)
    (quotient_transport_identity I A hrespect hid)
    (quotient_transport_composition I A hrespect hcomp) hinv e

def descendedTransportPolyIsoSet
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} (I : AmbiguityGenerators Raw)
    (A : ProcessionAlgorithmRaw G Raw)
    (hrespect : RawTransportRespectsGenerators I A)
    (hid : RawTransportIdentityModulo I A)
    (hcomp : RawTransportCompositionModulo I A)
    (hinv : ProcessionInverseLaws G) (p q : Obj) :
    Set (RLGPAmbiguityQuotientV2 I p ≃ RLGPAmbiguityQuotientV2 I q) :=
  Set.range (fun e : G.Hom p q =>
    descendedTransportEquiv I A hrespect hid hcomp hinv e)

def HasSeparatedQuotientClasses
    {Obj : Type uObj} {Raw : Obj -> Type uRaw}
    (I : AmbiguityGenerators Raw) : Prop :=
  ∃ p, ∃ x y : Raw p,
    ¬ Relation.EqvGen (ambiguityStep I p) x y

def HasNontrivialInd1Step
    {Obj : Type uObj} {Raw : Obj -> Type uRaw}
    (I : AmbiguityGenerators Raw) : Prop :=
  ∃ p, ∃ x y : Raw p, x ≠ y /\ I.ind1Step p x y

def HasNontrivialInd2Step
    {Obj : Type uObj} {Raw : Obj -> Type uRaw}
    (I : AmbiguityGenerators Raw) : Prop :=
  ∃ p, ∃ x y : Raw p, x ≠ y /\ I.ind2Step p x y

def NondegenerateAmbiguityCheck
    {Obj : Type uObj} {Raw : Obj -> Type uRaw}
    (I : AmbiguityGenerators Raw) : Prop :=
  HasNontrivialInd1Step I /\ HasNontrivialInd2Step I /\
    HasSeparatedQuotientClasses I

structure AmbiguityObservable
    {Obj : Type uObj} {Raw : Obj -> Type uRaw}
    (I : AmbiguityGenerators Raw) (Obs : Obj -> Type uObs) where
  observe : (p : Obj) -> Raw p -> Obs p
  ind1Invariant : forall p {x y},
    I.ind1Step p x y -> observe p x = observe p y
  ind2Invariant : forall p {x y},
    I.ind2Step p x y -> observe p x = observe p y

theorem observable_constant_on_ambiguity
    {Obj : Type uObj} {Raw : Obj -> Type uRaw}
    {I : AmbiguityGenerators Raw} {Obs : Obj -> Type uObs}
    (O : AmbiguityObservable I Obs) {p : Obj} {x y : Raw p}
    (hxy : Relation.EqvGen (ambiguityStep I p) x y) :
    O.observe p x = O.observe p y := by
  induction hxy with
  | rel x y h =>
      exact h.elim (O.ind1Invariant p) (O.ind2Invariant p)
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ hxy hyz => exact hxy.trans hyz

def quotientObservable
    {Obj : Type uObj} {Raw : Obj -> Type uRaw}
    {I : AmbiguityGenerators Raw} {Obs : Obj -> Type uObs}
    (O : AmbiguityObservable I Obs) (p : Obj) :
    RLGPAmbiguityQuotientV2 I p -> Obs p :=
  Quotient.lift (O.observe p) (fun _ _ h => observable_constant_on_ambiguity O h)

theorem quotient_observable_on_representative
    {Obj : Type uObj} {Raw : Obj -> Type uRaw}
    {I : AmbiguityGenerators Raw} {Obs : Obj -> Type uObs}
    (O : AmbiguityObservable I Obs) (p : Obj) (x : Raw p) :
    quotientObservable O p (Quotient.mk _ x) = O.observe p x :=
  rfl

def RawObservableSquareCommutes
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} {I : AmbiguityGenerators Raw}
    {Obs : Obj -> Type uObs} (A : ProcessionAlgorithmRaw G Raw)
    (O : AmbiguityObservable I Obs)
    (obsTransport : {p q : Obj} -> G.Hom p q -> Obs p -> Obs q) : Prop :=
  forall {p q} (e : G.Hom p q) (x : Raw p),
    obsTransport e (O.observe p x) = O.observe q (A.transport e x)

theorem quotient_observable_square_commutes
    {Obj : Type uObj} {G : ProcessionIsoRaw Obj}
    {Raw : Obj -> Type uRaw} {I : AmbiguityGenerators Raw}
    {Obs : Obj -> Type uObs} (A : ProcessionAlgorithmRaw G Raw)
    (hrespect : RawTransportRespectsGenerators I A)
    (O : AmbiguityObservable I Obs)
    (obsTransport : {p q : Obj} -> G.Hom p q -> Obs p -> Obs q)
    (hsquare : RawObservableSquareCommutes A O obsTransport)
    {p q : Obj} (e : G.Hom p q) (x : RLGPAmbiguityQuotientV2 I p) :
    obsTransport e (quotientObservable O p x) =
      quotientObservable O q
        ((quotientProcessionAlgorithm I A hrespect).transport e x) := by
  refine Quotient.inductionOn x ?_
  intro a
  exact hsquare e a

abbrev TripleBitRaw (_ : Bool) := Bool × Bool × Bool

def tripleBitAmbiguity : AmbiguityGenerators TripleBitRaw where
  ind1Step := fun _ x y => x.2 = y.2
  ind2Step := fun _ x y => x.1 = y.1 /\ x.2.2 = y.2.2

def tripleBitTransport
    (p q : Bool) (x : Bool × Bool × Bool) : Bool × Bool × Bool :=
  (x.1, x.2.1, Bool.xor (Bool.xor x.2.2 p) q)

def tripleBitBuild (p : Bool) : Bool × Bool × Bool :=
  (false, false, p)

def tripleBitAlgorithm :
    ProcessionAlgorithmRaw boolProcessionIsoRaw TripleBitRaw where
  build := tripleBitBuild
  transport := fun {p q} _ x => tripleBitTransport p q x

theorem triple_bit_transport_respects_generators :
    RawTransportRespectsGenerators tripleBitAmbiguity tripleBitAlgorithm := by
  intro p q e x y h
  apply Relation.EqvGen.rel
  rcases h with h1 | h2
  · left
    change x.2 = y.2 at h1
    change
      (x.2.1, Bool.xor (Bool.xor x.2.2 p) q) =
        (y.2.1, Bool.xor (Bool.xor y.2.2 p) q)
    simp [h1]
  · right
    change x.1 = y.1 /\ x.2.2 = y.2.2 at h2
    change x.1 = y.1 /\
      Bool.xor (Bool.xor x.2.2 p) q =
        Bool.xor (Bool.xor y.2.2 p) q
    constructor
    · exact h2.1
    · exact congrArg (fun c => Bool.xor (Bool.xor c p) q) h2.2

theorem triple_bit_strict_identity :
    TransportIdentityLaw tripleBitAlgorithm := by
  intro p x
  rcases x with ⟨a, b, c⟩
  cases p <;> cases c <;> rfl

theorem triple_bit_strict_composition :
    TransportCompositionLaw tripleBitAlgorithm := by
  intro p q r e f x
  cases p <;> cases q <;> cases r <;>
    simp [tripleBitAlgorithm, tripleBitTransport]

theorem triple_bit_strict_construction :
    ConstructionCommutes tripleBitAlgorithm := by
  intro p q e
  cases p <;> cases q <;> rfl

theorem triple_ambiguity_preserves_third
    {p : Bool} {x y : TripleBitRaw p}
    (h : Relation.EqvGen (ambiguityStep tripleBitAmbiguity p) x y) :
    x.2.2 = y.2.2 := by
  induction h with
  | rel x y h =>
      rcases h with h1 | h2
      · exact congrArg Prod.snd h1
      · exact h2.2
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ hxy hyz => exact hxy.trans hyz

theorem triple_bit_nontrivial_ind1 :
    HasNontrivialInd1Step tripleBitAmbiguity := by
  refine ⟨false, (false, false, false), (true, false, false), ?_, rfl⟩
  intro h
  have hf := congrArg Prod.fst h
  exact Bool.noConfusion hf

theorem triple_bit_nontrivial_ind2 :
    HasNontrivialInd2Step tripleBitAmbiguity := by
  refine ⟨false, (false, false, false), (false, true, false), ?_, rfl, rfl⟩
  intro h
  have hf := congrArg (fun z => z.2.1) h
  exact Bool.noConfusion hf

theorem triple_bit_separated_classes :
    HasSeparatedQuotientClasses tripleBitAmbiguity := by
  refine ⟨false, (false, false, false), (false, false, true), ?_⟩
  intro h
  exact Bool.noConfusion (triple_ambiguity_preserves_third h)

theorem triple_bit_ambiguity_checked :
    NondegenerateAmbiguityCheck tripleBitAmbiguity :=
  ⟨triple_bit_nontrivial_ind1, triple_bit_nontrivial_ind2,
    triple_bit_separated_classes⟩

abbrev TripleBitObs (_ : Bool) := Bool

def tripleBitObservable :
    AmbiguityObservable tripleBitAmbiguity TripleBitObs where
  observe := fun _ x => x.2.2
  ind1Invariant := fun _ _ _ h => congrArg Prod.snd h
  ind2Invariant := fun _ _ _ h => h.2

def tripleBitObsTransport
    {p q : Bool} (_ : boolProcessionIsoRaw.Hom p q) (c : Bool) : Bool :=
  Bool.xor (Bool.xor c p) q

theorem triple_bit_observable_square :
    RawObservableSquareCommutes tripleBitAlgorithm tripleBitObservable
      tripleBitObsTransport := by
  intro p q e x
  rfl

theorem triple_bit_quotient_classes_are_distinct :
    (Quotient.mk (ambiguitySetoid tripleBitAmbiguity false)
        (false, false, false) : RLGPAmbiguityQuotientV2
          tripleBitAmbiguity false) ≠
      Quotient.mk (ambiguitySetoid tripleBitAmbiguity false)
        (false, false, true) := by
  intro h
  exact Bool.noConfusion
    (triple_ambiguity_preserves_third (Quotient.exact h))

theorem triple_bit_quotient_output_nontrivial :
    EveryOutputNontrivial (RLGPAmbiguityQuotientV2 tripleBitAmbiguity) := by
  intro p
  cases p
  · exact ⟨Quotient.mk _ (false, false, false),
      Quotient.mk _ (false, false, true),
      triple_bit_quotient_classes_are_distinct⟩
  · refine ⟨Quotient.mk _ (false, false, false),
      Quotient.mk _ (false, false, true), ?_⟩
    intro h
    exact Bool.noConfusion
      (triple_ambiguity_preserves_third (Quotient.exact h))

theorem triple_bit_quotient_algorithm_checked :
    CheckedProcessionFunctorialAlgorithm
      (quotientProcessionAlgorithm tripleBitAmbiguity tripleBitAlgorithm
        triple_bit_transport_respects_generators) := by
  let QA := quotientProcessionAlgorithm tripleBitAmbiguity tripleBitAlgorithm
    triple_bit_transport_respects_generators
  have hid : TransportIdentityLaw QA :=
    quotient_transport_identity tripleBitAmbiguity tripleBitAlgorithm
      triple_bit_transport_respects_generators
      (strict_identity_implies_modulo tripleBitAmbiguity tripleBitAlgorithm
        triple_bit_strict_identity)
  have hcomp : TransportCompositionLaw QA :=
    quotient_transport_composition tripleBitAmbiguity tripleBitAlgorithm
      triple_bit_transport_respects_generators
      (strict_composition_implies_modulo tripleBitAmbiguity tripleBitAlgorithm
        triple_bit_strict_composition)
  have hbuild : ConstructionCommutes QA :=
    quotient_construction_commutes tripleBitAmbiguity tripleBitAlgorithm
      triple_bit_transport_respects_generators
      (strict_construction_implies_modulo tripleBitAmbiguity tripleBitAlgorithm
        triple_bit_strict_construction)
  have hinj : EveryTransportInjective QA := by
    intro p q e
    exact (transportEquiv QA hid hcomp bool_procession_groupoid_laws.2.2 e).injective
  exact ⟨⟨false⟩, bool_every_pair_connected,
    triple_bit_quotient_output_nontrivial, bool_procession_groupoid_laws,
    hid, hcomp, hbuild, hinj⟩

def swapFirstThird (x : Bool × Bool × Bool) : Bool × Bool × Bool :=
  (x.2.2, x.2.1, x.1)

def relationDestroyingAlgorithm :
    ProcessionAlgorithmRaw boolProcessionIsoRaw TripleBitRaw where
  build := tripleBitBuild
  transport := fun {p q} _ x =>
    match p, q with
    | false, true => swapFirstThird x
    | _, _ => x

theorem relation_destroying_transport_does_not_descend :
    ¬ RawTransportRespectsGenerators tripleBitAmbiguity
      relationDestroyingAlgorithm := by
  intro h
  have hbad := h (p := false) (q := true) ()
    (x := (false, false, false)) (y := (true, false, false)) (Or.inl rfl)
  exact Bool.noConfusion (triple_ambiguity_preserves_third hbad)

def constantTripleBitAlgorithm :
    ProcessionAlgorithmRaw boolProcessionIsoRaw TripleBitRaw where
  build := tripleBitBuild
  transport := fun {_ q} _ _ => tripleBitBuild q

theorem constant_triple_respects_generators :
    RawTransportRespectsGenerators tripleBitAmbiguity
      constantTripleBitAlgorithm := by
  intro p q e x y h
  exact Relation.EqvGen.refl _

theorem constant_triple_composition_modulo :
    RawTransportCompositionModulo tripleBitAmbiguity
      constantTripleBitAlgorithm := by
  intro p q r e f x
  exact Relation.EqvGen.refl _

theorem constant_triple_construction_modulo :
    RawConstructionCommutesModulo tripleBitAmbiguity
      constantTripleBitAlgorithm := by
  intro p q e
  exact Relation.EqvGen.refl _

theorem constant_triple_not_identity_modulo :
    ¬ RawTransportIdentityModulo tripleBitAmbiguity
      constantTripleBitAlgorithm := by
  intro h
  have hbad := h false (false, false, true)
  exact Bool.noConfusion (triple_ambiguity_preserves_third hbad)

def totalAmbiguity : AmbiguityGenerators TripleBitRaw where
  ind1Step := fun _ _ _ => True
  ind2Step := fun _ _ _ => True

theorem total_ambiguity_has_no_separated_classes :
    ¬ HasSeparatedQuotientClasses totalAmbiguity := by
  rintro ⟨p, x, y, hxy⟩
  exact hxy (Relation.EqvGen.rel _ _ (Or.inl trivial))

def emptyAmbiguity : AmbiguityGenerators TripleBitRaw where
  ind1Step := fun _ _ _ => False
  ind2Step := fun _ _ _ => False

theorem empty_ambiguity_has_no_ind1_move :
    ¬ HasNontrivialInd1Step emptyAmbiguity := by
  rintro ⟨p, x, y, hxy, h⟩
  exact h

theorem empty_ambiguity_has_no_ind2_move :
    ¬ HasNontrivialInd2Step emptyAmbiguity := by
  rintro ⟨p, x, y, hxy, h⟩
  exact h

def onlyInd1Ambiguity : AmbiguityGenerators TripleBitRaw where
  ind1Step := tripleBitAmbiguity.ind1Step
  ind2Step := fun _ _ _ => False

theorem only_ind1_ambiguity_preserves_second
    {p : Bool} {x y : TripleBitRaw p}
    (h : Relation.EqvGen (ambiguityStep onlyInd1Ambiguity p) x y) :
    x.2.1 = y.2.1 := by
  induction h with
  | rel x y h =>
      rcases h with h1 | h2
      · exact congrArg Prod.fst h1
      · exact False.elim h2
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ hxy hyz => exact hxy.trans hyz

theorem omitting_ind2_rejects_an_ind2_move :
    ¬ Relation.EqvGen (ambiguityStep onlyInd1Ambiguity false)
      (false, false, false) (false, true, false) := by
  intro h
  exact Bool.noConfusion (only_ind1_ambiguity_preserves_second h)

def onlyInd2Ambiguity : AmbiguityGenerators TripleBitRaw where
  ind1Step := fun _ _ _ => False
  ind2Step := tripleBitAmbiguity.ind2Step

theorem only_ind2_ambiguity_preserves_first
    {p : Bool} {x y : TripleBitRaw p}
    (h : Relation.EqvGen (ambiguityStep onlyInd2Ambiguity p) x y) :
    x.1 = y.1 := by
  induction h with
  | rel x y h =>
      rcases h with h1 | h2
      · exact False.elim h1
      · exact h2.1
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ hxy hyz => exact hxy.trans hyz

theorem omitting_ind1_rejects_an_ind1_move :
    ¬ Relation.EqvGen (ambiguityStep onlyInd2Ambiguity false)
      (false, false, false) (true, false, false) := by
  intro h
  exact Bool.noConfusion (only_ind2_ambiguity_preserves_first h)

end CitedLV.Theorem311
