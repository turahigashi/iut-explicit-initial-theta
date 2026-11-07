import Cor312LogVolume.thetalink.RetainedThetaDatum
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.ZMod

namespace CitedLV.ThetaLink

universe uG uO uG' uO' uG'' uO''

noncomputable section

structure RetainedThetaSide where
  G : Type uG
  O : Type uO
  [topG : TopologicalSpace G]
  [groupG : Group G]
  [topologicalGroupG : IsTopologicalGroup G]
  [topO : TopologicalSpace O]
  [monoidO : CommMonoid O]
  [continuousMulO : ContinuousMul O]
  [action : MulAction G O]
  [continuousAction : ContinuousSMul G O]
  datum : RetainedThetaDatum G O

attribute [instance]
  RetainedThetaSide.topG RetainedThetaSide.groupG
  RetainedThetaSide.topologicalGroupG RetainedThetaSide.topO
  RetainedThetaSide.monoidO RetainedThetaSide.continuousMulO
  RetainedThetaSide.action RetainedThetaSide.continuousAction

def transportOpen
    {G : Type uG} {G' : Type uG'}
    [TopologicalSpace G] [Group G]
    [TopologicalSpace G'] [Group G']
    (e : G ≃ₜ* G') (H : OpenSubgroup G) : OpenSubgroup G' :=
  H.comap e.symm.toMulEquiv.toMonoidHom e.symm.continuous_toFun

@[simp] theorem mem_transportOpen
    {G : Type uG} {G' : Type uG'}
    [TopologicalSpace G] [Group G]
    [TopologicalSpace G'] [Group G']
    (e : G ≃ₜ* G') (H : OpenSubgroup G) (g : G') :
    g ∈ transportOpen e H ↔ e.symm g ∈ H :=
  Iff.rfl

@[simp] theorem transportOpen_refl
    {G : Type uG} [TopologicalSpace G] [Group G]
    (H : OpenSubgroup G) :
    transportOpen (ContinuousMulEquiv.refl G) H = H := by
  ext g
  rfl

@[simp] theorem transportOpen_trans
    {G : Type uG} {G' : Type uG'} {G'' : Type uG''}
    [TopologicalSpace G] [Group G]
    [TopologicalSpace G'] [Group G']
    [TopologicalSpace G''] [Group G'']
    (e : G ≃ₜ* G') (f : G' ≃ₜ* G'') (H : OpenSubgroup G) :
    transportOpen (e.trans f) H =
      transportOpen f (transportOpen e H) := by
  ext g
  rfl

@[simp] theorem transportOpen_symm_cancel
    {G : Type uG} {G' : Type uG'}
    [TopologicalSpace G] [Group G]
    [TopologicalSpace G'] [Group G']
    (e : G ≃ₜ* G') (H : OpenSubgroup G') :
    transportOpen e (transportOpen e.symm H) = H := by
  ext g
  simp

def PreservesLattices
    (D : RetainedThetaSide.{uG, uO})
    (E : RetainedThetaSide.{uG', uO'})
    (eG : D.G ≃ₜ* E.G) (eO : D.O ≃ₜ* E.O) : Prop :=
  ∀ H x,
    x ∈ D.datum.lattice H ↔
      eO x ∈ E.datum.lattice (transportOpen eG H)

structure AdmissibleIso
    (D : RetainedThetaSide.{uG, uO})
    (E : RetainedThetaSide.{uG', uO'}) where
  groupEquiv : D.G ≃ₜ* E.G
  monoidEquiv : D.O ≃ₜ* E.O
  equivariant : ∀ g x,
    monoidEquiv (g • x) = groupEquiv g • monoidEquiv x
  preservesLattices : PreservesLattices D E groupEquiv monoidEquiv

namespace AdmissibleIso

def refl (D : RetainedThetaSide.{uG, uO}) : AdmissibleIso D D where
  groupEquiv := ContinuousMulEquiv.refl D.G
  monoidEquiv := ContinuousMulEquiv.refl D.O
  equivariant := by
    intro g x
    rfl
  preservesLattices := by
    intro H x
    simp

def trans
    {D : RetainedThetaSide.{uG, uO}}
    {E : RetainedThetaSide.{uG', uO'}}
    {F : RetainedThetaSide.{uG'', uO''}}
    (e : AdmissibleIso D E) (f : AdmissibleIso E F) :
    AdmissibleIso D F where
  groupEquiv := e.groupEquiv.trans f.groupEquiv
  monoidEquiv := e.monoidEquiv.trans f.monoidEquiv
  equivariant := by
    intro g x
    change f.monoidEquiv (e.monoidEquiv (g • x)) =
      f.groupEquiv (e.groupEquiv g) •
        f.monoidEquiv (e.monoidEquiv x)
    rw [e.equivariant, f.equivariant]
  preservesLattices := by
    intro H x
    rw [transportOpen_trans]
    exact (e.preservesLattices H x).trans
      (f.preservesLattices
        (transportOpen e.groupEquiv H) (e.monoidEquiv x))

def symm
    {D : RetainedThetaSide.{uG, uO}}
    {E : RetainedThetaSide.{uG', uO'}}
    (e : AdmissibleIso D E) : AdmissibleIso E D where
  groupEquiv := e.groupEquiv.symm
  monoidEquiv := e.monoidEquiv.symm
  equivariant := by
    intro g x
    apply e.monoidEquiv.injective
    symm
    simpa using
      e.equivariant (e.groupEquiv.symm g) (e.monoidEquiv.symm x)
  preservesLattices := by
    intro H x
    have h := (e.preservesLattices
      (transportOpen e.groupEquiv.symm H)
      (e.monoidEquiv.symm x)).symm
    simpa using h

end AdmissibleIso

def CompletePolyIso
    (D : RetainedThetaSide.{uG, uO})
    (E : RetainedThetaSide.{uG', uO'}) :
    Set (AdmissibleIso D E) :=
  Set.univ

theorem mem_completePolyIso
    {D : RetainedThetaSide.{uG, uO}}
    {E : RetainedThetaSide.{uG', uO'}}
    (e : AdmissibleIso D E) : e ∈ CompletePolyIso D E :=
  Set.mem_univ e

theorem completePolyIso_self_nonempty
    (D : RetainedThetaSide.{uG, uO}) :
    (CompletePolyIso D D).Nonempty :=
  ⟨AdmissibleIso.refl D, Set.mem_univ _⟩

abbrev C3 := Multiplicative (ZMod 3)
abbrev C3Square := C3 × C3

local instance : ContinuousMul C3Square :=
  ⟨continuous_of_discreteTopology⟩
local instance : ContinuousInv C3Square :=
  ⟨continuous_of_discreteTopology⟩
local instance : IsTopologicalGroup C3Square where
local instance : ContinuousSMul C3Square C3Square :=
  ⟨continuous_of_discreteTopology⟩

def c3Generator : C3 := Multiplicative.ofAdd (1 : ZMod 3)

def c3FirstAxis : Submonoid C3Square where
  carrier := {x | x.2 = 1}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    change x.2 = 1 at hx
    change y.2 = 1 at hy
    change x.2 * y.2 = 1
    rw [hx, hy, one_mul]

abbrev c3SquareAll : RetainedThetaSide where
  G := C3Square
  O := C3Square
  datum := { lattice := fun _ ↦ ⊤ }

abbrev c3SquareMarked : RetainedThetaSide where
  G := C3Square
  O := C3Square
  datum := { lattice := fun _ ↦ c3FirstAxis }

def c3SquareSwap : C3Square ≃ₜ* C3Square where
  toFun x := (x.2, x.1)
  invFun x := (x.2, x.1)
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl
  map_mul' := by
    intro x y
    rfl
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

def c3SquareSwapAll : AdmissibleIso c3SquareAll c3SquareAll where
  groupEquiv := c3SquareSwap
  monoidEquiv := c3SquareSwap
  equivariant := by
    intro g x
    rfl
  preservesLattices := by
    intro H x
    simp

def c3AxisWitness : C3Square := (c3Generator, 1)

theorem c3Generator_ne_one : c3Generator ≠ 1 := by
  decide

theorem c3SquareSwap_moves_axis_witness :
    c3SquareSwap c3AxisWitness ∉ c3FirstAxis := by
  simpa [c3SquareSwap, c3AxisWitness, c3FirstAxis] using c3Generator_ne_one

theorem c3SquareSwapAll_ne_identity :
    c3SquareSwapAll ≠ AdmissibleIso.refl c3SquareAll := by
  intro h
  have happ := congrArg
    (fun e : AdmissibleIso c3SquareAll c3SquareAll ↦
      e.monoidEquiv c3AxisWitness) h
  have hfirst := congrArg Prod.fst happ
  exact c3Generator_ne_one (by
    simpa [c3SquareSwapAll, c3SquareSwap, AdmissibleIso.refl,
      c3AxisWitness] using hfirst.symm)

theorem c3SquareSwap_passes_universal_lattices :
    c3SquareSwapAll ∈ CompletePolyIso c3SquareAll c3SquareAll :=
  Set.mem_univ _

theorem c3SquareSwap_fails_marked_lattices :
    ¬ PreservesLattices c3SquareMarked c3SquareMarked
      c3SquareSwap c3SquareSwap := by
  intro h
  have hw : c3AxisWitness ∈ c3FirstAxis := by
    simp [c3AxisWitness, c3FirstAxis]
  have himage :=
    (h (⊤ : OpenSubgroup C3Square) c3AxisWitness).mp hw
  exact c3SquareSwap_moves_axis_witness (by
    simpa [c3SquareMarked] using himage)

theorem no_admissible_marked_swap :
    ¬ ∃ e : AdmissibleIso c3SquareMarked c3SquareMarked,
      e.groupEquiv = c3SquareSwap ∧ e.monoidEquiv = c3SquareSwap := by
  rintro ⟨e, heG, heO⟩
  apply c3SquareSwap_fails_marked_lattices
  simpa [heG, heO] using e.preservesLattices

theorem c3Square_identity_passes_marked_lattices :
    AdmissibleIso.refl c3SquareMarked ∈
      CompletePolyIso c3SquareMarked c3SquareMarked :=
  Set.mem_univ _

end

end CitedLV.ThetaLink
