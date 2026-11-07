import Cor312LogVolume.entanglement.MonoidSubquotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.OpenSubgroup

namespace CitedLV.ThetaLink

open CitedLV.Entanglement

noncomputable section

structure RetainedThetaDatum
    (G O : Type*)
    [Group G] [CommMonoid O] [MulAction G O]
    [TopologicalSpace G] [TopologicalSpace O]
    [IsTopologicalGroup G] [ContinuousMul O] [ContinuousSMul G O] where

  lattice : OpenSubgroup G → Submonoid O

structure RealizedThetaDatum
    (K G FieldAut O : Type*)
    [CommRing K]
    [Group G] [Group FieldAut] [CommMonoid O] [MulAction G O]
    [TopologicalSpace G] [TopologicalSpace FieldAut] [TopologicalSpace O]
    [IsTopologicalGroup G] [IsTopologicalGroup FieldAut]
    [ContinuousMul O] [ContinuousSMul G O] where
  retained : RetainedThetaDatum G O
  groupAsFieldAutomorphisms : G ≃ₜ* FieldAut
  unitFromRing : RingUnitSubquotient K O

def forgetOrigins
    {K G FieldAut O : Type*}
    [CommRing K]
    [Group G] [Group FieldAut] [CommMonoid O] [MulAction G O]
    [TopologicalSpace G] [TopologicalSpace FieldAut] [TopologicalSpace O]
    [IsTopologicalGroup G] [IsTopologicalGroup FieldAut]
    [ContinuousMul O] [ContinuousSMul G O]
    (X : RealizedThetaDatum K G FieldAut O) :
    RetainedThetaDatum G O :=
  X.retained

theorem forgetOrigins_identifies_group_realizations
    {K G FieldAut O : Type*}
    [CommRing K]
    [Group G] [Group FieldAut] [CommMonoid O] [MulAction G O]
    [TopologicalSpace G] [TopologicalSpace FieldAut] [TopologicalSpace O]
    [IsTopologicalGroup G] [IsTopologicalGroup FieldAut]
    [ContinuousMul O] [ContinuousSMul G O]
    (D : RetainedThetaDatum G O)
    (R : RingUnitSubquotient K O) (e₁ e₂ : G ≃ₜ* FieldAut) :
    forgetOrigins
        ({ retained := D, groupAsFieldAutomorphisms := e₁,
           unitFromRing := R } :
          RealizedThetaDatum K G FieldAut O) =
      forgetOrigins
        ({ retained := D, groupAsFieldAutomorphisms := e₂,
           unitFromRing := R } :
          RealizedThetaDatum K G FieldAut O) :=
  rfl

theorem forgetOrigins_has_no_left_inverse_of_distinct_group_realizations
    {K G FieldAut O : Type*}
    [CommRing K]
    [Group G] [Group FieldAut] [CommMonoid O] [MulAction G O]
    [TopologicalSpace G] [TopologicalSpace FieldAut] [TopologicalSpace O]
    [IsTopologicalGroup G] [IsTopologicalGroup FieldAut]
    [ContinuousMul O] [ContinuousSMul G O]
    (D : RetainedThetaDatum G O)
    (R : RingUnitSubquotient K O) (e₁ e₂ : G ≃ₜ* FieldAut)
    (hne : e₁ ≠ e₂) :
    ¬ ∃ recover : RetainedThetaDatum G O →
        RealizedThetaDatum K G FieldAut O,
      Function.LeftInverse recover forgetOrigins := by
  rintro ⟨recover, hrecover⟩
  let X : RealizedThetaDatum K G FieldAut O :=
    { retained := D, groupAsFieldAutomorphisms := e₁, unitFromRing := R }
  let Y : RealizedThetaDatum K G FieldAut O :=
    { retained := D, groupAsFieldAutomorphisms := e₂, unitFromRing := R }
  have hXY : X = Y := by
    calc
      X = recover (forgetOrigins X) := (hrecover X).symm
      _ = recover (forgetOrigins Y) := by
        rw [show forgetOrigins X = forgetOrigins Y from rfl]
      _ = Y := hrecover Y
  apply hne
  exact congrArg RealizedThetaDatum.groupAsFieldAutomorphisms hXY

theorem forgetOrigins_has_no_left_inverse_of_distinct_unit_realizations
    {K G FieldAut O : Type*}
    [CommRing K]
    [Group G] [Group FieldAut] [CommMonoid O] [MulAction G O]
    [TopologicalSpace G] [TopologicalSpace FieldAut] [TopologicalSpace O]
    [IsTopologicalGroup G] [IsTopologicalGroup FieldAut]
    [ContinuousMul O] [ContinuousSMul G O]
    (D : RetainedThetaDatum G O)
    (e : G ≃ₜ* FieldAut) (R₁ R₂ : RingUnitSubquotient K O)
    (hne : R₁ ≠ R₂) :
    ¬ ∃ recover : RetainedThetaDatum G O →
        RealizedThetaDatum K G FieldAut O,
      Function.LeftInverse recover forgetOrigins := by
  rintro ⟨recover, hrecover⟩
  let X : RealizedThetaDatum K G FieldAut O :=
    { retained := D, groupAsFieldAutomorphisms := e, unitFromRing := R₁ }
  let Y : RealizedThetaDatum K G FieldAut O :=
    { retained := D, groupAsFieldAutomorphisms := e, unitFromRing := R₂ }
  have hXY : X = Y := by
    calc
      X = recover (forgetOrigins X) := (hrecover X).symm
      _ = recover (forgetOrigins Y) := by
        rw [show forgetOrigins X = forgetOrigins Y from rfl]
      _ = Y := hrecover Y
  apply hne
  exact congrArg RealizedThetaDatum.unitFromRing hXY

abbrev OriginToyGroup := (ZMod 5)ˣ

local instance : TopologicalSpace OriginToyGroup := ⊥
local instance : DiscreteTopology OriginToyGroup := discreteTopology_bot OriginToyGroup
local instance : ContinuousMul OriginToyGroup :=
  ⟨continuous_of_discreteTopology⟩
local instance : ContinuousInv OriginToyGroup :=
  ⟨continuous_of_discreteTopology⟩
local instance : IsTopologicalGroup OriginToyGroup where
local instance : ContinuousSMul OriginToyGroup OriginToyGroup :=
  ⟨continuous_of_discreteTopology⟩

def originToyRetained : RetainedThetaDatum
    OriginToyGroup OriginToyGroup where
  lattice _ := ⊤

def originToyUnitFromRing :
    RingUnitSubquotient (ZMod 5) OriginToyGroup where
  carrier := ⊤
  quotient := Submonoid.subtype ⊤
  quotient_surjective := by
    intro u
    exact ⟨⟨u, trivial⟩, rfl⟩

def originToyUnitFromRingInversion :
    RingUnitSubquotient (ZMod 5) OriginToyGroup where
  carrier := ⊤
  quotient :=
    (MulEquiv.inv OriginToyGroup).toMonoidHom.comp (Submonoid.subtype ⊤)
  quotient_surjective := by
    intro u
    exact ⟨⟨u⁻¹, trivial⟩, by simp⟩

def originToyUnitProbe
    (R : RingUnitSubquotient (ZMod 5) OriginToyGroup)
    (u : OriginToyGroup) : OriginToyGroup := by
  classical
  exact if h : u ∈ R.carrier then R.quotient ⟨u, h⟩ else 1

theorem originToyUnitProbe_identity :
    originToyUnitProbe originToyUnitFromRing
      CitedLV.Labels.twoUnitModFive =
        CitedLV.Labels.twoUnitModFive := by
  classical
  simp [originToyUnitProbe, originToyUnitFromRing]
  rfl

theorem originToyUnitProbe_inversion :
    originToyUnitProbe originToyUnitFromRingInversion
      CitedLV.Labels.twoUnitModFive =
        CitedLV.Labels.twoUnitModFive⁻¹ := by
  classical
  simp [originToyUnitProbe, originToyUnitFromRingInversion]
  rfl

def originToyIdentity : OriginToyGroup ≃ₜ* OriginToyGroup :=
  ContinuousMulEquiv.refl OriginToyGroup

def originToyInversion : OriginToyGroup ≃ₜ* OriginToyGroup where
  __ := MulEquiv.inv OriginToyGroup
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

theorem originToyIdentity_ne_inversion :
    originToyIdentity ≠ originToyInversion := by
  intro h
  have hv := congrArg
    (fun e : OriginToyGroup ≃ₜ* OriginToyGroup ↦
      ((e CitedLV.Labels.twoUnitModFive : OriginToyGroup) : ZMod 5)) h
  exact (by decide : (2 : ZMod 5) ≠ 3) (by
    simpa [originToyIdentity, originToyInversion,
      CitedLV.Labels.twoUnitModFive] using hv)

theorem originToyUnitFromRing_ne_inversion :
    originToyUnitFromRing ≠ originToyUnitFromRingInversion := by
  intro h
  have hq := congrArg
    (fun R ↦ originToyUnitProbe R CitedLV.Labels.twoUnitModFive) h
  change originToyUnitProbe originToyUnitFromRing
      CitedLV.Labels.twoUnitModFive =
    originToyUnitProbe originToyUnitFromRingInversion
      CitedLV.Labels.twoUnitModFive at hq
  rw [originToyUnitProbe_identity, originToyUnitProbe_inversion] at hq
  have hv := congrArg (fun u : OriginToyGroup ↦ (u : ZMod 5)) hq
  exact (by decide : (2 : ZMod 5) ≠ 3) (by
    simpa [CitedLV.Labels.twoUnitModFive] using hv)

def originToyRealizedIdentity : RealizedThetaDatum
    (ZMod 5) OriginToyGroup OriginToyGroup OriginToyGroup where
  retained := originToyRetained
  groupAsFieldAutomorphisms := originToyIdentity
  unitFromRing := originToyUnitFromRing

def originToyRealizedInversion : RealizedThetaDatum
    (ZMod 5) OriginToyGroup OriginToyGroup OriginToyGroup where
  retained := originToyRetained
  groupAsFieldAutomorphisms := originToyInversion
  unitFromRing := originToyUnitFromRing

def originToyRealizedUnitInversion : RealizedThetaDatum
    (ZMod 5) OriginToyGroup OriginToyGroup OriginToyGroup where
  retained := originToyRetained
  groupAsFieldAutomorphisms := originToyIdentity
  unitFromRing := originToyUnitFromRingInversion

theorem originToy_realizations_distinct :
    originToyRealizedIdentity ≠ originToyRealizedInversion := by
  intro h
  apply originToyIdentity_ne_inversion
  exact congrArg RealizedThetaDatum.groupAsFieldAutomorphisms h

theorem originToy_forgetting_identifies_realizations :
    forgetOrigins originToyRealizedIdentity =
      forgetOrigins originToyRealizedInversion :=
  rfl

theorem originToy_forgetting_identifies_unit_realizations :
    forgetOrigins originToyRealizedIdentity =
      forgetOrigins originToyRealizedUnitInversion :=
  rfl

theorem originToy_forgetOrigins_has_no_left_inverse :
    ¬ ∃ recover :
        RetainedThetaDatum OriginToyGroup OriginToyGroup →
          RealizedThetaDatum (ZMod 5) OriginToyGroup OriginToyGroup
            OriginToyGroup,
      Function.LeftInverse recover forgetOrigins :=
  forgetOrigins_has_no_left_inverse_of_distinct_group_realizations
    originToyRetained originToyUnitFromRing
    originToyIdentity originToyInversion originToyIdentity_ne_inversion

theorem originToy_unitOrigin_has_no_left_inverse :
    ¬ ∃ recover :
        RetainedThetaDatum OriginToyGroup OriginToyGroup →
          RealizedThetaDatum (ZMod 5) OriginToyGroup OriginToyGroup
            OriginToyGroup,
      Function.LeftInverse recover forgetOrigins :=
  forgetOrigins_has_no_left_inverse_of_distinct_unit_realizations
    originToyRetained originToyIdentity originToyUnitFromRing
    originToyUnitFromRingInversion originToyUnitFromRing_ne_inversion

end

end CitedLV.ThetaLink
