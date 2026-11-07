import Cor312LogVolume.theorem311.Remark395HullIsAClosure
import Cor312LogVolume.theorem311.PacketReadoutObject

set_option autoImplicit false
noncomputable section
namespace CitedLV.Theorem311.PacketHullEndpoint

open Src.IUT3.Theorem311
open Src.CoreLayer.Theorem311.Remark395

abbrev HullFamily (S : PacketSystem) :=
  ∀ (vQ : S.PlaceQ) (j : Fin (S.lstar + 1)), HullOperator (S.Packet vQ j)

def RegionLE (S : PacketSystem) (R T : S.Regions) : Prop :=
  ∀ vQ j, R vQ j ⊆ T vQ j

def unionProfile (S : PacketSystem) (output : Set S.Regions) : S.Regions :=
  fun vQ j => {x | ∃ R ∈ output, x ∈ R vQ j}

def hullProfile (S : PacketSystem) (H : HullFamily S)
    (output : Set S.Regions) : S.Regions :=
  fun vQ j => (H vQ j).φ (unionProfile S output vQ j)

def endpoint (S : PacketSystem) (H : HullFamily S)
    (output : Set S.Regions) : ℝ :=
  S.procVol (hullProfile S H output)

def endpointRay (S : PacketSystem) (H : HullFamily S)
    (output : Set S.Regions) : Set ℝ := Set.Iic (endpoint S H output)

def UnionAdmissible (S : PacketSystem) (H : HullFamily S)
    (output : Set S.Regions) : Prop :=
  ∀ vQ j, (H vQ j).isDomain (unionProfile S output vQ j)

@[simp] theorem unionProfile_singleton (S : PacketSystem) (R : S.Regions) :
    unionProfile S {R} = R := by
  funext vQ j
  ext x
  constructor
  · rintro ⟨T, hT, hx⟩
    have he : T = R := Set.mem_singleton_iff.mp hT
    exact he ▸ hx
  · intro hx
    exact ⟨R, rfl, hx⟩

theorem member_le_union (S : PacketSystem) {output : Set S.Regions}
    {R : S.Regions} (hR : R ∈ output) : RegionLE S R (unionProfile S output) :=
  fun _ _ _ hx => ⟨R, hR, hx⟩

theorem union_le_iff (S : PacketSystem) (output : Set S.Regions) (T : S.Regions) :
    RegionLE S (unionProfile S output) T ↔ ∀ R ∈ output, RegionLE S R T := by
  constructor
  · intro h R hR vQ j x hx
    exact h vQ j ⟨R, hR, hx⟩
  · intro h vQ j x hx
    obtain ⟨R, hR, hxR⟩ := hx
    exact h R hR vQ j hxR

theorem unionProfile_mono (S : PacketSystem) {A B : Set S.Regions}
    (h : A ⊆ B) : RegionLE S (unionProfile S A) (unionProfile S B) := by
  intro vQ j x hx
  obtain ⟨R, hR, hxR⟩ := hx
  exact ⟨R, h hR, hxR⟩

theorem union_le_hull (S : PacketSystem) (H : HullFamily S)
    (output : Set S.Regions) (hdom : UnionAdmissible S H output) :
    RegionLE S (unionProfile S output) (hullProfile S H output) :=
  fun vQ j => (H vQ j).P2 (hdom vQ j)

theorem member_le_hull (S : PacketSystem) (H : HullFamily S)
    (output : Set S.Regions) (hdom : UnionAdmissible S H output)
    (R : S.Regions) (hR : R ∈ output) :
    RegionLE S R (hullProfile S H output) :=
  fun vQ j => (member_le_union S hR vQ j).trans (union_le_hull S H output hdom vQ j)

theorem hullProfile_isHull (S : PacketSystem) (H : HullFamily S)
    (output : Set S.Regions) (hdom : UnionAdmissible S H output) :
    ∀ vQ j, (H vQ j).isHull (hullProfile S H output vQ j) :=
  fun vQ j => (H vQ j).φ_isHull (hdom vQ j)

theorem hullProfile_minimal (S : PacketSystem) (H : HullFamily S)
    (output : Set S.Regions) (hdom : UnionAdmissible S H output)
    (T : S.Regions) (hT : ∀ vQ j, (H vQ j).isHull (T vQ j))
    (hcontain : ∀ R ∈ output, RegionLE S R T) :
    RegionLE S (hullProfile S H output) T := by
  have hu := (union_le_iff S output T).mpr hcontain
  intro vQ j
  have hm := (H vQ j).P3 (hdom vQ j)
    ((H vQ j).hull_sub_domain (hT vQ j)) (hu vQ j)
  rw [(H vQ j).P1 (hT vQ j)] at hm
  exact hm

theorem hullProfile_idempotent (S : PacketSystem) (H : HullFamily S)
    (output : Set S.Regions) (hdom : UnionAdmissible S H output) :
    hullProfile S H {hullProfile S H output} = hullProfile S H output := by
  unfold hullProfile
  rw [unionProfile_singleton]
  funext vQ j
  exact (H vQ j).hull_idempotent (hdom vQ j)

theorem endpoint_unique (S : PacketSystem) (H H' : HullFamily S)
    (output : Set S.Regions)
    (hdom : UnionAdmissible S H output)
    (hd : ∀ vQ j, (H vQ j).isDomain = (H' vQ j).isDomain)
    (hh : ∀ vQ j, (H vQ j).isHull = (H' vQ j).isHull) :
    endpoint S H output = endpoint S H' output := by
  apply congrArg S.procVol
  funext vQ j
  exact (H vQ j).hull_unique (H' vQ j) (hd vQ j) (hh vQ j) (hdom vQ j)

theorem endpoint_eq_coarseVolume (S : PacketSystem) (H : HullFamily S)
    (output : Set S.Regions) :
    endpoint S H output = S.coarseVolume (Quot.mk _ (hullProfile S H output)) := rfl

end CitedLV.Theorem311.PacketHullEndpoint
end
