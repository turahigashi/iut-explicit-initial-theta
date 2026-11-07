import Cor312LogVolume.theorem311.Remark395HullIsAClosure
import Mathlib.Analysis.Normed.Group.Basic

set_option autoImplicit false
noncomputable section
namespace CitedLV.Theorem311.NormBallHullTransport

open Metric
open Src.CoreLayer.Theorem311.Remark395
universe u
variable {E : Type u} [NormedAddCommGroup E]

def Bounded (A : Set E) : Prop := ∃ r : ℝ, 0 ≤ r ∧ A ⊆ closedBall 0 r

def radiusSet (A : Set E) : Set ℝ := insert 0 (norm '' A)
def radius (A : Set E) : ℝ := sSup (radiusSet A)

theorem bounded_radiusSet {A : Set E} (hA : Bounded A) : BddAbove (radiusSet A) := by
  obtain ⟨r, hr, hAr⟩ := hA
  refine ⟨r, ?_⟩
  intro t ht
  rcases ht with hzero | ht
  · simpa only [hzero] using hr
  · obtain ⟨x, hx, rfl⟩ := ht
    exact mem_closedBall_zero_iff.mp (hAr hx)

theorem radius_nonneg {A : Set E} (hA : Bounded A) : 0 ≤ radius A :=
  le_csSup (bounded_radiusSet hA) (Set.mem_insert 0 _)

theorem norm_le_radius {A : Set E} (hA : Bounded A) {x : E} (hx : x ∈ A) :
    ‖x‖ ≤ radius A :=
  le_csSup (bounded_radiusSet hA) (Set.mem_insert_of_mem 0 ⟨x, hx, rfl⟩)

theorem radius_le {A : Set E} {r : ℝ} (hr : 0 ≤ r) (hAr : A ⊆ closedBall 0 r) :
    radius A ≤ r := by
  apply csSup_le ⟨0, Set.mem_insert 0 _⟩
  intro t ht
  rcases ht with hzero | ht
  · simpa only [hzero] using hr
  · obtain ⟨x, hx, rfl⟩ := ht
    exact mem_closedBall_zero_iff.mp (hAr hx)

def normHull (E : Type u) [NormedAddCommGroup E] : HullOperator E where
  isDomain := Bounded
  isHull := fun A => ∃ r : ℝ, 0 ≤ r ∧ A = closedBall 0 r
  hull_sub_domain := by
    rintro A ⟨r, hr, rfl⟩
    exact ⟨r, hr, Set.Subset.rfl⟩
  φ := fun A => closedBall 0 (radius A)
  φ_isHull := fun hA => ⟨radius _, radius_nonneg hA, rfl⟩
  P1 := by
    rintro A ⟨r, hr, rfl⟩
    apply Set.Subset.antisymm
    · intro x hx
      exact mem_closedBall_zero_iff.mpr
        ((mem_closedBall_zero_iff.mp hx).trans (radius_le hr Set.Subset.rfl))
    · intro x hx
      exact mem_closedBall_zero_iff.mpr (norm_le_radius ⟨r, hr, Set.Subset.rfl⟩ hx)
  P2 := fun hA x hx => mem_closedBall_zero_iff.mpr (norm_le_radius hA hx)
  P3 := by
    intro A B _ hB hAB x hx
    have hr : radius A ≤ radius B := radius_le (radius_nonneg hB)
      (fun y hy => mem_closedBall_zero_iff.mpr (norm_le_radius hB (hAB hy)))
    exact mem_closedBall_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx).trans hr)

@[simp] theorem hull_closedBall {r : ℝ} (hr : 0 ≤ r) :
    (normHull E).φ (closedBall (0 : E) r) = closedBall 0 r :=
  (normHull E).P1 ⟨r, hr, rfl⟩

theorem hull_subset_ball {A : Set E} {r : ℝ} (hr : 0 ≤ r)
    (hAr : A ⊆ closedBall 0 r) : (normHull E).φ A ⊆ closedBall 0 r := by
  intro x hx
  exact mem_closedBall_zero_iff.mpr
    ((mem_closedBall_zero_iff.mp hx).trans (radius_le hr hAr))

theorem hull_image_eq (f : E → E) {r : ℝ} {A : Set E}
    (hA : A ⊆ closedBall 0 r)
    (hf : ∀ x ∈ closedBall (0 : E) r, ‖f x‖ = ‖x‖) :
    (normHull E).φ (f '' A) = (normHull E).φ A := by
  have he : norm '' (f '' A) = norm '' A := by
    ext t
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, ht⟩
      exact ⟨x, hx, (hf x (hA hx)).symm.trans ht⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, hf x (hA hx)⟩
  change closedBall 0 (sSup (insert 0 (norm '' (f '' A)))) =
    closedBall 0 (sSup (insert 0 (norm '' A)))
  rw [he]

theorem image_hull_eq (f : E → E) {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ x ∈ closedBall (0 : E) r, ‖f x‖ = ‖x‖)
    (hs : Set.SurjOn f (closedBall 0 r) (closedBall 0 r))
    {A : Set E} (hA : A ⊆ closedBall 0 r) :
    f '' (normHull E).φ A = (normHull E).φ A := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxr := hull_subset_ball hr hA hx
    exact mem_closedBall_zero_iff.mpr
      ((hf x hxr).trans_le (mem_closedBall_zero_iff.mp hx))
  · intro hy
    obtain ⟨x, hxr, hxy⟩ := hs (hull_subset_ball hr hA hy)
    refine ⟨x, ?_, hxy⟩
    have hn : ‖x‖ = ‖y‖ := (hf x hxr).symm.trans (congrArg norm hxy)
    exact mem_closedBall_zero_iff.mpr (hn.trans_le (mem_closedBall_zero_iff.mp hy))

end CitedLV.Theorem311.NormBallHullTransport
end
