import Cor312LogVolume.independence.Cor312LanaTarget
import Cor312LogVolume.independence.Cor312CitedBadPlaceEnlarged
import Cor312LogVolume.Src.IUT3.Section3Remark395ixClosedLoop

set_option autoImplicit false
noncomputable section

open CategoryTheory
open Src.IUT3.Theorem311
open Src.IUT3.Remark3111
open Src.IUT3.Remark395ix
open CitedLV.Theorem311
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211PacketN
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Theorem311.P211RealCarrierPackage

namespace CitedLV.Independence.Cor312Cited

namespace CitedTheory

variable (T : CitedTheory)

def IndStep (x y : T.S.Regions) : Prop :=
  T.S.Ind1 x y ∨ T.S.Ind2 x y ∨ (RegionLE T.S x y ∧ RegionLE T.S y T.container)

theorem container_possible : T.container ∈ T.Possible :=
  T.ind3_saturated _ T.theta_possible _ (T.ind3_bound _ T.theta_possible) (fun _ _ => subset_rfl)

def primeStripLayer : AlgorithmSetting where
  Strip := ModelStrip
  diagram := modelDiagram
  qStrip := strip2
  thetaLink := idHom 3 0
  Output := T.S.Regions
  stripOf := fun _ => obj 8
  actual := T.thetaPilot
  actual_strip := rfl
  indStep := T.IndStep
  indStep_strip := fun _ _ _ => rfl
  hull := fun _ => T.container
  hull_strip := fun _ _ hF hs => by
    obtain ⟨x, hx⟩ := hF
    exact hs x hx

theorem layer_possible_subset_aux :
    ∀ y : T.primeStripLayer.Output, T.primeStripLayer.Possible y → y ∈ T.Possible := by
  intro y hy
  induction hy with
  | actual => exact T.theta_possible
  | ind _ hstep ih =>
    rcases hstep with h1 | h2 | ⟨hle, hc⟩
    · exact T.ind1_closed _ ih _ h1
    · exact T.ind2_closed _ ih _ h2
    · exact T.ind3_saturated _ ih _ hle hc
  | hull _ _ _ _ => exact T.container_possible

theorem layer_possible_subset {x : T.S.Regions} (hx : x ∈ T.primeStripLayer.possible) :
    x ∈ T.Possible :=
  T.layer_possible_subset_aux x hx

theorem layer_possible_eq (hlow : ∀ y ∈ T.Possible, RegionLE T.S T.thetaPilot y) :
    T.primeStripLayer.possible = T.Possible := by
  ext y
  refine ⟨T.layer_possible_subset, fun hy => ?_⟩
  show T.primeStripLayer.Possible y
  exact AlgorithmSetting.Possible.ind AlgorithmSetting.Possible.actual
    (Or.inr (Or.inr ⟨hlow y hy, T.ind3_bound y hy⟩))

theorem layer_ipl : ∀ x ∈ T.primeStripLayer.possible, T.primeStripLayer.Linked x :=
  T.primeStripLayer.ipl

def layerLoop : LoopData T.primeStripLayer where
  hullTarget := obj 9
  sq3 := idHom 8 9
  sq4 := inv (inv T.primeStripLayer.thetaLink ≫ T.primeStripLayer.diagram.iplComposite ≫ idHom 8 9)
  sq3Twist := ∅
  sq4Twist := ∅

theorem layer_holonomy_trivial : T.layerLoop.loopArrow (𝟙 _) (𝟙 _) = 𝟙 _ := by
  simp [LoopData.loopArrow, layerLoop]

theorem layer_id_mem_loopPoly : 𝟙 _ ∈ T.layerLoop.loopPoly :=
  ⟨𝟙 _, Set.mem_insert _ _, 𝟙 _, Set.mem_insert _ _, T.layer_holonomy_trivial.symm⟩

theorem layer_closed_before_sq5 : T.layerLoop.ClosedUpToFormalQuotient completedBeforeSQ5 :=
  T.layerLoop.closed_before_sq5

theorem layer_volume_production_implies_conclusion
    (h : ∃ x ∈ T.primeStripLayer.possible, T.S.HasVolume x ∧ T.S.procVol x = T.negLogQ) :
    T.Conclusion := by
  obtain ⟨x, hx, hv, he⟩ := h
  exact T.pilotVolumeMatch_implies_conclusion ⟨x, T.layer_possible_subset hx, hv, he⟩

theorem layer_on_every_cited_theory :
    T.primeStripLayer.possible ⊆ T.Possible ∧
      (∀ x ∈ T.primeStripLayer.possible, T.primeStripLayer.Linked x) ∧
      T.layerLoop.ClosedUpToFormalQuotient completedBeforeSQ5 ∧
      T.layerLoop.loopArrow (𝟙 _) (𝟙 _) = 𝟙 _ :=
  ⟨fun _ hx => T.layer_possible_subset hx, T.layer_ipl, T.layer_closed_before_sq5,
    T.layer_holonomy_trivial⟩

theorem restricted_hull_vol_le (P : Set T.S.Regions) (hP : P ⊆ T.Possible) (h : T.S.Regions)
    (hmin : ∀ U : T.S.Regions, (∀ vQ j, T.IsLambdaO vQ j (U vQ j)) →
      (∀ x ∈ P, RegionLE T.S x U) → RegionLE T.S h U)
    (hv : T.S.HasVolume h) : T.S.procVol h ≤ T.negLogTheta := by
  have hle : RegionLE T.S h T.hull :=
    hmin T.hull T.hull_isLambdaO (fun x hx => T.hull_contains x (hP hx))
  exact T.S.procVol_ind3 (fun vQ j => ⟨hle vQ j, T.hull_le_integral vQ j⟩) hv

theorem restriction_cannot_rescue (hnc : ¬ T.Conclusion) (P : Set T.S.Regions) (hP : P ⊆ T.Possible)
    (h : T.S.Regions)
    (hmin : ∀ U : T.S.Regions, (∀ vQ j, T.IsLambdaO vQ j (U vQ j)) →
      (∀ x ∈ P, RegionLE T.S x U) → RegionLE T.S h U)
    (hv : T.S.HasVolume h) : T.S.procVol h < T.negLogQ := by
  have h1 := T.restricted_hull_vol_le P hP h hmin hv
  have h2 : T.negLogTheta < T.negLogQ := lt_of_not_ge hnc
  linarith

end CitedTheory

theorem layer_does_not_produce_q_value :
    modelTheory.WeakSHE ∧
      modelTheory.primeStripLayer.possible = modelTheory.Possible ∧
      (∀ x ∈ modelTheory.primeStripLayer.possible, modelTheory.primeStripLayer.Linked x) ∧
      modelTheory.layerLoop.ClosedUpToFormalQuotient completedBeforeSQ5 ∧
      modelTheory.layerLoop.loopArrow (𝟙 _) (𝟙 _) = 𝟙 _ ∧
      modelTheory.qPilot ∉ modelTheory.primeStripLayer.possible ∧
      ¬ modelTheory.primeStripLayer.ScalarProduction modelTheory.S.procVol modelTheory.negLogQ ∧
      ¬ modelTheory.Conclusion := by
  have heq : modelTheory.primeStripLayer.possible = modelTheory.Possible :=
    modelTheory.layer_possible_eq (by
      rintro y rfl
      exact fun _ _ => subset_rfl)
  refine ⟨model_weakSHE, heq, modelTheory.layer_ipl, modelTheory.layer_closed_before_sq5,
    modelTheory.layer_holonomy_trivial, ?_, ?_, model_not_conclusion⟩
  · intro hq
    exact model_q_not_possible (modelTheory.layer_possible_subset hq)
  · rintro ⟨x, hx, he⟩
    have hx' : x = thetaPilotRegion := modelTheory.layer_possible_subset hx
    subst hx'
    have h1 : p211PacketSystemN.procVol thetaPilotRegion = p211PacketSystemN.procVol qRegionN := he
    have h2 := thetaPilot_below_q
    linarith

end CitedLV.Independence.Cor312Cited

namespace CitedLV.Independence.Cor312CitedFamily

open CitedLV.Independence.Cor312Cited

namespace CitedTheoryFam

variable (T : CitedTheoryFam)

def IndStep (x y : ∀ i, (T.S i).Regions) : Prop :=
  (∀ i, (T.S i).Ind1 (x i) (y i)) ∨ (∀ i, (T.S i).Ind2 (x i) (y i)) ∨
    (∀ i, RegionLE (T.S i) (x i) (y i) ∧ RegionLE (T.S i) (y i) (T.container i))

theorem container_possible : T.container ∈ T.Possible :=
  T.ind3_saturated _ T.theta_possible _ (T.ind3_bound _ T.theta_possible) (fun _ _ _ => subset_rfl)

def primeStripLayer : AlgorithmSetting where
  Strip := ModelStrip
  diagram := modelDiagram
  qStrip := strip2
  thetaLink := idHom 3 0
  Output := ∀ i, (T.S i).Regions
  stripOf := fun _ => obj 8
  actual := T.thetaPilot
  actual_strip := rfl
  indStep := T.IndStep
  indStep_strip := fun _ _ _ => rfl
  hull := fun _ => T.container
  hull_strip := fun _ _ hF hs => by
    obtain ⟨x, hx⟩ := hF
    exact hs x hx

theorem layer_possible_subset_aux :
    ∀ y : T.primeStripLayer.Output, T.primeStripLayer.Possible y → y ∈ T.Possible := by
  intro y hy
  induction hy with
  | actual => exact T.theta_possible
  | ind _ hstep ih =>
    rcases hstep with h1 | h2 | h3
    · exact T.ind1_closed _ ih _ h1
    · exact T.ind2_closed _ ih _ h2
    · exact T.ind3_saturated _ ih _ (fun i => (h3 i).1) (fun i => (h3 i).2)
  | hull _ _ _ _ => exact T.container_possible

theorem layer_possible_subset {x : ∀ i, (T.S i).Regions} (hx : x ∈ T.primeStripLayer.possible) :
    x ∈ T.Possible :=
  T.layer_possible_subset_aux x hx

theorem layer_possible_eq (hlow : ∀ y ∈ T.Possible, ∀ i, RegionLE (T.S i) (T.thetaPilot i) (y i)) :
    T.primeStripLayer.possible = T.Possible := by
  ext y
  refine ⟨T.layer_possible_subset, fun hy => ?_⟩
  show T.primeStripLayer.Possible y
  exact AlgorithmSetting.Possible.ind AlgorithmSetting.Possible.actual
    (Or.inr (Or.inr fun i => ⟨hlow y hy i, T.ind3_bound y hy i⟩))

theorem layer_ipl : ∀ x ∈ T.primeStripLayer.possible, T.primeStripLayer.Linked x :=
  T.primeStripLayer.ipl

def layerLoop : LoopData T.primeStripLayer where
  hullTarget := obj 9
  sq3 := idHom 8 9
  sq4 := inv (inv T.primeStripLayer.thetaLink ≫ T.primeStripLayer.diagram.iplComposite ≫ idHom 8 9)
  sq3Twist := ∅
  sq4Twist := ∅

theorem layer_holonomy_trivial : T.layerLoop.loopArrow (𝟙 _) (𝟙 _) = 𝟙 _ := by
  simp [LoopData.loopArrow, layerLoop]

theorem layer_closed_before_sq5 : T.layerLoop.ClosedUpToFormalQuotient completedBeforeSQ5 :=
  T.layerLoop.closed_before_sq5

theorem layer_volume_production_implies_conclusion
    (h : ∃ x ∈ T.primeStripLayer.possible,
      (∀ i, (T.S i).HasVolume (x i)) ∧ ∑ i, (T.S i).procVol (x i) = T.negLogQ) :
    T.Conclusion := by
  obtain ⟨x, hx, hv, he⟩ := h
  exact T.pilotVolumeMatch_implies_conclusion ⟨x, T.layer_possible_subset hx, hv, he⟩

theorem layer_on_every_cited_theory :
    T.primeStripLayer.possible ⊆ T.Possible ∧
      (∀ x ∈ T.primeStripLayer.possible, T.primeStripLayer.Linked x) ∧
      T.layerLoop.ClosedUpToFormalQuotient completedBeforeSQ5 ∧
      T.layerLoop.loopArrow (𝟙 _) (𝟙 _) = 𝟙 _ :=
  ⟨fun _ hx => T.layer_possible_subset hx, T.layer_ipl, T.layer_closed_before_sq5,
    T.layer_holonomy_trivial⟩

theorem restricted_hull_vol_le (P : Set (∀ i, (T.S i).Regions)) (hP : P ⊆ T.Possible)
    (h : ∀ i, (T.S i).Regions)
    (hmin : ∀ U : (∀ i, (T.S i).Regions), (∀ i vQ j, T.IsLambdaO i vQ j (U i vQ j)) →
      (∀ x ∈ P, ∀ i, RegionLE (T.S i) (x i) (U i)) → ∀ i, RegionLE (T.S i) (h i) (U i))
    (hv : ∀ i, (T.S i).HasVolume (h i)) : ∑ i, (T.S i).procVol (h i) ≤ T.negLogTheta := by
  have hle := hmin T.hull T.hull_isLambdaO (fun x hx => T.hull_contains x (hP hx))
  exact Finset.sum_le_sum fun i _ =>
    (T.S i).procVol_ind3 (fun vQ j => ⟨hle i vQ j, T.hull_le_integral i vQ j⟩) (hv i)

theorem restriction_cannot_rescue (hnc : ¬ T.Conclusion) (P : Set (∀ i, (T.S i).Regions))
    (hP : P ⊆ T.Possible) (h : ∀ i, (T.S i).Regions)
    (hmin : ∀ U : (∀ i, (T.S i).Regions), (∀ i vQ j, T.IsLambdaO i vQ j (U i vQ j)) →
      (∀ x ∈ P, ∀ i, RegionLE (T.S i) (x i) (U i)) → ∀ i, RegionLE (T.S i) (h i) (U i))
    (hv : ∀ i, (T.S i).HasVolume (h i)) : ∑ i, (T.S i).procVol (h i) < T.negLogQ := by
  have h1 := T.restricted_hull_vol_le P hP h hmin hv
  have h2 : T.negLogTheta < T.negLogQ := lt_of_not_ge hnc
  linarith

end CitedTheoryFam

variable {κ : Type} [Fintype κ] (E : κ → ExtraPlace)

theorem layer_does_not_produce_q_value_enlarged (c : ℕ) :
    ∃ (N : ℕ) (hc : c ≤ 29 * N) (hq : (N : ℝ) * unitVolP + extraQ E < 0)
      (hθ : (N : ℝ) * (14 / 3) * unitVolP + extraTheta E < 0)
      (hC : (N : ℝ) * (14 / 3) * unitVolP + (c : ℝ) / 7 * Real.log 211 + extraTheta E < 0),
      let T := famModelC E N c hc hq hθ hC
      T.WeakSHE ∧
        T.primeStripLayer.possible = T.Possible ∧
        (∀ x ∈ T.primeStripLayer.possible, T.primeStripLayer.Linked x) ∧
        T.layerLoop.ClosedUpToFormalQuotient completedBeforeSQ5 ∧
        T.layerLoop.loopArrow (𝟙 _) (𝟙 _) = 𝟙 _ ∧
        ¬ T.primeStripLayer.ScalarProduction (fun x => ∑ i, (T.S i).procVol (x i)) T.negLogQ ∧
        ¬ T.Conclusion := by
  obtain ⟨N, hc, hq, hθ, hC, hw, hnot⟩ := robust_enlarged E c
  refine ⟨N, hc, hq, hθ, hC, ?_⟩
  intro T
  have heq : T.primeStripLayer.possible = T.Possible :=
    T.layer_possible_eq (fun y hy i => (hy i).1)
  refine ⟨hw, heq, T.layer_ipl, T.layer_closed_before_sq5, T.layer_holonomy_trivial, ?_, hnot⟩
  rintro ⟨x, hx, he⟩
  have hxP : x ∈ famPoss E N c := T.layer_possible_subset hx
  exact hnot (T.layer_volume_production_implies_conclusion
    ⟨x, hx, famPoss_hasVolume E N c hxP, he⟩)

end CitedLV.Independence.Cor312CitedFamily

section Check
open CitedLV.Independence.Cor312Cited
open CitedLV.Independence.Cor312CitedFamily
end Check
