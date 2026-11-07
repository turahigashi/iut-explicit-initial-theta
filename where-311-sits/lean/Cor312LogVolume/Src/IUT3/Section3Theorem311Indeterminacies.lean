import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Src.IUT3.Theorem311

open MeasureTheory
open scoped Pointwise

section LogVolume

noncomputable def logVolume {P : Type*} [MeasurableSpace P] (μ : Measure P) (O A : Set P) : ℝ :=
  Real.log (μ A).toReal - Real.log (μ O).toReal

theorem logVolume_self {P : Type*} [MeasurableSpace P] (μ : Measure P) (O : Set P) :
    logVolume μ O O = 0 :=
  sub_self _

theorem measure_pos_ne_top {P : Type*} [TopologicalSpace P] [MeasurableSpace P] (μ : Measure P)
    [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    {O : Set P} (hOc : IsCompact O) (hOi : (interior O).Nonempty) : μ O ≠ 0 ∧ μ O ≠ ⊤ := by
  refine ⟨fun h => ?_, hOc.measure_lt_top.ne⟩
  exact (isOpen_interior.measure_pos μ hOi).ne' (measure_mono_null interior_subset h)

theorem image_eq_preimage_symm {P : Type*} [AddCommGroup P] [TopologicalSpace P]
    (e : P ≃ₜ+ P) (A : Set P) : e '' A = e.symm ⁻¹' A :=
  e.toEquiv.image_eq_preimage_symm A

theorem symm_preimage_eq {P : Type*} [AddCommGroup P] [TopologicalSpace P]
    {O : Set P} (e : P ≃ₜ+ P) (he : e ⁻¹' O = O) : e.symm ⁻¹' O = O := by
  rw [← image_eq_preimage_symm]
  conv_lhs => rw [← he]
  exact Set.image_preimage_eq O e.surjective

variable {P : Type*} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
  [LocallyCompactSpace P] [MeasurableSpace P] [BorelSpace P]

theorem measure_preimage_eq (μ : Measure P) [μ.IsAddHaarMeasure] [μ.Regular]
    {O : Set P} (hOc : IsCompact O) (hOi : (interior O).Nonempty)
    (e : P ≃ₜ+ P) (he : e ⁻¹' O = O) (X : Set P) : μ (e ⁻¹' X) = μ X := by
  obtain ⟨hpos, htop⟩ := measure_pos_ne_top μ hOc hOi
  have h1 := addEquivAddHaarChar_smul_preimage μ (X := O) e
  rw [he, ENNReal.smul_def, smul_eq_mul] at h1
  have hc : (addEquivAddHaarChar e : ENNReal) = 1 := (ENNReal.mul_eq_right hpos htop).1 h1
  have h2 := addEquivAddHaarChar_smul_preimage μ (X := X) e
  rwa [ENNReal.smul_def, smul_eq_mul, hc, one_mul] at h2

theorem logVolume_image_eq (μ : Measure P) [μ.IsAddHaarMeasure] [μ.Regular]
    {O : Set P} (hOc : IsCompact O) (hOi : (interior O).Nonempty)
    (e : P ≃ₜ+ P) (he : e ⁻¹' O = O) (A : Set P) :
    logVolume μ O (e '' A) = logVolume μ O A := by
  unfold logVolume
  rw [image_eq_preimage_symm, measure_preimage_eq μ hOc hOi e.symm (symm_preimage_eq e he)]

end LogVolume

structure ProcessionLabelMorphism (n m : ℕ) where
  stageMap : Fin (n + 1) → Fin (m + 1)
  stageMap_strictMono : StrictMono stageMap
  labelMap : ∀ j : Fin (n + 1), Fin (j.val + 1) ↪ Fin ((stageMap j).val + 1)

namespace ProcessionLabelMorphism

variable {n : ℕ} (f : ProcessionLabelMorphism n n)

theorem stageMap_eq_id : f.stageMap = id := by
  have hsurj : Function.Surjective f.stageMap :=
    Finite.surjective_of_injective f.stageMap_strictMono.injective
  exact (f.stageMap_strictMono.range_inj strictMono_id).1 (by rw [hsurj.range_eq, Set.range_id])

theorem labelMap_bijective (j : Fin (n + 1)) : Function.Bijective (f.labelMap j) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨(f.labelMap j).injective, by simp [congrFun f.stageMap_eq_id j]⟩

end ProcessionLabelMorphism

structure PacketSystem : Type 1 where

  lstar : ℕ
  lstar_pos : 0 < lstar

  PlaceQ : Type
  [placeQFintype : Fintype PlaceQ]
  IsArch : PlaceQ → Prop

  Above : PlaceQ → Type
  [aboveFintype : ∀ vQ, Fintype (Above vQ)]

  Packet : PlaceQ → Fin (lstar + 1) → Type
  [addCommGroup : ∀ vQ j, AddCommGroup (Packet vQ j)]
  [topologicalSpace : ∀ vQ j, TopologicalSpace (Packet vQ j)]
  [isTopologicalAddGroup : ∀ vQ j, IsTopologicalAddGroup (Packet vQ j)]
  [locallyCompactSpace : ∀ vQ j, LocallyCompactSpace (Packet vQ j)]
  [measurableSpace : ∀ vQ j, MeasurableSpace (Packet vQ j)]
  [borelSpace : ∀ vQ j, BorelSpace (Packet vQ j)]
  haar : ∀ vQ j, Measure (Packet vQ j)
  [isAddHaarMeasure : ∀ vQ j, (haar vQ j).IsAddHaarMeasure]
  [regular : ∀ vQ j, (haar vQ j).Regular]

  integral : ∀ vQ j, Set (Packet vQ j)
  integral_isCompact : ∀ vQ j, IsCompact (integral vQ j)
  integral_interior_nonempty : ∀ vQ j, (interior (integral vQ j)).Nonempty

  weight : PlaceQ → Fin (lstar + 1) → ℝ
  weight_pos : ∀ vQ j, 0 < weight vQ j

  adjustment : PlaceQ → Fin (lstar + 1) → ℝ

  StripAut : ∀ vQ, Above vQ → Type
  [stripAutGroup : ∀ vQ v, Group (StripAut vQ v)]

  Ism : ∀ vQ, Above vQ → Type
  [ismGroup : ∀ vQ v, Group (Ism vQ v)]
  ism_arch_order_two : ∀ vQ, IsArch vQ → ∀ v (g : Ism vQ v), g * g = 1

  labelAct : ∀ vQ (j : Fin (lstar + 1)), Equiv.Perm (Fin (j.val + 1)) →
    (Packet vQ j ≃ₜ+ Packet vQ j)

  stripAct : ∀ vQ (j : Fin (lstar + 1)), (Fin (j.val + 1) → ∀ v, StripAut vQ v) →
    (Packet vQ j ≃ₜ+ Packet vQ j)

  ismAct : ∀ vQ (j : Fin (lstar + 1)), (Fin (j.val + 1) → ∀ v, Ism vQ v) →
    (Packet vQ j ≃ₜ+ Packet vQ j)
  labelAct_one : ∀ vQ j, labelAct vQ j 1 = ContinuousAddEquiv.refl _
  labelAct_mul : ∀ vQ j σ τ, labelAct vQ j (σ * τ) = (labelAct vQ j τ).trans (labelAct vQ j σ)
  stripAct_one : ∀ vQ j, stripAct vQ j 1 = ContinuousAddEquiv.refl _
  stripAct_mul : ∀ vQ j g h, stripAct vQ j (g * h) = (stripAct vQ j h).trans (stripAct vQ j g)
  ismAct_one : ∀ vQ j, ismAct vQ j 1 = ContinuousAddEquiv.refl _
  ismAct_mul : ∀ vQ j g h, ismAct vQ j (g * h) = (ismAct vQ j h).trans (ismAct vQ j g)
  labelAct_integral : ∀ vQ j σ, labelAct vQ j σ ⁻¹' integral vQ j = integral vQ j
  stripAct_integral : ∀ vQ j g, stripAct vQ j g ⁻¹' integral vQ j = integral vQ j
  ismAct_integral : ∀ vQ j g, ismAct vQ j g ⁻¹' integral vQ j = integral vQ j

namespace PacketSystem

attribute [instance] placeQFintype aboveFintype addCommGroup topologicalSpace isTopologicalAddGroup
  locallyCompactSpace measurableSpace borelSpace isAddHaarMeasure regular stripAutGroup ismGroup

variable (S : PacketSystem)

abbrev Regions : Type := ∀ (vQ : S.PlaceQ) (j : Fin (S.lstar + 1)), Set (S.Packet vQ j)

noncomputable def packetLogVolume (vQ : S.PlaceQ) (j : Fin (S.lstar + 1)) (A : Set (S.Packet vQ j)) :
    ℝ :=
  S.weight vQ j * logVolume (S.haar vQ j) (S.integral vQ j) A + S.adjustment vQ j

noncomputable def procVol (x : S.Regions) : ℝ :=
  ∑ vQ, (∑ j : Fin S.lstar, S.packetLogVolume vQ j.succ (x vQ j.succ)) / (S.lstar : ℝ)

theorem packetLogVolume_image (vQ : S.PlaceQ) (j : Fin (S.lstar + 1))
    (e : S.Packet vQ j ≃ₜ+ S.Packet vQ j) (he : e ⁻¹' S.integral vQ j = S.integral vQ j)
    (A : Set (S.Packet vQ j)) :
    S.packetLogVolume vQ j (e '' A) = S.packetLogVolume vQ j A := by
  unfold packetLogVolume
  rw [logVolume_image_eq _ (S.integral_isCompact vQ j) (S.integral_interior_nonempty vQ j) e he]

structure ProcessionAut where
  labelPerm : ∀ j : Fin (S.lstar + 1), Equiv.Perm (Fin (j.val + 1))
  stripAut : ∀ j : Fin (S.lstar + 1), Fin (j.val + 1) → ∀ (vQ : S.PlaceQ) (v : S.Above vQ), S.StripAut vQ v

variable {S}

def ProcessionAut.packetAut (h : S.ProcessionAut) (vQ : S.PlaceQ) (j : Fin (S.lstar + 1)) :
    S.Packet vQ j ≃ₜ+ S.Packet vQ j :=
  (S.stripAct vQ j (fun α v => h.stripAut j α vQ v)).trans (S.labelAct vQ j (h.labelPerm j))

theorem ProcessionAut.packetAut_integral (h : S.ProcessionAut) (vQ : S.PlaceQ) (j : Fin (S.lstar + 1)) :
    h.packetAut vQ j ⁻¹' S.integral vQ j = S.integral vQ j := by
  rw [ProcessionAut.packetAut, ContinuousAddEquiv.coe_trans, Set.preimage_comp, S.labelAct_integral,
    S.stripAct_integral]

def ProcessionAut.act (h : S.ProcessionAut) (x : S.Regions) : S.Regions :=
  fun vQ j => h.packetAut vQ j '' x vQ j

variable (S)

def Ind1 (x y : S.Regions) : Prop :=
  ∃ h : S.ProcessionAut, y = h.act x

abbrev Ind2Element : Type :=
  ∀ (vQ : S.PlaceQ) (j : Fin (S.lstar + 1)), Fin (j.val + 1) → ∀ v : S.Above vQ, S.Ism vQ v

def ind2Act (g : S.Ind2Element) (x : S.Regions) : S.Regions :=
  fun vQ j => S.ismAct vQ j (g vQ j) '' x vQ j

def Ind2 (x y : S.Regions) : Prop :=
  ∃ g : S.Ind2Element, y = S.ind2Act g x

theorem procVol_ind1 {x y : S.Regions} (hxy : S.Ind1 x y) : S.procVol x = S.procVol y := by
  obtain ⟨h, rfl⟩ := hxy
  unfold procVol
  refine Finset.sum_congr rfl fun vQ _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (S.packetLogVolume_image vQ j.succ (h.packetAut vQ j.succ) (h.packetAut_integral vQ j.succ)
    (x vQ j.succ)).symm

theorem procVol_ind2 {x y : S.Regions} (hxy : S.Ind2 x y) : S.procVol x = S.procVol y := by
  obtain ⟨g, rfl⟩ := hxy
  unfold procVol
  refine Finset.sum_congr rfl fun vQ _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (S.packetLogVolume_image vQ j.succ (S.ismAct vQ j.succ (g vQ j.succ))
    (S.ismAct_integral vQ j.succ _) (x vQ j.succ)).symm

def IndRel (x y : S.Regions) : Prop :=
  S.Ind1 x y ∨ S.Ind2 x y

def RLGP : Type :=
  Quot S.IndRel

noncomputable def coarseVolume : S.RLGP → ℝ :=
  Quot.lift S.procVol fun _ _ h => h.elim (S.procVol_ind1) (S.procVol_ind2)

theorem coarseVolume_mk (x : S.Regions) : S.coarseVolume (Quot.mk _ x) = S.procVol x :=
  rfl

end PacketSystem

noncomputable section Model

open Metric

def permPacketAut (k : ℕ) (σ : Equiv.Perm (Fin k)) : (Fin k → ℝ) ≃ₜ+ (Fin k → ℝ) where
  toFun z := z ∘ σ.symm
  invFun z := z ∘ σ
  left_inv z := by ext α; simp
  right_inv z := by ext α; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

theorem units_int_mul_self_real (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

def signPacketAut (k : ℕ) (g : Fin k → Unit → ℤˣ) : (Fin k → ℝ) ≃ₜ+ (Fin k → ℝ) where
  toFun z α := ((g α () : ℤ) : ℝ) * z α
  invFun z α := ((g α () : ℤ) : ℝ) * z α
  left_inv z := by ext α; simp [← mul_assoc, units_int_mul_self_real]
  right_inv z := by ext α; simp [← mul_assoc, units_int_mul_self_real]
  map_add' z w := by ext α; simp [mul_add]
  continuous_toFun := continuous_pi fun α => continuous_const.mul (continuous_apply α)
  continuous_invFun := continuous_pi fun α => continuous_const.mul (continuous_apply α)

theorem closedBall_pi_iff {k : ℕ} (z : Fin k → ℝ) : z ∈ closedBall (0 : Fin k → ℝ) 1 ↔ ∀ α, |z α| ≤ 1 := by
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  simp only [Real.norm_eq_abs]

theorem permPacketAut_integral (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    permPacketAut k σ ⁻¹' closedBall 0 1 = closedBall 0 1 := by
  ext z
  simp only [Set.mem_preimage, closedBall_pi_iff]
  exact ⟨fun h α => by simpa [permPacketAut] using h (σ α), fun h α => h _⟩

theorem signPacketAut_integral (k : ℕ) (g : Fin k → Unit → ℤˣ) :
    signPacketAut k g ⁻¹' closedBall 0 1 = closedBall 0 1 := by
  ext z
  simp only [Set.mem_preimage, closedBall_pi_iff]
  refine forall_congr' fun α => ?_
  change |((g α () : ℤ) : ℝ) * z α| ≤ 1 ↔ |z α| ≤ 1
  rcases Int.units_eq_one_or (g α ()) with h | h <;> simp [h]

def modelSystem : PacketSystem where
  lstar := 2
  lstar_pos := by norm_num
  PlaceQ := Unit
  IsArch := fun _ => True
  Above := fun _ => Unit
  Packet := fun _ j => Fin (j.val + 1) → ℝ
  haar := fun _ _ => volume
  integral := fun _ _ => closedBall 0 1
  integral_isCompact := fun _ _ => isCompact_closedBall 0 1
  integral_interior_nonempty := fun _ _ =>
    ⟨0, ball_subset_interior_closedBall (mem_ball_self one_pos)⟩
  weight := fun _ j => 1 / ((j.val : ℝ) + 1)
  weight_pos := fun _ _ => by positivity
  adjustment := fun _ _ => 0
  StripAut := fun _ _ => Unit
  Ism := fun _ _ => ℤˣ
  ism_arch_order_two := fun _ _ _ g => Int.units_mul_self g
  labelAct := fun _ j σ => permPacketAut (j.val + 1) σ
  stripAct := fun _ _ _ => ContinuousAddEquiv.refl _
  ismAct := fun _ j g => signPacketAut (j.val + 1) g
  labelAct_one := fun _ _ => rfl
  labelAct_mul := fun _ _ _ _ => rfl
  stripAct_one := fun _ _ => rfl
  stripAct_mul := fun _ _ _ _ => rfl
  ismAct_one := fun _ _ => by ext z α; simp [signPacketAut]
  ismAct_mul := fun _ _ g h => by ext z α; simp [signPacketAut, mul_assoc]
  labelAct_integral := fun _ j σ => permPacketAut_integral (j.val + 1) σ
  stripAct_integral := fun _ _ _ => rfl
  ismAct_integral := fun _ j g => signPacketAut_integral (j.val + 1) g

theorem logVolume_two_smul (k : ℕ) :
    logVolume (volume : Measure (Fin k → ℝ)) (closedBall 0 1) ((2 : ℝ) • closedBall 0 1) =
      k * Real.log 2 := by
  obtain ⟨hpos, htop⟩ := measure_pos_ne_top (volume : Measure (Fin k → ℝ))
    (isCompact_closedBall (0 : Fin k → ℝ) 1) ⟨0, ball_subset_interior_closedBall (mem_ball_self one_pos)⟩
  have hreal : (volume (closedBall (0 : Fin k → ℝ) 1)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨hpos, htop⟩
  unfold logVolume
  rw [Measure.addHaar_smul, Module.finrank_fin_fun, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (by positivity),
    Real.log_mul (by positivity) hreal, Real.log_pow]
  ring

def integralRegions : modelSystem.Regions :=
  fun _ j => (show Set (Fin (j.val + 1) → ℝ) from closedBall 0 1)

def scaledRegions : modelSystem.Regions :=
  fun _ j => (2 : ℝ) • closedBall (0 : Fin (j.val + 1) → ℝ) 1

theorem model_procVol_integral : modelSystem.procVol integralRegions = 0 := by
  unfold PacketSystem.procVol
  refine Finset.sum_eq_zero fun vQ _ => ?_
  rw [Finset.sum_eq_zero fun j _ => ?_, zero_div]
  change 1 / ((j.succ.val : ℝ) + 1) *
    logVolume (volume : Measure (Fin (j.succ.val + 1) → ℝ)) (closedBall 0 1) (closedBall 0 1) + 0 = 0
  rw [logVolume_self, mul_zero, add_zero]

theorem model_procVol_scaled_pos : 0 < modelSystem.procVol scaledRegions := by
  have hterm : ∀ (vQ : modelSystem.PlaceQ) (j : Fin modelSystem.lstar),
      0 < modelSystem.packetLogVolume vQ j.succ (scaledRegions vQ j.succ) := by
    intro vQ j
    change 0 < 1 / ((j.succ.val : ℝ) + 1) * logVolume (volume : Measure (Fin (j.succ.val + 1) → ℝ))
      (closedBall 0 1) ((2 : ℝ) • closedBall 0 1) + 0
    rw [logVolume_two_smul, add_zero]
    exact mul_pos (by positivity) (mul_pos (by positivity) (Real.log_pos one_lt_two))
  have hl : (0 : ℝ) < modelSystem.lstar := by exact_mod_cast modelSystem.lstar_pos
  unfold PacketSystem.procVol
  exact Finset.sum_pos (fun vQ _ => div_pos (Finset.sum_pos (fun j _ => hterm vQ j)
    ⟨⟨0, modelSystem.lstar_pos⟩, Finset.mem_univ _⟩) hl) ⟨(), Finset.mem_univ _⟩

def twoSmulAut (k : ℕ) : (Fin k → ℝ) ≃ₜ+ (Fin k → ℝ) where
  toFun z := (2 : ℝ) • z
  invFun z := (1 / 2 : ℝ) • z
  left_inv z := by simp [smul_smul]
  right_inv z := by simp [smul_smul]
  map_add' z w := smul_add _ _ _
  continuous_toFun := continuous_const.smul continuous_id
  continuous_invFun := continuous_const.smul continuous_id

theorem twoSmulAut_changes_logVolume (k : ℕ) (hk : 0 < k) :
    logVolume (volume : Measure (Fin k → ℝ)) (closedBall 0 1) (twoSmulAut k '' closedBall 0 1) ≠
      logVolume (volume : Measure (Fin k → ℝ)) (closedBall 0 1) (closedBall 0 1) := by
  have himg : twoSmulAut k '' closedBall 0 1 = (2 : ℝ) • closedBall (0 : Fin k → ℝ) 1 := by
    change (fun z : Fin k → ℝ => (2 : ℝ) • z) '' closedBall 0 1 = _
    exact Set.image_smul
  rw [himg, logVolume_two_smul, logVolume_self]
  exact (mul_pos (by exact_mod_cast hk) (Real.log_pos one_lt_two)).ne'

def halfSpace (k : ℕ) : Set (Fin (k + 1) → ℝ) :=
  {z | 0 ≤ z 0}

def halfRegions : modelSystem.Regions :=
  fun _ j => halfSpace j.val

theorem model_ind2_nontrivial :
    ∃ x y : modelSystem.Regions, modelSystem.Ind2 x y ∧ x ≠ y := by
  let g : modelSystem.Ind2Element := fun _ _ _ _ => (-1 : ℤˣ)
  refine ⟨halfRegions, modelSystem.ind2Act g halfRegions, ⟨g, rfl⟩, fun hxy => ?_⟩
  have h0 := congrFun (congrFun hxy ()) 0
  have hmem : (fun _ : Fin 1 => (-1 : ℝ)) ∈ modelSystem.ind2Act g halfRegions () 0 := by
    refine ⟨fun _ : Fin 1 => (1 : ℝ), ?_, ?_⟩
    · change (0 : ℝ) ≤ 1
      norm_num
    · funext α
      change (((-1 : ℤˣ) : ℤ) : ℝ) * 1 = -1
      simp
  rw [← h0] at hmem
  change (0 : ℝ) ≤ -1 at hmem
  norm_num at hmem

theorem model_ind1_nontrivial :
    ∃ x y : modelSystem.Regions, modelSystem.Ind1 x y ∧ x ≠ y := by
  let h : modelSystem.ProcessionAut := ⟨fun j => finRotate (j.val + 1), fun _ _ _ _ => ()⟩
  refine ⟨halfRegions, h.act halfRegions, ⟨h, rfl⟩, fun hxy => ?_⟩
  have h1 := congrFun (congrFun hxy ()) 1
  let w : Fin 2 → ℝ := fun α => if α = 0 then 1 else -1
  have hx : w ∈ halfRegions () 1 := by
    change (0 : ℝ) ≤ w 0
    simp [w]
  rw [h1] at hx
  obtain ⟨z, hz, hzw⟩ := hx
  have hw1 : w 1 = z ((finRotate 2).symm 1) := (congrFun hzw 1).symm
  have hwv : w 1 = -1 := by simp [w]
  have hz' : (0 : ℝ) ≤ z ((finRotate 2).symm 1) := by
    have hrot : (finRotate 2).symm 1 = 0 := by decide
    rw [hrot]
    exact hz
  linarith

theorem model_nondegenerate :
    (∃ x y : modelSystem.Regions, modelSystem.Ind1 x y ∧ x ≠ y) ∧
      (∃ x y : modelSystem.Regions, modelSystem.Ind2 x y ∧ x ≠ y) ∧
      modelSystem.procVol integralRegions = 0 ∧
      0 < modelSystem.procVol scaledRegions ∧
      logVolume (volume : Measure (Fin 1 → ℝ)) (closedBall 0 1) (twoSmulAut 1 '' closedBall 0 1) ≠
        logVolume (volume : Measure (Fin 1 → ℝ)) (closedBall 0 1) (closedBall 0 1) :=
  ⟨model_ind1_nontrivial, model_ind2_nontrivial, model_procVol_integral, model_procVol_scaled_pos,
    twoSmulAut_changes_logVolume 1 one_pos⟩

end Model

end Src.IUT3.Theorem311

section Check
open Src.IUT3.Theorem311
end Check
