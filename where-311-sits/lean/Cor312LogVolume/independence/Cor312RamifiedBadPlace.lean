import Cor312LogVolume.thetalink.GaussianThetaHorizontalVerticalPrincipalHull
import Cor312LogVolume.independence.Cor312CitedPrimeStripLayer
import Cor312LogVolume.thetalink.P211FiniteLocalField
import Cor312LogVolume.Src.EtTh.Section1ThetaValueAnalyticFacts

set_option autoImplicit false
noncomputable section

namespace CitedLV.Independence.Cor312RamifiedBadPlace

open MeasureTheory
open Src.IUT3.Theorem311
open CitedLV.Theorem311 CitedLV.Theorem311.TensorIntegralLattice
open CitedLV.Theorem311.TensorFactorHaarCharacter
open CitedLV.Theorem311.PadicNormedRamification
open CitedLV.Theorem311.PadicNormDifferent
open CitedLV.Theorem311.PadicNormIntegerRing
open CitedLV.ActualTensorHaarBound
open CitedLV.ThetaLink.GaussianThetaHorizontalVerticalHull
open CitedLV.ThetaLink.GaussianThetaHorizontalVerticalPrincipalHull
open CitedLV.ThetaLink.GaussianMonoidFromThetaValues
open CitedLV.ThetaLink.GaussianThetaLogReadout
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Independence.Cor312Cited
open Src.EtTh.ThetaValueArithmetic
open Src.IUT4.Proposition12i Src.IUT4.Proposition12ii

section General

variable (p : ℕ) [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Lf : ι → Type*)
  [∀ i, NormedField (Lf i)] [∀ i, NormedAlgebra ℚ_[p] (Lf i)]
  [∀ i, IsUltrametricDist (Lf i)] [∀ i, FiniteDimensional ℚ_[p] (Lf i)]
  [∀ i, CompleteSpace (Lf i)] [∀ i, ProperSpace (Lf i)]
  [∀ i, Algebra ℤ_[p] (Lf i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (Lf i)]

theorem boundRegion_subset_anchor (i₀ : ι) (k : ℤ)
    (hk : bI p (fun i => finiteExtensionRamification p (Lf i)) ≤ (boundExponent p Lf i₀ k : ℝ)) :
    (boundRegion p Lf i₀ k).val ⊆ (integralAnchor p Lf).val := by
  rintro y ⟨w, hw, rfl⟩
  change IsIntegral ℤ_[p] w at hw
  change IsIntegral ℤ_[p] (boundEquiv p Lf i₀ k w)
  rw [boundEquiv_apply]
  set R := fun i => finiteExtensionRamification p (Lf i) with hR
  have hsum : ∑ i, (((-bNum p (R i).e : ℤ) : ℝ) / (R i).e) = -bI p R := by
    unfold bI
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have he : ((R i).e : ℝ) ≠ 0 := by exact_mod_cast (R i).e_pos.ne'
    push_cast
    rw [bNum_eq p (R i).e (R i).e_pos]
    field_simp
  have hpi : IsIntegral ℤ_[p] (((p : ℚ_[p]) ^ boundExponent p Lf i₀ k) • piNegB p R) := by
    unfold piNegB
    refine isIntegral_zpow_smul_tprod p R (fun i => (R i).pi ^ (-bNum p (R i).e))
      (fun i => -bNum p (R i).e) (fun i => norm_zpow _ _) _ ?_
    rw [hsum]
    linarith
  have h := hpi.mul hw
  rw [smul_mul_assoc] at h
  exact h

omit [∀ i, CompleteSpace (Lf i)] [∀ i, ProperSpace (Lf i)] in

theorem factorRegion_subset_anchor (i : ι) (a : (Lf i)ˣ) (ha : ‖(a : Lf i)‖ ≤ 1) :
    (factorRegion p Lf i a (integralAnchor p Lf)).val ⊆ (integralAnchor p Lf).val := by
  rintro y ⟨w, hw, rfl⟩
  change IsIntegral ℤ_[p] w at hw
  change IsIntegral ℤ_[p] ((factorUnit p Lf i a : Packet p Lf) * w)
  have ha' : IsIntegral ℤ_[p] (a : Lf i) := SrcLib.PadicLog.isIntegral_of_norm_le_one ha
  have hf : IsIntegral ℤ_[p] (factorHom p Lf i (a : Lf i)) := ha'.map (factorHom p Lf i)
  exact hf.mul hw

def errCoeff : ℝ := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (Lf i)) :=
    fun i => normIntegers_discreteValuationRing p (Lf i)
  exact bI p (fun i => finiteExtensionRamification p (Lf i)) +
    dI p (actualDifferentData p Lf).val + aI p (fun i => finiteExtensionRamification p (Lf i)) + 1

omit [DecidableEq ι] [∀ i, CompleteSpace (Lf i)] [∀ i, ProperSpace (Lf i)] in

theorem bI_sub_boundExponent_le (i₀ : ι) (k : ℤ) :
    bI p (fun i => finiteExtensionRamification p (Lf i)) - (boundExponent p Lf i₀ k : ℝ) ≤
      errCoeff p Lf - (k : ℝ) / (finiteExtensionRamification p (Lf i₀)).e := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (Lf i)) :=
    fun i => normIntegers_discreteValuationRing p (Lf i)
  have h := Int.sub_one_lt_floor ((k : ℝ) / (finiteExtensionRamification p (Lf i₀)).e -
    dI p (actualDifferentData p Lf).val - aI p (fun i => finiteExtensionRamification p (Lf i)))
  have hb : (boundExponent p Lf i₀ k : ℤ) = ⌊(k : ℝ) / (finiteExtensionRamification p (Lf i₀)).e -
      dI p (actualDifferentData p Lf).val - aI p (fun i => finiteExtensionRamification p (Lf i))⌋ := rfl
  have he : errCoeff p Lf = bI p (fun i => finiteExtensionRamification p (Lf i)) +
      dI p (actualDifferentData p Lf).val + aI p (fun i => finiteExtensionRamification p (Lf i)) + 1 := rfl
  rw [hb, he]
  linarith

end General

section OneField

variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [FiniteDimensional ℚ_[p] K]

theorem k_div_e_log (x : K) (N : ℕ) (k : ℤ)
    (hk : ‖x‖ ^ N = ‖(finiteExtensionRamification p K).pi‖ ^ k) :
    (k : ℝ) / (finiteExtensionRamification p K).e * Real.log p = -((N : ℝ) * Real.log ‖x‖) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have he : ((finiteExtensionRamification p K).e : ℝ) ≠ 0 := by
    exact_mod_cast (finiteExtensionRamification p K).e_pos.ne'
  have hl := congrArg Real.log hk
  rw [Real.log_pow, Real.log_zpow, (finiteExtensionRamification p K).norm_pi,
    Real.log_rpow hp] at hl
  rw [hl]
  field_simp

end OneField

section Shapes

variable (L : Type)

abbrev KU : Unit → Type := fun _ => L

abbrev ch (j : ℕ) : Fin (j + 1) → Unit := fun _ => ()

abbrev LL (j : ℕ) : Fin (j + 1) → Type := fun t => KU L (ch j t)

end Shapes

def labOf (j : ℕ) : Labels 7 := ⟨min (j - 1) 2, by show min (j - 1) 2 < 3; omega⟩

theorem labOf_succ (k : Fin 3) : labOf (k.val + 1) = (k : Labels 7) :=
  Fin.ext (by simp only [labOf, Nat.add_sub_cancel]; have := k.isLt; omega)

section System

variable (p : ℕ) [Fact p.Prime]
variable (L : Type) [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
  [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]

abbrev PP (j : ℕ) := Packet p (LL L j)

abbrev anchor (j : ℕ) : NormalizedHaarRegion (PP p L j) := integralAnchor p (LL L j)

omit [CompleteSpace L] in
theorem finrank_pos (j : ℕ) : (0 : ℝ) < Module.finrank ℚ_[p] (PP p L j) := by
  exact_mod_cast packet_finrank_pos p (LL L j)

def rampSystem : PacketSystem where
  lstar := 3
  lstar_pos := by norm_num
  PlaceQ := Unit
  IsArch := fun _ => False
  Above := fun _ => Unit
  Packet := fun _ j => PP p L j.val
  haar := fun _ j => normalizedAddHaar (anchor p L j.val)
  integral := fun _ j => (anchor p L j.val).val
  integral_isCompact := fun _ j => (anchor p L j.val).2.1.1
  integral_interior_nonempty := fun _ j => by
    rw [(anchor p L j.val).2.1.2.interior_eq]
    exact (anchor p L j.val).2.2
  weight := fun _ j => 1 / (Module.finrank ℚ_[p] (PP p L j.val) : ℝ)
  weight_pos := fun _ j => one_div_pos.mpr (finrank_pos p L j.val)
  adjustment := fun _ _ => 0
  StripAut := fun _ _ => Unit
  Ism := fun _ _ => Unit
  ism_arch_order_two := fun _ h => absurd h id
  labelAct := fun _ _ _ => ContinuousAddEquiv.refl _
  stripAct := fun _ _ _ => ContinuousAddEquiv.refl _
  ismAct := fun _ _ _ => ContinuousAddEquiv.refl _
  labelAct_one := fun _ _ => rfl
  labelAct_mul := fun _ _ _ _ => rfl
  stripAct_one := fun _ _ => rfl
  stripAct_mul := fun _ _ _ _ => rfl
  ismAct_one := fun _ _ => rfl
  ismAct_mul := fun _ _ _ _ => rfl
  labelAct_integral := fun _ _ _ => rfl
  stripAct_integral := fun _ _ _ => rfl
  ismAct_integral := fun _ _ _ => rfl

omit [CompleteSpace L] in
theorem stage_le (j : Fin ((rampSystem p L).lstar + 1)) : j.val ≤ 3 := Nat.lt_succ_iff.mp j.isLt

omit [CompleteSpace L] in
theorem act_eq (h : (rampSystem p L).ProcessionAut) (x : (rampSystem p L).Regions) : h.act x = x := by
  funext vQ j
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    exact ⟨z, hz, rfl⟩

omit [CompleteSpace L] in
theorem ind2Act_eq (g : (rampSystem p L).Ind2Element) (x : (rampSystem p L).Regions) :
    (rampSystem p L).ind2Act g x = x := by
  funext vQ j
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    exact ⟨z, hz, rfl⟩

omit [CompleteSpace L] in

theorem packetLogVolume_region (vQ : Unit) (j : Fin ((rampSystem p L).lstar + 1))
    (U : NormalizedHaarRegion (PP p L j.val)) :
    (rampSystem p L).packetLogVolume vQ j U.val =
      normalizedHaarLogVolume (anchor p L j.val) U / (Module.finrank ℚ_[p] (PP p L j.val) : ℝ) := by
  show (1 / (Module.finrank ℚ_[p] (PP p L j.val) : ℝ)) *
      logVolume (normalizedAddHaar (anchor p L j.val)) (anchor p L j.val).val U.val + 0 = _
  unfold logVolume normalizedHaarLogVolume normalizedHaarRealVolume
  rw [normalizedAddHaar_anchor]
  simp only [ENNReal.toReal_one, Real.log_one, sub_zero, add_zero]
  ring

omit [CompleteSpace L] in

theorem packetLogVolume_factor (vQ : Unit) (j : Fin ((rampSystem p L).lstar + 1)) (a : Lˣ) :
    (rampSystem p L).packetLogVolume vQ j (factorRegion p (LL L j.val) 0 a (anchor p L j.val)).val =
      Real.log ‖(a : L)‖ := by
  rw [packetLogVolume_region, logVolume_factorRegion, normalizedHaarLogVolume_anchor, add_zero]
  field_simp [(finrank_pos p L j.val).ne']

omit [CompleteSpace L] in

theorem procVol_eq (x : (rampSystem p L).Regions) :
    (rampSystem p L).procVol x =
      (∑ k : Fin 3, (rampSystem p L).packetLogVolume () k.succ (x () k.succ)) / 3 := by
  rw [PacketSystem.procVol]
  show (∑ _vQ : Unit, (∑ k : Fin 3, (rampSystem p L).packetLogVolume () k.succ (x () k.succ)) /
      ((3 : ℕ) : ℝ)) = _
  simp only [Finset.univ_unique, Finset.sum_singleton, Nat.cast_ofNat]

end System

section Datum

variable (L : Type) [NormedField L]

structure ThetaDatum where
  s : Lˣ
  i : Lˣ
  hi : i ^ 2 = -1
  facts : PublishedThetaFacts s i
  ξ : Labels 7 → Lˣ
  hξ : ξ ∈ actualProfiles s i 7
  r : Lˣ
  hr : r ^ (2 * 7) = s ^ 2
  hq : ‖((s ^ 2 : Lˣ) : L)‖ < 1

variable {L}

namespace ThetaDatum

variable (D : ThetaDatum L)

def Lq : ℝ := Real.log ‖((D.s ^ 2 : Lˣ) : L)‖

theorem Lq_neg : D.Lq < 0 :=
  Real.log_neg (norm_pos_iff.mpr (Units.ne_zero _)) D.hq

theorem norm_r_pow : ‖(D.r : L)‖ ^ (2 * 7) = ‖((D.s ^ 2 : Lˣ) : L)‖ := by
  have h := congrArg (fun u : Lˣ => ‖(u : L)‖) D.hr
  simpa only [Units.val_pow_eq_pow_val, norm_pow] using h

theorem norm_r_lt_one : ‖(D.r : L)‖ < 1 := by
  have h : ‖(D.r : L)‖ ^ (2 * 7) < 1 := by rw [D.norm_r_pow]; exact D.hq
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h

theorem log_r : Real.log ‖(D.r : L)‖ = D.Lq / 14 := by
  have h := congrArg Real.log D.norm_r_pow
  rw [Real.log_pow] at h
  unfold Lq
  rw [← h]
  push_cast
  ring

theorem log_xi (k : Labels 7) : Real.log ‖(D.ξ k : L)‖ = ((k.val : ℝ) + 1) ^ 2 / 14 * D.Lq := by
  rw [actualProfile_log_norm D.s D.i D.hi D.facts 7 (by norm_num) D.ξ D.hξ k]
  unfold Lq
  norm_num

end ThetaDatum

end Datum

section Regions

variable (p : ℕ) [Fact p.Prime]
variable {L : Type} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
  [IsUltrametricDist L] [FiniteDimensional ℚ_[p] L] [ProperSpace L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]
variable (D : ThetaDatum L) (N : ℕ)

theorem hullSpec (j : ℕ) :
    ∃ (k : ℤ) (c : (PP p L j)ˣ),
      ‖(D.ξ (labOf j) : L)‖ ^ N = ‖(finiteExtensionRamification p L).pi‖ ^ k ∧
      (unitRegion p (LL L j) c (anchor p L j)).val =
        (lambdaIntersection p (LL L j)
          (horizontalVerticalImages p (KU L) j (ch j) 0 D.s D.i 7 (labOf j) N) : Set (PP p L j)) ∧
      horizontalVerticalImages p (KU L) j (ch j) 0 D.s D.i 7 (labOf j) N ⊆
        (unitRegion p (LL L j) c (anchor p L j)).val ∧
      (unitRegion p (LL L j) c (anchor p L j)).val ⊆ (boundRegion p (LL L j) 0 k).val ∧
      (∀ d : (PP p L j)ˣ,
        horizontalVerticalImages p (KU L) j (ch j) 0 D.s D.i 7 (labOf j) N ⊆
          (unitRegion p (LL L j) d (anchor p L j)).val →
        (unitRegion p (LL L j) c (anchor p L j)).val ⊆ (unitRegion p (LL L j) d (anchor p L j)).val) ∧
      normalizedHaarLogVolume (anchor p L j) (unitRegion p (LL L j) c (anchor p L j)) /
          (Module.finrank ℚ_[p] (PP p L j) : ℝ) ≤
        (bI p (fun t => finiteExtensionRamification p (LL L j t)) -
          (boundExponent p (LL L j) 0 k : ℝ)) * Real.log (p : ℝ) :=
  gaussian_horizontal_vertical_principal_hull p (KU L) j (ch j) 0 D.s D.i D.hi D.facts 7
    (by norm_num) D.ξ D.hξ (labOf j) N

def hullK (j : ℕ) : ℤ := (hullSpec p D N j).choose

def hullC (j : ℕ) : (PP p L j)ˣ := (hullSpec p D N j).choose_spec.choose

theorem hullK_spec (j : ℕ) :
    ‖(D.ξ (labOf j) : L)‖ ^ N = ‖(finiteExtensionRamification p L).pi‖ ^ hullK p D N j :=
  (hullSpec p D N j).choose_spec.choose_spec.1

theorem images_subset_hull (j : ℕ) :
    horizontalVerticalImages p (KU L) j (ch j) 0 D.s D.i 7 (labOf j) N ⊆
      (unitRegion p (LL L j) (hullC p D N j) (anchor p L j)).val :=
  (hullSpec p D N j).choose_spec.choose_spec.2.2.1

theorem hull_subset_bound (j : ℕ) :
    (unitRegion p (LL L j) (hullC p D N j) (anchor p L j)).val ⊆
      (boundRegion p (LL L j) 0 (hullK p D N j)).val :=
  (hullSpec p D N j).choose_spec.choose_spec.2.2.2.1

theorem hull_least (j : ℕ) (d : (PP p L j)ˣ)
    (hd : horizontalVerticalImages p (KU L) j (ch j) 0 D.s D.i 7 (labOf j) N ⊆
      (unitRegion p (LL L j) d (anchor p L j)).val) :
    (unitRegion p (LL L j) (hullC p D N j) (anchor p L j)).val ⊆
      (unitRegion p (LL L j) d (anchor p L j)).val :=
  (hullSpec p D N j).choose_spec.choose_spec.2.2.2.2.1 d hd

theorem hull_vol_le (j : ℕ) :
    normalizedHaarLogVolume (anchor p L j) (unitRegion p (LL L j) (hullC p D N j) (anchor p L j)) /
        (Module.finrank ℚ_[p] (PP p L j) : ℝ) ≤
      (bI p (fun t => finiteExtensionRamification p (LL L j t)) -
        (boundExponent p (LL L j) 0 (hullK p D N j) : ℝ)) * Real.log (p : ℝ) :=
  (hullSpec p D N j).choose_spec.choose_spec.2.2.2.2.2

def baseSet (j : ℕ) : Set (Set (PP p L j)) :=
  {A | ∃ η ∈ actualProfiles D.s D.i 7, ∃ u : normOneUnits L,
    ∃ φ : PP p L j ≃ₗ[ℚ_[p]] PP p L j, Src.IUT4.Theorem110.IsAdmissibleAut p (LL L j) φ ∧
      A = φ '' (factorRegion p (LL L j) 0 ((u : Lˣ) * η (labOf j) ^ N) (anchor p L j)).val}

omit [ProperSpace L] in
theorem base_subset_images (j : ℕ) {A : Set (PP p L j)} (hA : A ∈ baseSet p D N j) :
    A ⊆ horizontalVerticalImages p (KU L) j (ch j) 0 D.s D.i 7 (labOf j) N := by
  obtain ⟨η, hη, u, φ, hφ, rfl⟩ := hA
  intro x hx
  exact Set.mem_iUnion_of_mem η (Set.mem_iUnion_of_mem hη (Set.mem_iUnion_of_mem u
    (Or.inl (Set.mem_iUnion_of_mem φ (Set.mem_iUnion_of_mem hφ hx)))))

omit [ProperSpace L] in

theorem base_measure_ne_zero (j : ℕ) {A : Set (PP p L j)} (hA : A ∈ baseSet p D N j) :
    normalizedAddHaar (anchor p L j) A ≠ 0 := by
  obtain ⟨η, hη, u, φ, hφ, rfl⟩ := hA
  set X := factorRegion p (LL L j) 0 ((u : Lˣ) * η (labOf j) ^ N) (anchor p L j)
  have hopen : IsOpen (φ '' X.val) := by
    have h : (φ '' X.val) = φ.toContinuousLinearEquiv '' X.val := rfl
    rw [h]
    exact φ.toContinuousLinearEquiv.toHomeomorph.isOpenMap _ X.2.1.2
  exact (hopen.measure_pos _ (X.2.2.image _)).ne'

omit [ProperSpace L] in
theorem theta_mem_base (j : ℕ) :
    (factorRegion p (LL L j) 0 (D.ξ (labOf j) ^ N) (anchor p L j)).val ∈ baseSet p D N j := by
  refine ⟨D.ξ, D.hξ, 1, LinearEquiv.refl ℚ_[p] (PP p L j), fun _ => Iff.rfl, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  exact (Set.image_id _).symm

def thetaR : (rampSystem p L).Regions := fun _ j =>
  (factorRegion p (LL L j.val) 0 (D.ξ (labOf j.val) ^ N) (anchor p L j.val)).val

def qR : (rampSystem p L).Regions := fun _ j =>
  (factorRegion p (LL L j.val) 0 (D.r ^ N) (anchor p L j.val)).val

def contR : (rampSystem p L).Regions := fun _ j =>
  (unitRegion p (LL L j.val) (hullC p D N j.val) (anchor p L j.val)).val

def possR : Set (rampSystem p L).Regions :=
  {y | (∃ b : (rampSystem p L).Regions, (∀ vQ j, b vQ j ∈ baseSet p D N j.val) ∧
      RegionLE (rampSystem p L) b y) ∧ RegionLE (rampSystem p L) y (contR p D N)}

theorem thetaR_le_contR : RegionLE (rampSystem p L) (thetaR p D N) (contR p D N) := fun _ j =>
  (base_subset_images p D N j.val (theta_mem_base p D N j.val)).trans (images_subset_hull p D N j.val)

theorem theta_mem_poss : thetaR p D N ∈ possR p D N :=
  ⟨⟨thetaR p D N, fun _ j => theta_mem_base p D N j.val, fun _ _ => subset_rfl⟩, thetaR_le_contR p D N⟩

theorem cont_mem_poss : contR p D N ∈ possR p D N :=
  ⟨⟨thetaR p D N, fun _ j => theta_mem_base p D N j.val, thetaR_le_contR p D N⟩, fun _ _ => subset_rfl⟩

theorem poss_hasVolume {x : (rampSystem p L).Regions} (hx : x ∈ possR p D N) :
    (rampSystem p L).HasVolume x := by
  obtain ⟨⟨b, hb, hbx⟩, _⟩ := hx
  intro vQ j h0
  exact base_measure_ne_zero p D N j.val (hb vQ j) (measure_mono_null (hbx vQ j) h0)

theorem cont_le_integral
    (hbig : ∀ j : ℕ, j ≤ 3 → bI p (fun t => finiteExtensionRamification p (LL L j t)) ≤
      (boundExponent p (LL L j) 0 (hullK p D N j) : ℝ)) :
    RegionLE (rampSystem p L) (contR p D N) (rampSystem p L).integralRegions := fun _ j =>
  (hull_subset_bound p D N j.val).trans
    (boundRegion_subset_anchor p (LL L j.val) 0 _ (hbig j.val (stage_le p L j)))

omit [CompleteSpace L] in
theorem q_le_integral' :
    RegionLE (rampSystem p L) (qR p D N) (rampSystem p L).integralRegions := fun _ j =>
  factorRegion_subset_anchor p (LL L j.val) 0 (D.r ^ N) (by
    show ‖((D.r ^ N : Lˣ) : L)‖ ≤ 1
    rw [Units.val_pow_eq_pow_val, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) D.norm_r_lt_one.le)

omit [CompleteSpace L] in
theorem procVol_theta : (rampSystem p L).procVol (thetaR p D N) = (N : ℝ) / 3 * D.Lq := by
  rw [procVol_eq]
  have hk : ∀ k : Fin 3, (rampSystem p L).packetLogVolume () k.succ (thetaR p D N () k.succ) =
      (N : ℝ) * (((k.val : ℝ) + 1) ^ 2 / 14 * D.Lq) := by
    intro k
    show (rampSystem p L).packetLogVolume () k.succ
      (factorRegion p (LL L k.succ.val) 0 (D.ξ (labOf k.succ.val) ^ N) (anchor p L k.succ.val)).val = _
    rw [packetLogVolume_factor, Units.val_pow_eq_pow_val, norm_pow, Real.log_pow, Fin.val_succ,
      labOf_succ, D.log_xi]
  rw [Fin.sum_univ_three, hk 0, hk 1, hk 2]
  norm_num
  ring

omit [CompleteSpace L] in
theorem procVol_q : (rampSystem p L).procVol (qR p D N) = (N : ℝ) / 14 * D.Lq := by
  rw [procVol_eq]
  have hk : ∀ k : Fin 3, (rampSystem p L).packetLogVolume () k.succ (qR p D N () k.succ) =
      (N : ℝ) * (D.Lq / 14) := by
    intro k
    show (rampSystem p L).packetLogVolume () k.succ
      (factorRegion p (LL L k.succ.val) 0 (D.r ^ N) (anchor p L k.succ.val)).val = _
    rw [packetLogVolume_factor, Units.val_pow_eq_pow_val, norm_pow, Real.log_pow, D.log_r]
  rw [Fin.sum_univ_three, hk 0, hk 1, hk 2]
  ring

theorem stage_cont_le (j : Fin ((rampSystem p L).lstar + 1)) :
    (rampSystem p L).packetLogVolume () j (contR p D N () j) ≤
      errCoeff p (LL L j.val) * Real.log p + (N : ℝ) * Real.log ‖(D.ξ (labOf j.val) : L)‖ := by
  have h1 := packetLogVolume_region p L () j
    (unitRegion p (LL L j.val) (hullC p D N j.val) (anchor p L j.val))
  have h2 := hull_vol_le p D N j.val
  have h3 : bI p (fun t => finiteExtensionRamification p (LL L j.val t)) -
      (boundExponent p (LL L j.val) 0 (hullK p D N j.val) : ℝ) ≤
      errCoeff p (LL L j.val) - (hullK p D N j.val : ℝ) / (finiteExtensionRamification p L).e :=
    bI_sub_boundExponent_le p (LL L j.val) 0 (hullK p D N j.val)
  have h4 := k_div_e_log p (D.ξ (labOf j.val) : L) N (hullK p D N j.val) (hullK_spec p D N j.val)
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have h5 := mul_le_mul_of_nonneg_right h3 hlogp
  have h6 : (errCoeff p (LL L j.val) - (hullK p D N j.val : ℝ) / (finiteExtensionRamification p L).e) *
      Real.log p = errCoeff p (LL L j.val) * Real.log p + (N : ℝ) * Real.log ‖(D.ξ (labOf j.val) : L)‖ := by
    rw [sub_mul, h4]
    ring
  show (rampSystem p L).packetLogVolume () j
    (unitRegion p (LL L j.val) (hullC p D N j.val) (anchor p L j.val)).val ≤ _
  rw [h1]
  linarith

def errBar : ℝ := (∑ k : Fin 3, errCoeff p (LL L (k.val + 1))) / 3 * Real.log p

theorem procVol_cont_le :
    (rampSystem p L).procVol (contR p D N) ≤ errBar p (L := L) + (N : ℝ) / 3 * D.Lq := by
  rw [procVol_eq]
  have hk : ∀ k : Fin 3, (rampSystem p L).packetLogVolume () k.succ (contR p D N () k.succ) ≤
      errCoeff p (LL L (k.val + 1)) * Real.log p + (N : ℝ) * (((k.val : ℝ) + 1) ^ 2 / 14 * D.Lq) := by
    intro k
    have h := stage_cont_le p D N k.succ
    rw [Fin.val_succ, labOf_succ, D.log_xi] at h
    exact h
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  unfold errBar
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  norm_num at h0 h1 h2 ⊢
  linarith

theorem enlargement_bounded :
    (rampSystem p L).procVol (contR p D N) - (rampSystem p L).procVol (thetaR p D N) ≤ errBar p (L := L) := by
  rw [procVol_theta]
  linarith [procVol_cont_le p D N]

def Big : Prop :=
  ∀ j : ℕ, j ≤ 3 → bI p (fun t => finiteExtensionRamification p (LL L j t)) ≤
    (boundExponent p (LL L j) 0 (hullK p D N j) : ℝ)

def rampTheory (hbig : Big p D N) (hneg : (rampSystem p L).procVol (contR p D N) < 0) (hN : 0 < N) :
    CitedTheory where
  S := rampSystem p L
  thetaPilot := thetaR p D N
  qPilot := qR p D N
  container := contR p D N
  Possible := possR p D N
  IsLambdaO := fun _ j A => ∃ d : (PP p L j.val)ˣ, A = (unitRegion p (LL L j.val) d (anchor p L j.val)).val
  hull := contR p D N
  theta_possible := theta_mem_poss p D N
  ind1_closed := by
    rintro x hx y ⟨h, rfl⟩
    rw [act_eq]
    exact hx
  ind2_closed := by
    rintro x hx y ⟨g, rfl⟩
    rw [ind2Act_eq]
    exact hx
  ind3_bound := fun _ hx => hx.2
  ind3_saturated := by
    rintro x ⟨⟨b, hb, hbx⟩, _⟩ y hxy hyc
    exact ⟨⟨b, hb, fun vQ j => (hbx vQ j).trans (hxy vQ j)⟩, hyc⟩
  container_le_integral := cont_le_integral p D N hbig
  hull_isLambdaO := fun _ j => ⟨hullC p D N j.val, rfl⟩
  hull_contains := fun _ hx => hx.2
  hull_minimal := fun _ _ hT => hT _ (cont_mem_poss p D N)
  hull_le_integral := cont_le_integral p D N hbig
  q_hasVolume := fun _ j =>
    (normalizedAddHaar_region_pos (anchor p L j.val)
      (factorRegion p (LL L j.val) 0 (D.r ^ N) (anchor p L j.val))).ne'
  q_le_integral := q_le_integral' p D N
  q_neg := by
    rw [procVol_q]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have := D.Lq_neg
    have : (N : ℝ) / 14 * D.Lq < 0 := mul_neg_of_pos_of_neg (by positivity) this
    exact this
  linkScale := 3 / 14
  linkScale_pos := by norm_num
  link_degree := by
    rw [procVol_q, procVol_theta]
    ring
  ipl := by
    intro x hx
    have hle : (rampSystem p L).procVol x ≤ (rampSystem p L).procVol (contR p D N) :=
      PacketSystem.procVol_ind3 (fun vQ j => ⟨hx.2 vQ j, cont_le_integral p D N hbig vQ j⟩)
        (poss_hasVolume p D N hx)
    have hxneg : (rampSystem p L).procVol x < 0 := lt_of_le_of_lt hle hneg
    have hqneg : (rampSystem p L).procVol (qR p D N) < 0 := by
      rw [procVol_q]
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      exact mul_neg_of_pos_of_neg (by positivity) D.Lq_neg
    exact ⟨(rampSystem p L).procVol (qR p D N) / (rampSystem p L).procVol x,
      div_pos_of_neg_of_neg hqneg hxneg, (div_mul_cancel₀ _ hxneg.ne).symm⟩

theorem rampTheory_weakSHE (hbig) (hneg) (hN) : (rampTheory p D N hbig hneg hN).WeakSHE :=
  ⟨fun c => {y | (∃ b : (rampSystem p L).Regions, (∀ vQ j, b vQ j ∈ baseSet p D N j.val) ∧
      RegionLE (rampSystem p L) b y) ∧ RegionLE (rampSystem p L) y c}, rfl, fun _ _ hx => hx.2⟩

theorem rampTheory_not_conclusion (hbig) (hneg) (hN)
    (hgap : errBar p (L := L) + (N : ℝ) / 3 * D.Lq < (N : ℝ) / 14 * D.Lq) :
    ¬ (rampTheory p D N hbig hneg hN).Conclusion := by
  intro h
  have h' : (rampSystem p L).procVol (qR p D N) ≤ (rampSystem p L).procVol (contR p D N) := h
  rw [procVol_q] at h'
  linarith [procVol_cont_le p D N]

theorem big_of_large (hN : ∀ j : ℕ, j ≤ 3 →
    errCoeff p (LL L j) * Real.log p < (N : ℝ) * (-D.Lq) / 14) : Big p D N := by
  intro j hj
  have hp : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have h3 := bI_sub_boundExponent_le p (LL L j) 0 (hullK p D N j)
  have h4 := k_div_e_log p (D.ξ (labOf j) : L) N (hullK p D N j) (hullK_spec p D N j)
  rw [D.log_xi] at h4
  have hsq : (1 : ℝ) ≤ (((labOf j).val : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ ((labOf j).val : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hA : 0 < -D.Lq := by linarith [D.Lq_neg]
  have hkey : errCoeff p (LL L j) * Real.log p <
      (hullK p D N j : ℝ) / (finiteExtensionRamification p L).e * Real.log p := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hmono : (N : ℝ) * (-D.Lq) / 14 ≤ (N : ℝ) * ((((labOf j).val : ℝ) + 1) ^ 2 / 14 * (-D.Lq)) := by
      have : (N : ℝ) * (-D.Lq) ≥ 0 := mul_nonneg hN0 hA.le
      nlinarith
    have hrw : (hullK p D N j : ℝ) / (finiteExtensionRamification p L).e * Real.log p =
        (N : ℝ) * ((((labOf j).val : ℝ) + 1) ^ 2 / 14 * (-D.Lq)) := by
      have h4' : (hullK p D N j : ℝ) / (finiteExtensionRamification p (LL L j 0)).e * Real.log p =
          -((N : ℝ) * ((((labOf j).val : ℝ) + 1) ^ 2 / 14 * D.Lq)) := h4
      rw [show (finiteExtensionRamification p L).e = (finiteExtensionRamification p (LL L j 0)).e from rfl, h4']
      ring
    rw [hrw]
    linarith [hN j hj]
  have hlt : errCoeff p (LL L j) < (hullK p D N j : ℝ) / (finiteExtensionRamification p L).e :=
    lt_of_mul_lt_mul_right hkey hp.le
  have h3' : bI p (fun t => finiteExtensionRamification p (LL L j t)) -
      (boundExponent p (LL L j) 0 (hullK p D N j) : ℝ) ≤
      errCoeff p (LL L j) - (hullK p D N j : ℝ) / (finiteExtensionRamification p L).e := h3
  linarith

theorem exists_ramified_counterexample :
    ∃ (N : ℕ) (hbig : Big p D N) (hneg : (rampSystem p L).procVol (contR p D N) < 0) (hN : 0 < N),
      (rampTheory p D N hbig hneg hN).WeakSHE ∧ ¬ (rampTheory p D N hbig hneg hN).Conclusion := by
  have hA : 0 < -D.Lq := by linarith [D.Lq_neg]
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  set M : ℝ := |errCoeff p (LL L 0)| + |errCoeff p (LL L 1)| + |errCoeff p (LL L 2)| +
    |errCoeff p (LL L 3)| with hM
  set E : ℝ := errBar p (L := L) with hE
  obtain ⟨N, hNgt⟩ := exists_nat_gt ((14 * M * Real.log p + 42 * |E| + 1) / (-D.Lq))
  have hkey : 14 * M * Real.log p + 42 * |E| + 1 < (N : ℝ) * (-D.Lq) := by
    rwa [div_lt_iff₀ hA] at hNgt
  have hM0 : 0 ≤ M := by positivity
  have hE0 : 0 ≤ |E| := abs_nonneg E
  have hML : 0 ≤ M * Real.log p := mul_nonneg hM0 hlogp
  have hNpos : 0 < N := by
    have : (0 : ℝ) < (N : ℝ) * (-D.Lq) := by linarith
    have h' : (0 : ℝ) < N := lt_of_not_ge fun hc => by nlinarith
    exact_mod_cast h'
  have hbig : Big p D N := by
    apply big_of_large
    intro j hj
    have hj' : |errCoeff p (LL L j)| ≤ M := by
      interval_cases j <;> simp only [hM] <;> linarith [abs_nonneg (errCoeff p (LL L 0)),
        abs_nonneg (errCoeff p (LL L 1)), abs_nonneg (errCoeff p (LL L 2)),
        abs_nonneg (errCoeff p (LL L 3))]
    have h1 : errCoeff p (LL L j) * Real.log p ≤ M * Real.log p :=
      mul_le_mul_of_nonneg_right ((le_abs_self _).trans hj') hlogp
    linarith
  have hgap : E + (N : ℝ) / 3 * D.Lq < (N : ℝ) / 14 * D.Lq := by
    have hE' : E ≤ |E| := le_abs_self E
    nlinarith
  have hneg : (rampSystem p L).procVol (contR p D N) < 0 := by
    have h := procVol_cont_le p D N
    have hE' : E ≤ |E| := le_abs_self E
    have : E + (N : ℝ) / 3 * D.Lq < 0 := by nlinarith
    linarith
  exact ⟨N, hbig, hneg, hNpos, rampTheory_weakSHE p D N hbig hneg hNpos,
    rampTheory_not_conclusion p D N hbig hneg hNpos hgap⟩

end Regions

section Concrete

open Src.Lib.P211Datum Src.Lib.P211Valuation CitedLV.ThetaLink.P211FiniteLocalField

def rootB : ℂ_[211] := Classical.choose (IsAlgClosed.exists_pow_nat_eq qbVal (by norm_num : 0 < 14))

theorem rootB_pow : rootB ^ 14 = qbVal :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq qbVal (by norm_num : 0 < 14))

def iB : ℂ_[211] := Classical.choose (IsAlgClosed.exists_pow_nat_eq (-1 : ℂ_[211]) (by norm_num : 0 < 2))

theorem iB_sq : iB ^ 2 = -1 :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (-1 : ℂ_[211]) (by norm_num : 0 < 2))

theorem rootB_integral : IsIntegral ℚ_[211] rootB :=
  IsIntegral.of_pow (n := 14) (by norm_num) (by rw [rootB_pow]; exact qbVal_integral)

theorem iB_integral : IsIntegral ℚ_[211] iB :=
  IsIntegral.of_pow (n := 2) (by norm_num) (by rw [iB_sq]; exact isIntegral_one.neg)

def fieldB : IntermediateField ℚ_[211] ℂ_[211] := IntermediateField.adjoin ℚ_[211] {rootB, iB}

abbrev FB := ↥fieldB

instance fbFiniteDimensional : FiniteDimensional ℚ_[211] FB :=
  IntermediateField.finiteDimensional_adjoin (by
    rintro x (rfl | rfl)
    · exact rootB_integral
    · exact iB_integral)

instance fbComplete : CompleteSpace FB := FiniteDimensional.complete ℚ_[211] FB

instance fbProper : ProperSpace FB := FiniteDimensional.proper ℚ_[211] FB

instance fbUltra : IsUltrametricDist FB := IsUltrametricDist.of_normedAlgebra ℚ_[211]

instance fbZpAlgebra : Algebra ℤ_[211] FB :=
  ((algebraMap ℚ_[211] FB).comp (algebraMap ℤ_[211] ℚ_[211])).toAlgebra

instance fbZpTower : IsScalarTower ℤ_[211] ℚ_[211] FB := IsScalarTower.of_algebraMap_eq' rfl

theorem rootB_ne_zero : rootB ≠ 0 := by
  intro h
  apply qbVal_ne_zero
  rw [← rootB_pow, h, zero_pow (by norm_num)]

theorem iB_ne_zero : iB ≠ 0 := by
  intro h
  have := iB_sq
  rw [h, zero_pow (by norm_num)] at this
  exact zero_ne_one (neg_eq_zero.mp this.symm).symm |>.elim

def rU : FBˣ :=
  Units.mk0 ⟨rootB, IntermediateField.subset_adjoin ℚ_[211] _ (Set.mem_insert _ _)⟩
    (fun h => rootB_ne_zero (congrArg Subtype.val h))

def iU : FBˣ :=
  Units.mk0 ⟨iB, IntermediateField.subset_adjoin ℚ_[211] _ (Set.mem_insert_of_mem _ rfl)⟩
    (fun h => iB_ne_zero (congrArg Subtype.val h))

def sU : FBˣ := rU ^ 7

theorem iU_sq : iU ^ 2 = -1 := by
  apply Units.ext
  apply Subtype.ext
  show iB ^ 2 = -1
  exact iB_sq

theorem hr0 : rU ^ (2 * 7) = sU ^ 2 := by
  unfold sU
  rw [← pow_mul]

theorem norm_sU_sq : ‖((sU ^ 2 : FBˣ) : FB)‖ = ‖qbVal‖ := by
  rw [← hr0]
  show ‖rootB ^ (2 * 7)‖ = ‖qbVal‖
  rw [show 2 * 7 = 14 by norm_num, rootB_pow]

theorem norm_sU_lt : ‖((sU : FBˣ) : FB)‖ < 1 := by
  have h : ‖((sU : FBˣ) : FB)‖ ^ 2 < 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, norm_sU_sq]
    exact qbVal_spec.2.2
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h

def factsB : PublishedThetaFacts sU iU :=
  publishedThetaFactsOfCompleteUltrametric sU iU iU_sq norm_sU_lt

def D0 : ThetaDatum FB where
  s := sU
  i := iU
  hi := iU_sq
  facts := factsB
  ξ := fun j => rU ^ ((j.val + 1) * (j.val + 1))
  hξ := fun j => (mem_normalizedRootValues_iff_power sU iU iU_sq factsB 7 (j.val + 1) _).mpr (by
    rw [← hr0, ← pow_mul, ← pow_mul, Nat.mul_comm])
  r := rU
  hr := hr0
  hq := by
    rw [norm_sU_sq]
    exact qbVal_spec.2.2

theorem FB_ramified : 98 ∣ (finiteExtensionRamification 211 FB).e := by
  set R := finiteExtensionRamification 211 FB with hR
  have hr0' : ((rU : FBˣ) : FB) ≠ 0 := Units.ne_zero _
  obtain ⟨m, hm⟩ := R.valueGroup _ hr0'
  have h98 : ‖((rU : FBˣ) : FB)‖ ^ 98 = (211 : ℝ)⁻¹ ^ 29 := by
    show ‖rootB‖ ^ 98 = _
    rw [show (98 : ℕ) = 14 * 7 by norm_num, pow_mul, ← norm_pow, rootB_pow, qbVal_spec.2.1, norm_pC]
  have h211 : 0 < Real.log (211 : ℝ) := Real.log_pos (by norm_num)
  have hl := congrArg Real.log h98
  rw [Real.log_pow, Real.log_pow, hm, Real.log_zpow, R.norm_pi, Real.log_rpow (by norm_num),
    Real.log_inv] at hl
  push_cast at hl
  have he : (0 : ℝ) < R.e := by exact_mod_cast R.e_pos
  have key : (98 : ℝ) * m = 29 * R.e := by
    field_simp at hl
    linarith
  have hint : (98 : ℤ) * m = 29 * (R.e : ℤ) := by exact_mod_cast key
  have hdvd : (98 : ℤ) ∣ 29 * (R.e : ℤ) := ⟨m, hint.symm⟩
  have hcop : IsCoprime (98 : ℤ) 29 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    norm_num
  have h' : (98 : ℤ) ∣ (R.e : ℤ) := hcop.dvd_of_dvd_mul_left hdvd
  exact_mod_cast h'

theorem concrete_ramified :
    98 ∣ (finiteExtensionRamification 211 FB).e ∧
      ∃ (N : ℕ) (hbig : Big 211 D0 N) (hneg : (rampSystem 211 FB).procVol (contR 211 D0 N) < 0)
        (hN : 0 < N),
        (rampTheory 211 D0 N hbig hneg hN).WeakSHE ∧ ¬ (rampTheory 211 D0 N hbig hneg hN).Conclusion :=
  ⟨FB_ramified, exists_ramified_counterexample 211 D0⟩

end Concrete

end CitedLV.Independence.Cor312RamifiedBadPlace
