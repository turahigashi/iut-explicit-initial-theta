import Cor312LogVolume.Src.Lib.PadicLog.LocalFieldLogSurjective
import Cor312LogVolume.Src.Lib.PadicLog.LocalFieldLogAdd
import Mathlib

namespace Src.IUT3.Proposition39iv

open MeasureTheory Metric Set SrcLib.LocalFieldLogIsometry

section Translate

variable {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant]

theorem measure_translate (c : G) (S : Set G) : μ ((fun w => c + w) '' S) = μ S := by
  rw [show (fun w => c + w) '' S = (fun w => -c + w) ⁻¹' S by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [add_assoc] using hy
    · intro hz
      exact ⟨-c + z, hz, by simp⟩]
  exact measure_preimage_add μ (-c) S

end Translate

section Local

variable (p : ℕ) [Fact p.Prime] {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [CompleteSpace K]
  [IsUltrametricDist K]

noncomputable def logUnit (u : K) : K :=
  log1p (u - 1)

def basicRegion (a : K) (r : ℝ) : Set K :=
  {u | ∃ z : K, ‖z‖ ≤ r ∧ u = (1 + a) * (1 + z)}

variable {p}

include p

theorem norm_one_add_eq_one {a : K} (ha : ‖a‖ ≤ 1 / 4) : ‖1 + a‖ = 1 := by
  have h1 : ‖(1 : K)‖ = 1 := by
    have := norm_algebraMap' K (1 : ℚ_[p])
    simpa using this
  have hne : ‖(1 : K)‖ ≠ ‖a‖ := by rw [h1]; intro h; linarith
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, h1]
  exact max_eq_left (by linarith)

theorem basicRegion_eq {a : K} (ha : ‖a‖ ≤ 1 / 4) (r : ℝ) :
    basicRegion a r = (fun w => (1 + a) + w) '' closedBall (0 : K) r := by
  have hu : ‖1 + a‖ = 1 := norm_one_add_eq_one (p := p) ha
  have hne : (1 + a) ≠ 0 := by intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
  ext u
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(1 + a) * z, ?_, by ring⟩
    rw [mem_closedBall_zero_iff, norm_mul, hu, one_mul]
    exact hz
  · rintro ⟨w, hw, rfl⟩
    rw [mem_closedBall_zero_iff] at hw
    refine ⟨(1 + a)⁻¹ * w, ?_, ?_⟩
    · rw [norm_mul, norm_inv, hu, inv_one, one_mul]
      exact hw
    · field_simp

theorem log1p_image_closedBall {r : ℝ} (hr : r ≤ 1 / 4) :
    (log1p : K → K) '' closedBall (0 : K) r = closedBall (0 : K) r := by
  ext y
  simp only [mem_image, mem_closedBall_zero_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [norm_log1p_eq (p := p) x (le_trans hx hr)]
    exact hx
  · intro hy
    obtain ⟨x, hx, hxy⟩ := SrcLib.LocalFieldLogSurjective.log1p_surjOn (p := p) y (le_trans hy hr)
    refine ⟨x, ?_, hxy⟩
    rw [← norm_log1p_eq (p := p) x hx, hxy]
    exact hy

theorem logUnit_image_basicRegion {a : K} (ha : ‖a‖ ≤ 1 / 4) {r : ℝ} (hr : r ≤ 1 / 4) :
    logUnit '' basicRegion a r = (fun w => log1p a + w) '' closedBall (0 : K) r := by
  have hsplit : logUnit '' basicRegion a r = (fun z => log1p a + log1p z) '' closedBall (0 : K) r := by
    ext y
    simp only [mem_image, basicRegion, mem_setOf_eq, mem_closedBall_zero_iff]
    constructor
    · rintro ⟨u, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      unfold logUnit
      rw [show (1 + a) * (1 + z) - 1 = a + z + a * z by ring,
        SrcLib.LocalFieldLogAdd.log1p_add (p := p) a z (by linarith) (by linarith)]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(1 + a) * (1 + z), ⟨z, hz, rfl⟩, ?_⟩
      unfold logUnit
      rw [show (1 + a) * (1 + z) - 1 = a + z + a * z by ring,
        SrcLib.LocalFieldLogAdd.log1p_add (p := p) a z (by linarith) (by linarith)]
  rw [hsplit, show (fun z => log1p a + log1p z) = (fun w => log1p a + w) ∘ log1p from rfl, image_comp,
    log1p_image_closedBall (p := p) hr]

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddLeftInvariant]

theorem measure_logUnit_image_basicRegion {a : K} (ha : ‖a‖ ≤ 1 / 4) {r : ℝ} (hr : r ≤ 1 / 4) :
    μ (logUnit '' basicRegion a r) = μ (basicRegion a r) := by
  rw [logUnit_image_basicRegion (p := p) ha hr, basicRegion_eq (p := p) ha, measure_translate,
    measure_translate]

theorem basicRegion_subset {a : K} (ha : ‖a‖ ≤ 1 / 4) {r : ℝ} (hr : r ≤ 1 / 4) :
    basicRegion a r ⊆ {u : K | ‖u - 1‖ ≤ 1 / 4} := by
  rintro u ⟨z, hz, rfl⟩
  simp only [mem_setOf_eq]
  rw [show (1 + a) * (1 + z) - 1 = a + (z + a * z) by ring]
  have hz' : ‖z‖ ≤ 1 / 4 := le_trans hz hr
  have haz : ‖a * z‖ ≤ 1 / 4 := by
    rw [norm_mul]; nlinarith [norm_nonneg a, norm_nonneg z]
  refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ha ?_)
  exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hz' haz)

theorem logUnit_injOn : InjOn (logUnit : K → K) {u : K | ‖u - 1‖ ≤ 1 / 4} := by
  intro u hu v hv h
  have := SrcLib.LocalFieldLogSurjective.log1p_injOn (p := p) (K := K) hu hv h
  simpa using this

def Scope (A : Set K) : Prop :=
  ∃ (n : ℕ) (a : Fin n → K) (r : Fin n → ℝ), (∀ i, ‖a i‖ ≤ 1 / 4 ∧ 0 < r i ∧ r i ≤ 1 / 4) ∧
    Pairwise (fun i j => Disjoint (basicRegion (a i) (r i)) (basicRegion (a j) (r j))) ∧
    A = ⋃ i, basicRegion (a i) (r i)

theorem measurableSet_basicRegion {a : K} (ha : ‖a‖ ≤ 1 / 4) (r : ℝ) :
    MeasurableSet (basicRegion a r) := by
  rw [basicRegion_eq (p := p) ha]
  have : (fun w => (1 + a) + w) '' closedBall (0 : K) r = (fun w => -(1 + a) + w) ⁻¹' closedBall (0 : K) r := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [add_assoc] using hy
    · intro hz
      exact ⟨-(1 + a) + z, hz, by abel_nf⟩
  rw [this]
  exact measurableSet_closedBall.preimage (measurable_const_add _)

theorem measurableSet_logUnit_image {a : K} (ha : ‖a‖ ≤ 1 / 4) {r : ℝ} (hr : r ≤ 1 / 4) :
    MeasurableSet (logUnit '' basicRegion a r) := by
  rw [logUnit_image_basicRegion (p := p) ha hr]
  have : (fun w => log1p a + w) '' closedBall (0 : K) r = (fun w => -log1p a + w) ⁻¹' closedBall (0 : K) r := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [add_assoc] using hy
    · intro hz
      exact ⟨-log1p a + z, hz, by simp⟩
  rw [this]
  exact measurableSet_closedBall.preimage (measurable_const_add _)

theorem measure_logUnit_image_of_scope {A : Set K} (hA : Scope A) :
    μ (logUnit '' A) = μ A := by
  obtain ⟨n, a, r, hsmall, hdisj, rfl⟩ := hA
  rw [image_iUnion]
  have hdisj' : Pairwise (fun i j => Disjoint (logUnit '' basicRegion (a i) (r i))
      (logUnit '' basicRegion (a j) (r j))) := by
    intro i j hij
    have hsub : ∀ k, basicRegion (a k) (r k) ⊆ {u : K | ‖u - 1‖ ≤ 1 / 4} :=
      fun k => basicRegion_subset (p := p) (hsmall k).1 (hsmall k).2.2
    rw [Set.disjoint_iff_inter_eq_empty, ← (logUnit_injOn (p := p)).image_inter (hsub i) (hsub j),
      Set.disjoint_iff_inter_eq_empty.mp (hdisj hij), Set.image_empty]
  rw [measure_iUnion hdisj' (fun i => measurableSet_logUnit_image (p := p) (hsmall i).1 (hsmall i).2.2),
    measure_iUnion hdisj (fun i => measurableSet_basicRegion (p := p) (hsmall i).1 _)]
  exact tsum_congr fun i => measure_logUnit_image_basicRegion (p := p) μ (hsmall i).1 (hsmall i).2.2

theorem logVolume_logUnit_image_of_scope (O : Set K) {A : Set K} (hA : Scope A) :
    Real.log (μ (logUnit '' A)).toReal - Real.log (μ O).toReal = Real.log (μ A).toReal - Real.log (μ O).toReal := by
  rw [measure_logUnit_image_of_scope (p := p) μ hA]

end Local

section Arch

open Complex Real

noncomputable def expI (t : ℝ) : ℂ :=
  Complex.exp (t * Complex.I)

noncomputable def angularMeasure : Measure ℂ :=
  Measure.map expI (volume.restrict (Ico 0 (2 * π)))

noncomputable def radialVolume (A : Set ℂ) : ENNReal :=
  volume ((fun z : ℂ => ‖z‖) '' A)

def vSeg (s s' : ℝ) : Set ℂ :=
  (fun t : ℝ => (t : ℂ) * Complex.I) '' Icc s s'

theorem continuous_expI : Continuous expI := by
  unfold expI
  fun_prop

theorem expI_injOn : InjOn expI (Ico 0 (2 * π)) := by
  intro x hx y hy h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have hre : x = y + n * (2 * π) := by
    have := congrArg Complex.im hn
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have hn0 : n = 0 := by
    have h1 : (n : ℝ) * (2 * π) < 2 * π := by rw [hre] at hx; linarith [hx.2, hy.1]
    have h2 : -(2 * π) < (n : ℝ) * (2 * π) := by rw [hre] at hx; linarith [hx.1, hy.2]
    have hpi : 0 < 2 * π := by positivity
    have h3 : (n : ℝ) < 1 := by nlinarith
    have h4 : -1 < (n : ℝ) := by nlinarith
    have h5 : n < 1 := by exact_mod_cast h3
    have h6 : -1 < n := by exact_mod_cast h4
    omega
  rw [hre, hn0]
  simp

theorem radialVolume_vSeg {s s' : ℝ} (hs : 0 ≤ s) :
    radialVolume (vSeg s s') = ENNReal.ofReal (s' - s) := by
  unfold radialVolume vSeg
  rw [← image_comp]
  have : ((fun z : ℂ => ‖z‖) ∘ fun t : ℝ => (t : ℂ) * Complex.I) '' Icc s s' = Icc s s' := by
    ext y
    simp only [mem_image, Function.comp, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [abs_of_nonneg (le_trans hs ht.1)]
      exact ht
    · intro hy
      exact ⟨y, hy, abs_of_nonneg (le_trans hs hy.1)⟩
  rw [this, Real.volume_Icc]

theorem angularMeasure_exp_vSeg {s s' : ℝ} (hs : 0 ≤ s) (hs' : s' < 2 * π) :
    angularMeasure (Complex.exp '' vSeg s s') = ENNReal.ofReal (s' - s) := by
  have himg : Complex.exp '' vSeg s s' = expI '' Icc s s' := by
    unfold vSeg expI
    rw [← image_comp]
    rfl
  have hmeas : MeasurableSet (expI '' Icc s s') :=
    ((isCompact_Icc).image continuous_expI).isClosed.measurableSet
  rw [himg, angularMeasure, Measure.map_apply continuous_expI.measurable hmeas, Measure.restrict_apply' measurableSet_Ico]
  have hpre : expI ⁻¹' (expI '' Icc s s') ∩ Ico 0 (2 * π) = Icc s s' := by
    ext θ
    constructor
    · rintro ⟨⟨t, ht, htθ⟩, hθ⟩
      have htmem : t ∈ Ico 0 (2 * π) := ⟨le_trans hs ht.1, lt_of_le_of_lt ht.2 hs'⟩
      rw [← expI_injOn htmem hθ htθ]
      exact ht
    · intro hθ
      exact ⟨⟨θ, hθ, rfl⟩, le_trans hs hθ.1, lt_of_le_of_lt hθ.2 hs'⟩
  rw [hpre, Real.volume_Icc]

theorem arch_compatible {s s' : ℝ} (hs : 0 ≤ s) (hs' : s' < 2 * π) :
    radialVolume (vSeg s s') = angularMeasure (Complex.exp '' vSeg s s') := by
  rw [radialVolume_vSeg hs, angularMeasure_exp_vSeg hs hs']

theorem arch_normalization :
    radialVolume (Metric.closedBall (0 : ℂ) 1) = 1 ∧ angularMeasure univ = ENNReal.ofReal (2 * π) := by
  constructor
  · unfold radialVolume
    have : (fun z : ℂ => ‖z‖) '' Metric.closedBall (0 : ℂ) 1 = Icc 0 1 := by
      ext y
      simp only [mem_image, Metric.mem_closedBall, dist_zero_right, mem_Icc]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨norm_nonneg z, hz⟩
      · rintro ⟨h0, h1⟩
        exact ⟨(y : ℂ), by simpa [Complex.norm_real, abs_of_nonneg h0] using h1, by simp [abs_of_nonneg h0]⟩
    rw [this, Real.volume_Icc]
    simp
  · rw [angularMeasure, Measure.map_apply continuous_expI.measurable MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ico]
    simp

theorem arch_contrast :
    radialVolume (vSeg 0 (2 * π + 1)) ≠ angularMeasure (Complex.exp '' vSeg 0 (2 * π + 1)) := by
  intro h
  have hle : angularMeasure (Complex.exp '' vSeg 0 (2 * π + 1)) ≤ angularMeasure univ := measure_mono (subset_univ _)
  rw [← h, radialVolume_vSeg le_rfl, arch_normalization.2] at hle
  have : ENNReal.ofReal (2 * π + 1 - 0) ≤ ENNReal.ofReal (2 * π) := hle
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
  linarith

end Arch

structure LogLinkVolume : Type 1 where
  p : ℕ
  [hp : Fact p.Prime]
  K : Type
  [nf : NormedField K]
  [na : NormedAlgebra ℚ_[p] K]
  [cs : CompleteSpace K]
  [ud : IsUltrametricDist K]
  [ms : MeasurableSpace K]
  [bs : BorelSpace K]
  μ : Measure K
  [inv : μ.IsAddLeftInvariant]

attribute [instance] LogLinkVolume.hp LogLinkVolume.nf LogLinkVolume.na LogLinkVolume.cs LogLinkVolume.ud
  LogLinkVolume.ms LogLinkVolume.bs LogLinkVolume.inv

namespace LogLinkVolume

variable (L : LogLinkVolume)

theorem compatible : ∀ A : Set L.K, Scope A → L.μ (logUnit '' A) = L.μ A :=
  fun _ hA => measure_logUnit_image_of_scope (p := L.p) L.μ hA

end LogLinkVolume

section Model

noncomputable instance : MeasurableSpace ℚ_[2] := borel _

instance : BorelSpace ℚ_[2] := ⟨rfl⟩

noncomputable def modelLogLink : LogLinkVolume where
  p := 2
  K := ℚ_[2]
  μ := Measure.addHaar

theorem norm_one_Q2 : ‖(1 : ℚ_[2])‖ = 1 := by simp

theorem one_mem_basicRegion : (1 : ℚ_[2]) ∈ basicRegion (0 : ℚ_[2]) (1 / 4) :=
  ⟨0, by simp, by simp⟩

theorem one_not_mem_logUnit_image : (1 : ℚ_[2]) ∉ logUnit '' basicRegion (0 : ℚ_[2]) (1 / 4) := by
  rw [logUnit_image_basicRegion (p := 2) (by simp) (le_refl _), log1p_zero (p := 2)]
  rintro ⟨w, hw, hw1⟩
  rw [mem_closedBall_zero_iff] at hw
  simp only [zero_add] at hw1
  rw [hw1, norm_one_Q2] at hw
  norm_num at hw

theorem basicRegion_zero_measure_pos :
    0 < (Measure.addHaar : Measure ℚ_[2]) (basicRegion (0 : ℚ_[2]) (1 / 4)) ∧
      (Measure.addHaar : Measure ℚ_[2]) (basicRegion (0 : ℚ_[2]) (1 / 4)) < ⊤ := by
  rw [basicRegion_eq (p := 2) (by simp), measure_translate]
  refine ⟨(IsUltrametricDist.isOpen_closedBall (0 : ℚ_[2]) (by norm_num)).measure_pos _ ⟨0, by simp⟩, ?_⟩
  exact (isCompact_closedBall (0 : ℚ_[2]) (1 / 4)).measure_lt_top

theorem dirac_not_compatible :
    (Measure.dirac (1 : ℚ_[2])) (logUnit '' basicRegion (0 : ℚ_[2]) (1 / 4)) ≠
      (Measure.dirac (1 : ℚ_[2])) (basicRegion (0 : ℚ_[2]) (1 / 4)) := by
  rw [Measure.dirac_apply' _ (measurableSet_logUnit_image (p := 2) (by simp) (le_refl _)),
    Measure.dirac_apply' _ (measurableSet_basicRegion (p := 2) (by simp) _),
    Set.indicator_of_notMem one_not_mem_logUnit_image, Set.indicator_of_mem one_mem_basicRegion]
  simp

theorem model_nondegenerate :
    (0 < modelLogLink.μ (basicRegion (0 : ℚ_[2]) (1 / 4)) ∧ modelLogLink.μ (basicRegion (0 : ℚ_[2]) (1 / 4)) < ⊤) ∧
      logUnit '' basicRegion (0 : ℚ_[2]) (1 / 4) ≠ basicRegion (0 : ℚ_[2]) (1 / 4) ∧
      (Measure.dirac (1 : ℚ_[2])) (logUnit '' basicRegion (0 : ℚ_[2]) (1 / 4)) ≠
        (Measure.dirac (1 : ℚ_[2])) (basicRegion (0 : ℚ_[2]) (1 / 4)) :=
  ⟨basicRegion_zero_measure_pos, fun h => one_not_mem_logUnit_image (by rw [h]; exact one_mem_basicRegion), dirac_not_compatible⟩

end Model

end Src.IUT3.Proposition39iv

section Check
open Src.IUT3.Proposition39iv
end Check
