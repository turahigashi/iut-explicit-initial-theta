import Cor312LogVolume.theorem311.PadicNormedRamification
import Cor312LogVolume.theorem311.FiniteExtensionHaarCharacter
import Cor312LogVolume.theorem311.PadicPrimeHaarCharacter

noncomputable section
set_option autoImplicit false

namespace CitedLV.Theorem311.FinitePadicHaarNorm

open MeasureTheory Src.IUT4.Proposition12i
open PadicNormedRamification
open scoped NNReal ENNReal Pointwise

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] [IsUltrametricDist K] [ProperSpace K]

local instance : MeasurableSpace K := borel K
local instance : BorelSpace K := ⟨rfl⟩

def integerAnchor : NormalizedHaarRegion K :=
  ⟨Metric.closedBall 0 1, ⟨⟨ProperSpace.isCompact_closedBall 0 1,
    IsUltrametricDist.isOpen_closedBall (0 : K) one_ne_zero⟩, ⟨0, by simp⟩⟩⟩

theorem norm_one_preserves_integerAnchor (u : Kˣ) (hu : ‖(u : K)‖ = 1) :
    localScalarHaarRegion u (integerAnchor K) = integerAnchor K := by
  apply Subtype.ext
  rw [localScalarHaarRegion_carrier]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change dist ((u : K) * y) 0 ≤ 1
    rw [dist_zero_right]
    rw [norm_mul, hu, one_mul]
    simpa only [integerAnchor, Metric.mem_closedBall, dist_zero_right] using hy
  · intro hx
    refine ⟨(u : K)⁻¹ * x, ?_, ?_⟩
    · change dist ((u : K)⁻¹ * x) 0 ≤ 1
      rw [dist_zero_right]
      rw [norm_mul, norm_inv, hu, inv_one, one_mul]
      simpa only [integerAnchor, Metric.mem_closedBall, dist_zero_right] using hx
    · change (u : K) * ((u : K)⁻¹ * x) = x
      rw [← mul_assoc, mul_inv_cancel₀ u.ne_zero, one_mul]

theorem log_character_norm_one (u : Kˣ) (hu : ‖(u : K)‖ = 1) :
    Real.log (distribHaarChar K u : ℝ) = 0 := by
  have h := normalizedHaarLogVolume_localScalarRegion
    (integerAnchor K) (integerAnchor K) u
  rw [norm_one_preserves_integerAnchor K u hu,
    normalizedHaarLogVolume_anchor] at h
  linarith

theorem log_character_eq_degree_mul_log_norm (u : Kˣ) :
    Real.log (distribHaarChar K u : ℝ) =
      (Module.finrank ℚ_[p] K : ℝ) * Real.log ‖(u : K)‖ := by
  let R := finiteExtensionRamification p K
  obtain ⟨n, hn⟩ := R.valueGroup (u : K) u.ne_zero
  let P : Kˣ := Units.map (algebraMap ℚ_[p] K).toMonoidHom (padicPrimeUnit p)
  have hP : ‖(P : K)‖ = (p : ℝ)⁻¹ := by
    change ‖algebraMap ℚ_[p] K (p : ℚ_[p])‖ = _
    rw [norm_algebraMap', Padic.norm_p]
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.out.pos
  have he0 : (R.e : ℝ) ≠ 0 := by exact_mod_cast R.e_pos.ne'
  have hpi : ‖R.pi‖ ^ R.e = ‖(P : K)‖ := by
    rw [R.norm_pi, ← Real.rpow_mul_natCast hp0.le]
    have ht : (-(1 : ℝ) / R.e) * R.e = -1 := by field_simp
    rw [ht, Real.rpow_neg_one, hP]
  have hpow : ‖(u : K)‖ ^ R.e = ‖(P : K)‖ ^ n := by
    rw [hn, ← zpow_natCast, ← zpow_mul, mul_comm n (R.e : ℤ),
      zpow_mul, zpow_natCast, hpi]
  let w : Kˣ := u ^ R.e * P ^ (-n)
  have hw : ‖(w : K)‖ = 1 := by
    dsimp only [w]
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
    rw [norm_mul, norm_pow, norm_zpow, hpow, zpow_neg]
    exact mul_inv_cancel₀ (zpow_ne_zero _ (norm_ne_zero_iff.mpr P.ne_zero))
  have hc := log_character_norm_one K w hw
  have huχ : (distribHaarChar K u : ℝ) ≠ 0 := by
    exact_mod_cast (distribHaarChar_pos (A := K) (g := u)).ne'
  have hPχ : (distribHaarChar K P : ℝ) ≠ 0 := by
    exact_mod_cast (distribHaarChar_pos (A := K) (g := P)).ne'
  simp only [w, map_mul, map_pow, map_zpow, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_zpow] at hc
  rw [Real.log_mul (pow_ne_zero _ huχ) (zpow_ne_zero _ hPχ),
    Real.log_pow, Real.log_zpow] at hc
  have hPc : Real.log (distribHaarChar K P : ℝ) =
      (Module.finrank ℚ_[p] K : ℝ) * (-Real.log (p : ℝ)) := by
    dsimp only [P]
    rw [FiniteExtensionHaarCharacter.character_algebraMap,
      NNReal.coe_pow, Real.log_pow, realLog_distribHaarChar_padicPrime]
  rw [hPc] at hc
  simp only [Int.cast_neg] at hc
  have hnu : Real.log ‖(u : K)‖ = (n : ℝ) * (-(1 : ℝ) / R.e * Real.log (p : ℝ)) := by
    rw [hn, Real.log_zpow, R.norm_pi, Real.log_rpow hp0]
  rw [hnu]
  apply (mul_left_cancel₀ he0)
  field_simp at hc ⊢
  nlinarith [hc]

theorem log_character_div_finrank (u : Kˣ) :
    Real.log (distribHaarChar K u : ℝ) / Module.finrank ℚ_[p] K =
      Real.log ‖(u : K)‖ := by
  rw [log_character_eq_degree_mul_log_norm p K]
  have hd : (Module.finrank ℚ_[p] K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ_[p] K).ne'
  exact mul_div_cancel_left₀ _ hd

end CitedLV.Theorem311.FinitePadicHaarNorm
