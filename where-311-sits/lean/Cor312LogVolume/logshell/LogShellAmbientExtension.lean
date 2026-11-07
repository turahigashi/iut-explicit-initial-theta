import Cor312LogVolume.logshell.PrincipalLogImagePadicStability
import Cor312LogVolume.theorem311.CanonicalFiniteSplitNormalizedHaar
import Mathlib.RingTheory.Localization.Module
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
set_option autoImplicit false

namespace CitedLV.LogShellAmbientExtension

open Src.IUT3.Remark122
open CitedLV.LocalLogShellCompactness
open CitedLV.PrincipalLogImagePadicStability
open scoped Topology nonZeroDivisors

variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]
  [CompleteSpace K] [IsUltrametricDist K] [ProperSpace K]

local instance : Module ℤ_[p] K := Module.restrictScalars ℤ_[p] ℚ_[p] K
local instance : IsScalarTower ℤ_[p] ℚ_[p] K :=
  IsScalarTower.restrictScalars ℤ_[p] ℚ_[p] K

local instance : ContinuousSMul ℤ_[p] K := ⟨by
  change Continuous (fun z : ℤ_[p] × K => (z.1 : ℚ_[p]) • z.2)
  exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd⟩

def logShellModule : Submodule ℤ_[p] K where
  __ := logShellAddSubgroup (K := K) p
  smul_mem' a _ hx := logShell_padicInt_smul_mem p hx a

theorem exists_pow_smul_mem (x : K) :
    ∃ n : ℕ, (p : ℚ_[p]) ^ n • x ∈ logShell (K := K) p := by
  have ht : Filter.Tendsto (fun n : ℕ => (p : ℚ_[p]) ^ n • x)
      Filter.atTop (𝓝 (0 : K)) := by
    simpa only [zero_smul] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := p))).smul_const x
  exact (ht.eventually ((logShell_open (K := K) p).mem_nhds
    (logShellAddSubgroup (K := K) p).zero_mem)).exists

instance shell_isLocalizedModule :
    IsLocalizedModule (ℤ_[p])⁰ (logShellModule (K := K) p).subtype where
  map_units := (isLocalizedModule_id (ℤ_[p])⁰ K ℚ_[p]).map_units
  surj x := by
    obtain ⟨n, hn⟩ := exists_pow_smul_mem p x
    have hp0 : (p : ℤ_[p]) ≠ 0 := by
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    refine ⟨⟨⟨(p : ℚ_[p]) ^ n • x, hn⟩,
      ⟨(p : ℤ_[p]) ^ n, mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hp0)⟩⟩, ?_⟩
    change ((algebraMap ℤ_[p] ℚ_[p]) ((p : ℤ_[p]) ^ n)) • x = _
    simp only [map_pow, map_natCast, Submodule.subtype_apply]
  exists_of_eq h := by
    exact ⟨1, by simpa using Subtype.ext h⟩

def extend (e : logShellModule (K := K) p ≃ₗ[ℤ_[p]] logShellModule (K := K) p) :
    K ≃ₗ[ℚ_[p]] K :=
  IsLocalizedModule.mapEquiv (ℤ_[p])⁰ (logShellModule (K := K) p).subtype
    (logShellModule (K := K) p).subtype ℚ_[p] e

@[simp] theorem extend_on_shell
    (e : logShellModule (K := K) p ≃ₗ[ℤ_[p]] logShellModule (K := K) p)
    (x : logShellModule (K := K) p) : extend p e (x : K) = (e x : K) := by
  exact IsLocalizedModule.map_apply (ℤ_[p])⁰
    (logShellModule (K := K) p).subtype (logShellModule (K := K) p).subtype e x

theorem extend_unique
    (e : logShellModule (K := K) p ≃ₗ[ℤ_[p]] logShellModule (K := K) p)
    (f : K →ₗ[ℚ_[p]] K)
    (hf : ∀ x : logShellModule (K := K) p, f (x : K) = (e x : K)) :
    f = (extend p e).toLinearMap := by
  apply LinearMap.restrictScalars_injective ℤ_[p]
  apply IsLocalizedModule.linearMap_ext (ℤ_[p])⁰
    (logShellModule (K := K) p).subtype (logShellModule (K := K) p).subtype
  ext x
  exact (hf x).trans (extend_on_shell p e x).symm

theorem extend_image_shell
    (e : logShellModule (K := K) p ≃ₗ[ℤ_[p]] logShellModule (K := K) p) :
    extend p e '' logShell (K := K) p = logShell (K := K) p := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [show extend p e x = (e ⟨x, hx⟩ : K) from extend_on_shell p e ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  · intro y hy
    refine ⟨(e.symm ⟨y, hy⟩ : K), (e.symm ⟨y, hy⟩).property, ?_⟩
    rw [extend_on_shell, e.apply_symm_apply]

variable [FiniteDimensional ℚ_[p] K]

def continuousExtend
    (e : logShellModule (K := K) p ≃ₗ[ℤ_[p]] logShellModule (K := K) p) :
    K ≃L[ℚ_[p]] K := (extend p e).toContinuousLinearEquiv

def ambientAction :
    (logShellModule (K := K) p ≃ₗ[ℤ_[p]] logShellModule (K := K) p) →*
      (K ≃L[ℚ_[p]] K) where
  toFun := continuousExtend p
  map_one' := by
    apply ContinuousLinearEquiv.toLinearEquiv_injective
    apply LinearEquiv.toLinearMap_injective
    symm
    apply extend_unique p
    intro x
    rfl
  map_mul' e f := by
    apply ContinuousLinearEquiv.toLinearEquiv_injective
    apply LinearEquiv.toLinearMap_injective
    symm
    apply extend_unique p
    intro x
    change extend p e (extend p f (x : K)) = ((e * f) x : K)
    rw [extend_on_shell, extend_on_shell]
    rfl

def additiveAmbientEquiv
    (e : logShellModule (K := K) p ≃ₜ+ logShellModule (K := K) p) :
    K ≃L[ℚ_[p]] K :=
  continuousExtend p (CitedLV.ClosedAddSubgroupPadicModule.padicIntLinearEquiv p e)

@[simp] theorem additiveAmbientEquiv_on_shell
    (e : logShellModule (K := K) p ≃ₜ+ logShellModule (K := K) p)
    (x : logShellModule (K := K) p) :
    additiveAmbientEquiv p e (x : K) = (e x : K) :=
  extend_on_shell p (CitedLV.ClosedAddSubgroupPadicModule.padicIntLinearEquiv p e) x

theorem continuousExtend_preserves_normalizedHaar
    [MeasurableSpace K] [BorelSpace K]
    (e : logShellModule (K := K) p ≃ₗ[ℤ_[p]] logShellModule (K := K) p) :
    MeasureTheory.Measure.map (continuousExtend p e)
        (CitedLV.Theorem311.normalizedAddHaar (logShellRegion (K := K) p)) =
      CitedLV.Theorem311.normalizedAddHaar (logShellRegion (K := K) p) := by
  let E : K ≃ₜ+ K := (continuousExtend p e).toContinuousAddEquiv
  change MeasureTheory.Measure.map E _ = _
  apply CitedLV.Theorem311.normalizedAddHaar_map_to_independent_anchor
  exact extend_image_shell p e

theorem continuousExtend_measurePreserving
    [MeasurableSpace K] [BorelSpace K]
    (e : logShellModule (K := K) p ≃ₗ[ℤ_[p]] logShellModule (K := K) p)
    (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure] :
    MeasureTheory.MeasurePreserving (continuousExtend p e) μ μ := by
  refine ⟨(continuousExtend p e).continuous.measurable, ?_⟩
  let R := logShellRegion (K := K) p
  have hμ : μ = μ R.val • CitedLV.Theorem311.normalizedAddHaar R :=
    MeasureTheory.Measure.addHaarMeasure_unique μ
      (CitedLV.Theorem311.normalizedHaarRegionToPositiveCompacts R)
  calc
    MeasureTheory.Measure.map (continuousExtend p e) μ =
        MeasureTheory.Measure.map (continuousExtend p e)
          (μ R.val • CitedLV.Theorem311.normalizedAddHaar R) := congrArg _ hμ
    _ = μ R.val • CitedLV.Theorem311.normalizedAddHaar R := by
      rw [MeasureTheory.Measure.map_smul, continuousExtend_preserves_normalizedHaar]
    _ = μ := hμ.symm

end CitedLV.LogShellAmbientExtension
