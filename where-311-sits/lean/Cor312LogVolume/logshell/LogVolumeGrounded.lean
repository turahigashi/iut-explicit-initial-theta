import Cor312LogVolume.logshell.HullIsSpan
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace CitedLV.LogVolume

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable def sizeOf (x : ℚ_[p]) : ℝ := ‖x‖

noncomputable def logVol (x : ℚ_[p]) : ℝ := Real.log ‖x‖

theorem norm_le_of_span_le {x y : ℚ_[p]}
    (h : (Submodule.span ℤ_[p] {x} : Submodule ℤ_[p] ℚ_[p])
       ≤ Submodule.span ℤ_[p] {y}) :
    ‖x‖ ≤ ‖y‖ := by
  have hx : x ∈ Submodule.span ℤ_[p] ({y} : Set ℚ_[p]) :=
    h (Submodule.mem_span_singleton_self x)
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨a, ha⟩ := hx
  have hnorm : ‖x‖ = ‖(a : ℚ_[p])‖ * ‖y‖ := by
    rw [← ha, Algebra.smul_def, norm_mul]
    rfl
  have hale : ‖(a : ℚ_[p])‖ ≤ 1 := a.2
  calc ‖x‖ = ‖(a : ℚ_[p])‖ * ‖y‖ := hnorm
    _ ≤ 1 * ‖y‖ := by
        apply mul_le_mul_of_nonneg_right hale (norm_nonneg _)
    _ = ‖y‖ := one_mul _

theorem sizeOf_mono {x y : ℚ_[p]}
    (h : (Submodule.span ℤ_[p] {x} : Submodule ℤ_[p] ℚ_[p])
       ≤ Submodule.span ℤ_[p] {y}) :
    sizeOf p x ≤ sizeOf p y :=
  norm_le_of_span_le p h

theorem logVol_mono {x y : ℚ_[p]} (hx : x ≠ 0)
    (h : (Submodule.span ℤ_[p] {x} : Submodule ℤ_[p] ℚ_[p])
       ≤ Submodule.span ℤ_[p] {y}) :
    logVol p x ≤ logVol p y := by
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  exact Real.log_le_log hxn (norm_le_of_span_le p h)

theorem logVol_indep_of_unit (x : ℚ_[p]) (u : ℤ_[p]ˣ) :
    logVol p ((u : ℤ_[p]) • x) = logVol p x := by
  simp only [logVol, Algebra.smul_def, norm_mul]
  have h1 : ‖(algebraMap ℤ_[p] ℚ_[p]) ((u : ℤ_[p]))‖ = 1 := by
    show ‖(((u : ℤ_[p]) : ℚ_[p]))‖ = 1
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.norm_units u
  rw [h1, one_mul]

theorem readout_exists_on_singletons :
    ∃ f : ℚ_[p] → ℝ,
      (∀ x y : ℚ_[p],
        (Submodule.span ℤ_[p] {x} : Submodule ℤ_[p] ℚ_[p])
          ≤ Submodule.span ℤ_[p] {y} → f x ≤ f y) ∧
      (∀ (x : ℚ_[p]) (u : ℤ_[p]ˣ), f ((u : ℤ_[p]) • x) = f x) :=
  ⟨sizeOf p,
   fun _ _ h => sizeOf_mono p h,
   fun x u => by
     simp only [sizeOf, Algebra.smul_def, norm_mul]
     have h1 : ‖(algebraMap ℤ_[p] ℚ_[p]) ((u : ℤ_[p]))‖ = 1 := by
       show ‖(((u : ℤ_[p]) : ℚ_[p]))‖ = 1
       rw [PadicInt.padic_norm_e_of_padicInt]
       exact PadicInt.norm_units u
     rw [h1, one_mul]⟩

theorem grounded_logVolume (x y : ℚ_[p]) (u : ℤ_[p]ˣ)
    (h : (Submodule.span ℤ_[p] {x} : Submodule ℤ_[p] ℚ_[p])
       ≤ Submodule.span ℤ_[p] {y}) :
    (‖x‖ ≤ ‖y‖) ∧
    (sizeOf p x ≤ sizeOf p y) ∧
    (logVol p ((u : ℤ_[p]) • x) = logVol p x) :=
  ⟨norm_le_of_span_le p h, sizeOf_mono p h, logVol_indep_of_unit p x u⟩

end CitedLV.LogVolume
