import Cor312LogVolume.Src.Lib.P211RootOfUnity
import Cor312LogVolume.Src.Lib.P211Valuation

noncomputable section
namespace Src.Lib.P211Datum

open Src.Lib.P211RootOfUnity Src.Lib.P211Valuation

def zeta7C : ℂ_[211]ˣ :=
  Units.map (algebraMap ℚ_[211] ℂ_[211]).toMonoidHom zeta7Unit

theorem zeta7C_isPrimitiveRoot : IsPrimitiveRoot zeta7C 7 := by
  apply zeta7Unit_isPrimitiveRoot.map_of_injective
    (f := Units.map (algebraMap ℚ_[211] ℂ_[211]).toMonoidHom)
  intro a b hab
  apply Units.ext
  exact (algebraMap ℚ_[211] ℂ_[211]).injective (congrArg Units.val hab)

def qbVal : ℂ_[211] := Classical.choose exists_qb

theorem qbVal_spec :
    qbVal ^ 7 = pC ^ 29 ∧ ‖qbVal‖ ^ 7 = ‖pC‖ ^ 29 ∧ ‖qbVal‖ < 1 :=
  Classical.choose_spec exists_qb

theorem qbVal_ne_zero : qbVal ≠ 0 := by
  intro h
  have h7 := qbVal_spec.1
  rw [h, zero_pow (by norm_num)] at h7
  have : (pC : ℂ_[211]) ≠ 0 := by
    intro hp
    have := norm_pC
    rw [hp, norm_zero] at this
    norm_num at this
  exact this (pow_eq_zero_iff (by norm_num) |>.mp h7.symm)

def qb : ℂ_[211]ˣ := Units.mk0 qbVal qbVal_ne_zero

theorem qb_norm_lt_one : ‖((qb : ℂ_[211]))‖ < 1 := qbVal_spec.2.2

theorem qb_ord : ‖((qb : ℂ_[211]))‖ ^ 7 = ‖pC‖ ^ 29 := qbVal_spec.2.1

theorem p211_hypotheses_on_one_field :
    IsNonarchimedean (norm : ℂ_[211] → ℝ) ∧
      ‖((qb : ℂ_[211]))‖ < 1 ∧
      IsPrimitiveRoot zeta7C 7 ∧
      ‖((qb : ℂ_[211]))‖ ^ 7 = ‖pC‖ ^ 29 :=
  ⟨PadicComplex.isNonarchimedean 211, qb_norm_lt_one,
   zeta7C_isPrimitiveRoot, qb_ord⟩

end Src.Lib.P211Datum
end
