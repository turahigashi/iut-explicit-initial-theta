import Cor312LogVolume.independence.Cor312CitedTheory
import Cor312LogVolume.independence.Cor312CitedBadPlaceEnlarged

set_option autoImplicit false
noncomputable section

namespace CitedLV.Independence.Cor312Cited

theorem approx_le_iff (a b : ℝ) : (∀ ε : ℝ, 0 < ε → a ≤ b + ε) ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hab
    rw [not_le] at hab
    have := h ((a - b) / 2) (by linarith)
    linarith
  · intro h ε hε
    linarith

namespace CitedTheory

variable (T : CitedTheory)

def ApproxConclusion : Prop := ∀ ε : ℝ, 0 < ε → T.negLogQ ≤ T.negLogTheta + ε

theorem approx_iff_conclusion : T.ApproxConclusion ↔ T.Conclusion :=
  approx_le_iff _ _

end CitedTheory

theorem approx_not_derivable :
    ¬ ∀ T : CitedTheory, T.WeakSHE → T.ApproxConclusion := fun h =>
  model_not_conclusion ((modelTheory.approx_iff_conclusion).mp (h modelTheory model_weakSHE))

end CitedLV.Independence.Cor312Cited

namespace CitedLV.Independence.Cor312CitedFamily

open CitedLV.Independence.Cor312Cited

namespace CitedTheoryFam

variable (T : CitedTheoryFam)

def ApproxConclusion : Prop := ∀ ε : ℝ, 0 < ε → T.negLogQ ≤ T.negLogTheta + ε

theorem approx_iff_conclusion : T.ApproxConclusion ↔ T.Conclusion :=
  approx_le_iff _ _

end CitedTheoryFam

theorem approx_not_derivable_enlarged (c : ℕ) :
    ¬ ∀ T : CitedTheoryFam, T.WeakSHE → T.ApproxConclusion := by
  intro h
  obtain ⟨N, hc, hq, hθ, hC, hw, hnot⟩ := robust_enlarged ![goodPlace5, archPlace] c
  exact hnot ((CitedTheoryFam.approx_iff_conclusion _).mp (h _ hw))

end CitedLV.Independence.Cor312CitedFamily

section Check
open CitedLV.Independence.Cor312Cited
open CitedLV.Independence.Cor312CitedFamily
end Check
