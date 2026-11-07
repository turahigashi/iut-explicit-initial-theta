import Cor312LogVolume.independence.Cor312CitedTheoryFamily

set_option autoImplicit false
noncomputable section

namespace CitedLV.Independence.Cor312CitedFamily

open MeasureTheory
open Src.IUT3.Theorem311
open CitedLV.Theorem311.PacketHullEndpoint

namespace CitedTheoryFam

variable (T : CitedTheoryFam)

theorem negLogTheta_le_containers
    (hLam : ∀ i vQ j, T.IsLambdaO i vQ j (T.container i vQ j))
    (hθ : ∀ i, (T.S i).HasVolume (T.thetaPilot i)) :
    T.negLogTheta ≤ ∑ i, (T.S i).procVol (T.container i) := by
  have hle := T.hull_minimal T.container hLam T.ind3_bound
  refine Finset.sum_le_sum fun i _ => ?_
  have hhv : (T.S i).HasVolume (T.hull i) := by
    intro vQ j h0
    have hsub : T.thetaPilot i vQ j ⊆ T.hull i vQ j := T.hull_contains _ T.theta_possible i vQ j
    exact hθ i vQ j (measure_mono_null hsub h0)
  exact (T.S i).procVol_ind3 (fun vQ j => ⟨hle i vQ j, T.container_le_integral i vQ j⟩) hhv

theorem not_conclusion_of_container_gap
    (hLam : ∀ i vQ j, T.IsLambdaO i vQ j (T.container i vQ j))
    (hθ : ∀ i, (T.S i).HasVolume (T.thetaPilot i))
    (hgap : ∑ i, (T.S i).procVol (T.container i) < ∑ i, (T.S i).procVol (T.qPilot i)) :
    ¬ T.Conclusion := by
  intro h
  have h1 := T.negLogTheta_le_containers hLam hθ
  have h2 : T.negLogQ ≤ T.negLogTheta := h
  have h3 : T.negLogQ = ∑ i, (T.S i).procVol (T.qPilot i) := rfl
  linarith

theorem erased_gives_conclusion (h : T.thetaPilot = T.qPilot) : T.Conclusion := by
  apply T.strongCarrier_implies_conclusion
  show T.qPilot ∈ T.Possible
  rw [← h]
  exact T.theta_possible

theorem erased_linkScale (h : T.thetaPilot = T.qPilot) : T.linkScale = 1 := by
  have hl := T.link_degree
  rw [h] at hl
  have hq := T.q_neg
  have hne : ∑ i, (T.S i).procVol (T.qPilot i) ≠ 0 := hq.ne
  have : (T.linkScale - 1) * ∑ i, (T.S i).procVol (T.qPilot i) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact absurd h1 hne

end CitedTheoryFam

end CitedLV.Independence.Cor312CitedFamily

section Check
open CitedLV.Independence.Cor312CitedFamily
end Check
