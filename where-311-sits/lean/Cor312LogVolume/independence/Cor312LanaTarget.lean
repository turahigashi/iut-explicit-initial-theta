import Cor312LogVolume.independence.Cor312CitedTheory
import Cor312LogVolume.independence.Cor312CitedTheoryFamily

set_option autoImplicit false
noncomputable section

open Src.IUT3.Theorem311
open CitedLV.Theorem311.PacketHullEndpoint

namespace CitedLV.Independence.Cor312Cited

namespace CitedTheory

variable (T : CitedTheory)

def PilotVolumeMatch : Prop :=
  ∃ x ∈ T.Possible, T.S.HasVolume x ∧ T.S.procVol x = T.negLogQ

theorem pilotVolumeMatch_implies_conclusion (h : T.PilotVolumeMatch) : T.Conclusion := by
  obtain ⟨x, hx, hv, he⟩ := h
  have hle := T.hull_contains x hx
  have := T.S.procVol_ind3 (fun vQ j => ⟨hle vQ j, T.hull_le_integral vQ j⟩) hv
  show T.negLogQ ≤ T.negLogTheta
  rw [← he]
  exact this

theorem strongCarrier_implies_pilotVolumeMatch (h : T.StrongSHECarrier) : T.PilotVolumeMatch :=
  ⟨T.qPilot, h, T.q_hasVolume, rfl⟩

end CitedTheory

theorem model_not_pilotVolumeMatch : ¬ modelTheory.PilotVolumeMatch := fun h =>
  model_not_conclusion (modelTheory.pilotVolumeMatch_implies_conclusion h)

theorem pilotVolumeMatch_not_derivable :
    ¬ ∀ T : CitedTheory, T.WeakSHE → T.PilotVolumeMatch := fun h =>
  model_not_pilotVolumeMatch (h modelTheory model_weakSHE)

end CitedLV.Independence.Cor312Cited

namespace CitedLV.Independence.Cor312CitedFamily

namespace CitedTheoryFam

variable (T : CitedTheoryFam)

def PilotVolumeMatch : Prop :=
  ∃ x ∈ T.Possible, (∀ i, (T.S i).HasVolume (x i)) ∧ ∑ i, (T.S i).procVol (x i) = T.negLogQ

theorem pilotVolumeMatch_implies_conclusion (h : T.PilotVolumeMatch) : T.Conclusion := by
  obtain ⟨x, hx, hv, he⟩ := h
  show T.negLogQ ≤ T.negLogTheta
  rw [← he]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle := T.hull_contains x hx i
  exact (T.S i).procVol_ind3 (fun vQ j => ⟨hle vQ j, T.hull_le_integral i vQ j⟩) (hv i)

theorem strongCarrier_implies_pilotVolumeMatch (h : T.StrongSHECarrier) : T.PilotVolumeMatch :=
  ⟨T.qPilot, h, T.q_hasVolume, rfl⟩

end CitedTheoryFam

theorem pilotVolumeMatch_not_derivable_fam :
    ¬ ∀ T : CitedTheoryFam, T.WeakSHE → T.PilotVolumeMatch := by
  intro h
  obtain ⟨N, hq, hθ, hw, hnot⟩ := concrete
  exact hnot ((famModel _ N hq hθ).pilotVolumeMatch_implies_conclusion (h _ hw))

end CitedLV.Independence.Cor312CitedFamily

section Check
open CitedLV.Independence.Cor312Cited
open CitedLV.Independence.Cor312CitedFamily
end Check
