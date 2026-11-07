import Cor312LogVolume.independence.Cor312CitedTheory
import Cor312LogVolume.independence.Cor312CitedTheoryFamily

set_option autoImplicit false
noncomputable section

namespace CitedLV.Independence.Cor312Cited

open Src.IUT3.Theorem311
open CitedLV.Theorem311.PacketHullEndpoint

namespace CitedTheory

variable (T : CitedTheory)

theorem weakSHE_holds : T.WeakSHE :=
  ⟨fun c => {y | y ∈ T.Possible ∧ RegionLE T.S y c},
    Set.ext fun y => ⟨fun hy => ⟨hy, T.ind3_bound y hy⟩, fun hy => hy.1⟩,
    fun _ _ hx => hx.2⟩

theorem conclusion_of_linkScale_one (h1 : T.linkScale = 1) (hθ : T.S.HasVolume T.thetaPilot) :
    T.Conclusion := by
  have hle : T.S.procVol T.thetaPilot ≤ T.S.procVol T.hull :=
    T.S.procVol_ind3
      (fun vQ j => ⟨T.hull_contains _ T.theta_possible vQ j, T.hull_le_integral vQ j⟩) hθ
  show T.S.procVol T.qPilot ≤ T.S.procVol T.hull
  rw [T.link_degree, h1, one_mul]
  exact hle

theorem linkScale_ne_one (hθ : T.S.HasVolume T.thetaPilot) (hc : ¬ T.Conclusion) :
    T.linkScale ≠ 1 :=
  fun h1 => hc (T.conclusion_of_linkScale_one h1 hθ)

end CitedTheory

theorem gap_between_readings :
    (∀ T : CitedTheory, T.WeakSHE) ∧ (∀ T : CitedTheory, T.StrongSHEValue ↔ T.Conclusion) ∧
      ¬ (∀ T : CitedTheory, T.StrongSHECarrier) ∧ ¬ (∀ T : CitedTheory, T.StrongSHEValue) :=
  ⟨fun T => T.weakSHE_holds, fun T => T.strongValue_iff_conclusion,
    fun h => model_q_not_possible (h modelTheory),
    fun h => model_not_conclusion ((modelTheory.strongValue_iff_conclusion).mp (h modelTheory))⟩

end CitedLV.Independence.Cor312Cited

namespace CitedLV.Independence.Cor312CitedFamily

open Src.IUT3.Theorem311
open CitedLV.Theorem311.PacketHullEndpoint

namespace CitedTheoryFam

variable (T : CitedTheoryFam)

theorem weakSHE_holds : T.WeakSHE :=
  ⟨fun c => {y | y ∈ T.Possible ∧ ∀ i, RegionLE (T.S i) (y i) (c i)},
    Set.ext fun y => ⟨fun hy => ⟨hy, T.ind3_bound y hy⟩, fun hy => hy.1⟩,
    fun _ _ hx => hx.2⟩

theorem conclusion_of_linkScale_one (h1 : T.linkScale = 1)
    (hθ : ∀ i, (T.S i).HasVolume (T.thetaPilot i)) : T.Conclusion := by
  have hle : ∑ i, (T.S i).procVol (T.thetaPilot i) ≤ ∑ i, (T.S i).procVol (T.hull i) :=
    Finset.sum_le_sum fun i _ => (T.S i).procVol_ind3
      (fun vQ j => ⟨T.hull_contains _ T.theta_possible i vQ j, T.hull_le_integral i vQ j⟩) (hθ i)
  show ∑ i, (T.S i).procVol (T.qPilot i) ≤ ∑ i, (T.S i).procVol (T.hull i)
  rw [T.link_degree, h1, one_mul]
  exact hle

theorem linkScale_ne_one (hθ : ∀ i, (T.S i).HasVolume (T.thetaPilot i)) (hc : ¬ T.Conclusion) :
    T.linkScale ≠ 1 :=
  fun h1 => hc (T.conclusion_of_linkScale_one h1 hθ)

end CitedTheoryFam

theorem gap_between_readings_fam :
    (∀ T : CitedTheoryFam, T.WeakSHE) ∧ (∀ T : CitedTheoryFam, T.StrongSHEValue ↔ T.Conclusion) ∧
      ¬ (∀ T : CitedTheoryFam, T.StrongSHECarrier) ∧ ¬ (∀ T : CitedTheoryFam, T.StrongSHEValue) :=
  ⟨fun T => T.weakSHE_holds, fun T => T.strongValue_iff_conclusion,
    fun h => strongCarrier_not_derivable_fam (fun T _ => h T),
    fun h => strongValue_not_derivable_fam (fun T _ => h T)⟩

end CitedLV.Independence.Cor312CitedFamily
