import Cor312LogVolume.theorem311.PacketOutputTraceFrontier
import Cor312LogVolume.theorem311.PacketUnionHullEndpoint
import Mathlib.Order.WithBot

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.PacketProcessionNormalizationAdapter

open scoped BigOperators
open Src.IUT3.Theorem311
open Src.CoreLayer.RelativeXiFFamily
open CitedLV.Theorem311.PacketOutputTraceFrontier

variable {Input : Type}

def packetProcessionNormalization
    (S : PacketSystem) (T : PacketOutputTrace S Input)
    (qReadout : Input → ℝ) :
    ProcessionNormalization (packetFamilyPresentation T qReadout) where
  normalize := fun profile =>
    ((∑ vQ : S.PlaceQ,
        (∑ j : Fin S.lstar,
          WithBot.unbotD 0 (profile j.succ vQ)) / (S.lstar : ℝ)) : ℝ)

theorem extendedReadout_region_eq_procVol
    (S : PacketSystem) (T : PacketOutputTrace S Input)
    (qReadout : Input → ℝ) (R : S.Regions) :

    extendedFamilyReadout
        (packetFamilyPresentation T qReadout)
        (packetProcessionNormalization S T qReadout)
        (b := ()) (regionToOutputFamily S R)
      = (S.procVol R : WithTop ℝ) := by
  change
    (((∑ vQ : S.PlaceQ,
        (∑ j : Fin S.lstar,
          WithBot.unbotD 0
            ((S.packetLogVolume vQ j.succ (R vQ j.succ) : ℝ) : WithBot ℝ)) /
          (S.lstar : ℝ)) : ℝ) : WithTop ℝ)
      = (S.procVol R : WithTop ℝ)
  simp only [WithBot.unbotD_coe]
  rfl

end CitedLV.Theorem311.PacketProcessionNormalizationAdapter
end
