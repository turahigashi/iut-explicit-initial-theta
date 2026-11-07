import Cor312LogVolume.Src.IUT3.Section3Theorem311Indeterminacies

namespace Src.CoreLayer.Theorem311.PacketReadoutObject

open Src.IUT3.Theorem311

structure PacketReadoutObject (S : PacketSystem) where
  region : S.Regions

namespace PacketReadoutObject

variable {S : PacketSystem}

def coarseClass (R : PacketReadoutObject S) : S.RLGP :=
  Quot.mk _ R.region

noncomputable def value (R : PacketReadoutObject S) : ℝ :=
  S.coarseVolume R.coarseClass

theorem value_eq_procVol (R : PacketReadoutObject S) :
    R.value = S.procVol R.region := by
  rfl

def ofRegion (region : S.Regions) : PacketReadoutObject S :=
  ⟨region⟩

@[simp] theorem ofRegion_region (region : S.Regions) :
    (ofRegion region).region = region := rfl

@[simp] theorem ofRegion_value (region : S.Regions) :
    (ofRegion region).value = S.procVol region := by
  rfl

theorem coarseClass_eq_of_ind1
    (R T : PacketReadoutObject S)
    (h : S.Ind1 R.region T.region) :
    R.coarseClass = T.coarseClass := by
  exact Quot.sound (Or.inl h)

theorem coarseClass_eq_of_ind2
    (R T : PacketReadoutObject S)
    (h : S.Ind2 R.region T.region) :
    R.coarseClass = T.coarseClass := by
  exact Quot.sound (Or.inr h)

theorem value_eq_of_ind1
    (R T : PacketReadoutObject S)
    (h : S.Ind1 R.region T.region) :
    R.value = T.value := by
  rw [value_eq_procVol, value_eq_procVol]
  exact S.procVol_ind1 h

theorem value_eq_of_ind2
    (R T : PacketReadoutObject S)
    (h : S.Ind2 R.region T.region) :
    R.value = T.value := by
  rw [value_eq_procVol, value_eq_procVol]
  exact S.procVol_ind2 h

theorem quotient_readout_coherent (R : PacketReadoutObject S) :
    S.coarseVolume R.coarseClass = S.procVol R.region := by
  rfl

end PacketReadoutObject

end Src.CoreLayer.Theorem311.PacketReadoutObject
