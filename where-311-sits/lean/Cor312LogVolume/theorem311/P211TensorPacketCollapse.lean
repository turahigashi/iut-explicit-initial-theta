import Cor312LogVolume.theorem311.PadicTensorPacketTopology
import Cor312LogVolume.theorem311.P211PacketSystem

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211TensorPacketCollapse

open CitedLV.Theorem311.PadicTensorPacketTopology
open CitedLV.Theorem311.P211Packet

def tensorEquivScalar (n : ℕ) :
    TensorPacket n ≃ₗ[ℚ_[211]] ℚ_[211] :=
  (tensorEquivCoord n).trans
    (LinearEquiv.funUnique (Fin n → Fin 1) ℚ_[211] ℚ_[211])

@[simp] theorem tensorEquivScalar_tprod
    (n : ℕ) (x : Fin n → ℚ_[211]) :
    tensorEquivScalar n (PiTensorProduct.tprod ℚ_[211] x) =
      ∏ i, x i := by
  unfold tensorEquivScalar tensorEquivCoord
  rw [LinearEquiv.trans_apply, LinearEquiv.funUnique_apply]
  change
    (tensorBasis n).repr (PiTensorProduct.tprod ℚ_[211] x)
        (fun _ => (0 : Fin 1)) =
      ∏ i, x i
  unfold tensorBasis
  rw [Basis.piTensorProduct_repr_tprod_apply]
  simp

@[simp] theorem tensorEquivScalar_tprod_const
    (n : ℕ) (c : ℚ_[211]) :
    tensorEquivScalar n
        (PiTensorProduct.tprod ℚ_[211] (fun _ : Fin n => c)) =
      c ^ n := by
  rw [tensorEquivScalar_tprod]
  simp

instance p211PacketModule
    (v : p211PacketSystem.PlaceQ)
    (j : Fin (p211PacketSystem.lstar + 1)) :
    Module ℚ_[211] (p211PacketSystem.Packet v j) :=
  inferInstanceAs (Module ℚ_[211] ℚ_[211])

def stageTensorEquivPacket
    (j : Fin (p211PacketSystem.lstar + 1)) :
    TensorPacket (j.val + 1) ≃ₗ[ℚ_[211]]
      p211PacketSystem.Packet () j :=
  tensorEquivScalar (j.val + 1)

theorem stage_tensor_carrier_equivalent
    (j : Fin (p211PacketSystem.lstar + 1)) :
    Nonempty
      (TensorPacket (j.val + 1) ≃ₗ[ℚ_[211]]
        p211PacketSystem.Packet () j) :=
  ⟨stageTensorEquivPacket j⟩

end CitedLV.Theorem311.P211TensorPacketCollapse
end
