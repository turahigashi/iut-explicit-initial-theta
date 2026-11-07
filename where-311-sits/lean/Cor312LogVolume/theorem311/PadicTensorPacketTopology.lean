import Cor312LogVolume.Src.IUT4.Section1Proposition14iiLogUnitsVolumeQp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

noncomputable section
namespace CitedLV.Theorem311.PadicTensorPacketTopology

open Metric MeasureTheory Module

instance fact211 : Fact (Nat.Prime 211) := ⟨by norm_num⟩

abbrev Coord (n : ℕ) := Fin n → ℚ_[211]

theorem coord_finiteDimensional (n : ℕ) : FiniteDimensional ℚ_[211] (Coord n) :=
  inferInstance

theorem coord_properSpace (n : ℕ) : ProperSpace (Coord n) :=
  FiniteDimensional.proper ℚ_[211] (Coord n)

theorem coord_locallyCompact (n : ℕ) : LocallyCompactSpace (Coord n) := by
  haveI := coord_properSpace n
  infer_instance

instance msCoord (n : ℕ) : MeasurableSpace (Coord n) := borel _
instance bsCoord (n : ℕ) : BorelSpace (Coord n) := ⟨rfl⟩

def haarCoord (n : ℕ) : Measure (Coord n) := by
  haveI := coord_properSpace n
  haveI := coord_locallyCompact n
  exact Measure.addHaarMeasure
    ⟨⟨closedBall (0 : Coord n) 1, isCompact_closedBall 0 1⟩,
      ⟨0, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self one_pos)⟩⟩

instance haarCoord_isAddHaar (n : ℕ) : (haarCoord n).IsAddHaarMeasure := by
  haveI := coord_properSpace n
  haveI := coord_locallyCompact n
  unfold haarCoord
  infer_instance

theorem coord_ball_compact (n : ℕ) : IsCompact (closedBall (0 : Coord n) 1) := by
  haveI := coord_properSpace n
  exact isCompact_closedBall 0 1

theorem coord_ball_interior (n : ℕ) :
    (interior (closedBall (0 : Coord n) 1)).Nonempty :=
  ⟨0, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self one_pos)⟩

abbrev TensorPacket (n : ℕ) :=
  PiTensorProduct ℚ_[211] (fun _ : Fin n => ℚ_[211])

def tensorBasis (n : ℕ) :
    Basis (Fin n → Fin 1) ℚ_[211] (TensorPacket n) :=
  Basis.piTensorProduct (fun _ => Basis.singleton (Fin 1) ℚ_[211])

theorem tensorPacket_finite (n : ℕ) : Module.Finite ℚ_[211] (TensorPacket n) :=
  Module.Finite.of_basis (tensorBasis n)

def tensorEquivCoord (n : ℕ) :
    TensorPacket n ≃ₗ[ℚ_[211]] ((Fin n → Fin 1) → ℚ_[211]) :=
  (tensorBasis n).equivFun

end CitedLV.Theorem311.PadicTensorPacketTopology
end
