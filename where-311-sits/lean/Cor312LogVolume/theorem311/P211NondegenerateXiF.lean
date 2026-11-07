import Cor312LogVolume.theorem311.P211ComponentCTraceBridge
import Cor312LogVolume.theorem311.P211ProcVolN
import Cor312LogVolume.theorem311.P211IndeterminacyOrbit
import Cor312LogVolume.theorem311.PacketHullPipelineAdapter
import Cor312LogVolume.theorem311.logkummer.NormBallHullTransport
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211NondegenerateXiF

open Metric
open scoped Pointwise
open Src.IUT3.Theorem311
open Src.CoreLayer.RelativeXiFFamily
open Src.CoreLayer.Theorem311.Remark395
open CitedLV.Theorem311
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211PacketN
open CitedLV.Theorem311.P211IndeterminacyOrbit
open CitedLV.Theorem311.P211ComponentCTraceBridge
open CitedLV.Theorem311.PacketOutputTraceFrontier
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Theorem311.PacketHullPipelineAdapter
open CitedLV.Theorem311.PacketProcessionNormalizationAdapter
open CitedLV.Theorem311.NormBallHullTransport

def integralContainerN : p211PacketSystemN.Regions :=
  fun vQ j => p211PacketSystemN.integral vQ j

def fieldCopyActOnContainerN
    (x : P211RLGPRaw.Global.GlobalCopy selectedLabel) (n : ℕ) :
    p211PacketSystemN.Regions :=
  fun vQ j =>
    (fun z : Fin (j.val + 1) → ℚ_[211] =>
      fun α => (fieldCopyPadicScalar x ^ n) * z α) ''
      integralContainerN vQ j

theorem qBallN_eq_closedBall (n k : ℕ) :
    qBallN n k =
      closedBall (0 : Fin n → ℚ_[211]) (((211 : ℝ)⁻¹) ^ k) := by
  rw [qBallN, closedBall_pi _ (by positivity)]
  congr 1
  funext i
  exact qBall_eq k

theorem fieldCopyActOnContainerN_y211_eq_qRegionN :
    fieldCopyActOnContainerN componentCGlobal211 29 = qRegionN := by
  funext vQ j
  unfold fieldCopyActOnContainerN integralContainerN
  rw [componentCGlobal211_padic]
  change
    (fun z : Fin (j.val + 1) → ℚ_[211] =>
      fun α => (pElt ^ 29) * z α) ''
      closedBall (0 : Fin (j.val + 1) → ℚ_[211]) 1 =
      qBallN (j.val + 1) 29
  change
    (pElt ^ 29) •
      closedBall (0 : Fin (j.val + 1) → ℚ_[211]) 1 =
      qBallN (j.val + 1) 29
  rw [qBallN_eq_closedBall]
  rw [smul_closedBall' (pow_ne_zero _ pElt_ne_zero)]
  rw [norm_pow, norm_p211]
  simp

def inputRegionN (i : ComponentCInput) : p211PacketSystemN.Regions :=
  fieldCopyActOnContainerN i.globalElement i.exponent

theorem p211Input_regionN_eq_qRegionN :
    inputRegionN p211Input = qRegionN := by
  simpa [inputRegionN, p211Input] using
    fieldCopyActOnContainerN_y211_eq_qRegionN

theorem p211Input_readout_eq_packetNProcVol :
    componentCInputReadout p211Input =
      p211PacketSystemN.procVol (inputRegionN p211Input) := by
  rw [p211Input_regionN_eq_qRegionN, p211N_procVol,
    p211Input_readout_eq_obligationE]

def nondegenerateTrace :
    PacketOutputTrace p211PacketSystemN ComponentCInput where
  Trace := fun i R => PLift (R = inputRegionN i)

theorem nondegenerateTrace_inputRegion (i : ComponentCInput) :
    Nonempty (nondegenerateTrace.Trace i (inputRegionN i)) :=
  ⟨PLift.up rfl⟩

theorem nondegenerateTrace_qRegionN :
    Nonempty (nondegenerateTrace.Trace p211Input qRegionN) := by
  refine ⟨PLift.up ?_⟩
  exact p211Input_regionN_eq_qRegionN.symm

theorem nondegenerate_tracedRegions_p211 :
    tracedRegions nondegenerateTrace p211Input = {qRegionN} := by
  ext R
  constructor
  · rintro ⟨h⟩
    exact Set.mem_singleton_iff.mpr
      (h.down.trans p211Input_regionN_eq_qRegionN)
  · intro hR
    have hR' : R = qRegionN := Set.mem_singleton_iff.mp hR
    subst R
    exact nondegenerateTrace_qRegionN

theorem qRegionN_fixed_by_actual_indeterminacies :
    (∀ y, p211PacketSystemN.Ind1 qRegionN y → y = qRegionN) ∧
    (∀ y, p211PacketSystemN.Ind2 qRegionN y → y = qRegionN) :=
  indeterminacies_fix_qRegionN

def p211NormHullsN : HullFamily p211PacketSystemN :=
  fun _ j => by
    change HullOperator (Fin (j.val + 1) → ℚ_[211])
    exact normHull (Fin (j.val + 1) → ℚ_[211])

theorem qRegionN_is_closedBall
    (vQ : p211PacketSystemN.PlaceQ)
    (j : Fin (p211PacketSystemN.lstar + 1)) :
    qRegionN vQ j =
      closedBall (0 : Fin (j.val + 1) → ℚ_[211])
        (((211 : ℝ)⁻¹) ^ 29) :=
  qBallN_eq_closedBall (j.val + 1) 29

theorem nondegenerate_union_admissible :
    UnionAdmissible p211PacketSystemN p211NormHullsN
      (tracedRegions nondegenerateTrace p211Input) := by
  rw [nondegenerate_tracedRegions_p211]
  intro vQ j
  rw [unionProfile_singleton, qRegionN_is_closedBall]
  unfold p211NormHullsN
  change Bounded
    (closedBall (0 : Fin (j.val + 1) → ℚ_[211])
      (((211 : ℝ)⁻¹) ^ 29))
  have hr : 0 ≤ (((211 : ℝ)⁻¹) ^ 29) :=
    pow_nonneg (inv_nonneg.mpr (by norm_num)) _
  exact ⟨(((211 : ℝ)⁻¹) ^ 29), hr, Set.Subset.rfl⟩

theorem nondegenerate_hull_eq_qRegionN :
    hullProfile p211PacketSystemN p211NormHullsN
        (tracedRegions nondegenerateTrace p211Input) =
      qRegionN := by
  rw [nondegenerate_tracedRegions_p211]
  unfold hullProfile
  rw [unionProfile_singleton]
  funext vQ j
  rw [qRegionN_is_closedBall]
  unfold p211NormHullsN
  change
    (normHull (Fin (j.val + 1) → ℚ_[211])).φ
        (closedBall (0 : Fin (j.val + 1) → ℚ_[211])
          (((211 : ℝ)⁻¹) ^ 29)) =
      closedBall (0 : Fin (j.val + 1) → ℚ_[211])
        (((211 : ℝ)⁻¹) ^ 29)
  have hr : 0 ≤ (((211 : ℝ)⁻¹) ^ 29) :=
    pow_nonneg (inv_nonneg.mpr (by norm_num)) _
  exact hull_closedBall (E := Fin (j.val + 1) → ℚ_[211]) hr

theorem nondegenerate_endpoint_eq_inputReadout :
    endpoint p211PacketSystemN p211NormHullsN
        (tracedRegions nondegenerateTrace p211Input) =
      componentCInputReadout p211Input := by
  unfold endpoint
  rw [nondegenerate_hull_eq_qRegionN, p211N_procVol,
    p211Input_readout_eq_obligationE]

abbrev nondegeneratePresentation :=
  packetFamilyPresentation nondegenerateTrace componentCInputReadout

def nondegenerateProducedFamily :
    ProducedFamily nondegeneratePresentation (b := ()) p211Input where
  output := regionToOutputFamily p211PacketSystemN qRegionN
  trace := by
    change nondegenerateTrace.Trace p211Input
      (outputFamilyToRegion p211PacketSystemN
        (regionToOutputFamily p211PacketSystemN qRegionN))
    rw [outputFamilyToRegion_regionToOutputFamily]
    exact nondegenerateTrace_qRegionN.some

def nondegenerateFiniteReadout :
    FiniteFamilyReadout
      nondegeneratePresentation
      (packetRegularHull
        nondegenerateTrace componentCInputReadout p211NormHullsN)
      (packetProcessionNormalization
        p211PacketSystemN nondegenerateTrace componentCInputReadout)
      (b := ()) p211Input :=
  packetFiniteReadout
    nondegenerateTrace componentCInputReadout p211NormHullsN p211Input
    nondegenerateProducedFamily nondegenerate_union_admissible

theorem nondegenerateFiniteReadout_value :
    nondegenerateFiniteReadout.value =
      componentCInputReadout p211Input := by
  calc
    nondegenerateFiniteReadout.value =
        endpoint p211PacketSystemN p211NormHullsN
          (tracedRegions nondegenerateTrace p211Input) :=
      packetFiniteReadout_value_eq_endpoint
        nondegenerateTrace componentCInputReadout p211NormHullsN p211Input
        nondegenerateFiniteReadout
    _ = componentCInputReadout p211Input :=
      nondegenerate_endpoint_eq_inputReadout

def nondegenerateXiFGenerated :
    XiFGenerated
      nondegeneratePresentation
      (packetRegularHull
        nondegenerateTrace componentCInputReadout p211NormHullsN)
      (packetProcessionNormalization
        p211PacketSystemN nondegenerateTrace componentCInputReadout)
      (b := ()) p211Input where
  readout := nondegenerateFiniteReadout
  generates_q := nondegenerateFiniteReadout_value

theorem nondegenerateXiFGenerated_value :
    nondegenerateXiFGenerated.readout.value =
      -(29 / 7) * Real.log 211 := by
  rw [nondegenerateXiFGenerated.generates_q]
  change componentCInputReadout p211Input =
    -(29 / 7) * Real.log 211
  exact p211Input_readout_eq_obligationE

theorem p211_nondegenerate_obligationE_completed :
    ∃ x :
      XiFGenerated
        nondegeneratePresentation
        (packetRegularHull
          nondegenerateTrace componentCInputReadout p211NormHullsN)
        (packetProcessionNormalization
          p211PacketSystemN nondegenerateTrace componentCInputReadout)
        (b := ()) p211Input,
      x.readout.value = -(29 / 7) * Real.log 211 :=
  ⟨nondegenerateXiFGenerated, nondegenerateXiFGenerated_value⟩

end CitedLV.Theorem311.P211NondegenerateXiF
end
