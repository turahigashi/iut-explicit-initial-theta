import Cor312LogVolume.theorem311.P211HullIndependentXiF

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.P211LambdaHullSourceBinding

open Src.IUT3.Theorem311
open Src.CoreLayer.RelativeXiFFamily
open CitedLV.Theorem311
open CitedLV.Theorem311.P211Packet
open CitedLV.Theorem311.P211ComponentCTraceBridge
open CitedLV.Theorem311.P211ComponentCRadialXiF
open CitedLV.Theorem311.P211SourceFacingSimultaneousXiF
open CitedLV.Theorem311.P211HullIndependentXiF
open CitedLV.Theorem311.NormBallHullTransport
open CitedLV.Theorem311.PacketHullEndpoint
open CitedLV.Theorem311.PacketHullPipelineAdapter
open CitedLV.Theorem311.PacketProcessionNormalizationAdapter

def SourceLambdaIntegralHullLaw
    (H : HullFamily p211PacketSystem) : Prop :=
  ∀ vQ j (c : ℚ_[211]), c ≠ 0 →
    (H vQ j).isHull
      ((fun z : ℚ_[211] => c * z) '' p211PacketSystem.integral vQ j)

theorem p211NormHulls_sourceLambdaIntegralHullLaw :
    SourceLambdaIntegralHullLaw p211NormHulls := by
  intro vQ j c hc
  change
    (normHull ℚ_[211]).isHull
      ((fun z : ℚ_[211] => c * z) '' Metric.closedBall (0 : ℚ_[211]) 1)
  refine ⟨‖c‖, norm_nonneg c, ?_⟩
  have him :
      (fun z : ℚ_[211] => c * z) ''
          Metric.closedBall (0 : ℚ_[211]) (1 : ℝ) =
        Metric.closedBall 0 (‖c‖ * 1) :=
    image_mul_closedBall c hc (r := (1 : ℝ)) (show (0 : ℝ) ≤ 1 from zero_le_one)
  simpa only [mul_one] using him

theorem qRegionIsHull_of_sourceLambdaIntegralHullLaw
    (H : HullFamily p211PacketSystem)
    (hH : SourceLambdaIntegralHullLaw H) :
    QRegionIsHull H := by
  intro vQ j
  have hc : (pElt ^ 29 : ℚ_[211]) ≠ 0 :=
    pow_ne_zero _ pElt_ne_zero
  have h := hH vQ j (pElt ^ 29) hc
  change (H vQ j).isHull (qBall 29)
  exact h

theorem p211NormHulls_qRegionIsHull :
    QRegionIsHull p211NormHulls :=
  qRegionIsHull_of_sourceLambdaIntegralHullLaw
    p211NormHulls p211NormHulls_sourceLambdaIntegralHullLaw

theorem qRegion_is_nonzero_lambda_integral
    (vQ : p211PacketSystem.PlaceQ)
    (j : Fin (p211PacketSystem.lstar + 1)) :
    ∃ c : ℚ_[211], c ≠ 0 ∧
      p211QRegion vQ j =
        (fun z : ℚ_[211] => c * z) '' p211PacketSystem.integral vQ j := by
  refine ⟨pElt ^ 29, pow_ne_zero _ pElt_ne_zero, ?_⟩
  rfl

def xifGenerated_of_sourceLambdaIntegralHullLaw
    (H : HullFamily p211PacketSystem)
    (hH : SourceLambdaIntegralHullLaw H) :
    XiFGenerated
      simultaneousPresentation
      (packetRegularHull simultaneousTrace componentCInputReadout H)
      (packetProcessionNormalization
        p211PacketSystem simultaneousTrace componentCInputReadout)
      (b := ()) p211Input :=
  P211HullIndependentXiF.xifGenerated H
    (qRegionIsHull_of_sourceLambdaIntegralHullLaw H hH)

theorem xifGenerated_nonempty_of_sourceLambdaIntegralHullLaw
    (H : HullFamily p211PacketSystem)
    (hH : SourceLambdaIntegralHullLaw H) :
    Nonempty
      (XiFGenerated
        simultaneousPresentation
        (packetRegularHull simultaneousTrace componentCInputReadout H)
        (packetProcessionNormalization
          p211PacketSystem simultaneousTrace componentCInputReadout)
        (b := ()) p211Input) :=
  ⟨xifGenerated_of_sourceLambdaIntegralHullLaw H hH⟩

end CitedLV.Theorem311.P211LambdaHullSourceBinding
end
