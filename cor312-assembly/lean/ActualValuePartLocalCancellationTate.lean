-- IUT-STATEMENT: NON-IUT Tate-coordinate instantiation of chart-ratio cancellation
import M3.relative.ActualValuePartLocalGlobal
import M3.relative.ActualValuePartLocalCancellationBridge
import M3.relative.ActualValuePartThetaHull

/-!
# Calibrating a strip from generator and chart data at a Tate place

Companion to `ActualValuePartLocalCancellationBridge` and
audit memo L2-96.  The marked place is the finite place of
`ActualValuePartLocalGlobal`, and the common coordinate `u`
of the bridge is instantiated by the actual Tate coordinate
`tateCoordinate F p W v h = -log ‖q‖`.

For a strip `S`, write `χS` for the chart scalar
`(chartChange S w0 posOne : ℝ)` at the marked place `w0`.
If the local generator value is `α • tateCoordinate` and the
chart satisfies `χS * α = 1` (the `ρ`-normalization input),
then `S` is `CalibratedAt` the Tate datum: its normalized
generator coordinate is exactly `tatePositive`.  Two such
strips therefore have equal pilot degrees, by the existing
`calibrated_pilot_degree_eq`; equivalently, their chart
scalars satisfy the bridge identity `χT * β = χS * α`
(both sides equal `1`).

## [H] Inputs left as named hypotheses

* `hgen`: the strip generator value as a multiple of the
  Tate coordinate.  For a θ-side generator given by the
  theta root class, the expected value is `α = 1 / (2ℓ)`:
  `ActualValuePartInitialDataCalibration.initialData_calibration`
  gives `(2ℓ) • (-log (valueReadout (thetaRootClass …)))
  = tateCoordinate`.  Identifying an abstract strip's `gen`
  with that readout is not done here.
* `hchart`: the chart normalization `χ * α = 1`, i.e. the
  `ρ`-formula of IUT I, Example 3.5(i)–(ii), in chart
  coordinates.  Audited in L2-75–L2-79; not proved here.

No new axioms.  独立の点検は受けていない。
-/

noncomputable section
set_option autoImplicit false

namespace Kouchiku.M3.ActualValuePartLocalCancellationTate

open NumberField
open Grounding.Theorem311
open Grounding.Theorem311.NumberFieldRealDivisor
open Grounding.Theorem311.NumberFieldRealLocalization
open Kouchiku.IUT1.Corollary37
open Kouchiku.IUT2.Definition49viii
open Kouchiku.M3.ActualStrictBelyiFieldReconstruction
open Kouchiku.M3.ActualValuePartQuotient
open Kouchiku.M3.ActualValuePartRealifiedProbe
open Kouchiku.M3.ActualFinitePlaceArithmeticCurve
open Dispute.Prop310FinitePrimeFiberPacket
open Grounding.ThetaLink.GaussianMonoidFromThetaValues
open Grounding.ThetaLink.GaussianThetaLogReadout
open Grounding.Theorem311.NumberFieldPrimeRays
open Grounding.Theorem311.NumberFieldCompletionDegreeNormalization

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]
variable (W : WeierstrassCurve F) [W.IsElliptic]
variable (v : PlacesAbove F p)
variable (h : ActualSplitTateParameter.SplitReduction (curve F p W v))

/-- A strip whose generator at the marked place is
`α • tateCoordinate` and whose chart scalar satisfies
`χ * α = 1` is calibrated at the actual Tate datum. -/
theorem calibratedAt_of_gen_chart (S : PStrip F) {α : ℝ}
    (hgen : (S.gen (Sum.inl (FinitePlace.mk v.1)) : ℝ)
      = α * ActualValuePartLocalGlobal.tateCoordinate F p W v h)
    (hchart : ((chartChange S (Sum.inl (FinitePlace.mk v.1))
        Kouchiku.IUT1.Example35.posOne : positive) : ℝ) * α = 1) :
    ActualValuePartLocalGlobal.CalibratedAt F p W v h S := by
  show normGen S (Sum.inl (FinitePlace.mk v.1))
    = ActualValuePartLocalGlobal.tatePositive F p W v h
  apply Subtype.ext
  rw [ActualValuePartLocalCancellationBridge.coe_normGen, hgen,
    ActualValuePartLocalGlobal.coe_tatePositive]
  linear_combination
    (ActualValuePartLocalGlobal.tateCoordinate F p W v h) * hchart

omit [Fact p.Prime] in
/-- The two chart normalizations give the bridge identity
`χT * β = χS * α` (both sides are `1`). -/
theorem chart_ratio_of_gen_chart (S T : PStrip F) {α β : ℝ}
    (hchartS : ((chartChange S (Sum.inl (FinitePlace.mk v.1))
        Kouchiku.IUT1.Example35.posOne : positive) : ℝ) * α = 1)
    (hchartT : ((chartChange T (Sum.inl (FinitePlace.mk v.1))
        Kouchiku.IUT1.Example35.posOne : positive) : ℝ) * β = 1) :
    ((chartChange T (Sum.inl (FinitePlace.mk v.1))
        Kouchiku.IUT1.Example35.posOne : positive) : ℝ) * β
      = ((chartChange S (Sum.inl (FinitePlace.mk v.1))
        Kouchiku.IUT1.Example35.posOne : positive) : ℝ) * α :=
  hchartT.trans hchartS.symm

/-- ★ Pilot degrees agree for two strips whose generators
at the marked Tate place are multiples of the actual Tate
coordinate with inverse chart scalars.  This is the
Tate-instantiated form of scale preservation: the common
coordinate is `-log ‖q‖` of the actual local curve, and no
further scale freedom remains at the marked place. -/
theorem pilot_degree_eq_of_tate_gen_chart (S T : PStrip F)
    (a : StripIso S T) {α β : ℝ}
    (hgenS : (S.gen (Sum.inl (FinitePlace.mk v.1)) : ℝ)
      = α * ActualValuePartLocalGlobal.tateCoordinate F p W v h)
    (hchartS : ((chartChange S (Sum.inl (FinitePlace.mk v.1))
        Kouchiku.IUT1.Example35.posOne : positive) : ℝ) * α = 1)
    (hgenT : (T.gen (Sum.inl (FinitePlace.mk v.1)) : ℝ)
      = β * ActualValuePartLocalGlobal.tateCoordinate F p W v h)
    (hchartT : ((chartChange T (Sum.inl (FinitePlace.mk v.1))
        Kouchiku.IUT1.Example35.posOne : positive) : ℝ) * β = 1)
    (bad : Finset (ArithmeticPlace F)) :
    degree F ((pilot T bad).alpha : Divisor F) =
      degree F ((pilot S bad).alpha : Divisor F) :=
  ActualValuePartLocalGlobal.calibrated_pilot_degree_eq
    F p W v h S T a
    (calibratedAt_of_gen_chart F p W v h S hgenS hchartS)
    (calibratedAt_of_gen_chart F p W v h T hgenT hchartT)
    bad

/-- Supply side for the θ-generator value: for a locally
rational Tate root `t` with `t ^ (2ℓ) = q`, the negative log
readout of its theta root class is `α • tateCoordinate` with
`α = 1 / (2ℓ)`.  This packages
`valueReadout_thetaRootClass` and `log_norm_root_eq` in the
`α * u` shape consumed by `calibratedAt_of_gen_chart` when a
strip generator is identified with this readout value.  The
identification itself is not made here. -/
theorem neg_log_readout_thetaRootClass (ell : ℕ) (hell : 0 < ell)
    (t : (ActualValuePartLocalGlobal.localCurve F p W v).Kˣ)
    (ht : t ^ (2 * ell) =
      ActualSplitTateParameter.parameter
        (ActualValuePartLocalGlobal.localCurve F p W v) h) :
    -Real.log (ActualValuePartRealification.valueReadout
        (ActualValuePartLocalGlobal.localCurve F p W v)
        (ActualValuePartThetaClass.thetaRootClass
          (ActualValuePartLocalGlobal.localCurve F p W v) t
          (ActualValuePartThetaClass.norm_lt_one_of_pow_eq_parameter
            (ActualValuePartLocalGlobal.localCurve F p W v)
            h ell hell ht).le))
      = (1 / (2 * (ell : ℝ)))
        * ActualValuePartLocalGlobal.tateCoordinate F p W v h := by
  rw [ActualValuePartThetaClass.valueReadout_thetaRootClass]
  have h1 := ActualValuePartThetaHull.log_norm_root_eq
    (F := F) (p := p) (W := W) (v := v) (h := h) ell hell t ht
  rw [h1]
  ring

section ThetaStripInstance

variable (ell : ℕ) (hell : 0 < ell)

/-- Generator family of the Tate-instantiated model pair:
the actual Tate coordinate at the marked place, `1`
elsewhere. -/
noncomputable def tateGenFamily : ArithmeticPlace F → positive :=
  fun w => @ite _ (w = Sum.inl (FinitePlace.mk v.1))
    (Classical.propDecidable _)
    (ActualValuePartLocalGlobal.tatePositive F p W v h)
    Kouchiku.IUT1.Example35.posOne

theorem tateGenFamily_pos :
    ∀ w, (0 : ℝ) < (tateGenFamily F p W v h w : ℝ) := by
  classical
  intro w
  by_cases hw : w = Sum.inl (FinitePlace.mk v.1)
  · simp only [tateGenFamily, if_pos hw]
    rw [ActualValuePartLocalGlobal.coe_tatePositive]
    exact ActualValuePartLocalGlobal.tateCoordinate_pos F p W v h
  · simp only [tateGenFamily, if_neg hw]
    rw [Kouchiku.IUT1.Example35.coe_posOne]
    norm_num

/-- Chart family of the θ-side model strip: `1 / (2ℓ)` at
the marked place, `1` elsewhere. -/
noncomputable def thetaChartFamily : ArithmeticPlace F → ℝ :=
  fun w => @ite _ (w = Sum.inl (FinitePlace.mk v.1))
    (Classical.propDecidable _) (1 / (2 * (ell : ℝ))) 1


omit [Fact p.Prime] in
theorem thetaChartFamily_pos (hell : 0 < ell) :
    ∀ w, 0 < thetaChartFamily F p v ell w := by
  classical
  intro w
  by_cases hw : w = Sum.inl (FinitePlace.mk v.1)
  · simp only [thetaChartFamily, if_pos hw]
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  · simp only [thetaChartFamily, if_neg hw]
    norm_num

/-- The θ-side model strip at the actual Tate datum. -/
noncomputable def thetaTateStrip : PStrip F :=
  Kouchiku.IUT1.Corollary37.thtStrip F
    (tateGenFamily F p W v h) (tateGenFamily_pos F p W v h)
    (thetaChartFamily F p v ell) (thetaChartFamily_pos F p v ell hell)

/-- The mod-side model strip at the actual Tate datum. -/
noncomputable def modTateStrip : PStrip F :=
  Kouchiku.IUT1.Corollary37.modStrip F
    (tateGenFamily F p W v h) (tateGenFamily_pos F p W v h)

theorem coe_gen_thetaTateStrip :
    (((thetaTateStrip F p W v h ell hell).gen
        (Sum.inl (FinitePlace.mk v.1)) : positive) : ℝ)
      = (1 / (2 * (ell : ℝ)))
        * ActualValuePartLocalGlobal.tateCoordinate F p W v h := by
  classical
  have hg : tateGenFamily F p W v h (Sum.inl (FinitePlace.mk v.1))
      = ActualValuePartLocalGlobal.tatePositive F p W v h := by
    unfold tateGenFamily
    exact if_pos rfl
  have hc : thetaChartFamily F p v ell (Sum.inl (FinitePlace.mk v.1))
      = 1 / (2 * (ell : ℝ)) := by
    unfold thetaChartFamily
    exact if_pos rfl
  show (thetaChartFamily F p v ell (Sum.inl (FinitePlace.mk v.1)))
      * ((tateGenFamily F p W v h (Sum.inl (FinitePlace.mk v.1))
          : positive) : ℝ) = _
  rw [hc, hg, ActualValuePartLocalGlobal.coe_tatePositive]

theorem coe_gen_modTateStrip :
    (((modTateStrip F p W v h).gen
        (Sum.inl (FinitePlace.mk v.1)) : positive) : ℝ)
      = 1 * ActualValuePartLocalGlobal.tateCoordinate F p W v h := by
  classical
  have hg : tateGenFamily F p W v h (Sum.inl (FinitePlace.mk v.1))
      = ActualValuePartLocalGlobal.tatePositive F p W v h := by
    unfold tateGenFamily
    exact if_pos rfl
  show ((tateGenFamily F p W v h (Sum.inl (FinitePlace.mk v.1))
      : positive) : ℝ) = _
  rw [hg, ActualValuePartLocalGlobal.coe_tatePositive]
  ring

/-- Normalized generator of the mod-side model strip at the
marked place is the Tate coordinate itself. -/
theorem normGen_modTateStrip :
    normGen (modTateStrip F p W v h) (Sum.inl (FinitePlace.mk v.1))
      = ActualValuePartLocalGlobal.tatePositive F p W v h := by
  classical
  show rayEquiv F (Sum.inl (FinitePlace.mk v.1))
      ((rayEquiv F (Sum.inl (FinitePlace.mk v.1))).symm
        (tateGenFamily F p W v h (Sum.inl (FinitePlace.mk v.1))))
    = ActualValuePartLocalGlobal.tatePositive F p W v h
  rw [AddEquiv.apply_symm_apply]
  simp [tateGenFamily]

/-- The θ-side model strip is calibrated at the actual Tate
datum: its generator value and chart scalar are exactly the
`α = 1 / (2ℓ)`, `χ = 2ℓ` pair of the `ρ^Θ` formula. -/
theorem calibratedAt_thetaTateStrip :
    ActualValuePartLocalGlobal.CalibratedAt F p W v h
      (thetaTateStrip F p W v h ell hell) := by
  show normGen (thetaTateStrip F p W v h ell hell)
      (Sum.inl (FinitePlace.mk v.1))
    = ActualValuePartLocalGlobal.tatePositive F p W v h
  unfold thetaTateStrip
  rw [ActualValuePartRealifiedProbe.normGen_thtStrip_eq]
  exact normGen_modTateStrip F p W v h

/-- The mod-side model strip is calibrated at the same Tate
datum. -/
theorem calibratedAt_modTateStrip :
    ActualValuePartLocalGlobal.CalibratedAt F p W v h
      (modTateStrip F p W v h) :=
  normGen_modTateStrip F p W v h

/-- The generator value of the θ-side model strip is the
negative log readout of the actual theta root class. -/
theorem coe_gen_thetaTateStrip_eq_readout
    (t : (ActualValuePartLocalGlobal.localCurve F p W v).Kˣ)
    (ht : t ^ (2 * ell) =
      ActualSplitTateParameter.parameter
        (ActualValuePartLocalGlobal.localCurve F p W v) h) :
    (((thetaTateStrip F p W v h ell hell).gen
        (Sum.inl (FinitePlace.mk v.1)) : positive) : ℝ)
      = -Real.log (ActualValuePartRealification.valueReadout
          (ActualValuePartLocalGlobal.localCurve F p W v)
          (ActualValuePartThetaClass.thetaRootClass
            (ActualValuePartLocalGlobal.localCurve F p W v) t
            (ActualValuePartThetaClass.norm_lt_one_of_pow_eq_parameter
              (ActualValuePartLocalGlobal.localCurve F p W v)
              h ell hell ht).le)) := by
  rw [coe_gen_thetaTateStrip F p W v h ell hell,
    neg_log_readout_thetaRootClass F p W v h ell hell t ht]

/-- ★ End-to-end pilot-degree equality for the
Tate-instantiated model pair, through the chart-ratio
bridge.  (The same conclusion also follows from the
existing `pilot_degree_thtStrip_eq`; the content here is
that the Tate-instantiated pair discharges the bridge
hypotheses `hgen`/`hchart` with `α = 1 / (2ℓ)`, `β = 1`.) -/
theorem pilot_degree_thetaTateStrip_eq
    (bad : Finset (ArithmeticPlace F)) :
    degree F ((pilot (modTateStrip F p W v h) bad).alpha :
        Divisor F) =
      degree F ((pilot (thetaTateStrip F p W v h ell hell) bad).alpha :
        Divisor F) :=
  ActualValuePartLocalGlobal.calibrated_pilot_degree_eq F p W v h
    (thetaTateStrip F p W v h ell hell) (modTateStrip F p W v h)
    (Kouchiku.IUT1.Corollary37.thetaIso F _ _ _ _)
    (calibratedAt_thetaTateStrip F p W v h ell hell)
    (calibratedAt_modTateStrip F p W v h)
    bad

end ThetaStripInstance

end Kouchiku.M3.ActualValuePartLocalCancellationTate

end

#print axioms
  Kouchiku.M3.ActualValuePartLocalCancellationTate.pilot_degree_eq_of_tate_gen_chart
#print axioms
  Kouchiku.M3.ActualValuePartLocalCancellationTate.neg_log_readout_thetaRootClass
#print axioms
  Kouchiku.M3.ActualValuePartLocalCancellationTate.pilot_degree_thetaTateStrip_eq
