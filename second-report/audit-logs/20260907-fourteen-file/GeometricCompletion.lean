/-!
# Conditions (e) and (f), relative to the geometric interface

Append after GeometricInput, GeometricFinite, and SplitReduction.  The original
AnabelianInput and its 74-theorem baseline are left unchanged; AnabelianInputEF
extends that interface.  All numerical antecedents used below are theorems.

There are two different sorts of inputs.  GeometricData contains carriers,
interpretations, and an explicitly supplied initial lift in every fibre.
GeometricRules contains seven propositions: five cited-result applications and
two named modelling links (datum_localization and galois_transport).  A locator
on a modelling link identifies its intended source interpretation; it does NOT
mean that the paper proves a theorem about these Lean encodings.

The local interpretation retains split Tate reduction, rational ORIGINAL
E[7] and E[2], roots of unity, and the LOCAL CANONICAL toric model, its period and
arithmetic splitting.  Before flag correction these are not identified with the
fixed global quotient.  That identification is the graph rule's conclusion.
A split Tate curve alone does not make E(k)[7] surject onto
Z/7.  EtTh Cor. 2.9 labels cusp automorphism-orbits; our CanonicalCusp predicate
concerns the fixed single-underlined quotient (EtTh Rem. 2.6.1).

The base of places is arbitrary, not a finite substitute for all number-field
places.  The input initialLift is named data, not an application of choice or an
assertion that the required final marked section already exists.  It can have
the wrong flag.  We compute different correcting matrices at different places.
The finite-cardinality statement is stated only for a finite base.

The relative conclusions below do not instantiate this entire interface in an
algebraic number-field library.  The scalar-extension, number-field, curve, and
Galois-realization adapters remain explicit inputs.  The nondegeneracy and
deletion countermodels check the logical interface, not those geometric adapters.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace IMQGeomEF

open IMQGeom IMQGeomFinite

/-- The one fixed global line and quotient class, used at every place. -/
def fixedFlag : Nat := flagKey (lineOf 1) 7

/-- The fixed line and quotient class really form one of the 24 marked flags. -/
theorem fixed_flag_valid : fixedFlag ∈ allFlags := by decide

/-- The actual Legendre cubic on Gaussian integers. -/
def cubicAt (x : IMQGeom.GI) : IMQGeom.GI :=
  GI.mul x (GI.mul (GI.sub x GI.one) (GI.sub x IMQGeom.a))

/-- The three nonidentity 2-torsion candidates have y=0 and rational x=0,1,a.
The elliptic-curve identification of these roots with E[2] is part of the named
datum adapter, not an extra finite calculation assumed downstream. -/
theorem two_torsion_roots_computed :
    cubicAt ⟨0, 0⟩ = ⟨0, 0⟩ ∧ cubicAt GI.one = ⟨0, 0⟩ ∧
      cubicAt IMQGeom.a = ⟨0, 0⟩ := by decide

/-- The exact numerical inputs to the localization adapter.  They include actual
curve reductions and polynomial coefficients, not a predicate named 'is split'. -/
def ConcreteChecks : Prop :=
  (cubicAt ⟨0, 0⟩ = ⟨0, 0⟩ ∧ cubicAt GI.one = ⟨0, 0⟩ ∧
    cubicAt IMQGeom.a = ⟨0, 0⟩) ∧
  IMQSplit.shiftedRhs 0 0 = [0, 0, -1, 1] ∧
  IMQSplit.shiftedRhs 1 1 = [0, 0, 1, 1] ∧
  ((33 : Fin 109) * 33 + 1 = 0 ∧ (76 : Fin 109) * 76 + 1 = 0 ∧
    (33 : Fin 109) ≠ 76 ∧ (10 : Fin 109) + 3 * 33 = 0 ∧
    IMQ7.aMod 109 33 = 0 ∧ IMQ7.aMod 109 76 ≠ 0 ∧ IMQ7.aMod 109 76 ≠ 1) ∧
  (∀ q : Nat, 2 < q →
    IMQSplit.reduceQuadratic q (IMQSplit.lineProduct 1 (-1)) =
      IMQSplit.reduceQuadratic q (IMQSplit.quadraticPart (IMQSplit.shiftedRhs 1 1)) ∧
    (1 : Int) % (q : Int) ≠ (-1 : Int) % (q : Int))

/-- Discharge every arithmetic premise of ConcreteChecks from kernel proofs. -/
theorem concrete_checks : ConcreteChecks :=
  ⟨two_torsion_roots_computed, IMQSplit.zero_center_expansion,
    IMQSplit.one_center_expansion, IMQSplit.residue109_certificate,
    IMQSplit.one_cone_split_modulo⟩

/-- Carriers and interpretations, not assumed conclusions.  The bracketed
locators specify what each carrier/predicate is to represent. -/
structure GeometricData where
  /-- [IUT1, Def. 3.1(e)] the complete moduli-place type, possibly infinite. -/
  ModPlace : Type
  /-- [IUT1, Def. 3.1(e)] places of K above the specified moduli place. -/
  Fibre : ModPlace → Type
  /-- [IUT1, Def. 3.1(e)] explicitly supplied unadjusted lifts.  This is input
  data (the initial lying-over choices), not a proved global choice principle. -/
  initialLift : (u : ModPlace) → Fibre u
  /-- [IUT1, Def. 3.1(b),(e)] the selected-bad classification. -/
  bad : ModPlace → Bool
  /-- [EtTh, Def. 2.5(i), Cor. 2.9] the local toric line and nonzero quotient
  class up to sign, encoded using GeometricInput's finite flag representation. -/
  localFlag : (u : ModPlace) → Fibre u → Nat
  /-- [IUT1, Def. 3.1(c),(e)] move a place by the inverse of a realized matrix.
  Keeping the fibre index in the type prevents movement to another moduli place.
  Compatibility with actual automorphisms is the named galois_transport link. -/
  move : (u : ModPlace) → Nat → Fibre u → Fibre u
  /-- [IUT1, §1, Def. 1.1, Rem. 1.1.2; EtTh, Def. 2.1] the global geometric
  setup: characteristic zero, original X of type (1,1), the fixed
  type-(1,7-tors)^± quotient and NONZERO cusp, and the trivial original mod-7
  torsion action.  It includes the finite etale maps from X and the quotient
  to the same hemi-elliptic curve interpreted by A.X0, not its corehood.
  core_of_datum supplies that corehood; common-core consequences are then used
  in the arrow rule.  No full rationality of quotient E'[7] is included. -/
  GlobalSetup : Prop
  /-- [EtTh, Thm. 1.10(iii), Prop. 2.2(ii), Def. 2.5(i); IUT1, Def. 3.1(e)]
  neutral local setup: a finite extension of Q_p with p≠2,7, split Tate
  uniformization, full original
  E[7] and E[2], μ7 and μ12, the LOCAL CANONICAL toric quotient/period and its
  arithmetic splitting, with the stated finite torsion coordinates.  The original
  local curve and its hemi-elliptic quotient are base changes of the named global
  data; this does not yet identify the auxiliary canonical toric cover with the
  fixed global cover.  No local-core assertion is
  included here.  It does
  NOT identify the fixed global quotient with this toric model at the initial
  lift; the flag may differ.  Identification occurs only after correction.
  The identification of these hypotheses with the actual curve is explicit in
  datum_localization; it is not certified by the polynomial computations alone. -/
  LocalSetup : (u : ModPlace) → Fibre u → Prop
  /-- [IUT1, Def. 3.1(e), p.63] K_v equals double-dotted K_v. -/
  SameLocalField : (u : ModPlace) → Fibre u → Prop
  /-- [EtTh, Def. 2.5(i), Cor. 2.9, Rem. 2.6.1; IUT1, Def. 3.1(f)]
  the fixed global dual quotient identifies with the local graph quotient,
  and its fixed cusp has canonical label ±1 for the single-underlined curve.
  This is the post-match conclusion, not part of the initial local setup. -/
  CanonicalCusp : (u : ModPlace) → Fibre u → Prop
  /-- [EtTh, Def. 2.5(i); IUT1, Def. 3.1(e)] the compatible local arithmetic
  theta model, including the stated cover and subgroup data. -/
  ThetaModel : (u : ModPlace) → Fibre u → Prop
  /-- [IUT1, §1, Def. 1.1, Rem. 1.1.2, Def. 3.1(f)] global arrow-marked
  covers, determined up to base-field isomorphism, at the specified cusp and
  their base changes at EVERY good place (including complex places).  This refers
  to the original torsion-rational curve, not rationality of the quotient E'[7].
  The Nat argument is the AUXILIARY cusp multiplier used in the construction;
  it does not replace the fixed marked cusp ε with another cusp. -/
  ArrowCovers : Nat → Prop

/-- A fixed finite list of the seven logical obligations, used to make deletion
countermodels precise.  Removing a carrier is ill-typed, not a logical weakening;
necessity below concerns each new proof field, including both modelling links. -/
inductive Obligation where
  | datum | tate | transport | field | graph | theta | arrow
deriving DecidableEq, Repr

/-- Explicit statements of the rules; none is a global Lean axiom. -/
def Rule (A : AnabelianInput) (D : GeometricData) : Obligation → Prop
  | .datum => ConcreteChecks →
      D.GlobalSetup ∧ ∀ u, D.bad u = true → D.LocalSetup u (D.initialLift u)
  | .tate => ∀ u w, D.bad u = true → D.LocalSetup u w → D.localFlag u w ∈ allFlags
  | .transport => ∀ u w m, D.bad u = true → D.LocalSetup u w → m ∈ SL7 →
      actFlag m (lineOf 1) 7 = D.localFlag u w →
      D.LocalSetup u (D.move u m w) ∧ D.localFlag u (D.move u m w) = fixedFlag
  | .field => ∀ u w, D.bad u = true → D.LocalSetup u w → D.SameLocalField u w
  | .graph => ∀ u w, D.bad u = true → D.LocalSetup u w →
      D.localFlag u w = fixedFlag → D.CanonicalCusp u w
  | .theta => A.IsCore A.X0 → ∀ u w, D.bad u = true → D.LocalSetup u w →
      D.SameLocalField u w → D.CanonicalCusp u w → D.ThetaModel u w
  | .arrow => A.IsCore A.X0 → D.GlobalSetup →
      (5 ≤ 7 ∧ Nat.gcd 7 6 = 1) →
      ((List.range 7).all (fun x => x == 0 ||
        ((2 * x % 7 != x) && (2 * x % 7 != (7 - x) % 7))) = true) →
      D.ArrowCovers 2

/-- Public results interpreted in the explicitly specified geometric data.
The two modelling fields expose the remaining representation boundary. -/
structure GeometricRules (A : AnabelianInput) (D : GeometricData) : Prop where
  /-- [IUT1, Def. 3.1(c),(d),(e); EtTh, §1, Thm. 1.10(iii), Def. 2.1]
  THE MODELLING LINK for the actual datum/localizations.  Given the computed
  polynomial, torsion-root and residue certificates, identifies the supplied
  global/local setup with the constructed number-field and curve data.  This is
  an explicit interface premise, not a theorem of Lean or a verbatim claim that
  these cited definitions formalize the number-field adapter. -/
  datum_localization : Rule A D .datum
  /-- [EtTh, §1, pp.10–12, displayed Tate/graph exact sequence;
  Def. 2.5(i)] the geometric torsion consequence is the exact sequence
  0→μ7→E(kbar)[7]→Z/7→0 gives the toric marked flag.  Its E(k)[7] form here
  uses full original 7-torsion and torsion coordinates in LocalSetup. -/
  tate_marked_flag : Rule A D .tate
  /-- [IUT1, Def. 3.1(c),(e); EtTh, Cor. 2.9] THE MODELLING LINK for the
  realized SL2 action and completion/localization covariance.  The inverse
  convention moves a local flag reached from the fixed flag back to that fixed
  flag.  Group generation is not asserted anew by this field; its identification
  with the actual Galois action is exposed here. -/
  galois_transport : Rule A D .transport
  /-- [IUT1, Def. 3.1(e), p.63; EtTh, §1, pp.12,16] in the split Tate setup,
  rational original E[2] gives K_v=double-dotted K_v.  Rational original E[2]
  is part of LocalSetup, connected to the computed Legendre roots above. -/
  rational_two_field : Rule A D .field
  /-- [EtTh, Def. 2.5(i), Cor. 2.9, Rem. 2.6.1] matching the fixed flag
  identifies the fixed global dual quotient with the LOCAL CANONICAL toric
  model and gives graph label ±1 for its fixed cusp.  LocalSetup supplies μ7
  and the canonical model's period, without this global identification; no claim
  that all theta covers have a unique cusp is made. -/
  graph_cusp_label : Rule A D .graph
  /-- [CanLift, Prop. 2.3(i),(ii); EtTh, Thm. 1.10(iii), Prop. 2.2(ii),
  Def. 2.5(i); IUT1, Def. 3.1(e)]
  the core, split Tate model, field equality and post-match graph/cusp
  identification supply the local arithmetic theta model for the FIXED global
  data.  LocalSetup's arithmetic splitting belongs to the local canonical toric
  model and is transported through that identification only at this stage.
  CanLift supplies the base-change/descent of the proved global core to the
  specified local curves; local corehood is not another setup assumption. -/
  arithmetic_theta_model : Rule A D .theta
  /-- [IUT1, §1, Def. 1.1, Rem. 1.1.2, Def. 3.1(f)] the common core,
  torsion-rational original curve and fixed type-(1,7-tors)^± quotient give the
  arrow-marked covers associated with ε using the AUXILIARY cusp 2ε when
  2ξ≠±ξ, up to base-field isomorphism; this
  includes all their good-place base changes.  The core is supplied by
  core_of_datum and the finite etale maps in GlobalSetup, not a common-core
  premise hidden in GlobalSetup.  The numeric restrictions on 7 and noncoincidence are discharged
  below, rather than assumed as extra fields. -/
  arrow_marked_covers : Rule A D .arrow

/-- Extend, rather than alter, the already checked core interface. -/
structure AnabelianInputEF extends AnabelianInput where
  /-- [IUT1, Def. 3.1(e),(f)] named carriers and interpretations. -/
  geometry : GeometricData
  /-- [IUT1, Def. 3.1(e),(f)] the seven separately inspected relative premises. -/
  geometricRules : GeometricRules toAnabelianInput geometry

/-- Correct each bad place independently; good places keep their supplied lift. -/
def correctedLift (D : GeometricData) (u : D.ModPlace) : D.Fibre u :=
  if D.bad u then
    D.move u (matrixForFlag (D.localFlag u (D.initialLift u))) (D.initialLift u)
  else D.initialLift u

/-- A good place keeps its original lift; correction is confined to bad fibres. -/
theorem corrected_lift_good (D : GeometricData) (u : D.ModPlace)
    (hu : D.bad u = false) : correctedLift D u = D.initialLift u := by
  simp [correctedLift, hu]

/-- The selected places above distinct moduli places cannot coincide.  This
uses the fibre index, with no geometric law or finiteness assumption. -/
theorem corrected_places_distinct (D : GeometricData) (u v : D.ModPlace)
    (huv : u ≠ v) : select (correctedLift D) u ≠ select (correctedLift D) v := by
  intro h
  exact huv (select_injective (correctedLift D) h)

/-- The finite-field search and the localization rule produce the SAME fixed
global flag at every selected bad place, without changing the global cusp. -/
theorem corrected_lift_has_fixed_flag (A : AnabelianInput) (D : GeometricData)
    (H : GeometricRules A D) (u : D.ModPlace) (hu : D.bad u = true) :
    D.LocalSetup u (correctedLift D u) ∧ D.localFlag u (correctedLift D u) = fixedFlag := by
  have hlocal := (H.datum_localization concrete_checks).2 u hu
  have valid := H.tate_marked_flag u (D.initialLift u) hu hlocal
  -- The old transitivity theorem is retained, together with actual representatives.
  have representative := flags_transitive_with_representatives.2 _ valid
  have result := H.galois_transport u (D.initialLift u)
    (matrixForFlag (D.localFlag u (D.initialLift u))) hu hlocal
    representative.1 representative.2
  simpa [correctedLift, hu] using result

/-- The section is bijective over all moduli places, not just a finite list. -/
theorem corrected_section_bijective (D : GeometricData) :
    (∀ p q : Selected (correctedLift D),
      selectedProjection p = selectedProjection q → p = q) ∧
    (∀ u : D.ModPlace, ∃ p : Selected (correctedLift D), selectedProjection p = u) :=
  selectedProjection_bijective (correctedLift D)

/-- Local fields, theta models and the prescribed ±1 cusp at all bad places. -/
theorem bad_place_conditions (A : AnabelianInput) (D : GeometricData)
    (H : GeometricRules A D) (u : D.ModPlace) (hu : D.bad u = true) :
    D.SameLocalField u (correctedLift D u) ∧
    D.ThetaModel u (correctedLift D u) ∧ D.CanonicalCusp u (correctedLift D u) := by
  have h := corrected_lift_has_fixed_flag A D H u hu
  have field := H.rational_two_field u (correctedLift D u) hu h.1
  have cusp := H.graph_cusp_label u (correctedLift D u) hu h.1 h.2
  exact ⟨field, H.arithmetic_theta_model (core_of_datum A)
    u (correctedLift D u) hu h.1 field cusp, cusp⟩

/-- The good-place covers use the ORIGINAL curve's torsion and the already
proved 2ξ≠±ξ statement, with the numerical conditions on ell=7 discharged. -/
theorem arrow_covers_of_datum (A : AnabelianInput) (D : GeometricData)
    (H : GeometricRules A D) : D.ArrowCovers 2 :=
  H.arrow_marked_covers (core_of_datum A) (H.datum_localization concrete_checks).1
    (by decide) two_xi_ne_pm_xi

/-- The encoded (e),(f) conclusions.  Geometric predicates retain the explicit
interface interpretation; this is not a library definition of number-field IUT data. -/
def ConditionsEF (D : GeometricData) : Prop :=
  ((∀ p q : Selected (correctedLift D), selectedProjection p = selectedProjection q → p = q) ∧
   (∀ u : D.ModPlace, ∃ p : Selected (correctedLift D), selectedProjection p = u)) ∧
  (∀ u, D.bad u = true → D.SameLocalField u (correctedLift D u) ∧
    D.ThetaModel u (correctedLift D u) ∧ D.CanonicalCusp u (correctedLift D u)) ∧
  D.ArrowCovers 2

/-- Conditions (e),(f) relative to the listed sources and modelling links. -/
theorem conditions_e_f (A : AnabelianInput) (D : GeometricData)
    (H : GeometricRules A D) : ConditionsEF D :=
  ⟨corrected_section_bijective D, bad_place_conditions A D H, arrow_covers_of_datum A D H⟩

/-- Join the previously proved core condition with the new (e),(f) conclusions.
The full geometric realization remains relative to AnabelianInputEF. -/
theorem conditions_d_e_f (A : AnabelianInputEF) :
    A.IsCore A.X0 ∧ ConditionsEF A.geometry :=
  ⟨core_of_datum A.toAnabelianInput,
    conditions_e_f A.toAnabelianInput A.geometry A.geometricRules⟩

end IMQGeomEF
