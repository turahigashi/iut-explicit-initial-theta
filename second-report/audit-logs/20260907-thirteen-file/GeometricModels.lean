/-!
# Finite models for the seven geometric proof fields

Append after GeometricCompletion.lean.  This file checks the logical interface,
not a number-field realization of its predicates or a proof of its cited results.
The core component reuses the existing nonconstant `IMQGeom.witness`.

There are two moduli places (false = bad, true = good), and two lifts over each
place.  At the bad place the supplied lift has a noncanonical flag; the complete
model really changes that lift.  The cusp predicate distinguishes the two lifts.
An omitted proof field changes the corresponding interpretation, while the other
six rules remain true.  Thus these are deletion countermodels for this explicit
interface, not claims of independence among the geometric source theorems.

The model with no omitted field and all seven deletion models are constructed
without extra hypotheses, choice, custom axioms, or additional interfaces.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace IMQGeomModels

open IMQGeom IMQGeomFinite IMQGeomEF

/-- A valid flag with the same line and a different quotient marking. -/
def altFlag : Nat := flagKey (lineOf 1) 14

/-- Both flags are genuine members of the finite marked-flag set. -/
theorem flags_valid : fixedFlag ∈ allFlags ∧ altFlag ∈ allFlags := by decide

/-- The alternate marking differs from the canonical one; the canonical key is
not the invalid zero key. -/
theorem flags_distinct : altFlag ≠ fixedFlag ∧ fixedFlag ≠ 0 := by decide

/-- Only the tate-deletion model gives its initial lift an invalid flag. -/
def modelFlag (skip : Option Obligation) (w : Bool) : Nat :=
  if w then fixedFlag else if skip = some .tate then 0 else altFlag

/-- Correct the alternate flag by changing the lift.  Deleting transport leaves
the supplied lift unchanged.  The base place is never changed. -/
def modelMove (skip : Option Obligation) (m : Nat) (w : Bool) : Bool :=
  if skip = some .transport then w
  else if actFlag m (lineOf 1) 7 = altFlag then !w else w

/-- The eight concrete interpretations.  Conjunction with `skip ≠ some o`
implements the false predicate precisely when obligation o is deleted. -/
def model (skip : Option Obligation) : GeometricData where
  ModPlace := Bool
  Fibre := fun _ => Bool
  initialLift := fun _ => false
  bad := fun u => !u
  localFlag := fun _ w => modelFlag skip w
  move := fun _ m w => modelMove skip m w
  GlobalSetup := skip ≠ some .datum
  LocalSetup := fun _ _ => skip ≠ some .datum
  SameLocalField := fun _ _ => skip ≠ some .field
  CanonicalCusp := fun _ w =>
    skip ≠ some .graph ∧ skip ≠ some .datum ∧ modelFlag skip w = fixedFlag
  ThetaModel := fun _ w =>
    skip ≠ some .theta ∧ skip ≠ some .datum ∧ skip ≠ some .field ∧
      (skip ≠ some .graph ∧ skip ≠ some .datum ∧ modelFlag skip w = fixedFlag)
  ArrowCovers := fun n => skip ≠ some .arrow ∧ skip ≠ some .datum ∧ n = 2

/-- A valid matrix whose image is the current flag effects the required
correction.  The invalid zero flag in the tate-deletion model has no such matrix;
this is proved from the existing concrete orbit theorem, not assumed. -/
theorem move_normalizes (skip : Option Obligation)
    (hkeep : skip ≠ some .transport) (w : Bool) (m : Nat) (hm : m ∈ SL7)
    (hflag : actFlag m (lineOf 1) 7 = modelFlag skip w) :
    modelFlag skip (modelMove skip m w) = fixedFlag := by
  cases w with
  | false =>
    by_cases ht : skip = some .tate
    · have hz : actFlag m (lineOf 1) 7 = 0 := by
        simpa [modelFlag, ht] using hflag
      exact False.elim (canonical_action_ne_zero m hm hz)
    · have ha : actFlag m (lineOf 1) 7 = altFlag := by
        simpa [modelFlag, ht] using hflag
      simp [modelMove, hkeep, ha, modelFlag]
  | true =>
    have hf : actFlag m (lineOf 1) 7 = fixedFlag := by
      simpa [modelFlag] using hflag
    have ha : actFlag m (lineOf 1) 7 ≠ altFlag := by
      rw [hf]
      exact Ne.symm flags_distinct.1
    simp [modelMove, hkeep, ha, modelFlag]

/-- Every rule other than the designated omitted rule holds in its concrete
model.  With skip=none this proves all seven rules in one nonempty model. -/
theorem rule_when_kept (skip : Option Obligation) (o : Obligation)
    (hkeep : skip ≠ some o) : Rule IMQGeom.witness (model skip) o := by
  cases o with
  | datum =>
    intro _
    exact ⟨hkeep, fun _ _ => hkeep⟩
  | tate =>
    intro _ w _ _
    cases w with
    | false => simpa [model, modelFlag, hkeep] using flags_valid.2
    | true => simpa [model, modelFlag] using flags_valid.1
  | transport =>
    intro _ w m _ hlocal hm hflag
    exact ⟨hlocal, move_normalizes skip hkeep w m hm hflag⟩
  | field =>
    intro _ _ _ _
    exact hkeep
  | graph =>
    intro _ _ _ hlocal hflag
    exact ⟨hkeep, hlocal, hflag⟩
  | theta =>
    intro _ _ _ _ hlocal hfield hcusp
    exact ⟨hkeep, hlocal, hfield, hcusp⟩
  | arrow =>
    intro _ hglobal _ _
    exact ⟨hkeep, hglobal, rfl⟩

/-- The complete finite model satisfies the seven-field structure. -/
theorem completeRules : GeometricRules IMQGeom.witness (model none) := {
  datum_localization := rule_when_kept none .datum (by decide)
  tate_marked_flag := rule_when_kept none .tate (by decide)
  galois_transport := rule_when_kept none .transport (by decide)
  rational_two_field := rule_when_kept none .field (by decide)
  graph_cusp_label := rule_when_kept none .graph (by decide)
  arithmetic_theta_model := rule_when_kept none .theta (by decide)
  arrow_marked_covers := rule_when_kept none .arrow (by decide)
}

/-- A witness for the extended structure itself, including its aggregate proof
field.  Its carriers remain the explicit finite interpretations above. -/
def completeWitness : AnabelianInputEF where
  toAnabelianInput := IMQGeom.witness
  geometry := model none
  geometricRules := completeRules

/-- The complete extended witness satisfies the encoded (d), (e), and (f). -/
theorem complete_witness_conditions :
    completeWitness.IsCore completeWitness.X0 ∧ ConditionsEF completeWitness.geometry :=
  conditions_d_e_f completeWitness

/-- Exact outputs of the same correcting algorithm used in the relative proof.
The complete model changes the bad lift and keeps the good lift.  In the two
flag-related deletion models the bad lift remains uncorrected. -/
theorem corrected_lift_values :
    correctedLift (model none) false = true ∧
    correctedLift (model none) true = false ∧
    correctedLift (model (some .tate)) false = false ∧
    correctedLift (model (some .transport)) false = false := by
  unfold correctedLift model
  decide

/-- Nondegeneracy: both place classes occur; the bad initial flag is not the
target flag, its initial cusp predicate fails, and the corrected lift satisfies
the cusp predicate.  The existing core model has both arithmetic and noncore
objects.  This is a finite interface witness, not a number-field example. -/
theorem complete_model_nondegenerate :
    (model none).bad false = true ∧ (model none).bad true = false ∧
    (model none).localFlag false ((model none).initialLift false) ≠ fixedFlag ∧
    ¬ (model none).CanonicalCusp false false ∧
    (model none).CanonicalCusp false true ∧
    correctedLift (model none) false ≠ (model none).initialLift false ∧
    IMQGeom.witness.IsArithmetic true ∧ ¬ IMQGeom.witness.IsCore true := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, witness_arithmetic_inhabited, witness_core_fails⟩
  · exact flags_distinct.1
  · intro h
    exact flags_distinct.1 h.2.2
  · exact ⟨by decide, by decide, rfl⟩
  · rw [corrected_lift_values.1]
    change true ≠ false
    decide

/-- All encoded conclusions hold in the complete finite witness. -/
theorem complete_model_conditions : ConditionsEF (model none) :=
  conditions_e_f IMQGeom.witness (model none) completeRules

/-! The following seven witnesses exhibit actual premises, one for every rule.
They prevent satisfaction of the complete rule structure only by empty premises.
The finite predicates are interpretations, not assertions about number fields. -/

/-- The datum rule is applied to the already computed concrete certificates. -/
theorem datum_premise_inhabited : ConcreteChecks := concrete_checks

/-- The Tate rule has a bad-place initial lift satisfying its local premise. -/
theorem tate_premise_inhabited :
    (model none).bad false = true ∧ (model none).LocalSetup false false :=
  ⟨rfl, (by intro h; cases h)⟩

/-- The transport rule applies to an actual determinant-one representative for
the alternate initial flag.  The two lift values are distinct by the earlier
nondegeneracy theorem, so this is a nontrivial correction. -/
theorem transport_premise_inhabited :
    (model none).bad false = true ∧ (model none).LocalSetup false false ∧
    matrixForFlag altFlag ∈ SL7 ∧
    actFlag (matrixForFlag altFlag) (lineOf 1) 7 =
      (model none).localFlag false false :=
  ⟨rfl, (by intro h; cases h), (matrixForFlag_spec altFlag flags_valid.2).1,
    (matrixForFlag_spec altFlag flags_valid.2).2⟩

/-- The local-field rule has premises at both the initial and corrected lifts. -/
theorem field_premise_inhabited :
    (model none).bad false = true ∧ (model none).LocalSetup false false ∧
    (model none).LocalSetup false true :=
  ⟨rfl, (by intro h; cases h), (by intro h; cases h)⟩

/-- The graph rule is applied at the lift with the fixed global flag. -/
theorem graph_premise_inhabited :
    (model none).bad false = true ∧ (model none).LocalSetup false true ∧
    (model none).localFlag false true = fixedFlag :=
  ⟨rfl, (by intro h; cases h), rfl⟩

/-- Corehood, the local setup, the field equality, and the matched cusp coexist
at one bad-place lift, exactly as required by the theta-model rule. -/
theorem theta_premise_inhabited :
    IMQGeom.witness.IsCore IMQGeom.witness.X0 ∧
    (model none).bad false = true ∧ (model none).LocalSetup false true ∧
    (model none).SameLocalField false true ∧
    (model none).CanonicalCusp false true :=
  ⟨witness_core_holds, rfl, (by intro h; cases h), (by intro h; cases h),
    (by intro h; cases h), (by intro h; cases h), rfl⟩

/-- The arrow rule has its core/global premises and its exact numerical
premises simultaneously; the noncoincidence computation is reused. -/
theorem arrow_premise_inhabited :
    IMQGeom.witness.IsCore IMQGeom.witness.X0 ∧ (model none).GlobalSetup ∧
    (5 ≤ 7 ∧ Nat.gcd 7 6 = 1) ∧
    ((List.range 7).all (fun x => x == 0 ||
      ((2 * x % 7 != x) && (2 * x % 7 != (7 - x) % 7))) = true) :=
  ⟨witness_core_holds, (by intro h; cases h), by decide, two_xi_ne_pm_xi⟩

/-- Keep exactly the six obligations other than the specified omission. -/
def AllExcept (A : AnabelianInput) (D : GeometricData) (omitted : Obligation) : Prop :=
  ∀ o, o ≠ omitted → Rule A D o

/-- Every one-field deletion model satisfies all six remaining rules. -/
theorem all_except (omitted : Obligation) :
    AllExcept IMQGeom.witness (model (some omitted)) omitted := by
  intro o hne
  apply rule_when_kept
  intro h
  exact hne (Option.some.inj h).symm

/-- The encoded conclusion fails in each of the seven deletion models. -/
theorem deleted_conditions_fail (omitted : Obligation) :
    ¬ ConditionsEF (model (some omitted)) := by
  intro h
  cases omitted with
  | datum => exact h.2.2.2.1 rfl
  | arrow => exact h.2.2.1 rfl
  | field => exact (h.2.1 false rfl).1 rfl
  | graph => exact (h.2.1 false rfl).2.2.1 rfl
  | theta => exact (h.2.1 false rfl).2.1.1 rfl
  | transport =>
    have hc := (h.2.1 false rfl).2.2.2.2
    rw [corrected_lift_values.2.2.2] at hc
    exact flags_distinct.1 hc
  | tate =>
    have hc := (h.2.1 false rfl).2.2.2.2
    rw [corrected_lift_values.2.2.1] at hc
    exact flags_distinct.2 hc.symm

/-- Deleting the aggregate geometricRules field also breaks the deduction:
the original core interface and all geometric carriers still exist, with the
same proved core, while the encoded geometric conclusions fail. -/
theorem aggregate_is_necessary :
    ∃ D : GeometricData, IMQGeom.witness.IsCore IMQGeom.witness.X0 ∧ ¬ ConditionsEF D :=
  ⟨model (some .arrow), witness_core_holds, deleted_conditions_fail .arrow⟩

/-- Dropping the named datum-localization link breaks the encoded deduction. -/
theorem datum_is_necessary :
    AllExcept IMQGeom.witness (model (some .datum)) .datum ∧
    ¬ ConditionsEF (model (some .datum)) :=
  ⟨all_except .datum, deleted_conditions_fail .datum⟩

/-- Dropping the Tate marked-flag rule breaks the encoded deduction. -/
theorem tate_is_necessary :
    AllExcept IMQGeom.witness (model (some .tate)) .tate ∧
    ¬ ConditionsEF (model (some .tate)) :=
  ⟨all_except .tate, deleted_conditions_fail .tate⟩

/-- Dropping the named Galois-transport link breaks the encoded deduction. -/
theorem transport_is_necessary :
    AllExcept IMQGeom.witness (model (some .transport)) .transport ∧
    ¬ ConditionsEF (model (some .transport)) :=
  ⟨all_except .transport, deleted_conditions_fail .transport⟩

/-- Dropping the local-field rule breaks the encoded deduction. -/
theorem field_is_necessary :
    AllExcept IMQGeom.witness (model (some .field)) .field ∧
    ¬ ConditionsEF (model (some .field)) :=
  ⟨all_except .field, deleted_conditions_fail .field⟩

/-- Dropping the canonical graph-cusp rule breaks the encoded deduction. -/
theorem graph_is_necessary :
    AllExcept IMQGeom.witness (model (some .graph)) .graph ∧
    ¬ ConditionsEF (model (some .graph)) :=
  ⟨all_except .graph, deleted_conditions_fail .graph⟩

/-- Dropping the arithmetic theta-model rule breaks the encoded deduction. -/
theorem theta_is_necessary :
    AllExcept IMQGeom.witness (model (some .theta)) .theta ∧
    ¬ ConditionsEF (model (some .theta)) :=
  ⟨all_except .theta, deleted_conditions_fail .theta⟩

/-- Dropping the arrow-cover rule breaks the encoded deduction. -/
theorem arrow_is_necessary :
    AllExcept IMQGeom.witness (model (some .arrow)) .arrow ∧
    ¬ ConditionsEF (model (some .arrow)) :=
  ⟨all_except .arrow, deleted_conditions_fail .arrow⟩

end IMQGeomModels
