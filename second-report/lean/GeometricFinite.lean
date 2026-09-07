/-!
# Constructive marked-flag representatives and sections

Append this file after `GeometricInput.lean`; it introduces no imports and no
external-result interface.  The flags and matrices are the concrete finite
encodings of `IMQGeom`.  A deterministic search supplies actual representatives,
not just an orbit cardinality.  The section lemmas work over an arbitrary base;
only the final enumeration/counting lemmas restrict the base to `Fin m`.

An initial point in each fibre is explicit input data, not an invocation of a
choice principle.  These statements do not assert that a finite list exhausts
the places of a number field.
-/

namespace IMQGeomFinite

open IMQGeom

/-- Search the finite, ordered list of determinant-one matrices for a matrix
sending the fixed flag to `k`.  The default is irrelevant for valid flag keys. -/
def matrixForFlag (k : Nat) : Nat :=
  (SL7.find? (fun m => actFlag m (lineOf 1) 7 == k)).getD 0

set_option maxHeartbeats 0 in
/-- The searched representatives really are determinant-one matrices and reach
every encoded marked flag.  This checks the target keys, not merely their count. -/
theorem matrixForFlag_checked :
    allFlags.all (fun k => decide
      (matrixForFlag k ∈ SL7 ∧ actFlag (matrixForFlag k) (lineOf 1) 7 = k)) = true := by
  decide

/-- Constructive transitivity from the fixed flag to any valid key. -/
theorem matrixForFlag_spec (k : Nat) (hk : k ∈ allFlags) :
    matrixForFlag k ∈ SL7 ∧ actFlag (matrixForFlag k) (lineOf 1) 7 = k := by
  have h := List.all_eq_true.mp matrixForFlag_checked k hk
  exact of_decide_eq_true h

/-- The verified representatives coexist with the previously checked 24-element
orbit; no existing declaration or arithmetic certificate is replaced. -/
theorem flags_transitive_with_representatives :
    (SL7.map (fun m => actFlag m (lineOf 1) 7)).eraseDups.length = 24 ∧
    ∀ k, k ∈ allFlags →
      matrixForFlag k ∈ SL7 ∧ actFlag (matrixForFlag k) (lineOf 1) 7 = k :=
  ⟨flags_transitive, matrixForFlag_spec⟩

set_option maxHeartbeats 0 in
/-- Every distinct target in the canonical orbit is a valid marked-flag key. -/
theorem canonical_orbit_checked :
    ((SL7.map (fun m => actFlag m (lineOf 1) 7)).eraseDups).all
      (fun k => allFlags.contains k) = true := by
  decide

/-- The forward membership direction, for any determinant-one matrix. -/
theorem canonical_action_mem (m : Nat) (hm : m ∈ SL7) :
    actFlag m (lineOf 1) 7 ∈ allFlags := by
  have hmap := List.mem_map_of_mem (f := fun m => actFlag m (lineOf 1) 7) hm
  have hdup := List.mem_eraseDups.mpr hmap
  have h := List.all_eq_true.mp canonical_orbit_checked _ hdup
  exact List.contains_iff_mem.mp h

/-- Zero is not a valid marked-flag key; useful for explicit countermodels. -/
theorem zero_not_flag : 0 ∉ allFlags := by decide

/-- No determinant-one action on the canonical flag can produce the invalid key. -/
theorem canonical_action_ne_zero (m : Nat) (hm : m ∈ SL7) :
    actFlag m (lineOf 1) 7 ≠ 0 := by
  intro h
  exact zero_not_flag (h ▸ canonical_action_mem m hm)

/-- Pointwise deterministic representatives over an arbitrary, possibly infinite
base.  This is an explicit function, not a choice of witnesses from existentials. -/
def simultaneousMatrices {B : Type} (flags : B → Nat) : B → Nat :=
  fun b => matrixForFlag (flags b)

/-- Every valid input flag is reached simultaneously by the explicit function. -/
theorem simultaneousMatrices_spec {B : Type} (flags : B → Nat)
    (valid : ∀ b, flags b ∈ allFlags) (b : B) :
    simultaneousMatrices flags b ∈ SL7 ∧
      actFlag (simultaneousMatrices flags b) (lineOf 1) 7 = flags b :=
  matrixForFlag_spec (flags b) (valid b)

/-- A selected point in every fibre; this is a function on any base type. -/
def select {B : Type} {F : B → Type} (s : (b : B) → F b) (b : B) : Sigma F :=
  ⟨b, s b⟩

/-- The chosen subset of the disjoint union of all fibres. -/
def Selected {B : Type} {F : B → Type} (s : (b : B) → F b) :=
  {p : Sigma F // p.2 = s p.1}

/-- The chosen point, with its membership in the selected subset. -/
def selectedPoint {B : Type} {F : B → Type} (s : (b : B) → F b)
    (b : B) : Selected s := ⟨select s b, rfl⟩

/-- Projection of the selected subset to the base. -/
def selectedProjection {B : Type} {F : B → Type} {s : (b : B) → F b}
    (p : Selected s) : B := p.val.1

/-- Distinct base points have disjoint fibres, with no finiteness hypothesis. -/
theorem fibres_disjoint {B : Type} {F : B → Type} {b c : B} (hne : b ≠ c)
    (p : Sigma F) : ¬ (p.1 = b ∧ p.1 = c) := by
  intro h
  exact hne (h.1.symm.trans h.2)

/-- Choosing a point never changes its base point. -/
theorem projection_select {B : Type} {F : B → Type}
    (s : (b : B) → F b) (b : B) : (select s b).1 = b := rfl

/-- Points selected in distinct fibres remain distinct. -/
theorem select_injective {B : Type} {F : B → Type}
    (s : (b : B) → F b) {b c : B} (h : select s b = select s c) : b = c :=
  congrArg Sigma.fst h

/-- One of the two inverse identities for the selected subset. -/
theorem selectedProjection_point {B : Type} {F : B → Type}
    (s : (b : B) → F b) (b : B) :
    selectedProjection (selectedPoint s b) = b := rfl

/-- The other inverse identity: every selected point is its prescribed point. -/
theorem selectedPoint_projection {B : Type} {F : B → Type}
    (s : (b : B) → F b) (p : Selected s) :
    selectedPoint s (selectedProjection p) = p := by
  apply Subtype.ext
  exact Sigma.ext rfl (heq_of_eq p.property.symm)

/-- The projection of the chosen subset is injective. -/
theorem selectedProjection_injective {B : Type} {F : B → Type}
    (s : (b : B) → F b) (p q : Selected s)
    (h : selectedProjection p = selectedProjection q) : p = q := by
  calc
    p = selectedPoint s (selectedProjection p) := (selectedPoint_projection s p).symm
    _ = selectedPoint s (selectedProjection q) := congrArg (selectedPoint s) h
    _ = q := selectedPoint_projection s q

/-- Surjectivity has an explicit witness; no choice is used. -/
theorem selectedProjection_surjective {B : Type} {F : B → Type}
    (s : (b : B) → F b) (b : B) :
    ∃ p : Selected s, selectedProjection p = b :=
  ⟨selectedPoint s b, rfl⟩

/-- The selected subset projects bijectively onto an arbitrary base. -/
theorem selectedProjection_bijective {B : Type} {F : B → Type}
    (s : (b : B) → F b) :
    (∀ p q : Selected s, selectedProjection p = selectedProjection q → p = q) ∧
    (∀ b : B, ∃ p : Selected s, selectedProjection p = b) :=
  ⟨selectedProjection_injective s, selectedProjection_surjective s⟩

/-- For a finite base, enumerate exactly one selected point per base element. -/
def selectedList {m : Nat} {F : Fin m → Type} (s : (b : Fin m) → F b) :
    List (Selected s) := (List.finRange m).map (selectedPoint s)

/-- The finite selected list has exactly as many entries as the base. -/
theorem selectedList_length {m : Nat} {F : Fin m → Type}
    (s : (b : Fin m) → F b) : (selectedList s).length = m := by
  simp [selectedList]

/-- The finite list includes every point of the selected subset. -/
theorem selectedList_complete {m : Nat} {F : Fin m → Type}
    (s : (b : Fin m) → F b) (p : Selected s) : p ∈ selectedList s := by
  have h := List.mem_map_of_mem (f := selectedPoint s)
    (List.mem_finRange (selectedProjection p))
  rw [selectedPoint_projection] at h
  exact h

/-- No two entries of the finite selected list coincide.  Thus its length is
the number of distinct selected points, not a count with multiplicity. -/
theorem selectedList_nodup {m : Nat} {F : Fin m → Type}
    (s : (b : Fin m) → F b) : (selectedList s).Nodup := by
  apply List.Pairwise.map (selectedPoint s) _ (List.nodup_finRange m)
  intro b c hne heq
  exact hne (congrArg selectedProjection heq)

/-- The finite enumeration is duplicate-free, complete, and has cardinality m. -/
theorem selectedList_cardinality {m : Nat} {F : Fin m → Type}
    (s : (b : Fin m) → F b) :
    (selectedList s).length = m ∧ (selectedList s).Nodup ∧
      ∀ p : Selected s, p ∈ selectedList s :=
  ⟨selectedList_length s, selectedList_nodup s, selectedList_complete s⟩

end IMQGeomFinite
