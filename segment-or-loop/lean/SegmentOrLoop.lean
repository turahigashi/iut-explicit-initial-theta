/-
  Segment or loop?  The quantitative core of a homotopy-type-theoretic overview
  of the dispute over Corollary 3.12 of inter-universal Teichmüller theory.

  The paper works in homotopy type theory.  For families of ordered real lines over
  graphs, its type-theoretic statements (transport, sections, truncation) reduce to
  statements about the group of positive scalings and about real inequalities.
  This file proves those reduced statements.  Nothing here asserts or refutes
  Corollary 3.12: the comparison of Section 5 is a schematic model whose parameters
  (the degree scale `s` and the blur `E`) are left free.
-/
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Find

namespace SegmentOrLoop

/-! ## 1. Positive scalings: the automorphisms of an ordered real line -/

/-- An order-preserving linear isomorphism of the ordered line `ℝ`, i.e. a positive scaling. -/
structure Scale where
  r : ℝ
  pos : 0 < r

namespace Scale

/-- The action on the line. -/
def act (a : Scale) (x : ℝ) : ℝ := a.r * x

/-- The identity. -/
def one : Scale := ⟨1, one_pos⟩

/-- Composition `a ∘ b`. -/
def comp (a b : Scale) : Scale := ⟨a.r * b.r, mul_pos a.pos b.pos⟩

/-- The inverse. -/
noncomputable def inv (a : Scale) : Scale := ⟨a.r⁻¹, inv_pos.mpr a.pos⟩

theorem act_comp (a b : Scale) (x : ℝ) : (a.comp b).act x = a.act (b.act x) := by
  simp [act, comp, mul_assoc]

theorem act_inv_act (a : Scale) (x : ℝ) : a.inv.act (a.act x) = x := by
  have h : a.r ≠ 0 := ne_of_gt a.pos
  simp [act, inv, ← mul_assoc, inv_mul_cancel₀ h]

theorem act_mono (a : Scale) {x y : ℝ} (h : x ≤ y) : a.act x ≤ a.act y :=
  mul_le_mul_of_nonneg_left h (le_of_lt a.pos)

end Scale

/-! ## 2. Two routes and their monodromy -/

/-- The monodromy of two routes `c, ℓ` between two lines: `c⁻¹ ∘ ℓ`. -/
noncomputable def monodromy (c ℓ : Scale) : Scale := c.inv.comp ℓ

/-- Transport along `ℓ` is transport along `c` after the monodromy. -/
theorem route_factor (c ℓ : Scale) (x : ℝ) :
    ℓ.act x = c.act ((monodromy c ℓ).act x) := by
  have h : c.r ≠ 0 := ne_of_gt c.pos
  simp only [monodromy, Scale.act, Scale.comp, Scale.inv]
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ h, one_mul]

/-- Relabelling: changing the identification at the source by `φ` and at the target by `ψ`
does not change the monodromy scale, because the group of positive scalings is commutative. -/
theorem monodromy_relabel (c ℓ φ ψ : Scale) :
    (monodromy ((ψ.inv.comp c).comp φ) ((ψ.inv.comp ℓ).comp φ)).r = (monodromy c ℓ).r := by
  have hc : c.r ≠ 0 := ne_of_gt c.pos
  have hφ : φ.r ≠ 0 := ne_of_gt φ.pos
  have hψ : ψ.r ≠ 0 := ne_of_gt ψ.pos
  simp only [monodromy, Scale.comp, Scale.inv]
  field_simp

/-! ## 3. Values over the loop, the segment and the universal cover -/

/-- A value over the two-route graph (equivalently over the loop): a value at `†`
whose transports along the two routes agree. -/
def LoopSection (c ℓ : Scale) (x : ℝ) : Prop := ℓ.act x = c.act x

/-- Values over the loop are exactly the fixed points of the monodromy. -/
theorem loopSection_iff_fixed (c ℓ : Scale) (x : ℝ) :
    LoopSection c ℓ x ↔ (monodromy c ℓ).act x = x := by
  unfold LoopSection
  rw [route_factor c ℓ x]
  constructor
  · intro h
    have := congrArg c.inv.act h
    simpa [Scale.act_inv_act] using this
  · intro h
    rw [h]

/-- If the monodromy is not the identity, the only value over the loop is `0`. -/
theorem loopSection_iff_zero (c ℓ : Scale) (hm : (monodromy c ℓ).r ≠ 1) (x : ℝ) :
    LoopSection c ℓ x ↔ x = 0 := by
  rw [loopSection_iff_fixed]
  simp only [Scale.act]
  constructor
  · intro h
    have h' : ((monodromy c ℓ).r - 1) * x = 0 := by linarith
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact absurd (by linarith) hm
    · exact h1
  · intro h
    simp [h]

/-- All values are consistent around the loop iff the monodromy is the identity. -/
theorem all_values_consistent_iff (c ℓ : Scale) :
    (∀ x, LoopSection c ℓ x) ↔ (monodromy c ℓ).r = 1 := by
  constructor
  · intro h
    have h1 := (loopSection_iff_fixed c ℓ 1).mp (h 1)
    simpa [Scale.act] using h1
  · intro hm x
    rw [loopSection_iff_fixed]
    simp [Scale.act, hm]

/-- Over the segment (a single route), every value at `†` extends uniquely to `‡`. -/
theorem segment_section (ℓ : Scale) (x : ℝ) : ∃! y : ℝ, y = ℓ.act x :=
  ⟨ℓ.act x, rfl, fun _ h => h⟩

/-- Over the universal cover (copies labelled by `n`, each edge the monodromy `m`),
the value at level `n` is `m^n x`. -/
def uniValue (m : Scale) (x : ℝ) (n : ℕ) : ℝ := m.r ^ n * x

/-- The values over the universal cover are compatible along every edge, for every `m`. -/
theorem uni_edge (m : Scale) (x : ℝ) (n : ℕ) :
    uniValue m x (n + 1) = m.act (uniValue m x n) := by
  simp only [uniValue, Scale.act, pow_succ]
  ring

/-! ## 4. Hulls invariant under the loop carry no information -/

/-- If a bound `H` dominates the whole orbit `{m^n v}` of a negative value under a
contracting monodromy `0 < m < 1`, then `0 ≤ H`.  (The trivial multiradial
representation: a hull that must contain the whole orbit says nothing about `v`.) -/
theorem orbit_hull_nonneg (m v H : ℝ) (hm1 : m < 1) (hv : v < 0)
    (hH : ∀ n : ℕ, m ^ n * v ≤ H) : 0 ≤ H := by
  by_contra hneg0
  have hneg : H < 0 := lt_of_not_ge hneg0
  have hpos : 0 < (-H) / (-v) := div_pos (by linarith) (by linarith)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hm1
  have h1 := hH n
  have h2 : m ^ n * (-v) < -H := (lt_div_iff₀ (by linarith : (0 : ℝ) < -v)).mp hn
  linarith

/-! ## 5. Step (xi) of the proof of Corollary 3.12 as a 2-cell -/

/-- Data of the schematic comparison: the degree scale `s ∈ (0,1)` (which is the
monodromy of the two routes), `Q = |log q| > 0`, and the blur `E ≥ 0` (the excess of
the hull of possible images over the image). -/
structure Step where
  s : ℝ
  Q : ℝ
  E : ℝ
  hs0 : 0 < s
  hs1 : s < 1
  hQ : 0 < Q
  hE : 0 ≤ E

namespace Step

variable (K : Step)

/-- The coric route: the identity in coric coordinates. -/
def core : Scale := Scale.one

/-- Log-volume of the Θ-pilot, in coric coordinates. -/
noncomputable def thetaValue : ℝ := -K.Q / K.s

/-- Log-volume of the q-pilot (not subject to indeterminacy). -/
def qValue : ℝ := -K.Q

/-- The route through the Θ-link. -/
def link : Scale := ⟨K.s, K.hs0⟩

/-- Value of the hull of possible images, computed through the core. -/
noncomputable def hull : ℝ := core.act K.thetaValue + K.E

/-- Corollary 3.12, schematically: `-|log Θ| ≥ -|log q|`. -/
def Cor312 : Prop := K.qValue ≤ K.hull

/-- IPL: the Θ-link carries the Θ-pilot to the q-pilot. -/
theorem ipl : K.link.act K.thetaValue = K.qValue := by
  have h : K.s ≠ 0 := ne_of_gt K.hs0
  simp only [link, thetaValue, qValue, Scale.act]
  field_simp

/-- The monodromy of the two routes is the degree scale `s`. -/
theorem monodromy_eq : (monodromy core K.link).r = K.s := by
  simp [monodromy, core, link, Scale.one, Scale.comp, Scale.inv]

theorem thetaValue_neg : K.thetaValue < 0 := by
  unfold thetaValue
  exact div_neg_of_neg_of_pos (by linarith [K.hQ]) K.hs0

/-- No strict 2-cell: the two routes disagree on the Θ-pilot. -/
theorem no_strict_cell : K.link.act K.thetaValue ≠ core.act K.thetaValue := by
  intro h
  have hm : (monodromy core K.link).r ≠ 1 := by
    rw [monodromy_eq]; exact ne_of_lt K.hs1
  have := (loopSection_iff_zero core K.link hm K.thetaValue).mp h
  linarith [K.thetaValue_neg]

/-- Corollary 3.12 is the lax 2-cell `ℓ(b) ≤ c(b) + E` between the two routes. -/
theorem cor312_iff_lax : K.Cor312 ↔ K.link.act K.thetaValue ≤ core.act K.thetaValue + K.E := by
  rw [Cor312, hull, ipl]

/-- The lax 2-cell holds iff the blur absorbs the monodromy discrepancy. -/
theorem cor312_iff_blur : K.Cor312 ↔ (1 / K.s - 1) * K.Q ≤ K.E := by
  have h : K.s ≠ 0 := ne_of_gt K.hs0
  have key : (1 / K.s - 1) * K.Q = -K.Q - (-K.Q / K.s) := by
    field_simp
    ring
  unfold Cor312 hull qValue thetaValue core
  simp only [Scale.act, Scale.one, one_mul]
  constructor
  · intro hc; rw [key]; linarith
  · intro hb; rw [key] at hb; linarith

/-- With an upper estimate `E ≤ C` of the blur, Corollary 3.12 bounds `Q = |log q|`. -/
theorem height_bound (C : ℝ) (hcor : K.Cor312) (hEC : K.E ≤ C) :
    K.Q ≤ C / (1 / K.s - 1) := by
  have hpos : 0 < 1 / K.s - 1 := by
    have : 1 < 1 / K.s := by
      rw [lt_div_iff₀ K.hs0]; linarith [K.hs1]
    linarith
  rw [le_div_iff₀ hpos]
  have := (K.cor312_iff_blur).mp hcor
  linarith

/-- Without blur, Corollary 3.12 fails. -/
theorem cor312_needs_blur (hE0 : K.E = 0) : ¬ K.Cor312 := by
  intro hc
  have hb := (K.cor312_iff_blur).mp hc
  rw [hE0] at hb
  have hpos : 0 < 1 / K.s - 1 := by
    have : 1 < 1 / K.s := by
      rw [lt_div_iff₀ K.hs0]; linarith [K.hs1]
    linarith
  have : 0 < (1 / K.s - 1) * K.Q := mul_pos hpos K.hQ
  linarith

/-- If the hull must be invariant under the loop (it dominates the whole orbit of the
Θ-pilot under the monodromy), its value is nonnegative and Corollary 3.12 holds for a
reason that says nothing about `Q`. -/
theorem loop_hull_trivial (H : ℝ) (hH : ∀ n : ℕ, K.s ^ n * K.thetaValue ≤ H) :
    0 ≤ H ∧ K.qValue ≤ H := by
  have h0 := orbit_hull_nonneg K.s K.thetaValue H K.hs1 K.thetaValue_neg hH
  refine ⟨h0, ?_⟩
  unfold qValue
  linarith [K.hQ]

end Step

/-! ## 6. The qualitative package does not decide Corollary 3.12 -/

/-- IPL: the Θ-link carries the Θ-pilot to the q-pilot. -/
def IPL (K : Step) : Prop := K.link.act K.thetaValue = K.qValue

/-- SHE: the hull is a function of the coric data. -/
def SHE (K : Step) : Prop := ∃ f : ℝ → ℝ, K.hull = f (Step.core.act K.thetaValue)

/-- APT: the construction commutes with relabelling the coric coordinates. -/
def APT (K : Step) : Prop :=
  ∀ φ : Scale, φ.act (Step.core.act K.thetaValue) = Step.core.act (φ.act K.thetaValue)

theorem package_holds (K : Step) : IPL K ∧ SHE K ∧ APT K :=
  ⟨K.ipl, ⟨fun x => x + K.E, rfl⟩, by intro φ; simp [Step.core, Scale.one, Scale.act]⟩

/-- For every degree scale and every `|log q|`, the package IPL ∧ SHE ∧ APT holds both in a
configuration where Corollary 3.12 fails and in one where it holds. -/
theorem package_does_not_decide (s Q : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hQ : 0 < Q) :
    ∃ K₁ K₂ : Step, K₁.s = s ∧ K₁.Q = Q ∧ K₂.s = s ∧ K₂.Q = Q ∧
      (IPL K₁ ∧ SHE K₁ ∧ APT K₁) ∧ ¬ K₁.Cor312 ∧
      (IPL K₂ ∧ SHE K₂ ∧ APT K₂) ∧ K₂.Cor312 := by
  have hpos : 0 ≤ (1 / s - 1) * Q := by
    have : 1 < 1 / s := by rw [lt_div_iff₀ hs0]; linarith
    exact mul_nonneg (by linarith) (le_of_lt hQ)
  let K₁ : Step := ⟨s, Q, 0, hs0, hs1, hQ, le_refl 0⟩
  let K₂ : Step := ⟨s, Q, (1 / s - 1) * Q, hs0, hs1, hQ, hpos⟩
  exact ⟨K₁, K₂, rfl, rfl, rfl, rfl, package_holds K₁, K₁.cor312_needs_blur rfl,
    package_holds K₂, (K₂.cor312_iff_blur).mpr le_rfl⟩

/-! ## 7. Possible images: the least label-free family containing all images -/

/-- The possible images along `π`: the union of the images over each fibre. -/
def possibleImages {X Y Z : Type*} (π : X → Y) (Φ : X → Set Z) (y : Y) : Set Z :=
  {z | ∃ x, π x = y ∧ z ∈ Φ x}

/-- Universal property: a label-free family contains all possible images iff it
contains the image of every labelled datum. -/
theorem possibleImages_universal {X Y Z : Type*} (π : X → Y) (Φ : X → Set Z)
    (Ψ : Y → Set Z) :
    (∀ y, possibleImages π Φ y ⊆ Ψ y) ↔ (∀ x, Φ x ⊆ Ψ (π x)) := by
  constructor
  · intro h x z hz
    exact h (π x) ⟨x, rfl, hz⟩
  · rintro h y z ⟨x, rfl, hz⟩
    exact h x hz

/-! ## 8. Deleting labels: from a labelled pair (∧) to an unlabelled set (∨) -/

/-- The two routes, as labels. -/
inductive Route
  | link
  | core
  deriving DecidableEq

/-- The labelled datum (∧): the value attached via each route. -/
def labelled (c ℓ : Scale) (x : ℝ) : Route → ℝ
  | .link => ℓ.act x
  | .core => c.act x

/-- The unlabelled datum (∨): the set of attached values. -/
def unlabelled (c ℓ : Scale) (x : ℝ) : Set ℝ := Set.range (labelled c ℓ x)

/-- Exchanging the two routes does not change the unlabelled set. -/
theorem unlabelled_swap (c ℓ : Scale) (x : ℝ) : unlabelled c ℓ x = unlabelled ℓ c x := by
  ext z
  constructor
  · rintro ⟨r, rfl⟩
    cases r
    · exact ⟨.core, rfl⟩
    · exact ⟨.link, rfl⟩
  · rintro ⟨r, rfl⟩
    cases r
    · exact ⟨.core, rfl⟩
    · exact ⟨.link, rfl⟩

/-- When the monodromy is not the identity and the value is nonzero, the two labelled
values differ. -/
theorem labelled_distinct (c ℓ : Scale) (x : ℝ) (hx : x ≠ 0) (hm : (monodromy c ℓ).r ≠ 1) :
    labelled c ℓ x .link ≠ labelled c ℓ x .core := by
  intro h
  exact hx ((loopSection_iff_zero c ℓ hm x).mp h)

/-- No procedure that sees only the unlabelled set recovers the value attached via the link. -/
theorem link_value_not_recoverable :
    ¬ ∃ F : Set ℝ → ℝ, ∀ (c ℓ : Scale) (x : ℝ), F (unlabelled c ℓ x) = ℓ.act x := by
  rintro ⟨F, hF⟩
  let one : Scale := Scale.one
  let two : Scale := ⟨2, by norm_num⟩
  have h1 := hF one two 1
  have h2 := hF two one 1
  rw [unlabelled_swap one two 1] at h1
  have : two.act 1 = one.act 1 := h1.symm.trans h2
  simp [Scale.act, one, two, Scale.one] at this


/-! ## 9. One level down: presented reals and locators -/

namespace OneLevelDown

/-- In a set, any two identifications of the same two points agree.  In Lean this holds
by definition (proof irrelevance), which is why Lean sits at this level for equality and the
higher phenomena of Sections 2–5 had to be modelled by explicit isomorphisms (`Scale`). -/
theorem paths_in_a_set_agree {A : Type*} {a b : A} (p q : a = b) : p = q := rfl

/-- A locator for `x` (Booij): for every pair of rationals `q < r`, a choice of one of the
true disjuncts, `q < x` (`true`) or `x < r` (`false`).  It is structure, not property. -/
structure Locator (x : ℝ) where
  choose : ∀ q r : ℚ, q < r → Bool
  sound_true : ∀ q r h, choose q r h = true → (q : ℝ) < x
  sound_false : ∀ q r h, choose q r h = false → x < (r : ℝ)

/-- The locator that prefers the lower disjunct. -/
noncomputable def lowerLocator (x : ℝ) : Locator x where
  choose q _ _ := decide ((q : ℝ) < x)
  sound_true q r h hc := by simpa using hc
  sound_false q r h hc := by
    have hn : ¬ ((q : ℝ) < x) := by simpa using hc
    have hqr : (q : ℝ) < r := by exact_mod_cast h
    linarith [not_lt.mp hn]

/-- The locator that prefers the upper disjunct. -/
noncomputable def upperLocator (x : ℝ) : Locator x where
  choose _ r _ := !decide (x < (r : ℝ))
  sound_true q r h hc := by
    have hn : ¬ (x < (r : ℝ)) := by simpa using hc
    have hqr : (q : ℝ) < r := by exact_mod_cast h
    linarith [not_lt.mp hn]
  sound_false q r h hc := by simpa using hc

/-- Rounding by one query of the locator at the pair `(0, 1)`: answer `1` if the locator
says `0 < x`, and `0` if it says `x < 1`. -/
def round01 {x : ℝ} (L : Locator x) : ℤ :=
  if L.choose 0 1 (by norm_num) then 1 else 0

/-- For `-1 < x < 2`, every locator rounds `x` to an integer at distance `< 1`. -/
theorem round01_close {x : ℝ} (L : Locator x) (h1 : -1 < x) (h2 : x < 2) :
    |x - (round01 L : ℝ)| < 1 := by
  unfold round01
  by_cases hc : L.choose 0 1 (by norm_num) = true
  · have h0 : ((0 : ℚ) : ℝ) < x := L.sound_true 0 1 (by norm_num) hc
    simp only [hc, if_true]
    rw [abs_lt]
    push_cast at h0 ⊢
    constructor <;> linarith
  · have hc' : L.choose 0 1 (by norm_num) = false := by simpa using hc
    have h0 : x < ((1 : ℚ) : ℝ) := L.sound_false 0 1 (by norm_num) hc'
    simp only [hc', Bool.false_eq_true, if_false]
    rw [abs_lt]
    push_cast at h0 ⊢
    constructor <;> linarith

/-- The rounding depends on the locator, not only on the real number. -/
theorem round01_depends_on_locator :
    round01 (lowerLocator (1 / 2)) = 1 ∧ round01 (upperLocator (1 / 2)) = 0 := by
  constructor
  · unfold round01 lowerLocator
    simp only [decide_eq_true_eq]
    norm_num
  · unfold round01 upperLocator
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    norm_num

/-- The possible roundings of `x` over all locators. -/
def possibleRoundings (x : ℝ) : Set ℤ := {k | ∃ L : Locator x, round01 L = k}

/-- Their blur is uniform: they all lie within distance `< 1` of `x`, and any two differ by at
most `1`.  No monodromy enters, and the bound does not grow with `x`. -/
theorem possibleRoundings_blur {x : ℝ} (h1 : -1 < x) (h2 : x < 2) :
    (∀ k ∈ possibleRoundings x, |x - (k : ℝ)| < 1) ∧
    (∀ k ∈ possibleRoundings x, ∀ k' ∈ possibleRoundings x, |k - k'| ≤ 1) := by
  refine ⟨?_, ?_⟩
  · rintro k ⟨L, rfl⟩
    exact round01_close L h1 h2
  · rintro k ⟨L, rfl⟩ k' ⟨L', rfl⟩
    unfold round01
    split_ifs <;> norm_num

/-- For `x = 1/2` both roundings occur. -/
theorem possibleRoundings_half : possibleRoundings (1 / 2) = {0, 1} := by
  ext k
  constructor
  · rintro ⟨L, rfl⟩
    unfold round01
    split_ifs <;> simp
  · rintro (rfl | rfl)
    · exact ⟨upperLocator (1 / 2), round01_depends_on_locator.2⟩
    · exact ⟨lowerLocator (1 / 2), round01_depends_on_locator.1⟩

/-- Restoring data from a proposition without choice: the least witness. -/
def restoreLeast (P : ℕ → Prop) [DecidablePred P] (h : ∃ n, P n) :
    {n : ℕ // P n ∧ ∀ m < n, ¬ P m} :=
  ⟨Nat.find h, Nat.find_spec h, fun _ hm => Nat.find_min h hm⟩

/-- The least witness is unique, so the restored datum is canonical (the type of least
witnesses is a proposition). -/
theorem least_witness_unique (P : ℕ → Prop) (a b : {n : ℕ // P n ∧ ∀ m < n, ¬ P m}) :
    a = b := by
  apply Subtype.ext
  rcases Nat.lt_trichotomy a.1 b.1 with h | h | h
  · exact absurd a.2.1 (b.2.2 a.1 h)
  · exact h
  · exact absurd b.2.1 (a.2.2 b.1 h)

/-- One level up there is no canonical identification: no isomorphism of ordered lines is
fixed by all automorphisms, so an identification restored from its mere existence is
determined only up to the action of `ℝ_{>0}`. -/
theorem no_invariant_identification (s : Scale) : ¬ ∀ g : Scale, (g.comp s).r = s.r := by
  intro h
  have h2 := h ⟨2, by norm_num⟩
  simp only [Scale.comp] at h2
  have hs := s.pos
  linarith

end OneLevelDown

end SegmentOrLoop

#print axioms SegmentOrLoop.segment_section
#print axioms SegmentOrLoop.monodromy_relabel
#print axioms SegmentOrLoop.loopSection_iff_zero
#print axioms SegmentOrLoop.all_values_consistent_iff
#print axioms SegmentOrLoop.uni_edge
#print axioms SegmentOrLoop.orbit_hull_nonneg
#print axioms SegmentOrLoop.Step.no_strict_cell
#print axioms SegmentOrLoop.Step.cor312_iff_lax
#print axioms SegmentOrLoop.Step.cor312_iff_blur
#print axioms SegmentOrLoop.Step.height_bound
#print axioms SegmentOrLoop.Step.loop_hull_trivial
#print axioms SegmentOrLoop.package_does_not_decide
#print axioms SegmentOrLoop.possibleImages_universal
#print axioms SegmentOrLoop.link_value_not_recoverable
#print axioms SegmentOrLoop.route_factor
#print axioms SegmentOrLoop.loopSection_iff_fixed
#print axioms SegmentOrLoop.Step.cor312_needs_blur
#print axioms SegmentOrLoop.package_holds
#print axioms SegmentOrLoop.unlabelled_swap
#print axioms SegmentOrLoop.labelled_distinct
#print axioms SegmentOrLoop.OneLevelDown.paths_in_a_set_agree
#print axioms SegmentOrLoop.OneLevelDown.round01_close
#print axioms SegmentOrLoop.OneLevelDown.round01_depends_on_locator
#print axioms SegmentOrLoop.OneLevelDown.possibleRoundings_blur
#print axioms SegmentOrLoop.OneLevelDown.possibleRoundings_half
#print axioms SegmentOrLoop.OneLevelDown.restoreLeast
#print axioms SegmentOrLoop.OneLevelDown.least_witness_unique
#print axioms SegmentOrLoop.OneLevelDown.no_invariant_identification
