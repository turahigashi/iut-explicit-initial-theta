/-!
# The entrance margin with positive-denominator fractions

Init only; none of the existing seven files is changed. The report's comparison
section writes s = ord_p(q-double-underlined), lambda = j^2 s, and
margin = j^2 s - (j+2). Here j is a positive stage and ell a positive integer.

Fraction is an unnormalized integer numerator with a positive natural denominator.
Its ordinary mathematical interpretation is num/den. Positive and Less are exact
sign/cross-product predicates. No Nat or Int division occurs in the margin,
depth, threshold, or their main equivalence. No transport into Lean Rat or Real
has been formalized: in the installed toolchain Rat.mul/div/sub themselves have
Classical.choice dependencies, so they are deliberately not used here.

The arbitrary-depth theorem REQUIRES RepresentsDepth s ell ord, the equation
(2 ell)*s.num = ord*s.den. Thus it cannot relate independently chosen s and ord.
The canonical depth constructor proves this equation without assuming it.

The integer interval/search statements do not establish a seed, a tame tuple,
primality/Galois hypotheses, or a height bound. Applying this algebra to any
actual log-volume requires the stated mathematical interpretation and premises.
-/

namespace IMQEntrance

/-- A fraction presentation with a strictly positive denominator, not a quotient type. -/
structure Fraction where
  num : Int
  den : Nat
  den_pos : 0 < den

/-- Exact positivity of the ordinary fraction num/den. -/
def Positive (q : Fraction) : Prop := 0 < q.num

/-- Exact strict order by cross multiplication of positive denominators. -/
def Less (q r : Fraction) : Prop := q.num * r.den < r.num * q.den

/-- Equality of fraction values by cross multiplication; literal presentations may differ. -/
def SameValue (q r : Fraction) : Prop := q.num * r.den = r.num * q.den

instance instDecidablePositive (q : Fraction) : Decidable (Positive q) :=
  inferInstanceAs (Decidable (0 < q.num))

instance instDecidableLess (q r : Fraction) : Decidable (Less q r) :=
  inferInstanceAs (Decidable (q.num * r.den < r.num * q.den))

instance instDecidableSameValue (q r : Fraction) : Decidable (SameValue q r) :=
  inferInstanceAs (Decidable (q.num * r.den = r.num * q.den))

/-- The integer ord as the fraction ord/1. -/
def integer (ord : Int) : Fraction := ⟨ord, 1, by decide⟩

/-- The report's margin j^2 s - (j+2), keeping s's positive denominator. -/
def margin (j : Nat) (s : Fraction) : Fraction :=
  ⟨(j : Int) * (j : Int) * s.num - ((j : Int) + 2) * s.den, s.den, s.den_pos⟩

/-- The exact fraction ord/(2 ell); its denominator cannot be zero. -/
def depth (ell : Nat) (ord : Int) (hell : 0 < ell) : Fraction :=
  ⟨ord, 2 * ell, Nat.mul_pos (by decide) hell⟩

/-- The exact fraction 2 ell (j+2)/j^2; j>0 is used in the constructor. -/
def threshold (j ell : Nat) (hj : 0 < j) : Fraction :=
  ⟨2 * (ell : Int) * ((j : Int) + 2), j * j, Nat.mul_pos hj hj⟩

/-- The required relation s = ord/(2 ell), expressed without any truncated division. -/
def RepresentsDepth (s : Fraction) (ell : Nat) (ord : Int) : Prop :=
  (2 * (ell : Int)) * s.num = ord * s.den

/-- The canonical depth constructor discharges the relation on s and ord. -/
theorem depth_represents (ell : Nat) (ord : Int) (hell : 0 < ell) :
    RepresentsDepth (depth ell ord hell) ell ord := by
  simp only [RepresentsDepth, depth, Int.natCast_mul]
  exact Int.mul_comm _ _

/-- RepresentsDepth is precisely equality of the supplied and canonical fraction values. -/
theorem represents_iff_same_value (s : Fraction) (ell : Nat) (ord : Int)
    (hell : 0 < ell) :
    RepresentsDepth s ell ord ↔ SameValue s (depth ell ord hell) := by
  simp only [RepresentsDepth, SameValue, depth, Int.natCast_mul, Int.cast_ofNat_Int]
  rw [Int.mul_comm (2 * (ell : Int)) s.num]

/-- Positivity of the explicitly constructed margin is an exact integer inequality. -/
theorem margin_positive_iff (j : Nat) (s : Fraction) :
    Positive (margin j s) ↔ ((j : Int) + 2) * s.den < (j : Int) * j * s.num := by
  exact Int.sub_pos

/-- The positive-denominator threshold is exactly its cross-multiplied inequality. -/
theorem threshold_less_iff (j ell : Nat) (ord : Int) (hj : 0 < j) :
    Less (threshold j ell hj) (integer ord) ↔
      2 * (ell : Int) * ((j : Int) + 2) < (j : Int) * j * ord := by
  simp only [Less, threshold, integer, Int.cast_ofNat_Int, Int.mul_one, Int.natCast_mul]
  rw [Int.mul_comm ord ((j : Int) * j)]

/-- Clear the positive denominator 2 ell and the positive denominator of s.
No hypothesis on the sign of ord is needed. -/
theorem margin_pos_iff_cross_mul (j ell : Nat) (s : Fraction) (ord : Int)
    (hell : 0 < ell) (hs : RepresentsDepth s ell ord) :
    Positive (margin j s) ↔
      2 * (ell : Int) * ((j : Int) + 2) < (j : Int) * j * ord := by
  let B : Int := 2 * (ell : Int)
  let C : Int := (j : Int) + 2
  let J : Int := (j : Int) * j
  let D : Int := s.den
  have hB : 0 < B := Int.mul_pos (by decide) (Int.natCast_pos.mpr hell)
  have hD : 0 < D := Int.natCast_pos.mpr s.den_pos
  have hrel : B * s.num = ord * D := hs
  have hl : (C * D) * B = (B * C) * D := by
    simp only [Int.mul_assoc, Int.mul_comm]
  have hr : (J * s.num) * B = (J * ord) * D := by
    calc
      (J * s.num) * B = J * (B * s.num) := by
        rw [Int.mul_assoc, Int.mul_comm s.num B]
      _ = J * (ord * D) := congrArg (fun z => J * z) hrel
      _ = (J * ord) * D := (Int.mul_assoc _ _ _).symm
  calc
    Positive (margin j s) ↔ C * D < J * s.num := margin_positive_iff j s
    _ ↔ (C * D) * B < (J * s.num) * B := (Int.mul_lt_mul_right hB).symm
    _ ↔ (B * C) * D < (J * ord) * D := by rw [hl, hr]
    _ ↔ B * C < J * ord := Int.mul_lt_mul_right hD

/-- General entrance equivalence for arbitrary s, with its depth relation explicit.
This is the fraction-presentation version of margin>0 iff ord>2 ell(j+2)/j^2. -/
theorem margin_pos_iff_ord_gt_threshold (j ell : Nat) (s : Fraction) (ord : Int)
    (hj : 0 < j) (hell : 0 < ell) (hs : RepresentsDepth s ell ord) :
    Positive (margin j s) ↔ Less (threshold j ell hj) (integer ord) :=
  (margin_pos_iff_cross_mul j ell s ord hell hs).trans
    (threshold_less_iff j ell ord hj).symm

/-- At canonical depth the s/ord relation is proved, not an extra assumption. -/
theorem entrance_canonical_depth (j ell : Nat) (ord : Int)
    (hj : 0 < j) (hell : 0 < ell) :
    Positive (margin j (depth ell ord hell)) ↔
      Less (threshold j ell hj) (integer ord) :=
  margin_pos_iff_ord_gt_threshold j ell (depth ell ord hell) ord hj hell
    (depth_represents ell ord hell)

/-- An exact decidable integer criterion, using no division. -/
def EntranceNat (j ell ord : Nat) : Prop := 2 * ell * (j + 2) < j * j * ord

/-- The integer criterion has a computational decision procedure. -/
instance instDecidableEntranceNat (j ell ord : Nat) : Decidable (EntranceNat j ell ord) :=
  inferInstanceAs (Decidable (2 * ell * (j + 2) < j * j * ord))

/-- Natural-number q-orders reduce to the exact cross-multiplied criterion. -/
theorem margin_pos_iff_nat_criterion (j ell ord : Nat) (hell : 0 < ell) :
    Positive (margin j (depth ell (ord : Int) hell)) ↔ EntranceNat j ell ord := by
  rw [margin_pos_iff_cross_mul j ell _ _ hell (depth_represents ell (ord : Int) hell)]
  unfold EntranceNat
  rw [← Int.ofNat_lt]
  simp only [Int.natCast_mul, Int.natCast_add, Int.cast_ofNat_Int]

/-- In particular, stage one has the strict threshold ord_p(q)>6 ell. -/
theorem stage_one_criterion (ell ord : Nat) (hell : 0 < ell) :
    Positive (margin 1 (depth ell (ord : Int) hell)) ↔ 6 * ell < ord := by
  rw [margin_pos_iff_nat_criterion 1 ell ord hell]
  simp only [EntranceNat, Nat.one_mul]
  rw [Nat.mul_right_comm 2 ell 3]

/-- An admissible entrance value remains admissible when ell is decreased. -/
theorem entrance_downward (j ord lo ell : Nat) (hle : lo ≤ ell)
    (h : EntranceNat j ell ord) : EntranceNat j lo ord := by
  unfold EntranceNat at h ⊢
  exact Nat.lt_of_le_of_lt
    (Nat.mul_le_mul_right (j + 2) (Nat.mul_le_mul_left 2 hle)) h

/-- Exact nonemptiness of an integer interval with the entrance criterion.
This statement does not impose primality or any geometric eligibility test.
The endpoints are supplied integers: deriving them from a finite Tate height or
from a full Weil height is a separate task, and those heights are not identified. -/
theorem interval_nonempty_iff (j ord lo hi : Nat) :
    (∃ ell, lo ≤ ell ∧ ell ≤ hi ∧ EntranceNat j ell ord) ↔
      lo ≤ hi ∧ EntranceNat j lo ord := by
  constructor
  · intro ⟨ell, hlo, hhi, hent⟩
    exact ⟨Nat.le_trans hlo hhi, entrance_downward j ord lo ell hlo hent⟩
  · intro ⟨hle, hent⟩
    exact ⟨lo, Nat.le_refl lo, hle, hent⟩

/-- The complementary excluded interval, including an empty numerical window. -/
theorem interval_empty_iff (j ord lo hi : Nat) :
    (¬ ∃ ell, lo ≤ ell ∧ ell ≤ hi ∧ EntranceNat j ell ord) ↔
      hi < lo ∨ j * j * ord ≤ 2 * lo * (j + 2) := by
  rw [interval_nonempty_iff]
  unfold EntranceNat
  constructor
  · intro h
    by_cases hle : lo ≤ hi
    · exact Or.inr (Nat.le_of_not_lt (fun hent => h ⟨hle, hent⟩))
    · exact Or.inl (Nat.lt_of_not_ge hle)
  · intro h contra
    cases h with
    | inl hbad => exact Nat.not_le_of_gt hbad contra.1
    | inr hbad => exact Nat.not_lt_of_ge hbad contra.2

/-- A positive-ell interval can also start at lo=0: its first possible value
is max 1 lo. All other eligibility requirements are still separate. -/
theorem positive_interval_nonempty_iff (j ord lo hi : Nat) :
    (∃ ell, 0 < ell ∧ lo ≤ ell ∧ ell ≤ hi ∧ EntranceNat j ell ord) ↔
      max 1 lo ≤ hi ∧ EntranceNat j (max 1 lo) ord := by
  constructor
  · intro ⟨ell, hpos, hlo, hhi, hent⟩
    have hfirst : max 1 lo ≤ ell := by omega
    exact ⟨Nat.le_trans hfirst hhi, entrance_downward j ord (max 1 lo) ell hfirst hent⟩
  · intro ⟨hhi, hent⟩
    exact ⟨max 1 lo, by omega, by omega, hhi, hent⟩

/-- With positive j and ord, strict entrance has this exact largest integer ell.
The subtraction by one handles equality correctly before Nat division. -/
theorem entrance_iff_integer_upper (j ell ord : Nat) (hj : 0 < j) (ho : 0 < ord) :
    EntranceNat j ell ord ↔ ell ≤ (j * j * ord - 1) / (2 * (j + 2)) := by
  have ha : 0 < j * j * ord := Nat.mul_pos (Nat.mul_pos hj hj) ho
  have hc : 0 < 2 * (j + 2) := Nat.mul_pos (by decide) (by omega)
  rw [Nat.le_div_iff_mul_le hc]
  unfold EntranceNat
  have rearrange : ell * (2 * (j + 2)) = 2 * ell * (j + 2) := by
    rw [← Nat.mul_assoc, Nat.mul_comm ell 2]
  rw [rearrange]
  exact ⟨Nat.le_sub_one_of_lt, Nat.lt_of_le_sub_one ha⟩

/-- A finite candidate enumeration. `eligible` is an additional Boolean test,
not an assumption that actual primality, Galois, or IUT hypotheses are proved. -/
def candidates (j ord lo hi : Nat) (eligible : Nat → Bool) : List Nat :=
  (List.range (hi + 1)).filter fun ell =>
    decide (0 < ell ∧ lo ≤ ell ∧ EntranceNat j ell ord) && eligible ell

/-- Exact membership in the bounded candidate search; no candidate is inferred
to satisfy an external condition unless its eligibility test has that meaning. -/
theorem mem_candidates_iff (j ord lo hi ell : Nat) (eligible : Nat → Bool) :
    ell ∈ candidates j ord lo hi eligible ↔
      0 < ell ∧ lo ≤ ell ∧ ell ≤ hi ∧ EntranceNat j ell ord ∧ eligible ell = true := by
  simp only [candidates, List.mem_filter, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, Nat.lt_succ_iff]
  constructor
  · intro ⟨hhi, ⟨⟨hpos, hlo, hent⟩, helig⟩⟩
    exact ⟨hpos, hlo, hhi, hent, helig⟩
  · intro ⟨hpos, hlo, hhi, hent, helig⟩
    exact ⟨hhi, ⟨⟨hpos, hlo, hent⟩, helig⟩⟩

/-- The finite search is nonempty exactly when a candidate in its stated window
passes all the displayed tests. This does not identify those tests with geometry. -/
theorem candidates_nonempty_iff (j ord lo hi : Nat) (eligible : Nat → Bool) :
    (∃ ell, ell ∈ candidates j ord lo hi eligible) ↔
      ∃ ell, 0 < ell ∧ lo ≤ ell ∧ ell ≤ hi ∧ EntranceNat j ell ord ∧ eligible ell = true := by
  constructor
  · intro ⟨ell, h⟩
    exact ⟨ell, (mem_candidates_iff j ord lo hi ell eligible).mp h⟩
  · intro ⟨ell, h⟩
    exact ⟨ell, (mem_candidates_iff j ord lo hi ell eligible).mpr h⟩

end IMQEntrance
