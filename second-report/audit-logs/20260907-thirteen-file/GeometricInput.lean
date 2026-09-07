/-!
# The geometric conditions, relative to a cited-results interface

Section 4 of the second report deduces conditions (d)-(f) of [IUT1, Def. 3.1] for the
`Q(i)` datum from published results of anabelian geometry.  Formalising those results
themselves is out of reach.  What is in reach, and what this file does, is the
Semeria/CoRN pattern: state the cited results as the fields of an *interface*, prove
the deduction relative to any structure satisfying it, and then discharge as much of
the input as possible by outright computation rather than by assumption.

Three things are done here, in increasing order of what they cost.

1. `j_not_rational` and `flags_transitive` are **proved outright**, with no interface
   and no assumption.  They are the two arithmetic inputs that section 4 uses.
2. `AnabelianInput` is the interface.  Every field carries the verbatim locator of
   the result it states.
3. `core_of_datum` is the deduction, relative to the interface.

The point of doing it this way is that the antecedent of the cited conditional is
*discharged*, not assumed: `mfhmp_2_1` says that an arithmetic curve has rational
`j`, and `j_not_rational` proves that ours does not.  A previous project of the
author's assumed bridge statements whose antecedents were never discharged and whose
interfaces had no non-degeneracy witness; §4 of this file records the two checks that
were missing there.
-/

set_option maxRecDepth 1000000

namespace IMQGeom

/-! ## 1. `j` is not rational -- proved, not assumed -/

structure GI where
  re : Int
  im : Int
deriving DecidableEq, Repr

namespace GI
def mul (x y : GI) : GI := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩
def add (x y : GI) : GI := ⟨x.re + y.re, x.im + y.im⟩
def sub (x y : GI) : GI := ⟨x.re - y.re, x.im - y.im⟩
def one : GI := ⟨1, 0⟩
def pw (x : GI) : Nat → GI
  | 0 => one
  | n + 1 => mul (pw x n) x
def conj (x : GI) : GI := ⟨x.re, -x.im⟩
end GI
open GI

def a : GI := pw ⟨10, 3⟩ 29

/-- Numerator and denominator of `j(E_0) = 256 (a^2 - a + 1)^3 / (a^2 (a-1)^2)`. -/
def jNum : GI := mul ⟨256, 0⟩ (pw (add (sub (mul a a) a) one) 3)
def jDen : GI := mul (mul a a) (pw (sub a one) 2)

/-- `j = jNum / jDen` lies in `Q` exactly when `Im(jNum * conj jDen) = 0`, since the
denominator of that quotient, `N(jDen)`, is a nonzero rational. -/
abbrev jIsRational : Prop := (mul jNum (conj jDen)).im = 0

theorem jDen_ne_zero : jDen ≠ ⟨0, 0⟩ := by decide

/-- **Proved.**  `j(E_0)` is not rational. -/
theorem j_not_rational : ¬ jIsRational := by decide

/-- The four `j`-invariants of [MFHMP, Prop. 2.1], as pairs (numerator, denominator)
of integers: `2^14 31^3 5^{-3}`, `2^2 73^3 3^{-4}`, `1728`, `0`. -/
def excJ : List (Int × Int) := [(488095744, 125), (1556068, 81), (1728, 1), (0, 1)]

/-- Each exceptional invariant is rational, i.e. is a quotient of integers with
nonzero denominator.  Together with `j_not_rational` this is what rules them out. -/
theorem exc_all_rational : excJ.all (fun p => p.2 ≠ 0) = true := by decide

/-! ## 2. `SL_2(F_7)` is transitive on marked flags -- proved, not assumed

A *marked flag* is a line `W` in `V = E_0[7]` together with a nonzero class in `V/W`
taken up to sign; this is the datum that the Tate parameter determines at a bad place
(the toric line, and the class of `q^{1/7}`).  Section 4 needs that any two marked
flags are related by an element of the image, so that one global choice of quotient
and cusp can be matched at every bad place at once.

Vectors of `F_7^2` are encoded as `x + 7 y`; a set of vectors as a bit set. -/

def encV (x y : Nat) : Nat := x % 7 + 7 * (y % 7)
def actV (m : Nat) (v : Nat) : Nat :=
  let a := m % 7; let b := m / 7 % 7; let c := m / 49 % 7; let d := m / 343 % 7
  let x := v % 7; let y := v / 7
  encV (a * x + b * y) (c * x + d * y)

/-- Image of a bit set of vectors under a matrix. -/
def actSet (m : Nat) : Nat → Nat → Nat
  | 0,     _ => 0
  | i + 1, S => (if (S >>> i) % 2 == 1 then 1 <<< actV m i else 0) ||| actSet m i S

def cardBits : Nat → Nat → Nat
  | 0,     _ => 0
  | i + 1, S => (if (S >>> i) % 2 == 1 then 1 else 0) + cardBits i S

/-- The line through `v`, as a bit set. -/
def lineOf (v : Nat) : Nat :=
  (List.range 7).foldl (fun acc t => acc ||| (1 <<< actV (encM t 0 0 t) v)) 0
where encM (a b c d : Nat) : Nat := a % 7 + 7 * (b % 7) + 49 * (c % 7) + 343 * (d % 7)

/-- The union of the coset `v + W` and its negative, as a bit set: this together with
the line is the marked flag. -/
def cosetPair (W v : Nat) : Nat :=
  (List.range 49).foldl
    (fun acc w =>
      if (W >>> w) % 2 == 1 then
        let x := (v % 7 + w % 7) % 7
        let y := (v / 7 + w / 7) % 7
        acc ||| (1 <<< encV x y) ||| (1 <<< encV ((7 - x) % 7) ((7 - y) % 7))
      else acc) 0

/-- A marked flag, keyed as one natural number. -/
def flagKey (W v : Nat) : Nat := W * 2 ^ 49 + cosetPair W v

def allFlags : List Nat :=
  let vs := (List.range 49).filter (fun v => v ≠ 0)
  let ks := vs.flatMap (fun v =>
    let W := lineOf v
    (vs.filter (fun u => (W >>> u) % 2 == 0)).map (fun u => flagKey W u))
  ks.foldl (fun acc k => if acc.contains k then acc else k :: acc) []

def actFlag (m W v : Nat) : Nat := actSet m 49 W * 2 ^ 49 + actSet m 49 (cosetPair W v)

def SL7 : List Nat :=
  (List.range 2401).filter (fun n =>
    let a := n % 7; let b := n / 7 % 7; let c := n / 49 % 7; let d := n / 343 % 7
    (a * d + 7 * 7 - b * c) % 7 == 1)

theorem sl7_card : SL7.length = 336 := by decide

/-- There are exactly `24` marked flags. -/
theorem flags_card : allFlags.length = 24 := by decide

/-- **Proved.**  The orbit of one marked flag under `SL_2(F_7)` is everything: the
action is transitive, with stabiliser of order `336 / 24 = 14`. -/
theorem flags_transitive :
    (SL7.map (fun m => actFlag m (lineOf 1) 7)).eraseDups.length = 24 := by decide

theorem stabiliser_order : 336 = 24 * 14 := by decide

/-- **Proved.**  For every nonzero class `x` in `V/W = F_7`, the class `2x` is
neither `x` nor `-x`.  This is the last step of section 4: it is what makes the cusp
`2*epsilon` distinct from `epsilon`, and hence supplies the arrow-marked covers of
[IUT1, Def. 1.1, Rem. 1.1.2] used in condition (f). -/
theorem two_xi_ne_pm_xi :
    (List.range 7).all (fun x => x == 0 || ((2 * x % 7 != x) && (2 * x % 7 != (7 - x) % 7)))
      = true := by decide

/-! ## 3. The interface, and the deduction relative to it -/

/-- What the cited results supply.  Each field is the statement of a published
result, named by its locator; nothing here is new mathematics. -/
structure AnabelianInput where
  /-- The orbicurves in play, abstractly. -/
  Curve : Type
  /-- `X` fails to admit a core over the base field. -/
  IsArithmetic : Curve → Prop
  /-- `X` is a core. -/
  IsCore : Curve → Prop
  /-- `X` is a punctured hemi-elliptic orbicurve [CanLift, Def. 2.6(ii)]. -/
  IsPuncturedHemiElliptic : Curve → Prop
  /-- `j` of the elliptic curve underlying `X` is rational. -/
  HasRationalJ : Curve → Prop
  /-- **[MFHMP, Prop. 2.1]** an arithmetic once-punctured elliptic curve in
      characteristic zero has `j` equal to one of four rational numbers; in
      particular its `j` is rational. -/
  mfhmp_2_1 : ∀ X, IsArithmetic X → HasRationalJ X
  /-- **[CanLift, Prop. 2.7]** a non-arithmetic punctured hemi-elliptic orbicurve
      over an algebraically closed field of characteristic zero is a core. -/
  canlift_2_7 : ∀ X, IsPuncturedHemiElliptic X → ¬ IsArithmetic X → IsCore X
  /-- The orbicurve of the datum of the report. -/
  X0 : Curve
  /-- It is punctured hemi-elliptic [CanLift, Def. 2.6(ii)]: it is the quotient of a
      once-punctured elliptic curve by `±1`. -/
  X0_phe : IsPuncturedHemiElliptic X0
  /-- **The modelling link, stated so that it can be inspected.**  The interface's
      predicate `HasRationalJ` at `X0` is the concrete condition on the `j` computed
      above from `a = (10+3i)^29`.  This is the one place where the abstract side is
      tied to the arithmetic side; it is a field of the interface, not a theorem. -/
  X0_j : HasRationalJ X0 ↔ jIsRational

/-- **The deduction.**  For any structure satisfying the interface, a punctured
hemi-elliptic orbicurve whose `j` is irrational is a core.  Applied to our datum the
second hypothesis is discharged by `j_not_rational`, not assumed. -/
theorem core_of_irrational_j (A : AnabelianInput) (X : A.Curve)
    (hphe : A.IsPuncturedHemiElliptic X) (hj : ¬ A.HasRationalJ X) : A.IsCore X :=
  A.canlift_2_7 X hphe (fun harith => hj (A.mfhmp_2_1 X harith))

/-- **The datum's orbicurve is a core.**  Every hypothesis is either a field of the
interface -- a cited result, or the modelling link -- or the computation
`j_not_rational`.  Nothing is assumed about `j` itself. -/
theorem core_of_datum (A : AnabelianInput) : A.IsCore A.X0 :=
  core_of_irrational_j A A.X0 A.X0_phe (fun h => j_not_rational (A.X0_j.mp h))

/-! ## 4. The two checks that a previous axiomatisation of the author's lacked -/

/-- **Non-degeneracy.**  The interface is not satisfied only vacuously: here is a
model in which `IsArithmetic` really does hold of something, `IsCore` really does
fail of something, and the two cited fields are still true.  So the fields do not
force the predicates to be constant. -/
def witness : AnabelianInput where
  Curve := Bool
  IsArithmetic := fun b => b = true
  IsCore := fun b => b = false
  IsPuncturedHemiElliptic := fun _ => True
  HasRationalJ := fun b => b = true
  mfhmp_2_1 := fun _ h => h
  canlift_2_7 := fun b _ h => by
    cases b with
    | false => rfl
    | true  => exact absurd rfl h
  X0 := false
  X0_phe := trivial
  X0_j := ⟨fun h => absurd h (fun k => Bool.noConfusion k),
           fun h => absurd h j_not_rational⟩

theorem witness_arithmetic_inhabited : witness.IsArithmetic true := rfl
theorem witness_core_fails : ¬ witness.IsCore true := fun h => Bool.noConfusion h
theorem witness_core_holds : witness.IsCore false := rfl

/-- **Necessity of the cited field.**  Dropping `mfhmp_2_1` really does break the
deduction: the remaining data can be satisfied while the conclusion fails.  Here
`IsCore` is empty, `canlift_2_7` holds because its second hypothesis never does, and
yet there is a curve that is punctured hemi-elliptic with irrational `j`.  So
`core_of_irrational_j` is not derivable from the other fields alone. -/
structure WeakInput where
  Curve : Type
  IsArithmetic : Curve → Prop
  IsCore : Curve → Prop
  IsPuncturedHemiElliptic : Curve → Prop
  HasRationalJ : Curve → Prop
  canlift_2_7 : ∀ X, IsPuncturedHemiElliptic X → ¬ IsArithmetic X → IsCore X

def counter : WeakInput where
  Curve := Unit
  IsArithmetic := fun _ => True
  IsCore := fun _ => False
  IsPuncturedHemiElliptic := fun _ => True
  HasRationalJ := fun _ => False
  canlift_2_7 := fun _ _ h => absurd trivial h

theorem mfhmp_is_necessary :
    counter.IsPuncturedHemiElliptic () ∧ ¬ counter.HasRationalJ () ∧ ¬ counter.IsCore () :=
  ⟨trivial, fun h => h, fun h => h⟩

end IMQGeom
