import LeanAuditSupport
set_option Elab.async false

#lean_audit_begin
/-!
# Kernel checks for the arithmetic of the Q(i) initial Theta-datum

This file re-proves, in the Lean 4 kernel and with no imports beyond `Init`, the
exact arithmetic asserted in section 3 of the second report:

    L = F_mod = Q(i),  pi = 10 + 3i  (norm 109, split),  a = pi^29,
    E_0 : y^2 = x(x-1)(x-a),  ell = 7,  F = L(E_0[15]),  K = F(E_0[7]).

Everything below is a statement about concrete integers and about finite groups of
2x2 matrices over F_7.  Every proof is `rfl` or `decide`, so nothing depends on a
tactic that could introduce choice.

## What this file does NOT establish

* It does not verify the geometric conditions (d)-(f) of [IUT1, Def. 3.1] -- the
  core condition, the section, the cusp and the local theta models.  Those are
  section 4 of the report and rest on cited results of anabelian geometry.
* It does not run the seventh-power sieve.  It proves that the bound the sieve uses
  is the correct one, namely that 34869670 = floor(C^(1/7)), which is what makes an
  exhaustive search up to that bound a proof.  The search itself is in
  `scripts/imq_sieve7.cpp`.
* It says nothing about inter-universal Teichmueller theory, about the hypothesis
  (SA) of the first report, or about abc.
-/

namespace IMQ

/-! ## 1. Gaussian integers -/

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
/-- The absolute norm `N(x) = x * conj x`, as an integer. -/
def nrm (x : GI) : Int := x.re * x.re + x.im * x.im

end GI

open GI

/-! ## 2. The datum -/

def pp : Nat := 109
def ell : Nat := 7
def NN : Nat := 29

def pi : GI := ⟨10, 3⟩
def pib : GI := conj pi
def a : GI := pw pi NN
def oma : GI := sub one a          -- 1 - a

/-- `109` is prime: trial division by every `m` with `2 <= m < 109`. -/
def isPrimeB (n : Nat) : Bool := 2 ≤ n && (List.range n).all (fun m => m < 2 || n % m ≠ 0)

theorem p_prime : isPrimeB pp = true := by decide
theorem p_split : pp % 4 = 1 := by decide
theorem norm_pi : nrm pi = 109 := by decide
theorem pi_pib : mul pi pib = ⟨109, 0⟩ := by decide

/-! ## 3. Condition (a): the field of moduli is `Q(i)`

`j(E_0)` is rational exactly when `conj a` lies in the Legendre orbit of `a`.  The
orbit is `{a, 1/a, 1-a, 1/(1-a), a/(a-1), (a-1)/a}`; each membership is cleared of
denominators before being tested, so all six tests are equalities in `Z[i]`. -/

def am1 : GI := sub a one          -- a - 1
def ab : GI := conj a

theorem orbit1 : ab ≠ a := by decide
theorem orbit2 : mul ab a ≠ one := by decide
theorem orbit3 : ab ≠ oma := by decide
theorem orbit4 : mul ab oma ≠ one := by decide
theorem orbit5 : mul ab am1 ≠ a := by decide
theorem orbit6 : mul ab a ≠ am1 := by decide

/-- No Legendre orbit comparison holds, so `j(E_0)` is not rational and
`F_mod = Q(i)`. -/
theorem j_not_rational :
    ab ≠ a ∧ mul ab a ≠ one ∧ ab ≠ oma ∧
    mul ab oma ≠ one ∧ mul ab am1 ≠ a ∧ mul ab a ≠ am1 :=
  ⟨orbit1, orbit2, orbit3, orbit4, orbit5, orbit6⟩

/-! ## 4. The mixed profile above `109`

Since `pi * conj pi = 109`, an element `z` is divisible by `pi` exactly when
`109` divides both coordinates of `z * conj pi`; likewise for `conj pi`. -/

def dvdPi (z : GI) : Bool :=
  let w := mul z pib
  (w.re % 109 == 0) && (w.im % 109 == 0)

def dvdPib (z : GI) : Bool :=
  let w := mul z pi
  (w.re % 109 == 0) && (w.im % 109 == 0)

/-- `a` is exactly the 29th power of `pi`, so `ord_pi(a) = 29`. -/
theorem a_is_pi_pow : a = pw pi 29 := rfl
/-- `pi` and `conj pi` are not associate, so the two places above `109` are distinct. -/
theorem pi_not_dvd_pib : dvdPi pib = false := by decide
/-- Good reduction at `conj pi`: it does not divide `a`. -/
theorem pib_not_dvd_a : dvdPib a = false := by decide
/-- `1 - a` is a unit at both places above `109`. -/
theorem pi_not_dvd_oma : dvdPi oma = false := by decide
theorem pib_not_dvd_oma : dvdPib oma = false := by decide

/-! ## 5. Condition (b): the norms, and the exhaustive sieve bound -/

def Na : Int := nrm a
def Noma : Int := nrm oma
/-- The cofactor left after removing `2 * 3^2 * 5 * 21577`. -/
def CC : Nat := 62680848855374732989482471526907792905767672615779497

theorem norm_a : Na = 109 ^ 29 := by decide
theorem norm_oma_factored : Noma = 2 * 3 ^ 2 * 5 * 21577 * (CC : Int) := by decide
theorem seven_not_dvd_norm_oma : Noma % 7 ≠ 0 := by decide

/-- `34869670` is exactly `floor(CC^(1/7))`.  Hence any prime `q` with `q^7 | CC`
satisfies `q <= 34869670`, and a search over all primes up to that bound is
exhaustive.  The search itself is not performed here. -/
theorem sieve_bound_is_seventh_root :
    (34869670 : Nat) ^ 7 ≤ CC ∧ CC < (34869671 : Nat) ^ 7 := by decide

/-! ## 6. Condition (c): the orders at the selected places -/

/-- The base Tate order at `pi` is `2 * 29 = 58`, which is prime to `7`. -/
theorem ord_q : 2 * NN = 58 := by decide
theorem seven_not_dvd_ord_q : 58 % 7 ≠ 0 := by decide
/-- The remaining selected places contribute `2 * v` with `v` the exponent in the
factorisation above; each is prime to `7`. -/
theorem seven_not_dvd_small : (2 * 2) % 7 ≠ 0 ∧ (2 * 1) % 7 ≠ 0 := by decide

/-! ## 7. Local invariants -/

def eb : Nat := 15 * ell            -- 105

theorem eb_val : eb = 105 := by decide
/-- `gcd(58, 105) = 1`, so adjoining `E_0[105]` has ramification index exactly `105`. -/
theorem gcd_ord_eb : Nat.gcd 58 eb = 1 := by decide
/-- Tameness: `e_b <= p - 2`. -/
theorem tame : eb ≤ pp - 2 := by decide
/-- `ord_109(qbb_b) = 58 / (2 * ell) = 29 / 7`, stated as an identity of integers. -/
theorem ord_qbb : 58 * 7 = 29 * (2 * ell) := by decide

end IMQ

#lean_audit_end "ImaginaryQuadraticDatum"

#lean_audit_begin
/-!
# Kernel checks for the mod-7 image of the Q(i) datum

This file re-proves, in the Lean 4 kernel with no imports beyond `Init`, the two
assertions of section 3(c) of the second report that concern the Galois image:

* at each of the degree-one places `13, 17, 37, 41, 53, 61` the Frobenius trace of
  `E_0` is the stated value and the characteristic polynomial modulo `7` has
  nonsquare discriminant, so the representation is irreducible there;
* conjugating the Tate transvection by the companion matrix of any of those six
  characteristic polynomials produces a second matrix which, together with the
  transvection, generates a group of order `336 = |SL_2(F_7)|`.

The traces are computed here from the curve, not taken from the report, so the
report's arithmetic is not part of the trust chain.

Group elements are encoded as indices in `[0, 2401)` and a subgroup as the bit set
of a natural number; the closure is computed by a fuel-bounded fixpoint and its
cardinality is compared with `336` by the kernel.
-/

set_option maxRecDepth 1000000

namespace IMQ7

/-! ## 1. The curve modulo a degree-one place -/

/-- `a = (10 + 3i)^29` reduced at the degree-one place of `Q(i)` above `q` at which
`i` reduces to `r`, where `r^2 = -1 mod q`.  There are two such places above each
split `q`, one for each root, and they give different traces; the root is therefore
part of the data. -/
def aMod (q r : Nat) : Nat :=
  let base := (10 + 3 * r) % q
  let rec go : Nat → Nat → Nat
    | 0,     acc => acc
    | n + 1, acc => go n (acc * base % q)
  go 29 1

def legendre (x q : Nat) : Int :=
  let rec pw : Nat → Nat → Nat
    | 0, acc => acc
    | n+1, acc => pw n (acc * x % q)
  if x % q == 0 then 0 else (if pw ((q-1)/2) 1 == 1 then 1 else -1)

/-- Frobenius trace of `y^2 = x(x-1)(x - aMod q r)` over `F_q`. -/
def traceAt (q r : Nat) : Int :=
  let am := aMod q r
  let s := (List.range q).foldl
    (fun acc x => acc + legendre (x * ((x + q - 1) % q) % q * ((x + q - am) % q) % q) q) 0
  -- affine points = q + s, all points = q + s + 1, trace = q + 1 - (#points)
  (q : Int) + 1 - ((q : Int) + s + 1)

/-- The smaller square root of `-1` modulo `q`; this pins down which of the two
places above `q` is used.  At `q = 13` and `q = 61` the other place does *not* give
an irreducible characteristic polynomial modulo `7`, so the choice matters. -/
def rootI (q : Nat) : Nat := ((List.range q).filter (fun t => (t*t + 1) % q == 0)).headD 0

theorem root13 : rootI 13 = 5  := by decide
theorem root17 : rootI 17 = 4  := by decide
theorem root37 : rootI 37 = 6  := by decide
theorem root41 : rootI 41 = 9  := by decide
theorem root53 : rootI 53 = 23 := by decide
theorem root61 : rootI 61 = 11 := by decide

/-! ## 2. The traces, computed from the curve -/

theorem tr13 : traceAt 13 (rootI 13) = 6   := by decide
theorem tr17 : traceAt 17 (rootI 17) = -6  := by decide
theorem tr37 : traceAt 37 (rootI 37) = -2  := by decide
theorem tr41 : traceAt 41 (rootI 41) = -6  := by decide
theorem tr53 : traceAt 53 (rootI 53) = -6  := by decide
theorem tr61 : traceAt 61 (rootI 61) = -10 := by decide

/-! ## 3. Irreducibility: the discriminant is a nonsquare modulo 7 -/

def sq7 : List Nat := [0, 1, 2, 4]        -- squares modulo 7

/-- `disc = tr^2 - 4q` reduced modulo `7`, as a natural number. -/
def disc7 (q : Nat) (tr : Int) : Nat := (((tr * tr - 4 * (q : Int)) % 7 + 7) % 7).toNat

theorem nonsq13 : ¬ (disc7 13 6   ∈ sq7) := by decide
theorem nonsq17 : ¬ (disc7 17 (-6) ∈ sq7) := by decide
theorem nonsq37 : ¬ (disc7 37 (-2) ∈ sq7) := by decide
theorem nonsq41 : ¬ (disc7 41 (-6) ∈ sq7) := by decide
theorem nonsq53 : ¬ (disc7 53 (-6) ∈ sq7) := by decide
theorem nonsq61 : ¬ (disc7 61 (-10) ∈ sq7) := by decide

/-- At `q = 13` the other place (root `8`) has trace `2` and *square* discriminant,
so it is not a witness; likewise `q = 61` with root `50`.  Recording this fixes the
choice of place as part of the claim rather than leaving it implicit. -/
theorem other_place_13_fails : traceAt 13 8 = 2 ∧ (disc7 13 2 ∈ sq7) := by decide
theorem other_place_61_fails : traceAt 61 50 = -6 ∧ (disc7 61 (-6) ∈ sq7) := by decide

/-! ## 4. Generation of `SL_2(F_7)` -/

def enc (a b c d : Nat) : Nat := a % 7 + 7 * (b % 7) + 49 * (c % 7) + 343 * (d % 7)
def dec (n : Nat) : Nat × Nat × Nat × Nat := (n % 7, n / 7 % 7, n / 49 % 7, n / 343 % 7)

def mulI (m n : Nat) : Nat :=
  let (a, b, c, d) := dec m
  let (p, q, r, s) := dec n
  enc (a*p + b*r) (a*q + b*s) (c*p + d*r) (c*q + d*s)

def stepOne (gs : List Nat) (S : Nat) : Nat → Nat → Nat
  | 0,     acc => acc
  | i + 1, acc =>
      let acc := if (S >>> i) % 2 == 1
                 then gs.foldl (fun t g => t ||| (1 <<< mulI i g)) acc else acc
      stepOne gs S i acc

def closure (gs : List Nat) (S : Nat) : Nat → Nat
  | 0 => S
  | k + 1 => let T := stepOne gs S 2401 S
             if T == S then S else closure gs T k

def card : Nat → Nat → Nat
  | 0,     _ => 0
  | i + 1, S => (if (S >>> i) % 2 == 1 then 1 else 0) + card i S

def ident : Nat := enc 1 0 0 1
/-- The Tate transvection at the split bad place. -/
def TT : Nat := enc 1 1 0 1
def inv7 (x : Nat) : Nat := ((List.range 7).filter (fun y => x * y % 7 == 1)).headD 0

/-- Companion matrix of `X^2 - tr X + q` modulo `7`, and its inverse. -/
def comp (q : Nat) (tr : Int) : Nat := enc 0 ((7 - q % 7) % 7) 1 (((tr % 7 + 7) % 7).toNat)
def compInv (q : Nat) (tr : Int) : Nat :=
  let di := inv7 (q % 7)
  enc (di * ((tr % 7 + 7) % 7).toNat) (di * (q % 7)) (di * 6) 0

def conjT (q : Nat) (tr : Int) : Nat := mulI (mulI (comp q tr) TT) (compInv q tr)

/-- Each companion matrix is invertible modulo `7` with the stated inverse. -/
theorem compInv13 : mulI (comp 13 6)    (compInv 13 6)    = ident := by decide
theorem compInv17 : mulI (comp 17 (-6)) (compInv 17 (-6)) = ident := by decide
theorem compInv37 : mulI (comp 37 (-2)) (compInv 37 (-2)) = ident := by decide
theorem compInv41 : mulI (comp 41 (-6)) (compInv 41 (-6)) = ident := by decide
theorem compInv53 : mulI (comp 53 (-6)) (compInv 53 (-6)) = ident := by decide
theorem compInv61 : mulI (comp 61 (-10)) (compInv 61 (-10)) = ident := by decide

def gensOrder (q : Nat) (tr : Int) : Nat :=
  card 2401 (closure [TT, conjT q tr] (1 <<< ident) 60)

theorem gen13 : gensOrder 13 6 = 336 := by decide
theorem gen17 : gensOrder 17 (-6) = 336 := by decide
theorem gen37 : gensOrder 37 (-2) = 336 := by decide
theorem gen41 : gensOrder 41 (-6) = 336 := by decide
theorem gen53 : gensOrder 53 (-6) = 336 := by decide
theorem gen61 : gensOrder 61 (-10) = 336 := by decide

/-- `[F : F_mod]` divides `|GL_2(Z/15)| = 23040`, which is prime to `7`, while
`7` divides `|PSL_2(F_7)| = 168`. -/
theorem index_prime_to_seven : 23040 = 2 ^ 9 * 3 ^ 2 * 5 ∧ 23040 % 7 ≠ 0 ∧ 168 % 7 = 0 := by
  decide

end IMQ7

#lean_audit_end "ModSevenImage"

#lean_audit_begin
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

#lean_audit_end "GeometricInput"

#lean_audit_begin
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

#lean_audit_end "GeometricFinite"

#lean_audit_begin
/-!
# The two nodal tangent cones of the Q(i) datum

This file uses only Init and is concatenated after ModSevenImage.lean.  The sole
cross-file definition it uses is `IMQ7.aMod`, the existing reduction of the actual
parameter `(10 + 3*i)^29` at the degree-one place where `i` reduces to `r`.

The computations in section 4 of the second report are checked here:
* multiplication of the three linear factors of the translated Legendre cubic;
* its vanishing constant and linear terms and its degree-two initial form;
* the two distinct factors of the a=1 cone modulo every integer greater than 2;
* the explicit roots 33 and 76 of -1 in the residue field at 109, the actual
  parameter's reduction there, and the factorization and zero set of the a=0 cone.

Coefficients are stored in ascending degree.  A quadratic triple `(xx, xy, yy)`
means `xx*X^2 + xy*X*Y + yy*Y^2`.  The multiplication and initial-form operations
below are explicit computations on coefficients, not abstract split-reduction
predicates.  `Fin 109` has its actual Init modular arithmetic operations.

Scope of the formalization:
* `one_cone_split_modulo` concerns Z/qZ for every q>2; it does not confuse Z/p^fZ
  with the finite field F_(p^f).  The integral identity also applies to every
  odd-characteristic field after scalar extension, but that field adapter is not
  formalized here.
* The geometric identification of these initial forms with the tangent cones of
  the reduced curve, the ordinary-node/split-multiplicative criterion, and the
  residue-field/scalar-extension identifications remain outside this file.
* For the actual a=0 place, the arithmetic root and the parameter are computed;
  neither a square root of -1 nor a reduction a=0 is assumed.  Identifying all
  a=0 places from the norm of a is a number-field adapter, not a theorem below.

The file adds no interface fields, custom axioms, or conclusions about (SA), IUT
inequalities, or abc.  The surrounding geometric interface remains explicit.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace IMQSplit

/-! ## 1. Exact polynomial multiplication and initial forms -/

/-- Addition of coefficient lists, padding the shorter list by zero. -/
def polyAdd : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: polyAdd p q

/-- Ordinary coefficient convolution, with coefficients in ascending degree. -/
def polyMul : List Int → List Int → List Int
  | [], _ => []
  | a :: p, q => polyAdd (q.map (fun b => a * b)) (0 :: polyMul p q)

/-- The RHS of the Legendre equation after x=c+X:
    `(X+c)*(X+c-1)*(X+c-a)`.  This expands the actual three linear factors. -/
def shiftedRhs (a c : Int) : List Int :=
  polyMul (polyMul [c, 1] [c - 1, 1]) [c - a, 1]

def coeff (p : List Int) (n : Nat) : Int := (p[n]?).getD 0

abbrev Quadratic := Int × Int × Int

/-- The homogeneous degree-two coefficient triple of `Y^2 - p(X)`.
    The initial-form theorems below also verify that degrees zero and one vanish. -/
def quadraticPart (p : List Int) : Quadratic := (-coeff p 2, 0, 1)

/-- Multiply `(Z-r)*(Z-s)` by coefficient convolution, then homogenize to
    the quadratic coefficients of `(Y-rX)*(Y-sX)`. -/
def lineProduct (r s : Int) : Quadratic :=
  let p := polyMul [-r, 1] [-s, 1]
  (coeff p 0, coeff p 1, coeff p 2)

/-- Reduction of each coefficient modulo an integer modulus. -/
def reduceQuadratic (q : Nat) (u : Quadratic) : Quadratic :=
  (u.1 % (q : Int), u.2.1 % (q : Int), u.2.2 % (q : Int))

/-- At a=0, c=0 the cubic is `X^3-X^2`. -/
theorem zero_center_expansion : shiftedRhs 0 0 = [0, 0, -1, 1] := by decide

/-- At a=1, c=1 the cubic is `X^3+X^2`. -/
theorem one_center_expansion : shiftedRhs 1 1 = [0, 0, 1, 1] := by decide

/-- The lower terms vanish at (0,0), and the initial form is `Y^2+X^2`.
    Thus its equation is `Y^2=-X^2`. -/
theorem zero_center_initial_form :
    coeff (shiftedRhs 0 0) 0 = 0 ∧ coeff (shiftedRhs 0 0) 1 = 0 ∧
    quadraticPart (shiftedRhs 0 0) = (1, 0, 1) := by decide

/-- After x=1+X the lower terms vanish, and the initial form is `Y^2-X^2`.
    Thus its equation is `Y^2=X^2`. -/
theorem one_center_initial_form :
    coeff (shiftedRhs 1 1) 0 = 0 ∧ coeff (shiftedRhs 1 1) 1 = 0 ∧
    quadraticPart (shiftedRhs 1 1) = (-1, 0, 1) := by decide

/-! ## 2. The a=1 cone: no square-root assumption at any odd prime -/

/-- Coefficient factorization by `Y-X` and `Y+X`, with distinct slopes modulo
    every q>2.  In particular no unknown square-root hypothesis is needed at any
    odd residue characteristic.  This statement uses Z/qZ, not F_(p^f). -/
theorem one_cone_split_modulo (q : Nat) (hq : 2 < q) :
    reduceQuadratic q (lineProduct 1 (-1)) =
      reduceQuadratic q (quadraticPart (shiftedRhs 1 1)) ∧
    (1 : Int) % (q : Int) ≠ (-1 : Int) % (q : Int) := by
  constructor
  · rfl
  · rw [Int.emod_eq_of_lt (by decide) (by omega), Int.neg_emod_eq_sub_emod]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-! ## 3. The actual a=0 residue at pi=10+3i -/

/-- The residue map i↦33 annihilates pi=10+3i.  Both 33 and 76 square to -1,
    are distinct, and the actual parameter reduces to zero at the first map.
    At the conjugate map the parameter is neither zero nor one.
    These are computations from `IMQ7.aMod`, not assumed reduction data. -/
theorem residue109_certificate :
    (33 : Fin 109) * 33 + 1 = 0 ∧
    (76 : Fin 109) * 76 + 1 = 0 ∧
    (33 : Fin 109) ≠ 76 ∧
    (10 : Fin 109) + 3 * 33 = 0 ∧
    IMQ7.aMod 109 33 = 0 ∧
    IMQ7.aMod 109 76 ≠ 0 ∧ IMQ7.aMod 109 76 ≠ 1 := by decide

/-- Equality of the homogeneous polynomial coefficients modulo 109, not just
    equality of the functions they define on the finite set of points. -/
theorem zero_cone_split_modulo109 :
    reduceQuadratic 109 (lineProduct 33 76) =
      reduceQuadratic 109 (quadraticPart (shiftedRhs 0 0)) := by decide

/-- Factorization of the computed a=0 initial form, at every point of the
    actual prime residue field F_109, by the two distinct slopes above. -/
theorem zero_cone_factorization109 : ∀ x y : Fin 109,
    (y - 33 * x) * (y - 76 * x) = y * y + x * x := by decide

/-- The cone has exactly the two specified lines as its zero set in F_109^2.
    Together with the distinct slopes in `residue109_certificate`, this rules out
    an irreducible or repeated tangent direction in this concrete residue field. -/
theorem zero_cone_zero_set109 : ∀ x y : Fin 109,
    y * y + x * x = 0 ↔ y = 33 * x ∨ y = 76 * x := by decide

end IMQSplit

#lean_audit_end "SplitReduction"

#lean_audit_begin
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

#lean_audit_end "GeometricCompletion"

#lean_audit_begin
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

#lean_audit_end "GeometricModels"

#lean_audit_begin
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

#lean_audit_end "EntranceMargin"

#lean_audit_begin
/-!
Exact arithmetic for L=Q(i), pi=10+3i, a=pi^100, ell=31.
Uses the unchanged IMQ.GI integer model in ImaginaryQuadraticDatum.lean.
Concatenate that file first (the full audit supplies the dependency).

The 31-power sieve itself is external. We kernel-check its EXACT bound.
The full norm is NOT seventh-power-free: v2=7, a counterexample below.
The height bounds are directed-rounding certificates in height_audit.py;
this file checks the integer consequences, not transcendental logarithms.
The geometric/number-field interpretation is source-based in datum-proof.md.
There is no assertion of an actual blur or of membership outside Exc_d.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace IMQDeep
open IMQ.GI
abbrev GI := IMQ.GI
def ell : Nat := 31
def NN : Nat := 100
def pi : GI := ⟨10, 3⟩
def a : GI := pw pi NN
def oma : GI := sub one a
def ab : GI := conj a
def am1 : GI := sub a one
def B : Nat := 552904079182587925544083239345463235688361412279973706362632978753327883959485143836167203756966788138316011412609681125016475037186637862888570854434659209800182963205386889166725176972197328279578000000

theorem ell_prime : IMQ.isPrimeB ell = true := by decide
theorem ell_ge_five : 5 ≤ ell := by decide
theorem norm_a : nrm a = 109^100 := by decide
theorem norm_oma : nrm oma = (B : Int) := by decide
theorem smooth : a ≠ ⟨0,0⟩ ∧ a ≠ one := by decide
/-- Cleared-denominator Legendre orbit tests, implying nonrational j in the
quadratic interpretation. They are not a library theorem about number fields. -/
theorem orbit_exclusion :
    ab ≠ a ∧ mul ab a ≠ one ∧ ab ≠ oma ∧
    mul ab oma ≠ one ∧ mul ab am1 ≠ a ∧ mul ab a ≠ am1 := by decide

def t : GI := add (sub (mul a a) a) one
def jNum : GI := mul ⟨256,0⟩ (mul (mul t t) t)
def jDen : GI := mul (mul a a) (mul oma oma)
theorem j_den_nonzero : jDen ≠ ⟨0,0⟩ := by decide
theorem j_nonreal : (mul jNum (conj jDen)).im ≠ 0 := by decide

theorem split_roots : (33*33+1)%109 = 0 ∧ (76*76+1)%109 = 0 := by decide
theorem residues_pi : (10+3*33)%109 = 0 ∧ (10+3*76)%109 = 20 := by decide
theorem conjugate_place_good : 20^100%109 = 81 := by decide
theorem thirty_one_good : B%31 = 2 ∧ (109^100)%31 ≠ 0 := by decide
theorem seven_power_counterexample : B%128 = 0 ∧ B%256 ≠ 0 := by decide
/-- Verified BEFORE the exhaustive external sieve of 265766 primes. -/
theorem sieve_root31 : (3735455:Nat)^31 ≤ B ∧ B < (3735456:Nat)^31 := by decide
/-- Exact seventh root too; no search is claimed at this enormous bound. -/
theorem sieve_root7 : (127671166876556913248840051207:Nat)^7 ≤ B ∧ B < (127671166876556913248840051208:Nat)^7 := by decide
/-- The old sieve's fixed 10^8 cap cannot bound a seventh-power search here. -/
theorem old_seven_cap_insufficient : (100000000:Nat)^7 < B := by decide

theorem order_at_pi : 2*NN = 200 := by decide
theorem order_prime_to_ell : 200%ell ≠ 0 := by decide
theorem degree_prime_to_ell : Nat.gcd 23040 ell = 1 := by decide
/-- Once the external norm sieve has given 1<=v<31, all possible ideal orders
2v are prime to 31. Ramification from F/L is separately prime to 31. -/
theorem remaining_orders :
    (List.range 31).all (fun v => v == 0 || (2*v)%31 != 0) = true := by decide
theorem torsion_order : 15*ell = 465 := by decide
theorem torsion_gcd : Nat.gcd 465 200 = 5 := by decide
theorem field_ramification : 15 / Nat.gcd 15 200 = 3 := by decide
theorem full_ramification : 465 / Nat.gcd 465 200 = 93 := by decide
theorem small_ramification : 93 ≤ 109-2 := by decide
theorem entrance_positive : 6*ell < 2*NN := by decide
theorem margin_numerator : (NN : Int)-3*(ell:Int) = 7 := by decide

/-! A genuine good Frobenius over Q(i), at i=4 in F17. -/
def residueA : Nat := 22^100%17
def quadraticSymbol (x : Nat) : Int :=
  if x%17 == 0 then 0 else if (x%17)^8%17 == 1 then 1 else -1
def rhs (x : Nat) : Nat := (x*((x+16)%17)*((x+17-residueA)%17))%17
def trace17 : Int := -((List.range 17).map (fun x => quadraticSymbol (rhs x))).sum
theorem frobenius_place : (4*4+1)%17 = 0 ∧ residueA = 13 := by decide
theorem frobenius_trace : trace17 = 2 := by decide
theorem frobenius_discriminant : ((2:Int)^2-4*17)%31 = 29 := by decide
theorem irreducible_discriminant :
    (List.range 31).all (fun x => x*x%31 != 29) = true := by decide

/-! Complete candidate set. Given 933 < Hq < 934, the integral square cutoff
below is equivalent to Hq <= ell^2. C1's upper bound exceeds 10*delta here. -/
def candidate (l : Nat) : Bool :=
  IMQ.isPrimeB l && 5 ≤ l && 934 ≤ l*l && 6*l < 200
theorem candidates_exact : (List.range 34).filter candidate = [31] := by decide
theorem larger_candidates_fail (l : Nat) (h : 34 ≤ l) : ¬6*l < 200 := by omega
/-- Necessary-region obstruction only: if ell>=31 and e=15ell, neither base
prime in the two families has the required small ramification. -/
theorem coprime_branch_empty (l : Nat) (hl : 31 ≤ l) :
    ¬(15*l ≤ 107) ∧ ¬(15*l ≤ 209) := by
  have lower : 465 ≤ 15*l := Nat.mul_le_mul_left 15 hl
  exact ⟨fun h => (by decide : ¬(465 ≤ 107)) (Nat.le_trans lower h),
         fun h => (by decide : ¬(465 ≤ 209)) (Nat.le_trans lower h)⟩
theorem actual_fraction_margin :
    IMQEntrance.SameValue
      (IMQEntrance.margin 1 (IMQEntrance.depth 31 200 (by decide)))
      ⟨7,31,by decide⟩ := by decide
theorem actual_fraction_entrance :
    IMQEntrance.Positive
      (IMQEntrance.margin 1 (IMQEntrance.depth 31 200 (by decide))) := by decide
/-- Replacing Hq by full Weil height would falsely discard this witness.
This is a counterfactual integer filter, not the condition in IUT IV. -/
theorem full_weil_proxy_empty :
    (List.range 34).filter (fun l => IMQ.isPrimeB l &&
      5 ≤ l && 1408 ≤ l*l && 6*l < 200) = [] := by decide
end IMQDeep

#lean_audit_end "DeepImaginaryDatum"

#lean_audit_begin
/-!
# The deficit between the combined blur and the stage margin is a constant

Arithmetic over the integers only; nothing about inter-universal Teichmüller theory
is asserted here.  What the two quantities mean, and why one would compare them, is
stated in the accompanying note and is marked there as a *reading*, not a theorem.

Fix a prime `l >= 5`, put `ls = (l-1)/2`, and write the depth as `s = N / l` for a
positive integer `N`.  Both quantities are scaled by `l` to stay in the integers:

* `margin l N j = j^2 N - l (j+2)`   -- `l` times the stage-`j` margin `j^2 s - (j+2)`
* `blur ls N    = ls^2 N`            -- `l` times `ls^2 s`, the diameter of
                                        `{0} u {j^2 s : 1 <= j <= ls}`

The datum's entry condition is `N > 3l`, i.e. `s > 3`, which makes `margin l N 1`
positive.

The content is: the blur dominates every stage margin, and at the top stage the
excess is exactly `l (ls + 2)` -- a constant independent of the depth `N`.  A deeper
datum therefore does not escape.
-/

namespace BlurMargin

/-- `l` times the stage-`j` margin. -/
def margin (l N j : Nat) : Int := (j * j * N : Nat) - (l * (j + 2) : Nat)
/-- `l` times the combined blur. -/
def blur (ls N : Nat) : Int := (ls * ls * N : Nat)

/-- **At the top stage the excess is exactly `l (ls + 2)`.** -/
theorem excess_at_top (l ls N : Nat) :
    blur ls N - margin l N ls = (l * (ls + 2) : Nat) := by
  simp only [blur, margin]
  generalize ((ls * ls * N : Nat) : Int) = A
  generalize ((l * (ls + 2) : Nat) : Int) = B
  omega

/-- **The excess does not depend on the depth.**  Two data of different depth give
the same value, so making the datum deeper changes both quantities by the same
amount. -/
theorem excess_independent_of_depth (l ls N M : Nat) :
    blur ls N - margin l N ls = blur ls M - margin l M ls := by
  rw [excess_at_top l ls N, excess_at_top l ls M]

/-- **The blur dominates every stage.**  Stated without subtraction, in `Nat`. -/
theorem blur_dominates (ls N j l : Nat) (hj : j ≤ ls) :
    j * j * N ≤ ls * ls * N + l * (j + 2) :=
  Nat.le_trans (Nat.mul_le_mul_right N (Nat.mul_le_mul hj hj)) (Nat.le_add_right _ _)

/-! ## The first report's datum: `l = 7`, `N = 29`, so `s = 29/7` and `ls = 3` -/

theorem datum_margins :
    margin 7 29 1 = 8 ∧ margin 7 29 2 = 88 ∧ margin 7 29 3 = 226 := by
  refine ⟨by decide, by decide, by decide⟩

theorem datum_blur : blur 3 29 = 261 := by decide

/-- The excess for the datum is `35 = 7 * 5`, i.e. `5` before the scaling by `l`. -/
theorem datum_excess : blur 3 29 - margin 7 29 3 = 35 := by decide

/-- A much deeper datum, `N = 1000`, has a far larger blur and a far larger margin,
and **exactly the same excess**. -/
theorem deeper_datum : blur 3 1000 = 9000 ∧ margin 7 1000 3 = 8965
    ∧ blur 3 1000 - margin 7 1000 3 = 35 := by
  refine ⟨by decide, by decide, by decide⟩

/-- And one just above the entry threshold, `N = 22` (`3l = 21`). -/
theorem shallow_datum : margin 7 22 1 = 1 ∧ blur 3 22 - margin 7 22 3 = 35 := by
  refine ⟨by decide, by decide⟩

end BlurMargin

#lean_audit_end "BlurExceedsMargin"

#lean_audit_begin
/-!
Exact integer/Gaussian arithmetic for pi=41+26i, a=pi^472, p=2357.
Concatenate ImaginaryQuadraticDatum.lean and EntranceMargin.lean before this file.
No imports beyond Init are used in the mathematical bundle.

The explicit factor constants come from the separate Gaussian-polynomial
certificate. Their norms, full product, ALL 36 pair gcds and ALL 9 exact root
bounds are kernel checked here. The exhaustive 89th-power prime sieve remains
external: these bounds and gcds do not alone prove power-freeness in Lean.
The height cutoff 7325 is an INTEGER input from a separately certified interval;
no transcendental height, number field, elliptic curve or actual blur is formalized.
The Frobenius checks are finite residue/character-sum/nonsquare computations;
abstract Galois-image and geometric adapters remain external.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024
namespace IMQLarge
open IMQ.GI
abbrev GI := IMQ.GI
def pp : Nat := 2357
def NN : Nat := 472
def pi : GI := ⟨41,26⟩
def a : GI := ⟨-7227697787969866684771505702543311838614051760400351150264968958145923014061580097218072991435430363247486620525843678468517585474451326402461486681223873069651326269213162545390194563612614771023308605500006784071189632786416547256401902685644123054537660019670307532070204843176683990214404435444208436410653448315053992495090413775421768737622150696438242537326640174062130666487662014055335930001209556742706418593310149054054749914992726146084361434441071949065180398714072850018930091862137657872164920553563296527463820527060640990991806584290127345312055696236133183703340309506821731164398433675102725713648906798929522807873245626000558635510687929934556590731637736776224107891766887034342660932486262528007377937116560283129298861200469507153196821833095769462238785041380253683084399, 2116282477539050748179122241321809888993633873527491314031598133165187283685498222410035038582694617005605653435914835932469110939584528987081309747876172480879847091948889834567480807645397576619493009401714540765664462345636162396216905804907397914087136073922712825125516342687286487079943674009273187530131248580017166451362063687369808435494437108073253419681380961672633430492844365575307360566742360992156498673602338996332683971681449944410254548919327508252635869898890769919273883850823529112455269094575595193672883753118753377500938995393884397196236209965489994311502236967460542874593152290836035719293599439087304987563754704510800302857673513046336578006314172453247984234566511244569835789064572736276583902447313292015331707783995602245156378437994917835156018984996212829011760⟩
def B : Nat := 56718266838963326786817725942303116338997217697431608129042997907643181092248997200186342001267306166453030459228010985744155373816038473409016930005745818558027640621418272093486039251412749128069537934384939029769274703900745769479471009637594528010739546335751871365675807569729288149557197206603432462926077947125686326772386772913100841874883560619118724375422934324551196738177404085900655732871355307254040579209393646953545929508695413456103911657010085052108516787705184417153194311926001990974643121162423366863449663903474105897932945664103182099663226351720468356690400495001719103091196206243747857151899486751465171062041048289332029861763226769786919970505931100348882898106777680122328497957658850116444101997798723029135713926122102515036807852202664317702463944825177064889428981112966044680265906764765368837427642892332207779189116596368603936224296638705820836750373450562509092217314215671935691442576521081728371096781719360773601442827451953095305734033170900003845053337604595252165245689715911818223210020583838964113108132620204068343408955694685357405766294283169537307783215597246964618633562740350105804480383644033615191973203276785583911581781763246046162262781213936204589993431304690823771962738738755778399683026678098129700246928058045835094479478832643057695830856131511084749100929707651808293549627367492990145679664488353163188358887366588295083080568577802682266815269999555136769274852299759727180702262657246714874500465843275100272642718769760762328390749625236223804046181391446178825707763781419206805848557299091822273612823611345477435741657600

def oma : GI := sub one a

theorem p_prime : IMQ.isPrimeB pp = true := by decide
theorem norm_pi : nrm pi = 2357 := by decide
theorem p_split : pp%4 = 1 := by decide
theorem a_is_power : a = pw pi NN := by decide
theorem norm_a : nrm a = (2357:Nat)^472 := by decide
theorem norm_oma : nrm oma = (B:Int) := by decide
theorem smooth : a ≠ ⟨0,0⟩ ∧ a ≠ one := by decide
/-- Six cleared Legendre-orbit exclusions, an integer test only. -/
theorem orbit_exclusion :
    conj a ≠ a ∧ mul (conj a) a ≠ one ∧ conj a ≠ oma ∧
    mul (conj a) oma ≠ one ∧ mul (conj a) (sub a one) ≠ a ∧
    mul (conj a) a ≠ sub a one := by decide

/-- Phi1,Phi2,Phi4,Phi8,Phi59,Phi118,Phi236,Gplus,Gminus, in that order. -/
def factorGI : List GI := [
  ⟨40, 26⟩,
  ⟨42, 26⟩,
  ⟨1006, 2132⟩,
  ⟨-3535398, 4285320⟩,
  ⟨13916715698874190982795944438203278285831095251824534175404328466027172073998420508165776667750687, 62444678743344582321069618352537943406429392518061622431030794725156746179360982474838026474452918⟩,
  ⟨12106827414710522817529354484456946960772021312442376291327457598463879756153076896945488710061093, 60591529645762825360469430307117198826397895789200023862553105513402748748533767449648774901858242⟩,
  ⟨-3615049550474032615728337720190184735180695227078770751296147450789337654003382565402611406886375853682725352634345396336737086296454138740747385737262168345139156158490083853702565695018105636675, 1595889322570042904903224083900488086410870121625643583977308730582616698100730134348078856058068613047782479627943070192993890460078835268905094583756265329397908745589468877028084065056784796772⟩,
  ⟨-3616768070446714615209530214329643306690320020857103624739859527591491164348900295414509162173277479644971478711511652928729265333864816641033594245708965949321299280422134258969057868647726917532, 1597524154245546736926702781785957259782253813601936346306892409135037006150875040043899337615838819699435764998525050761542736562452745022176804076638474077155526402728074646825318234583910795445⟩,
  ⟨-3613415351918646582665103193715683661924689408315826088499826839851246481674669990134286738186281199304694746092562127096388849991204241416249509184994289298393771844514502273800597604231398152468, 1597605932872934115845266190202955632248214553394144527848673499787018174493725347932570569416916918200410563288279960916244579950286299926472937165182765256727891156727940561406027062183180644155⟩
]
def factorNorms : List Nat := [
  2276,
  2440,
  5557460,
  30863006520804,
  4093012879202802086679954878961851761908515801684656117505705914166224591685623635681898752785541482003828199842205104920898283712901731450876113752277169766071886980170116811550764892511387686693,
  3817908734862941618558843157589005987747451624850113657148765024853412774867409588037705557926185413431615125144628202727899711138992931248570677587581792469290786030702096331678133122428455685213,
  15615445982275575742931589747187904648101145229020325161613398844040641782700312640115145048685776177007196437355715096934105703170575249926589179392120370570822153471882654121341287875936644178051417290671440941105958221162419740334854322256143713205337954419006267403878214455351245927935523725929673999398353659337414137440694742451011391262295676514742183239519891916643331833844446675609,
  15633094698800800615996760468196686719853413408318744187757354831886754484840839324233472631302437654344569595172435660164767507545656933213374997866137664029366208416336432426005785740020756384987574080732424918679817092815680451220432208443539881664483696066207208650612227057753463324175566807903413874088237532033206322036291207578254674180523778219953923641167962732450748544718961719049,
  15609115222232154597936619177966149439635957994326919743112685210030966535632170914715093978263855599887047051835200951453153000521671641465194486785567256630920454727320321687984193740721710245122978595339371661082573083595571654876475317451291107367163800095852591838766826815242538349533450344978073054684760728181843446705365788077149341018341484270895048036796131919959471922644510155049
]
def roots89 : List Nat := [1, 1, 1, 1, 157, 157, 24856, 24856, 24855]

theorem factor_lengths : factorGI.length = 9 ∧ factorNorms.length = 9 ∧ roots89.length = 9 := by decide
theorem factor_norms_exact : factorGI.map nrm = factorNorms.map Int.ofNat := by decide
theorem gaussian_factor_product : factorGI.foldl mul one = sub a one := by decide
theorem integer_factor_product : factorNorms.prod = B := by decide

/-- Every unordered pair (i,j) with 0<=j<i<9, generated explicitly. -/
def factorPairs : List (Nat × Nat) :=
  (List.range 9).flatMap fun i => (List.range i).map fun j => (i,j)
def pairGCDs : List Nat := factorPairs.map fun ij =>
  Nat.gcd (factorNorms[ij.1]!) (factorNorms[ij.2]!)
theorem pair_coverage : factorPairs.length = 36 ∧
    factorPairs.all (fun ij => decide (ij.2 < ij.1 ∧ ij.1 < 9)) = true := by decide
theorem all_pair_gcds : pairGCDs = [4, 4, 20, 4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by decide
theorem pair_gcd_support : pairGCDs.all (fun g => g == 1 || g == 4 || g == 20) = true := by decide
/-- Every one of the nine roots is checked on both sides. The list lengths
above prevent a truncated zip from dropping an input. No sieve is run here. -/
theorem all_roots89 :
    (factorNorms.zip roots89).all (fun nr => decide
      (nr.2^89 ≤ nr.1 ∧ nr.1 < (nr.2+1)^89)) = true := by decide
theorem maximum_root89 : roots89.foldl max 0 = 24856 := by decide
theorem exceptional_v2 : B%512 = 0 ∧ B%1024 ≠ 0 := by decide
theorem exceptional_v5 : B%25 = 0 ∧ B%125 ≠ 0 := by decide
/-- The direct whole-B bound is much larger than the factored bounds. -/
theorem whole_root157 : (13758108969:Nat)^157 ≤ B ∧ B < (13758108970:Nat)^157 := by decide

def ellCandidates : List Nat := [89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157]
theorem ell_count : ellCandidates.length = 14 := by decide
theorem ell_primes : ellCandidates.all IMQ.isPrimeB = true := by decide
theorem ell_B_residues : ellCandidates.map (fun l => B%l) = [88, 68, 59, 20, 78, 14, 75, 73, 34, 80, 12, 135, 123, 6] := by decide
theorem ell_B_nonzero : ellCandidates.all (fun l => B%l != 0) = true := by decide
theorem ell_pi_nonzero : ellCandidates.all (fun l => pp%l != 0) = true := by decide
theorem all_torsion_gcds : ellCandidates.all (fun l => Nat.gcd 944 (15*l) == 1) = true := by decide
theorem all_small_ramification : ellCandidates.all (fun l => decide (15*l ≤ 2355)) = true := by decide
theorem all_height_cutoffs : ellCandidates.all (fun l => decide (7325 ≤ l*l)) = true := by decide
theorem all_entrance_cutoffs : ellCandidates.all (fun l => decide (3*l < 472)) = true := by decide
/-- Exact FINITE numerical candidate filter; not all IUT input conditions. -/
def candidate (l : Nat) : Bool := IMQ.isPrimeB l && decide
  (5 ≤ l ∧ 7325 ≤ l*l ∧ 3*l < 472 ∧ 15*l ≤ 2355)
theorem finite_candidates_exact : (List.range 158).filter candidate = ellCandidates := by decide
/-- Once the external sieve gives 1<=v<=88, these are the order residues.
No ideal valuation, nor the sieve's conclusion, is assumed to be proved here. -/
theorem all_remaining_orders : ellCandidates.all (fun l =>
    (List.range 89).all (fun v => v == 0 || (2*v)%l != 0)) = true := by decide
theorem all_extension_degrees : ellCandidates.all (fun l => Nat.gcd 23040 l == 1) = true := by decide
/-- Only the integer arithmetic of the SL2 cardinality formula. -/
theorem sl157_order_formula : 157*(157*157-1) = (3869736:Nat) := by decide

/-- The actual positive-denominator fraction constructor is used. -/
def marginCheck (l : Nat) : Bool :=
  if hl : 0 < l then decide (IMQEntrance.SameValue
    (IMQEntrance.margin 1 (IMQEntrance.depth l 944 hl))
    ⟨(472:Int)-3*(l:Int),l,hl⟩) else false
theorem all_fraction_margins : ellCandidates.all marginCheck = true := by decide
/-- Positivity is checked with the same canonical depth, not a free s. -/
def positiveMarginCheck (l : Nat) : Bool :=
  if hl : 0 < l then decide (IMQEntrance.Positive
    (IMQEntrance.margin 1 (IMQEntrance.depth l 944 hl))) else false
theorem all_fraction_entrances : ellCandidates.all positiveMarginCheck = true := by decide
theorem margin157 : IMQEntrance.SameValue
    (IMQEntrance.margin 1 (IMQEntrance.depth 157 944 (by decide)))
    ⟨1,157,by decide⟩ := by decide

/-- A row of finite Frobenius arithmetic. The trace is recomputed below. -/
structure FrobeniusWitness where
  ell : Nat
  q : Nat
  rootI : Nat
  residueA : Nat
  trace : Int
  disc : Nat

def quadraticSymbol (q x : Nat) : Int :=
  if x%q == 0 then 0 else if (x%q)^((q-1)/2)%q == 1 then 1 else -1
def legendreTrace (q residue : Nat) : Int :=
  -((List.range q).map (fun x => quadraticSymbol q
    ((x*((x+q-1)%q)*((x+q-residue)%q))%q))).sum
def frobeniusWitnesses : List FrobeniusWitness := [
  ⟨89,13,5,3,-2,41⟩,
  ⟨97,29,12,20,-2,82⟩,
  ⟨101,13,5,3,-2,53⟩,
  ⟨103,29,12,20,-2,94⟩,
  ⟨107,13,5,3,-2,59⟩,
  ⟨109,101,10,24,6,68⟩,
  ⟨113,13,5,3,-2,65⟩,
  ⟨127,41,9,16,10,63⟩,
  ⟨131,13,5,3,-2,83⟩,
  ⟨137,13,5,3,-2,89⟩,
  ⟨139,29,12,20,-2,27⟩,
  ⟨149,13,5,3,-2,101⟩,
  ⟨151,41,9,16,10,87⟩,
  ⟨157,29,12,20,-2,45⟩
]
def frobeniusCheck (w : FrobeniusWitness) : Bool :=
  IMQ.isPrimeB w.q && w.q != w.ell &&
  (w.rootI*w.rootI+1)%w.q == 0 &&
  (41+26*w.rootI)^472%w.q == w.residueA &&
  w.residueA != 0 && w.residueA != 1 &&
  legendreTrace w.q w.residueA == w.trace &&
  (w.trace*w.trace-4*(w.q:Int))%(w.ell:Int) == (w.disc:Int) &&
  (List.range w.ell).all (fun x => x*x%w.ell != w.disc)
theorem frobenius_ell_coverage : frobeniusWitnesses.map (fun w => w.ell) = ellCandidates := by decide
theorem all_frobenius_checks : frobeniusWitnesses.all frobeniusCheck = true := by decide

end IMQLarge

#lean_audit_end "LargeImaginaryDatum"

#lean_audit_begin

/-!
# A finite distinction between invariance and closure

This is the finite model in Appendix B.  It proves statements about four-bit
subsets only, not statements about the possible images in IUT or hypothesis SA.
`act` interchanges 0 with 1 and 2 with 3; `hull` fills the interval spanned by a
subset.  `VolInvariant` and `UpToAct` are distinct predicates.  Invariance alone
does not imply closure.  For the orbit predicate both hold, yet the hull of the
union has strictly larger cardinality than the hull of either orbit member.
-/

namespace RegardedUpTo

def mem (n i : Nat) : Bool := (n / 2 ^ i) % 2 == 1

def card (n : Nat) : Nat :=
  (if mem n 0 then 1 else 0) + (if mem n 1 then 1 else 0)
  + (if mem n 2 then 1 else 0) + (if mem n 3 then 1 else 0)

def act (n : Nat) : Nat :=
  (if mem n 0 then 2 else 0) + (if mem n 1 then 1 else 0)
  + (if mem n 2 then 8 else 0) + (if mem n 3 then 4 else 0)

def hull (n : Nat) : Nat :=
  if n == 0 then 0 else
  let lo := if mem n 0 then 0 else if mem n 1 then 1 else if mem n 2 then 2 else 3
  let hi := if mem n 3 then 3 else if mem n 2 then 2 else if mem n 1 then 1 else 0
  (if 0 ≥ lo && 0 ≤ hi then 1 else 0) + (if 1 ≥ lo && 1 ≤ hi then 2 else 0)
  + (if 2 ≥ lo && 2 ≤ hi then 4 else 0) + (if 3 ≥ lo && 3 ≤ hi then 8 else 0)

def cup (m n : Nat) : Nat :=
  (if mem m 0 || mem n 0 then 1 else 0) + (if mem m 1 || mem n 1 then 2 else 0)
  + (if mem m 2 || mem n 2 then 4 else 0) + (if mem m 3 || mem n 3 then 8 else 0)

def A : Nat := 5

def sA : Nat := 10

theorem act_A : act A = sA := by decide

theorem act_is_nontrivial : A ≠ act A := by decide

theorem hull_card_invariant : card (hull A) = card (hull (act A)) := by decide

theorem union_hull_exceeds_every_member :
    card (hull A) < card (hull (cup A (act A)))
    ∧ card (hull (act A)) < card (hull (cup A (act A))) := by decide

abbrev VolInvariant (Output : Nat → Prop) : Prop :=
  ∀ r, Output r → card (hull (act r)) = card (hull r)

abbrev UpToAct (Output : Nat → Prop) : Prop :=
  ∀ r, Output r → Output (act r)

abbrev Single (r : Nat) : Prop := r = A

theorem orbit_not_forced_by_invariance :
    VolInvariant Single ∧ ¬ UpToAct Single := by
  constructor
  · intro r hr; subst hr; decide
  · intro h
    have h2 : act A = A := h A rfl
    exact absurd h2 (by decide)

abbrev Orbit (r : Nat) : Prop := r = A ∨ r = sA

theorem act_sA : act sA = A := by decide

theorem orbit_is_up_to_act : UpToAct Orbit := by
  intro r hr
  rcases hr with h | h
  · exact Or.inr (by rw [h, act_A])
  · exact Or.inl (by rw [h, act_sA])

theorem orbit_vol_invariant : VolInvariant Orbit := by
  intro r hr
  rcases hr with h | h <;> subst h <;> decide

theorem the_point :
    UpToAct Orbit
    ∧ VolInvariant Orbit
    ∧ card (hull A) < card (hull (cup A (act A)))
    ∧ card (hull (act A)) < card (hull (cup A (act A))) :=
  ⟨orbit_is_up_to_act, orbit_vol_invariant, by decide, by decide⟩

/-! ## Axiom check

The per-declaration axiom dependencies of this file are reported by
`scripts/lean_audit.py`, which runs Lean's print-axioms command on EVERY
declaration the file adds to the environment, not only on the named theorems.
The explicit print-axioms lines that used to stand here covered a self-selected
subset; an axiom report not attributable to a declaration the auditor is
tracking is exactly what the auditor refuses to accept, so they are removed.
-/

end RegardedUpTo

#lean_audit_end "RegardedUpToIsOrbit"

#lean_audit_begin
/-!
# A basis-free replacement for the mod-7 image argument

`ModSevenImage.lean` proves that the standard transvection `T = [[1,1],[0,1]]` and the
companion matrix `C` of a Frobenius characteristic polynomial generate a group of order
`336 = |SL_2(F_7)|`.  External review observed that this does not by itself settle the
image, because the basis putting inertia into the form `T` need not be the basis putting
Frobenius into the form `C`: the actual Frobenius `g` is only *conjugate* to `C`.

This file removes the dependence on any choice of basis.  It proves, with no imports
beyond `Init`:

* `irreducible_moves_every_line`: a matrix over `F_7` whose characteristic polynomial is
  irreducible fixes no line.  Hence for a transvection `T` with fixed line `L`, the
  conjugate `g T g⁻¹` is a transvection with fixed line `g L ≠ L`.
* `sl2_transitive_on_distinct_pairs`: `SL_2(F_7)` acts transitively on ordered pairs of
  distinct lines, so such a pair may be moved to `(⟨e₁⟩, ⟨e₂⟩)`.
* `normalized_pairs_generate`: for every `a, b ≠ 0`, the transvections `[[1,a],[0,1]]`
  and `[[1,0],[b,1]]` generate all of `SL_2(F_7)`.

Together these say: *whenever the image contains a nontrivial transvection and a matrix
with irreducible characteristic polynomial, it contains `SL_2(F_7)`* -- with no choice of
basis anywhere.  Nothing here depends on which matrices the arithmetic produces.

Encoding: a matrix is the index `a + 7b + 49c + 343d` in `[0, 2401)`; a subgroup is the
bit set of a natural number; closures are fuel-bounded fixpoints checked by the kernel.
-/

set_option maxRecDepth 4000000

namespace BasisFree

/-! ## 1. Encoding -/

def enc (a b c d : Nat) : Nat := a % 7 + 7 * (b % 7) + 49 * (c % 7) + 343 * (d % 7)
def dec (n : Nat) : Nat × Nat × Nat × Nat := (n % 7, n / 7 % 7, n / 49 % 7, n / 343 % 7)

def mulI (m n : Nat) : Nat :=
  let (a, b, c, d) := dec m
  let (p, q, r, s) := dec n
  enc (a*p + b*r) (a*q + b*s) (c*p + d*r) (c*q + d*s)

def detI (m : Nat) : Nat :=
  let (a, b, c, d) := dec m
  (a*d + 7*7 - b*c) % 7

def ident : Nat := enc 1 0 0 1

/-! ## 2. Lines of `F_7^2`, as the eight projective points -/

/-- The eight lines, each given by a representative vector. -/
def lines : List (Nat × Nat) := (List.range 7).map (fun x => (1, x)) ++ [(0, 1)]

/-- Normalize a nonzero vector to the representative of its line. -/
def normLine (v : Nat × Nat) : Nat × Nat :=
  let (x, y) := (v.1 % 7, v.2 % 7)
  if x == 0 then (0, 1)
  else
    let xi := ((List.range 7).filter (fun t => x * t % 7 == 1)).headD 0
    (1, y * xi % 7)

def actL (m : Nat) (v : Nat × Nat) : Nat × Nat :=
  let (a, b, c, d) := dec m
  normLine ((a * v.1 + b * v.2) % 7, (c * v.1 + d * v.2) % 7)

theorem lines_card : lines.length = 8 := by decide

/-! ## 3. An irreducible characteristic polynomial moves every line -/

/-- `X^2 - t X + d` has no root modulo `7`. -/
def irreducibleCharPoly (t d : Nat) : Bool :=
  (List.range 7).all (fun x => (x * x + 7 * 7 - t % 7 * x + d) % 7 != 0)

def traceI (m : Nat) : Nat := let (a, _, _, d) := dec m; (a + d) % 7

/-- The matrices of `GL_2(F_7)` whose characteristic polynomial is irreducible. -/
def irrMats : List Nat :=
  (List.range 2401).filter (fun m => detI m != 0 && irreducibleCharPoly (traceI m) (detI m))

theorem irrMats_card : irrMats.length = 882 := by decide

/-- **No basis is chosen here.**  Every matrix with irreducible characteristic
polynomial moves every line.  In particular the fixed line of a transvection is moved,
so the conjugate transvection has a different fixed line. -/
theorem irreducible_moves_every_line :
    irrMats.all (fun g => lines.all (fun L => actL g L != normLine L)) = true := by decide

/-! ## 4. `SL_2(F_7)` is transitive on ordered pairs of distinct lines -/

def sl2 : List Nat := (List.range 2401).filter (fun m => detI m == 1)

theorem sl2_card : sl2.length = 336 := by decide

/-- The orbit of `(⟨e₁⟩, ⟨e₂⟩)` has `56 = 8 * 7` elements, i.e. is everything. -/
theorem sl2_transitive_on_distinct_pairs :
    ((sl2.map (fun g => (actL g (1, 0), actL g (0, 1)))).eraseDups).length = 56 := by
  decide

/-! ## 5. Two transvections with distinct fixed lines generate -/

def stepOne (gs : List Nat) (S : Nat) : Nat → Nat → Nat
  | 0,     acc => acc
  | i + 1, acc =>
      let acc := if (S >>> i) % 2 == 1
                 then gs.foldl (fun t g => t ||| (1 <<< mulI i g)) acc else acc
      stepOne gs S i acc

def closure (gs : List Nat) (S : Nat) : Nat → Nat
  | 0 => S
  | k + 1 => let T := stepOne gs S 2401 S
             if T == S then S else closure gs T k

def card : Nat → Nat → Nat
  | 0,     _ => 0
  | i + 1, S => (if (S >>> i) % 2 == 1 then 1 else 0) + card i S

/-- Conjugating by `diag(u,1)` sends `[[1,a],[0,1]]` to `[[1,ua],[0,1]]` and
`[[1,0],[b,1]]` to `[[1,0],[u⁻¹b,1]]`, and conjugation carries the subgroup generated by
a pair to the subgroup generated by the conjugated pair.  Taking `u = a⁻¹` therefore
reduces the `36` pairs of section 5 to the `6` with `a = 1`. -/
theorem diagonal_conjugation_normalizes :
    ((List.range 6).map (· + 1)).all (fun a =>
      let u := ((List.range 7).filter (fun t => a * t % 7 == 1)).headD 0
      let D := enc u 0 0 1
      let Di := enc a 0 0 1
      mulI (mulI D (enc 1 a 0 1)) Di == enc 1 1 0 1) = true := by decide

/-- After that normalization the fixed lines are `⟨e₁⟩` and `⟨e₂⟩` and the first
transvection is `[[1,1],[0,1]]`.  Each of the six remaining pairs generates all of
`SL_2(F_7)`. -/
theorem normalized_pairs_generate_1 :
    card 2401 (closure [enc 1 1 0 1, enc 1 0 1 1] (1 <<< ident) 40) = 336 := by decide
theorem normalized_pairs_generate_2 :
    card 2401 (closure [enc 1 1 0 1, enc 1 0 2 1] (1 <<< ident) 40) = 336 := by decide
theorem normalized_pairs_generate_3 :
    card 2401 (closure [enc 1 1 0 1, enc 1 0 3 1] (1 <<< ident) 40) = 336 := by decide
theorem normalized_pairs_generate_4 :
    card 2401 (closure [enc 1 1 0 1, enc 1 0 4 1] (1 <<< ident) 40) = 336 := by decide
theorem normalized_pairs_generate_5 :
    card 2401 (closure [enc 1 1 0 1, enc 1 0 5 1] (1 <<< ident) 40) = 336 := by decide
theorem normalized_pairs_generate_6 :
    card 2401 (closure [enc 1 1 0 1, enc 1 0 6 1] (1 <<< ident) 40) = 336 := by decide

/-! ## 6. Axiom check

The per-declaration axiom dependencies of this file are reported by
`scripts/lean_audit.py`, which runs Lean's print-axioms command on EVERY
declaration the file adds to the environment, not only on the named theorems.
The explicit print-axioms lines that used to stand here covered a self-selected
subset; an axiom report not attributable to a declaration the auditor is
tracking is exactly what the auditor refuses to accept, so they are removed.
-/


end BasisFree

#lean_audit_end "BasisFreeImage"

#lean_audit_begin
/-!
# Finite arithmetic behind Proposition 2 (the existence family)

Proposition 2 of the report is an existence statement over all `N`, and most of its
proof -- Hensel lifting, a sieve over primes, a density bound and an asymptotic -- is
NOT formalised anywhere in this development, as the Reproduction section says.

What IS formalised here is the finite, algebraic part, and specifically the step whose
absence was a real gap: the root count in the sieve needs `q ∤ M = 5 p^(N+1)`, so the
case `q = p` has to be excluded, and an earlier version of the proof did not exclude
it.  External review found that on 2026-09-07.  The lemma below is the exclusion.

Nothing here imports anything beyond `Init`.

`f(A) = (A^2 + 1) * ((A-1)^2 + 1)`, the norm form of the family.
-/

namespace FamilyArith

/-- **The gap, closed.**  If `p` divides both `r^2 + 1` and `(r-1)^2 + 1`, then `p ∣ 5`.

The sieve chooses `A ≡ r (mod p)` with `r^2 ≡ -1 (mod p)`, so `p` divides the first
factor of `f(A)` to order exactly `N`.  This says `p` cannot also divide the second
factor unless `p ∣ 5`, which the family excludes.  Hence `p ∤ G_N(x)`, hence `q ≠ p`
for any `q` with `q^7 ∣ G_N(x)`, which is what makes `q ∤ M` and lets the roots in `x`
be counted by the roots of `f`. -/
theorem dvd_five_of_both (p r : Int)
    (h1 : p ∣ (r * r + 1)) (h2 : p ∣ ((r - 1) * (r - 1) + 1)) : p ∣ 5 := by
  -- p divides the difference of the two factors, which is 2r - 1
  have e1 : (r * r + 1) - ((r - 1) * (r - 1) + 1) = 2 * r - 1 := by
    simp [Int.sub_mul, Int.mul_sub]; omega
  have hlin : p ∣ (2 * r - 1) := e1 ▸ Int.dvd_sub h1 h2
  -- 4*(r^2+1) - (2r-1)(2r+1) = 5, and p divides each term on the left
  -- omega is linear, so the two products are supplied to it as facts
  -- NOTE: `Int.mul_left_comm` is flagged "unused" by the linter and is NOT: dropping
  -- it makes this `simp` fail, and a failed tactic silently puts `sorryAx` into every
  -- theorem below.  Verified by `#print axioms` after each edit.
  have sq4 : (2 * r) * (2 * r) = 4 * (r * r) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have key : 4 * (r * r + 1) - (2 * r - 1) * (2 * r + 1) = 5 := by
    simp [Int.sub_mul, Int.mul_add]; omega
  obtain ⟨d, hd⟩ := h1
  obtain ⟨c, hc⟩ := hlin
  have hA : p ∣ 4 * (r * r + 1) := ⟨4 * d, by
    rw [hd]; simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]⟩
  have hB : p ∣ (2 * r - 1) * (2 * r + 1) := ⟨c * (2 * r + 1), by
    rw [hc]; simp [Int.mul_assoc]⟩
  exact key ▸ Int.dvd_sub hA hB

/-- The contrapositive, in the form the proof uses: a prime not dividing `5` and
dividing `r^2 + 1` does not divide `(r-1)^2 + 1`. -/
theorem not_dvd_other_factor (p r : Int)
    (hp : ¬ (p ∣ 5)) (h1 : p ∣ (r * r + 1)) : ¬ (p ∣ ((r - 1) * (r - 1) + 1)) :=
  fun h2 => hp (dvd_five_of_both p r h1 h2)

/-- The factorisation of the integer `400`.  **This is not a discriminant theorem.**
`400` is the value of `disc(f)` for `f(A) = (A^2+1)((A-1)^2+1)`, computed by ordinary
means outside Lean; neither `f` nor the discriminant appears in the statement below.
What the kernel checks is the numeric identity, which is what the sieve uses when it
says only `2` and `5` need separate treatment. -/
theorem four_hundred_factors : (400 : Int) = 2 ^ 4 * 5 ^ 2 := by decide

end FamilyArith

#lean_audit_end "FamilyArithmetic"
