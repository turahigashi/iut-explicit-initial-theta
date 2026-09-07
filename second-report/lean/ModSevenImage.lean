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
