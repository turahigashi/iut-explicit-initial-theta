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
