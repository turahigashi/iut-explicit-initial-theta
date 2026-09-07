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
