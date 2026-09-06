#!/usr/bin/env python3
"""Reproduce the paper's displayed arithmetic and comparison constants.

The geometric constructions, cited theorems and hypothesis SA are not verified
by this program. Run the companion C++ sieve for the seventh-power-free norm.
All inequality certificates are rational; Decimal values are illustrative only.

    python3 scripts/checks.py
"""
import sys
from fractions import Fraction as F
from decimal import Decimal, getcontext
from math import factorial, gcd

if not __debug__:
    raise SystemExit("Run with assertions enabled (do not use python -O).")

getcontext().prec = 50
FAIL = []

def check(name, got, want):
    ok = (got == want)
    print(f"  [{'ok' if ok else 'FAIL'}] {name}: {got}" + ("" if ok else f"  (expected {want})"))
    if not ok:
        FAIL.append(name)

# ---------------------------------------------------------------- Z[sqrt5]
def mul(x, y):  return (x[0]*y[0] + 5*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def sub(x, y):  return (x[0]-y[0], x[1]-y[1])
def conj(x):    return (x[0], -x[1])
def norm(x):    return x[0]*x[0] - 5*x[1]*x[1]
def power(x, n):
    r = (1, 0)
    for _ in range(n):
        r = mul(r, x)
    return r

def is_prime(n):
    if n < 2: return False
    d = 2
    while d*d <= n:
        if n % d == 0: return False
        d += 1
    return True

PI  = (16, 3)
ONE = (1, 0)
A   = power(PI, 29)

print("(1) the quadratic field and the split prime")
check("Norm(pi)", norm(PI), 211)
check("211 is prime", is_prime(211), True)
roots = [x for x in range(211) if (x*x - 5) % 211 == 0]
check("sqrt(5) mod 211", roots, [65, 146])

print("(2) valuations of a = pi^29")
check("Norm(a) = 211^29", norm(A) == 211**29, True)
check("digits of A", len(str(abs(A[0]))), 40)
check("digits of B", len(str(abs(A[1]))), 39)
n, v211 = abs(norm(sub(ONE, A))), 0
while n % 211 == 0:
    n //= 211; v211 += 1
check("v_211(Norm(1-a))", v211, 0)

r_pi  = (-16 * pow(3, -1, 211)) % 211          # the place where pi vanishes
r_pib = (211 - r_pi) % 211
check("root at v_pi", r_pi, 65)
red = lambda x, r: (x[0] + x[1]*r) % 211
check("a mod v_pi",      red(A, r_pi),                0)
check("a-1 mod v_pi",    red(sub(A, ONE), r_pi),      210)
check("a mod v_pibar",   red(A, r_pib),               26)
check("a-1 mod v_pibar", red(sub(A, ONE), r_pib),     25)
check("a^2-a+1 mod v_pibar", (26*26-26+1) % 211, 18)

print("(3) the field of moduli: j is irrational")
orbit = {
    "abar == a":       conj(A) == A,
    "abar == 1/a":     mul(conj(A), A) == ONE,
    "abar == 1-a":     conj(A) == sub(ONE, A),
    "abar == 1/(1-a)": mul(conj(A), sub(ONE, A)) == ONE,
    "abar == a/(a-1)": mul(conj(A), sub(A, ONE)) == A,
    "abar == (a-1)/a": mul(conj(A), A) == sub(A, ONE),
}
for k, v in orbit.items():
    check(k, v, False)
check("j is rational", any(orbit.values()), False)

print("(4) numerical inputs to the cited K-core criterion")
four = [F(488095744, 125), F(1556068, 81), F(1728), F(0)]
check("first exceptional j factorization", F(2**14 * 31**3, 5**3), four[0])
check("second exceptional j factorization", F(2**2 * 73**3, 3**4), four[1])
check("each exceptional j has nonnegative 211-valuation (v(0)=infinity)",
      all(x.denominator % 211 != 0 for x in four), True)
check("degree bound: 2*48*480 = 2^10*3^2*5", 2*48*480, 2**10*3**2*5)

print("(5) mod 7 image contains SL_2(F_7)")
def legendre(n, p):
    n %= p
    return 0 if n == 0 else (1 if pow(n, (p-1)//2, p) == 1 else -1)

data = []
for p in range(7, 6000):
    if p in (2, 5, 7, 211) or not is_prime(p) or p % 5 not in (1, 4):
        continue
    r = next((x for x in range(p) if (x*x - 5) % p == 0), None)
    if r is None:
        continue
    for root in {r, (p - r) % p}:
        av = (A[0] + A[1]*root) % p
        if av in (0, 1):
            continue
        ap = -sum(legendre(x*(x-1)*(x-av), p) for x in range(p))
        assert ap*ap <= 4*p, (p, ap)              # Hasse, exact integer test
        data.append((p, root, ap))
    if len(data) >= 121:
        break
check("good degree-one places tested", len(data), 121)
check("irreducible Frobenius witness", (11, 4, 0) in data, True)

QR7 = {1, 2, 4}
W = {}
for (p, root, ap) in data:
    t7 = ap % 7
    d  = (ap*ap - 4*p) % 7
    isQR, isNR = d in QR7, (d != 0 and d not in QR7)
    if "Borel"     not in W and isNR:              W["Borel"]     = (p, root, ap, d)
    if "splitN"    not in W and t7 != 0 and isNR:  W["splitN"]    = (p, root, ap, d)
    if "nonsplitN" not in W and t7 != 0 and isQR:  W["nonsplitN"] = (p, root, ap, d)
    if "exc" not in W and p % 7 != 0:
        tt = (ap*ap * pow(p, -1, 7)) % 7
        if tt not in (0, 1, 2, 4):                 W["exc"]       = (p, root, ap, tt)
for k in ("Borel", "splitN", "nonsplitN", "exc"):
    check(f"witness excluding {k}", W.get(k) is not None, True)
    if k in W:
        print(f"        witness = {W[k]}")

print("(6) the local profile at 211")
check("ord(q) = -v_pi(j)", 58, 2*29)
check("ord(qbar) = ord(q)/(2*l)", F(58, 14), F(29, 7))
check("gcd(105, 58) = 1", gcd(105, 58), 1)
check("q-order over selected F-place", 15*58, 870)
check("q-order over selected K-place", 105*58, 6090)
check("tame: e_b <= p-2", 105 <= 209, True)
check("d_I + a_I = |I|", F(104,105) + F(106,105), F(2))

print("(7) the local comparison (Theorem 4 of the note)")
upper = -F(29,7) + F(104,105) + 1
seed  = -F(106,105)
check("upper bound -lambda+d_I+1", upper, -F(226,105))
check("hull of the seed",          seed,  -F(106,105))
check("margin",                    seed - upper, F(8,7))

print("(7b) the margin in closed form: lambda = j^2 * s  (Thm 1.10 Step (v))")
S29 = F(29,7)                      # s = ord_211(qbar)
for j, want in ((1,F(8,7)), (2,F(88,7)), (3,F(226,7))):
    check(f"j={j}: margin = j^2*s-(j+2)", j*j*S29 - (j+2), want)
# Rational cancellation checks, not assertions of realizable local fields.
# A source-compatible field profile additionally requires e_i <= p-2 and
# e_distinguished * lambda integral; the [3,1,11] test only checks algebra.
for (j, es) in ((1,[1,105]), (1,[1,7]), (2,[105,1,105]), (2,[3,1,11])):
    S  = sum(F(1,e) for e in es)
    dI = len(es) - S
    lam = j*j*S29
    check(f"  e={es}: margin independent of e", (-S) - (-lam + dI + 1), j*j*S29 - (j+2))
check("j=2 upper bound -lambda+d_I+1 for t=(b,g,b)",
      -F(116,7) + F(208,105) + 1, -F(1427,105))
check("j=2 seed", -F(107,105), -F(107,105))

print("(7c) finite residue checks for the nonsplit-selection obstruction")
# a = A - sqrt5 with A = 2 mod 5, 19: if both places over a split p were bad then
# A-s, A+s in {0,1}, forcing 2A = 1 and 4s^2 = 1, hence p = 19 and A = 10 mod 19.
p19 = 19
check("both-bad forces 2A = 1 mod 19, i.e. A = 10",
      [A for A in range(p19) if (2*A - 1) % p19 == 0], [10])
check("  and 4s^2 = 1 has solutions that square to 5 there",
      sorted(x for x in range(p19) if (4*x*x-1) % p19 == 0 and (x*x-5) % p19 == 0),
      sorted(x for x in range(p19) if (4*x*x-1) % p19 == 0))
check("excluded by the congruence A = 2 mod 19", 2 % p19 != 10 % p19, True)
import math as _m
def _mul(x, y): return (x[0]*y[0] + 5*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def _pow(x, n):
    r = (1, 0)
    for _ in range(n): r = _mul(r, x)
    return r
_A, _B = _pow((16, 3), 29)
check("gcd(A,B) for a = pi^29",   _m.gcd(_A, _B),     1)
check("gcd(A-1,B) for a = pi^29", _m.gcd(_A - 1, _B), 3)

print("(7d) the mechanism: two different tuple-dependences (Thm 1.10 Step (v))")
# upper: lambda is set by the DISTINGUISHED slot alone -> weight 1/2
upper = F(1,3)*sum(F(1,2)*F(j*j,7) for j in (1,2,3))
# lower: N-dependence survives only at the all-bad tuple -> weight 2^-(j+1)
lower = F(1,3)*sum(F(1,2**(j+1))*F(j*j,7) for j in (1,2,3))
check("upper-bound coefficient of N (weight 1/2)", upper, F(1,3))
check("  and it equals the coefficient of -N in B2", upper, F(1,3))
check("lower-bound coefficient of N (weight 2^-(j+1))", lower, F(1,16))
check("the two differ", upper != lower, True)
check("growth of the discrepancy", upper - lower, F(13,48))

print("(8) the averaged comparison")
baseline = F(1,3)*sum(F(53*(j+1), 105)              for j in (1,2,3))
slope    = F(1,3)*sum(F(1, 2**(j+1))*F(j*j, 7)      for j in (1,2,3))
corr     = {j: F(7 - (j*j) % 7, 7) for j in (1,2,3)}
rounding = F(1,3)*sum(F(1, 2**(j+1))*corr[j]        for j in (1,2,3))
check("baseline",       baseline, F(53,35))
check("slope",          slope,    F(1,16))
check("ceil remainders", [corr[j] for j in (1,2,3)], [F(6,7), F(3,7), F(5,7)])
check("rounding",       rounding, F(5,48))
Bconst = 2*(F(11,7)*F(52,105) + F(4,7))
check("B_2 constant",   Bconst,   F(1984,735))
check("B_2 slope in N", 2*F(1,6),  F(1,3))
check("B_2 s-coeff",    2*F(20,3), F(40,3))

N = 211
check("211 = 1 mod 105", N % 105, 1)
hlower = -baseline-F(N,16)-F(5,48)
check("exact sharp lower bound", hlower, -F(12437,840))
# exp(16) exceeds the positive series truncated at degree 25.
exp16_lower = sum(F(16**k, factorial(k)) for k in range(26))
check("log(7741440) < 16: exp series lower bound", exp16_lower > 7741440, True)
# For exp(5), terms after degree 20 have consecutive ratio <=5/22.
exp5_upper = sum(F(5**k, factorial(k)) for k in range(21)) + F(5**21, factorial(21))/(1-F(5,22))
check("log(211) > 5: exp series upper bound", exp5_upper < 211, True)
check("displayed integer bound for exp(16)", 65**16 > 7741440*24**16, True)
check("displayed integer bound for exp(5)", 11**5 < 211*4**5, True)
B2_upper = Bconst-F(N,3)+F(40,3)*F(16,5)
check("exact rational upper bound for B2/log211", B2_upper, -F(6117,245))
check("weak rigorous margin > 7438/735", hlower-F(1,24)-B2_upper, F(7438,735))
check("sharp rigorous margin > 59749/5880", hlower-B2_upper, F(59749,5880))
L  = Decimal(7741440).ln() / Decimal(211).ln()
h  = Decimal(-baseline.numerator)/Decimal(baseline.denominator) - Decimal(N)/16 - Decimal(5)/48
B2 = Decimal(Bconst.numerator)/Decimal(Bconst.denominator) - Decimal(N)/3 + (Decimal(40)/3)*L
diff_sharp = h - B2
diff_weak  = h - Decimal(2)/48 - B2
print(f"  [--] log(7741440)/log(211) = {L:.10f}")
print(f"  [approx] sharp lower bound for h/log211: {h:.10f}")
print(f"  [approx] B2/log211: {B2:.10f}")
print(f"  [approx] sharp lower bound minus B2/log211: {diff_sharp:.10f}")
print(f"  [approx] weak lower bound minus B2/log211: {diff_weak:.10f}")
check("difference of the two exact bounds is 1/24", F(7,48)-F(5,48), F(1,24))

print()
if FAIL:
    print(f"FAIL: {len(FAIL)} check(s) failed: {FAIL}")
    sys.exit(1)
print("OK: displayed arithmetic and rational comparison certificates PASS")
print("SA and geometric constructions require the separate mathematical arguments.")
