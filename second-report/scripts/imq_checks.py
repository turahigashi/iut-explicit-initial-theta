#!/usr/bin/env python3
"""Exact arithmetic for the Q(i) initial Theta-datum (second report, section 3).

L = F_mod = Q(i),  pi = 10 + 3i  (Norm 109, split),  a = pi^29,
E_0 : y^2 = x(x-1)(x-a),  ell = 7,  F = L(E_0[15]),  K = F(E_0[7]).

Standard library only.  Every number below is an exact integer or rational.
"""
from fractions import Fraction as Q
import math, sys

# ---------- Z[i] ----------
def zmul(x, y): return (x[0]*y[0] - x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def zpow(x, n):
    r = (1, 0)
    while n:
        if n & 1: r = zmul(r, x)
        x = zmul(x, x); n >>= 1
    return r
def zconj(x): return (x[0], -x[1])
def znorm(x): return x[0]*x[0] + x[1]*x[1]
def zdiv(x, y):
    """exact division in Z[i]; raises if not exact"""
    n = znorm(y); num = zmul(x, zconj(y))
    assert num[0] % n == 0 and num[1] % n == 0, "not divisible"
    return (num[0]//n, num[1]//n)
def zdivides(x, y):
    n = znorm(x); num = zmul(y, zconj(x))
    return num[0] % n == 0 and num[1] % n == 0
def zval(x, p):
    """v_p(x) for p a prime element of Z[i]"""
    k = 0
    while x != (0, 0) and zdivides(p, x):
        x = zdiv(x, p); k += 1
    return k

PI   = (10, 3)
PBAR = zconj(PI)
P    = 109
N    = 29
ELL  = 7
a    = zpow(PI, N)
one  = (1, 0)
oma  = (one[0] - a[0], one[1] - a[1])          # 1 - a

fails = []
def check(ok, label, extra=""):
    print(f"  {'OK ' if ok else 'FAIL'}  {label}{('   ' + extra) if extra else ''}")
    if not ok: fails.append(label)

print("=== the datum ===")
print(f"  pi = {PI[0]} + {PI[1]}i,  Norm(pi) = {znorm(PI)}")
check(znorm(PI) == P, "Norm(pi) = 109")
check(P % 4 == 1, "109 = 1 mod 4, so 109 splits in Q(i)")
check(zmul(PI, PBAR) == (P, 0), "pi * conj(pi) = 109")

print("\n=== (a) the field of moduli: six Legendre orbit comparisons ===")
# lambda -> {l, 1/l, 1-l, 1/(1-l), l/(l-1), (l-1)/l}; j is rational iff conj(a)
# lies in the orbit of a.  Work with exact equalities in Z[i] cleared of denominators.
ab   = zconj(a)
am1  = (a[0] - 1, a[1])
tests = [
    ("conj(a) = a",              ab == a),
    ("conj(a)*a = 1",            zmul(ab, a) == one),
    ("conj(a) = 1-a",            ab == oma),
    ("conj(a)*(1-a) = 1",        zmul(ab, oma) == one),
    ("conj(a)*(a-1) = a",        zmul(ab, am1) == a),
    ("conj(a)*a = a-1",          zmul(ab, a) == am1),
]
for label, holds in tests:
    check(not holds, f"{label:24s} fails (as required)")
check(not any(h for _, h in tests), "j(E_0) is not rational, so F_mod = Q(i)")

# exact j over Q(i): j = 256 (l^2-l+1)^3 / (l^2 (l-1)^2)
num = zpow((a[0]*a[0] - a[1]*a[1] - a[0] + 1, 2*a[0]*a[1] - a[1]), 3)
num = (256*num[0], 256*num[1])
den = zmul(zmul(a, a), zmul(am1, am1))
# imaginary part of num/den = Im(num * conj(den)) / Norm(den)
imnum = zmul(num, zconj(den))[1]
check(imnum != 0, "Im(j) != 0",
      f"|Im numerator| has {len(str(abs(imnum)))} digits, denominator {len(str(znorm(den)))}")

print("\n=== the mixed profile above 109 ===")
vals = [("ord_pi(a)", zval(a, PI), N), ("ord_pibar(a)", zval(a, PBAR), 0),
        ("ord_pi(1-a)", zval(oma, PI), 0), ("ord_pibar(1-a)", zval(oma, PBAR), 0)]
for label, got, want in vals:
    check(got == want, f"{label} = {want}", f"got {got}")

print("\n=== (b) norms ===")
Na, Noma = znorm(a), znorm(oma)
check(Na == P**N, f"Norm(a) = 109^{N}")
C = Noma
small = []
for q, e in [(2, 1), (3, 2), (5, 1), (21577, 1)]:
    k = 0
    while C % q == 0: C //= q; k += 1
    small.append((q, k)); check(k == e, f"v_{q}(Norm(1-a)) = {e}", f"got {k}")
print(f"  Norm(1-a) has {len(str(Noma))} digits; cofactor C has {len(str(C))} digits")
check(Noma % ELL != 0, "7 does not divide Norm(1-a)")
# integer seventh root of C -> the sieve bound
lo, hi = 1, 10**9
while lo < hi:
    m = (lo + hi + 1)//2
    if m**7 <= C: lo = m
    else: hi = m - 1
print(f"  floor(C^(1/7)) = {lo:,}   <- the exhaustive bound used by imq_sieve7.cpp")
check(lo == 34869670, "sieve bound = 34,869,670")
print(f"  C = {C}")

print("\n=== (c) orders at the selected places ===")
check((2*N) % ELL != 0, f"7 does not divide the base Tate order 2*{N} = {2*N}")
for q, k in small:
    if q == 2: continue                      # 2 is not selected
    check((2*k) % ELL != 0, f"7 does not divide 2*v_{q} = {2*k}")

print("\n=== (c) the mod-7 image ===")
def mul7(A, B):
    return ((A[0]*B[0]+A[1]*B[2]) % 7, (A[0]*B[1]+A[1]*B[3]) % 7,
            (A[2]*B[0]+A[3]*B[2]) % 7, (A[2]*B[1]+A[3]*B[3]) % 7)
def group(gs):
    I = (1, 0, 0, 1); S = {I}; fr = [I]
    while fr:
        nf = []
        for x in fr:
            for g in gs:
                y = mul7(x, g)
                if y not in S: S.add(y); nf.append(y)
        fr = nf
    return S
def legendre(x, q):
    x %= q
    return 0 if x == 0 else (1 if pow(x, (q-1)//2, q) == 1 else -1)
def trace_at(q):
    """a_q for y^2 = x(x-1)(x-a) at a degree-one place of Q(i) over q = 1 mod 4"""
    r = next(t for t in range(q) if (t*t + 1) % q == 0)      # i mod q
    am = (a[0] + a[1]*r) % q
    pts = sum(1 + legendre(x*(x-1)*(x-am), q) for x in range(q))
    return q + 1 - (pts + 1)

# --- the actual arithmetic checks: traces and irreducibility ---------------------
# What follows about the mod-7 image is split in two, because an earlier version ran
# them together and the second half was RETRACTED as an argument.  The actual Frobenius
# g is only CONJUGATE to the companion matrix C of its characteristic polynomial, and
# the basis putting inertia in the form T need not be the basis putting g in the form
# C.  So a closure computation on one chosen pair proves nothing about the actual image.
# The traces and the irreducibility below ARE actual arithmetic; the closure below them
# is an auxiliary check on a representative.  The image argument is basis-free and lives
# in lean/BasisFreeImage.lean (external review, 2026-09-07).
T = (1, 1, 0, 1)                                            # Tate transvection
witnesses = []
for q in [13, 17, 37, 41, 53, 61]:
    tr = trace_at(q)
    disc = (tr*tr - 4*q) % 7
    irred = disc != 0 and pow(disc, 3, 7) != 1              # nonsquare mod 7
    Cm = (0, (-q) % 7, 1, tr % 7)                           # companion of X^2 - tr X + q
    d = (Cm[0]*Cm[3] - Cm[1]*Cm[2]) % 7; di = pow(d, -1, 7)
    Ci = ((Cm[3]*di) % 7, (-Cm[1]*di) % 7, (-Cm[2]*di) % 7, (Cm[0]*di) % 7)
    T2 = mul7(mul7(Cm, T), Ci)
    n = len(group([T, T2]))
    witnesses.append((q, tr, disc, irred, n))
    check(irred, f"q={q:3d}: trace {tr:4d}, disc {disc} nonsquare mod 7  [actual arithmetic]")
    check(n == 336, f"q={q:3d}: AUXILIARY, companion representative: <T, C T C^-1> has "
                    f"order {n}")
check(all(w[3] for w in witnesses),
      f"all {len(witnesses)} witnesses have irreducible char. poly mod 7  [actual]")
check(all(w[4] == 336 for w in witnesses),
      "AUXILIARY ONLY: for each witness the CHOSEN COMPANION representative C gives "
      "<T, C T C^-1> = SL_2(F_7).  This is NOT a proof about the actual image: g is "
      "only conjugate to C, and the conjugating basis need not fix T.  The basis-free "
      "argument is in lean/BasisFreeImage.lean (12 theorems).")
G15 = 23040
check(G15 == 2**9 * 3**2 * 5, "|GL_2(Z/15)| = 23040 = 2^9 3^2 5")
check(G15 % ELL != 0, "7 does not divide 23040, so [F:F_mod] is prime to 7")
check(168 % ELL == 0, "7 divides |PSL_2(F_7)| = 168")

print("\n=== local invariants ===")
ordq = 2*N
check(ordq == 58, "ord_109(q) = 2*29 = 58")
eb = 15*ELL
check(math.gcd(ordq, eb) == 1, f"gcd(58, {eb}) = 1, so e_b = {eb} exactly")
check(eb <= P - 2, f"e_b = {eb} <= {P-2} = p-2, so 109 is tamely ramified")
qbb = Q(ordq, 2*ELL)
check(qbb == Q(29, 7), "ord_109(qbb_b) = 58/14 = 29/7", f"= {qbb}")
# Nothing further is computed here.  The report does compute ordinary normalised
# log-volumes, coefficients, and ratios of terms inside the explicit bounds; what it
# does not compute is the hull of the union of the possible images of the actual
# Theta-pilot, or the comparison of the two sides of [IUT3, Cor. 3.12].  See the Scope
# section.  (An earlier version of this comment denied the former as well.)

print("\n" + ("=" * 46))
print(f"RESULT: {'PASS - all checks hold' if not fails else 'FAIL: ' + '; '.join(fails)}")
sys.exit(1 if fails else 0)
