#!/usr/bin/env python3
"""Arithmetic checks for the curve y^2 = x(x-1)(x-a), a = (41+26i)^472, over Q(i),
at the fourteen levels 89, ..., 157.

Gaussian integers are pairs (x, y) standing for x + y*i.  Only the standard library is
used.  Every check is an assertion; the program exits with status 1 at the first
failure and prints the values it has checked.  The order bound (part 7) does not use a
factorization of 1 - a: it bounds the valuation at every place of odd residue
characteristic through the cyclotomic factor Phi_d(pi) with d the order of pi modulo
the place, and tests directly every place that the bound does not exclude.
"""

import math
import sys
import time

sys.set_int_max_str_digits(0)
from decimal import Decimal, getcontext
from fractions import Fraction

LEVELS = [89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157]
PI = (41, 26)
EXP = 472
P = 2357
WITNESSES = [(13, 5), (17, 13), (29, 12), (97, 75)]   # (q, r) with r^2 = -1 mod q

# The numbers printed in the report, compared with the computed ones below.
PRINTED = {
    "imj_digits": 7953,
    "j_mod_29": {12: (20, 16), 17: (23, 18)},               # i -> (a mod q, j mod q)
    "table1": {1: (1, 4, 1), 2: (1, 4, 1), 4: (2, 7, 1), 8: (4, 14, 1),
               59: (58, 196, 157), 118: (58, 196, 157), 236: (116, 392, 24856),
               472: (232, 783, 617831325)},                  # d -> (deg, digits of N, R_d)
    "tested_primes": 138731,
    "tested_places": 277462,
    "hits": {1181: 1, 21713: 1, 2876369: 1, 6188393: 1},    # p -> ord(1-a) at the place dividing 1-a
    "table2": [(13, 5, 3, 16, -2, -48, [89, 101, 107, 113, 131, 137, 149]),
               (17, 13, 16, 16, 2, -64, [103, 107, 127, 131, 139, 151]),
               (29, 12, 20, 32, -2, -112, [89, 97, 101, 103, 131, 139, 157]),
               (97, 75, 75, 96, 2, -384, [89, 109, 113, 137, 139, 157])],
    "logq": "7324.751610927",
    "sqrt_logq": "85.584762726",
    "C1_upper": "2.2251e+10",
    "direct_search_exponent": "17.9",
}

failures = 0


def check(cond, label):
    global failures
    if not cond:
        failures += 1
        print("FAIL:", label)
        sys.exit(1)
    print("ok  ", label)


# ---------------------------------------------------------------- Gaussian integers

def gmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def gsub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def gpow(a, n):
    result, base = (1, 0), a
    while n:
        if n & 1:
            result = gmul(result, base)
        base = gmul(base, base)
        n >>= 1
    return result


def gnorm(a):
    return a[0] * a[0] + a[1] * a[1]


def gconj(a):
    return (a[0], -a[1])


def gdiv_exact(a, b):
    """a / b in Z[i]; raises if b does not divide a."""
    num = gmul(a, gconj(b))
    n = gnorm(b)
    if num[0] % n or num[1] % n:
        raise ArithmeticError("not divisible")
    return (num[0] // n, num[1] // n)


def gpow_mod(a, n, m):
    """a^n in (Z/m)[i]."""
    result, base = (1, 0), (a[0] % m, a[1] % m)
    while n:
        if n & 1:
            result = ((result[0] * base[0] - result[1] * base[1]) % m,
                      (result[0] * base[1] + result[1] * base[0]) % m)
        base = ((base[0] * base[0] - base[1] * base[1]) % m,
                (2 * base[0] * base[1]) % m)
        n >>= 1
    return result


# ---------------------------------------------------------------- rational integers

SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]


def is_prime(n):
    """Deterministic Miller-Rabin for n < 3.3e24 (bases: the first 13 primes)."""
    if n < 2:
        return False
    for p in SMALL_PRIMES:
        if n % p == 0:
            return n == p
    if n >= 3317044064679887385961981:
        raise ValueError("outside the deterministic range")
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for b in SMALL_PRIMES:
        x = pow(b, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, n + 1, i)))
    return [i for i in range(n + 1) if sieve[i]]


def vp(n, p):
    if n == 0:
        raise ValueError("valuation of 0")
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def iroot(n, k):
    """floor(n^(1/k)) for n >= 0."""
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + k - 1) // k)
    while True:
        y = ((k - 1) * x + n // x ** (k - 1)) // k
        if y >= x:
            break
        x = y
    while x ** k > n:
        x -= 1
    while (x + 1) ** k <= n:
        x += 1
    return x


def sqrt_minus_one(p):
    """r with r^2 = -1 mod p, for a prime p = 1 mod 4."""
    for g in range(2, p):
        if pow(g, (p - 1) // 2, p) == p - 1:
            r = pow(g, (p - 1) // 4, p)
            assert r * r % p == p - 1
            return r
    raise ValueError(p)


def hensel_sqrt_minus_one(r, p, m):
    """Lift r (r^2 = -1 mod p, p odd) to a root of x^2 + 1 modulo p^m."""
    mod = p
    while mod < p ** m:
        mod = min(mod * mod, p ** m)
        r = (r - (r * r + 1) * pow(2 * r, -1, mod)) % mod
    assert (r * r + 1) % (p ** m) == 0
    return r


def legendre(x, p):
    x %= p
    if x == 0:
        return 0
    return 1 if pow(x, (p - 1) // 2, p) == 1 else -1


def mobius(n):
    result, m, f = 1, n, 2
    while f * f <= m:
        if m % f == 0:
            m //= f
            if m % f == 0:
                return 0
            result = -result
        f += 1
    if m > 1:
        result = -result
    return result


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


# ================================================================ the checks

t0 = time.time()
print("D2357: a = (41+26i)^472 over Q(i), levels", LEVELS)

# 1. the prime 2357 -----------------------------------------------------------
check(gnorm(PI) == P and is_prime(P) and P % 4 == 1,
      "N(pi) = 2357, prime, = 1 mod 4 (so 2357 splits in Q(i))")
assoc = [PI, gmul(PI, (0, 1)), gmul(PI, (-1, 0)), gmul(PI, (0, -1))]
check(gconj(PI) not in assoc, "conj(pi) is not an associate of pi")
for l in LEVELS:
    assert is_prime(l)
check(all(is_prime(l) for l in LEVELS) and LEVELS == sorted(set(LEVELS)), "the 14 levels are primes")

# 2. a = pi^472 and its reductions --------------------------------------------
a = gpow(PI, EXP)
one_minus_a = gsub((1, 0), a)
check(len(str(abs(a[0]))) == 796 and len(str(abs(a[1]))) == 796,
      "both coordinates of a have 796 digits")
check(gnorm(a) == P ** EXP, "N(a) = 2357^472")
# reductions of the big integer against direct modular exponentiation
cnt = 0
for p in primes_upto(3000):
    if p == 2 or p == P:
        continue
    if p % 4 == 1:
        r = sqrt_minus_one(p)
        for rr in (r, p - r):
            assert (a[0] + rr * a[1]) % p == pow(PI[0] + PI[1] * rr, EXP, p)
    else:
        assert (a[0] % p, a[1] % p) == gpow_mod(PI, EXP, p)
    cnt += 1
check(True, "a mod p agrees with (41+26r)^472 mod p, resp. pi^472 in F_p[i], for the %d odd primes p < 3000, p != 2357" % cnt)

# 3. the field of moduli --------------------------------------------------------
# j = 256 (a^2 - a + 1)^3 / (a^2 (a-1)^2)
asq = gmul(a, a)
c = (asq[0] - a[0] + 1, asq[1] - a[1])            # a^2 - a + 1
A = gmul((256, 0), gmul(c, gmul(c, c)))          # numerator
am1 = gsub(a, (1, 0))
B = gmul(asq, gmul(am1, am1))                     # denominator
imj_num = gmul(A, gconj(B))[1]                    # Im(j) = imj_num / N(B)
g = math.gcd(imj_num, gnorm(B))
check(imj_num != 0 and len(str(abs(imj_num // g))) == PRINTED["imj_digits"],
      "Im j != 0 exactly (Im j = %d-digit integer / %d-digit integer in lowest terms)"
      % (len(str(abs(imj_num // g))), len(str(gnorm(B) // g))))
for rr, (lam_exp, j_exp) in PRINTED["j_mod_29"].items():
    lam = pow(PI[0] + PI[1] * rr, EXP, 29)
    jj = 256 * pow(lam * lam - lam + 1, 3, 29) * pow(lam * lam * (lam - 1) ** 2, -1, 29) % 29
    assert (lam, jj) == (lam_exp, j_exp)
check(True, "at the places above 29 (i = 12, 17): a = 20, 23 and j = 16, 18 mod 29")
# the same by reduction: if j were rational, its images at the two places above a split
# prime p (prime to the denominator) would coincide
found = []
for p in primes_upto(400):
    if p % 4 != 1 or p == P:
        continue
    r = sqrt_minus_one(p)
    vals = []
    for rr in (r, p - r):
        lam = pow(PI[0] + PI[1] * rr, EXP, p)
        den = lam * lam * (lam - 1) * (lam - 1) % p
        if den == 0:
            vals = None
            break
        vals.append(256 * pow(lam * lam - lam + 1, 3, p) * pow(den, -1, p) % p)
    if vals is not None and vals[0] != vals[1]:
        found.append(p)
check(len(found) > 0, "j has different images at the two places above the split primes %s, so j is not rational"
      % found[:6])
print("note  (not a computation) the field of moduli is Q(j), so F_mod = Q(i); j is not real, so it is none of the "
      "four rational invariants of [MFHMP, Prop. 2.1]")

# 4. the places above 2357 ---------------------------------------------------------
r_pi = (-PI[0] * pow(PI[1], -1, P)) % P           # i mod pi
r_pibar = (PI[0] * pow(PI[1], -1, P)) % P         # i mod conj(pi)
check((r_pi * r_pi + 1) % P == 0 and (r_pibar * r_pibar + 1) % P == 0, "residue maps at pi and conj(pi)")
check((PI[0] + PI[1] * r_pi) % P == 0 and (PI[0] + PI[1] * r_pibar) % P == 82,
      "pi -> 0 at the place pi and pi -> 82 at the place conj(pi)")
check((one_minus_a[0] + r_pi * one_minus_a[1]) % P == 1, "1 - a = 1 at the place pi, so ord_pi(1-a) = 0")
red = (one_minus_a[0] + r_pibar * one_minus_a[1]) % P
check(red == (1 - pow(82, EXP, P)) % P and red != 0,
      "1 - a = 1 - 82^472 = %d != 0 at conj(pi), so ord_conj(pi)(1-a) = 0" % red)
check(pow(82, 4, P) == 202 and math.gcd(EXP, P - 1) == 4,
      "(82^4 = 202 != 1 mod 2357 and gcd(472, 2356) = 4, which is why 82^472 != 1)")
check(2 * EXP == 944 == 2 ** 4 * 59, "Tate order at pi: ord_pi(Delta) = 2*472 = 944 = 2^4 * 59")

# 5. Norm(1 - a) --------------------------------------------------------------------
n = gnorm(one_minus_a)
check(len(str(n)) == 1592, "Norm(1-a) has 1592 digits")
check((vp(n, 2), vp(n, 3), vp(n, 5)) == (9, 2, 2), "v_2, v_3, v_5 of Norm(1-a) = 9, 2, 2")
G = math.gcd(one_minus_a[0], one_minus_a[1])
check(G == 240, "gcd(Re(1-a), Im(1-a)) = 240 = 2^4 * 3 * 5")

# 6. the integer facts at each level -------------------------------------------------------
for l in LEVELS:
    z = gsub((1, 0), gpow_mod(PI, EXP, l))
    nmod = (z[0] * z[0] + z[1] * z[1]) % l
    assert nmod == n % l
    assert l != P and 944 % l and 23040 % l and nmod != 0
check(True, "for every level: l != 2357, l does not divide 944, 23040 or Norm(1-a) "
      "(Norm(1-a) mod l recomputed in F_l[i])")
check(23040 == 48 * 480 == 2 ** 9 * 3 ** 2 * 5, "|GL_2(Z/15)| = |GL_2(F_3)| |GL_2(F_5)| = 48 * 480 = 23040 = 2^9 3^2 5")

# 7. the order bound: ord_p(1 - a) <= 88 at every place p of odd residue characteristic -----
D = divisors(EXP)
pe_minus_1 = {e: gsub(gpow(PI, e), (1, 0)) for e in D}
phi = {}
for d in D:
    num, den = (1, 0), (1, 0)
    for e in divisors(d):
        mu = mobius(d // e)
        if mu == 1:
            num = gmul(num, pe_minus_1[e])
        elif mu == -1:
            den = gmul(den, pe_minus_1[e])
    phi[d] = gdiv_exact(num, den)
prod = (1, 0)
for d in D:
    prod = gmul(prod, phi[d])
check(prod == gsub(a, (1, 0)), "prod over d | 472 of Phi_d(pi) = pi^472 - 1 (each Phi_d(pi) by exact Moebius division)")

# Inert p: the place is (p), and ord_(p)(1-a) = min(v_p(Re), v_p(Im)) <= v_p(240).
check(vp(G, 3) == 1 and G % 7 and G % 59,
      "inert primes: only 3 divides gcd(Re, Im) = 240, to the first power; in particular 59 does not divide 1-a")

print("      d   deg  digits of N(Phi_d(pi))   R_d = floor(N^(1/89))")
bound = {}
table1 = {}
for d in D:
    Nd = gnorm(phi[d])
    bound[d] = iroot(Nd, 89)
    deg = len([k for k in range(1, d + 1) if math.gcd(k, d) == 1])
    table1[d] = (deg, len(str(Nd)), bound[d])
    print("   %4d  %4d  %6d                 %d" % (d, deg, len(str(Nd)), bound[d]))
check(table1 == PRINTED["table1"], "Table 1 (degrees, digits of the norms, R_d) as printed")

# A split place q above an odd prime p != 59 with ord_q(pi) = d satisfies, by
# x^m - 1 = (x - 1)(1 + x + ... + x^(m-1)) with the second factor = m (a unit) mod q,
#   ord_q(pi^472 - 1) = ord_q(pi^d - 1) = ord_q(Phi_d(pi)),
# so Nq^k divides N(Phi_d(pi)) with k = ord_q(1 - a); k >= 89 forces Nq = p <= R_d, and
# d | p - 1 because pi has order d in (Z[i]/q)^*.  Every such p is tested below.
U, W = one_minus_a
tested_primes = 0
tested_places = 0
tested_set = set()
hits = []
for d in D:
    R = bound[d]
    if R < 5:
        continue
    step = d if d % 4 == 0 else 4 * d // math.gcd(4, d)      # p = 1 mod 4 and mod d
    k = 1
    while step * k + 1 <= R:
        p = step * k + 1
        k += 1
        if not is_prime(p):
            continue
        tested_primes += 1
        tested_set.add(p)
        r = sqrt_minus_one(p)
        for rr in (r, p - r):
            tested_places += 1
            x = (PI[0] + PI[1] * rr) % p
            if pow(x, EXP, p) != 1:
                continue
            # the place divides 1 - a: compute the valuation with the root lifted mod p^90
            rl = hensel_sqrt_minus_one(rr, p, 90)
            val = (U + rl * W) % (p ** 90)
            v = 90 if val == 0 else vp(val, p)
            # cross-check modulo p^2 by exponentiation
            r2 = rl % (p * p)
            assert ((pow(PI[0] + PI[1] * r2, EXP, p * p) - 1) % (p * p) == 0) == (v >= 2)
            hits.append((d, p, rr, v))
distinct_primes = len({(p) for p in tested_set})
distinct_hits = sorted({(h[1], h[2], h[3]) for h in hits})
print("      tested %d primes (%d distinct, %d places); places dividing 1-a among them:"
      % (tested_primes, distinct_primes, 2 * distinct_primes))
for p, rr, v in distinct_hits:
    print("        p=%d  i=%d  ord(1-a)=%d" % (p, rr, v))
check(distinct_primes == PRINTED["tested_primes"] and 2 * distinct_primes == PRINTED["tested_places"]
      and {p: v for p, rr, v in distinct_hits} == PRINTED["hits"] and len(distinct_hits) == len(PRINTED["hits"]),
      "138,731 primes and 277,462 places tested; exactly the four places printed divide 1-a, each once")
check(all(h[3] <= 88 for h in hits), "every tested place has ord(1-a) <= 88 (largest found: %d)"
      % max([h[3] for h in hits] + [0]))
print("note  (not a computation) with Lemma 3.1 and the case analysis in the proof of Proposition 3.2(d), this gives "
      "ord_p(1-a) <= 88 at every place p of Q(i) of odd residue characteristic")

# 8. Frobenius witnesses ---------------------------------------------------------------
covered = set()
rows = []
for q, r in WITNESSES:
    assert (r * r + 1) % q == 0
    lam = pow(PI[0] + PI[1] * r, EXP, q)
    assert lam == (a[0] + r * a[1]) % q
    assert lam not in (0, 1)
    s = sum(legendre(x * (x - 1) * (x - lam), q) for x in range(q))
    npts = q + 1 + s
    aq = q + 1 - npts
    disc = aq * aq - 4 * q
    cov = [l for l in LEVELS if l != q and disc % l and legendre(disc, l) == -1]
    covered |= set(cov)
    rows.append((q, r, lam, npts, aq, disc, cov))
    print("      q=%-3d i=%-3d a=%-3d #E=%-4d a_q=%-3d a_q^2-4q=%-5d covers %s" % (q, r, lam, npts, aq, disc, cov))
check(rows == PRINTED["table2"], "Table 2 as printed")
check(covered == set(LEVELS), "every level has a witness at which X^2 - a_q X + q is irreducible mod l")
only109 = [row[0] for row in rows if 109 in row[6]]
check(only109 == [97], "l = 109 is covered only by the place above 97")
check(all((legendre(-48, l) == -1) == (l % 3 == 2) for l in LEVELS)
      and all((legendre(-64, l) == -1) == (l % 4 == 3) for l in LEVELS)
      and all((legendre(-112, l) == -1) == (legendre(l, 7) == -1) for l in LEVELS),
      "rows 13, 17, 29 are the congruence conditions l = 2 mod 3, l = 3 mod 4, (l/7) = -1")
# the other places above 17 and 97, for the record
lam17 = pow(PI[0] + PI[1] * 4, EXP, 17)
lam97 = pow(PI[0] + PI[1] * 22, EXP, 97)
s97 = sum(legendre(x * (x - 1) * (x - lam97), 97) for x in range(97))
check(lam17 == 1 and 97 + 1 + s97 == 112,
      "other places: above 17 (i = 4) a = 1 (a selected bad place); above 97 (i = 22) #E = 112, a_q = -14")

# 9. the levels and condition (C1) of [IUT IV, Cor. 2.2(ii)] -------------------------------
# log q^forall: normalized degree of the q-parameter divisor at all nonarchimedean places,
# = (1/2) sum_v max(0, -ord_v j) log Nv over Q(i); the place above 2 has ord j = -2.
v1i_c4 = 8      # ord_(1+i)(16), and a^2 - a + 1 is a unit there
v1i_delta = 8 + 2 * vp(n, 2)       # ord_(1+i)(16 a^2 (a-1)^2), since ord_(1+i)(1-a) = v_2(N(1-a))
check(3 * v1i_c4 - v1i_delta == -2, "ord_(1+i)(j) = 3*8 - 26 = -2")
getcontext().prec = 60
H = (Decimal(EXP) * Decimal(P).ln() + Decimal(n).ln() - Decimal(vp(n, 2)) * Decimal(2).ln()
     + Decimal(2).ln())
sqrtH = H.sqrt()
print("      log q^forall = %s" % str(H)[:22])
print("      sqrt          = %s" % str(sqrtH)[:22])
check(str(H).startswith(PRINTED["logq"]) and str(sqrtH).startswith(PRINTED["sqrt_logq"]),
      "log q^forall = 7324.751610927..., its square root = 85.584762726...")
window = [l for l in primes_upto(160) if Decimal(l) >= sqrtH and Fraction(l) < Fraction(EXP, 3)]
check(window == LEVELS, "the 14 levels are exactly the primes in [sqrt(log q^forall), 472/3)")
delta = 2 ** 12 * 3 ** 3 * 5 * 2
upper = 10 * delta * sqrtH * (2 * delta * H).ln()
print("      (C1) upper bound at d = 2: %.4e" % float(upper))
check("%.4e" % float(upper) == PRINTED["C1_upper"], "the upper bound of (C1) at d = 2 is about 2.2251e10")
check("%.1f" % (Decimal(n).log10() / 89) == PRINTED["direct_search_exponent"],
      "a direct search for 89th powers in Norm(1-a) would need primes up to about 10^17.9")
check(all(Decimal(l) >= sqrtH and Decimal(l) <= upper for l in LEVELS),
      "every level satisfies both inequalities of (C1) with d = 2")

# 10. local invariants above 2357 ----------------------------------------------------------
for l in LEVELS:
    assert math.gcd(15 * l, 944) == 1 and 15 * l % P
check(all((15 * l <= P - 2) and ((15 * l == P - 2) == (l == 157)) for l in LEVELS),
      "e_b = 15 l <= 2355 = p - 2 at every level, with equality exactly at l = 157")
check([Fraction(944, 2 * l) for l in LEVELS] == [Fraction(472, l) for l in LEVELS],
      "ord_2357 of q^(1/2l) at the bad place = 472/l")

print("all checks passed (%.1f s)" % (time.time() - t0))
