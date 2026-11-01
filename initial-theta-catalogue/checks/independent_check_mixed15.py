#!/usr/bin/env python3
"""Independent re-check of the datum D_15 of the note, written from the specification only
(certify_datum.py and certify_mixed15.py were not opened or imported).

Datum:  F0 = Q(sqrt5),  O = Z[w],  w = (1+sqrt5)/2,  l = 7,
        pi = -5932 - 919*sqrt5 = -5013 - 1838*w,  p = N(pi) = 30965819,
        a = pi^15,  E0 : y^2 = x(x-1)(x-a).

Arithmetic.  Elements of O are integer pairs (x, y) meaning x + y*w, with w^2 = w + 1,
conj(x + y w) = (x + y) - y w and N(x + y w) = x^2 + x y - y^2.  {1, w} is a Z-basis of O,
so an integer n divides an element of O iff it divides both coordinates.  A few quantities
are recomputed a second way with sympy's sqrt(5) as a cross-check of this arithmetic.

Route for claim 3 (bad share; a statement about ALL primes r, not an enumeration).
  * N(pi) = p is prime, so (pi) is a prime ideal of degree one; (a) = (pi)^15, hence v_pi is
    the only place of F0 dividing a.
  * For an odd prime r != 5, either r is inert (one place, = rO) or split (rO = P P', P != P',
    so P | x and P' | x  <=>  rO | x).  In both cases "every place above r divides a - 1"
    <=> r divides a - 1 in O <=> r divides the content gcd(x, y) of a - 1 = x + y w.
    So: content(a - 1) has no prime factor outside {2, 7}  =>  no inert prime outside {2, 7}
    has its (degree-two) place dividing a - 1, and no split prime has both places dividing a - 1.
  * 5 is ramified with the single degree-one place (sqrt5); it divides a - 1 iff 5 | N(a - 1).
  * Above p: v_pi divides a (and not a - 1, since a - 1 = -1 mod v_pi); the other place divides
    neither a nor a - 1 because a mod it is not 0 or 1.
  Together: for every prime r not in {2, 7}, the places above r dividing a(a - 1) carry at most
  half of the degree [F0:Q] = 2 (at most one place, and that place is split of degree one).

Route for claim 6 (Tate orders prime to 7; also for ALL primes r).
  * By claim 3, for r not in {2, 7} at most one place w above r divides a - 1 and it has degree
    one, so ord_w(a - 1) = v_r(N(a - 1)).  It therefore suffices that v_r(N(a - 1)) is never a
    positive multiple of 7; we prove the stronger v_r(N(a - 1)) <= 6 except where checked exactly.
  * pi^15 - 1 = prod_{d | 15} Phi_d(pi) (checked exactly), so N(a - 1) = prod_d N_d with
    N_d = N(Phi_d(pi)).  All six pairwise gcd(N_d, N_e) are computed and factored; a prime r not
    dividing any of them divides at most one N_d, and then v_r(N(a - 1)) = v_r(N_d).
  * If v_r(N_d) >= 7 then r^7 <= |N_d|, i.e. r <= B_d = floor(|N_d|^(1/7)).  For each block every
    prime r <= B_d is tested, by two different methods over one numpy segmented sieve:
      (A) vectorised Horner remainders of N_d (base 2^32 limbs) modulo all primes of a segment;
      (B) gcd(N_d, product of all primes <= B_d), the product reduced mod N_d chunk by chunk with
          Python integers, then the gcd factored.
    The two divisor sets must agree, and the sieve's prime count must equal sympy.primepi(B_d).
    Every divisor found gets its exact multiplicity.
  * Primes dividing two blocks (only possible at the same place for r | 15, by the resultant of
    cyclotomic polynomials, or at two places, which claim 3 excludes outside {2, 7}) and the primes
    3 and 5 are handled by a direct computation of the order of pi^15 - 1 at their places.
  * Positive controls: N_15 * R^7 (R the largest prime <= B_15) and N_15 * M^7 (M a mid-range
    prime) must be flagged with multiplicity 7 by both methods; N_15 * S^6 must show S with
    multiplicity 6 and not be flagged.

Claim 7 uses direct point counting at degree-one good places; claims 8 and 9 are exact rational
arithmetic from the Tate-curve description.

Exit status 0 iff every check passes.
"""
import math
import sys
import time
from fractions import Fraction as Fr
from math import gcd, isqrt

import numpy as np
import sympy

T0 = time.time()
P = 30965819
L = 7
EXP = 15
fails = []


def ok(name, cond):
    print(("  [ok]   " if cond else "  [FAIL] ") + name)
    if not cond:
        fails.append(name)
    return cond


def section(t):
    print()
    print("== " + t)


# ---------------------------------------------------------------- arithmetic in O = Z[w]
def mul(u, v):
    a, b = u
    c, d = v
    return (a * c + b * d, a * d + b * c + b * d)


def add(u, v):
    return (u[0] + v[0], u[1] + v[1])


def sub(u, v):
    return (u[0] - v[0], u[1] - v[1])


def conj(u):
    return (u[0] + u[1], -u[1])


def norm(u):
    return u[0] * u[0] + u[0] * u[1] - u[1] * u[1]


def power(u, n):
    r = (1, 0)
    for _ in range(n):
        r = mul(r, u)
    return r


def content(u):
    return gcd(u[0], u[1])


def residue(u, s, q):
    """Image of u in O/w_s = F_q, where w_s is the degree-one place sending w to s."""
    return (u[0] + u[1] * s) % q


def roots_w(q):
    """Roots of t^2 - t - 1 mod q (the degree-one places above an odd prime q != 5)."""
    return [t for t in range(q) if (t * t - t - 1) % q == 0]


def ord_at_pi(u, pi):
    """Exact order of u at the prime ideal (pi), by repeated exact division:
    u / pi = u * conj(pi) / N(pi)."""
    if u == (0, 0):
        raise ValueError("zero")
    n = abs(norm(pi))
    k = 0
    while True:
        t = mul(u, conj(pi))
        if t[0] % n or t[1] % n:
            return k
        u = (t[0] // n, t[1] // n)
        k += 1


def mult(r, n):
    n = abs(n)
    k = 0
    while n % r == 0:
        n //= r
        k += 1
    return k


ONE = (1, 0)
PI = (-5932 + 919, -2 * 919)  # -5932 - 919*sqrt5, sqrt5 = 2w - 1
A = power(PI, EXP)
AM1 = sub(A, ONE)
ABAR = conj(A)

# ---------------------------------------------------------------- claim 1
section("Claim 1: p prime, split, N(pi) = p, size")
s5 = sympy.sqrt(5)
pi_sym = -5932 - 919 * s5
ok("pi in w-basis is (-5013, -1838)", PI == (-5013, -1838))
ok("N(pi) = p (w-basis)", norm(PI) == P)
ok("N(pi) = p (sympy, sqrt5 form)", sympy.expand(pi_sym * (-5932 + 919 * s5)) == P)
td = all(P % d for d in range(2, isqrt(P) + 1))
ok(f"p prime by trial division up to isqrt(p) = {isqrt(P)}", td)
ok("p prime (sympy.isprime)", sympy.isprime(P))
ok(f"p = {P % 5} mod 5, i.e. +-1 mod 5 (split in F0)", P % 5 in (1, 4))
ok(f"p > 30965760 = 2^14*3^3*5*2*7 (margin {P - 30965760})",
   2**14 * 3**3 * 5 * 2 * 7 == 30965760 and P > 30965760)
ok("p > 7741440 = 2^12*3^3*5*2*7", 2**12 * 3**3 * 5 * 2 * 7 == 7741440 and P > 7741440)

# ---------------------------------------------------------------- claim 2
section("Claim 2: the two places above p")
r5 = pow(5, (P + 1) // 4, P)  # p = 3 mod 4
ok("p = 3 mod 4 and 5^((p+1)/4)^2 = 5 mod p", P % 4 == 3 and r5 * r5 % P == 5)
inv2 = pow(2, -1, P)
places_p = sorted({(1 + r5) * inv2 % P, (1 - r5) * inv2 % P})
ok("two distinct roots of t^2 - t - 1 mod p", len(places_p) == 2 and
   all((s * s - s - 1) % P == 0 for s in places_p))
zero_at = [s for s in places_p if residue(PI, s, P) == 0]
ok("pi vanishes at exactly one place above p (v_pi)", len(zero_at) == 1)
s_pi = zero_at[0]
s_bar = [s for s in places_p if s != s_pi][0]
a_bar_res = residue(A, s_bar, P)
ok(f"a mod the other place = {a_bar_res}, not 0 or 1", a_bar_res not in (0, 1))
ok("a = pi^15 mod the other place agrees with pow(pi mod place, 15)",
   a_bar_res == pow(residue(PI, s_bar, P), 15, P))
oa = ord_at_pi(A, PI)
ok(f"ord_v_pi(a) = {oa} (exact division by pi; expected 15)", oa == 15)
ok("ord_v_pi(a) = v_p(N(a)) = 15 (norm route: N(a) = p^15, other place prime to a)",
   norm(A) == P**15 and mult(P, norm(A)) == 15 and a_bar_res != 0)
ok("v_pi does not divide a - 1 (a - 1 = -1 mod v_pi)", residue(AM1, s_pi, P) == P - 1)
ok("ord_v_pi(a - 1) = 0", ord_at_pi(AM1, PI) == 0)

# ---------------------------------------------------------------- claim 3
section("Claim 3: bad share (at most one degree-one place above each r not in {2, 7})")
c = content(AM1)
cf = sympy.factorint(c)
print(f"    a - 1 = x + y*w with x ({len(str(abs(AM1[0])))} digits), y ({len(str(abs(AM1[1])))} digits)")
print(f"    content gcd(x, y) of a - 1 in the basis {{1, w}} = {c} = {cf}")
ok("content(a - 1) has no prime factor outside {2, 7}", set(cf) <= {2, 7})
NAM1 = norm(AM1)
ok(f"5 does not divide N(a - 1) (N(a - 1) mod 5 = {NAM1 % 5}): (sqrt5) does not divide a - 1",
   NAM1 % 5 != 0)
ok("5 does not divide N(a) = p^15: (sqrt5) does not divide a", norm(A) % 5 != 0)
ok("(pi) is a prime ideal (N(pi) = p prime), so v_pi is the only place dividing a = pi^15",
   sympy.isprime(abs(norm(PI))))
ok("above p: v_pi | a, v_pi does not divide a - 1, the other place divides neither",
   residue(A, s_pi, P) == 0 and residue(AM1, s_pi, P) != 0 and a_bar_res not in (0, 1))
# cross-check: N(a-1) in sympy's sqrt5 form
a_sym = sympy.expand(pi_sym**15)
abar_sym = sympy.expand((-5932 + 919 * s5) ** 15)
ok("N(a - 1) agrees with sympy (sqrt5 form)", sympy.expand((a_sym - 1) * (abar_sym - 1)) == NAM1)
print(f"    N(a - 1) has {len(str(abs(NAM1)))} digits; v_2 = {mult(2, NAM1)}, v_3 = {mult(3, NAM1)},"
      f" v_5 = {mult(5, NAM1)}, v_7 = {mult(7, NAM1)}")
ok("v_2(N(a - 1)) = 2 * v_2(content): the inert place above 2 has order "
   f"{mult(2, c)} (excluded, divides 2l)", mult(2, NAM1) == 2 * mult(2, c))

# ---------------------------------------------------------------- claim 4
section("Claim 4: good reduction above 7")
print(f"    N(a) mod 7 = {norm(A) % 7}, N(1 - a) mod 7 = {norm(sub(ONE, A)) % 7}, p mod 7 = {P % 7}")
ok("7 does not divide N(a)", norm(A) % 7 != 0)
ok("7 does not divide N(1 - a)", norm(sub(ONE, A)) % 7 != 0)

# ---------------------------------------------------------------- claim 5
section("Claim 5: j(E0) is not rational")
A2 = mul(A, A)
num = mul((256, 0), power(add(sub(A2, A), ONE), 3))
den = mul(A2, mul(AM1, AM1))
ok("denominator a^2 (a - 1)^2 is nonzero", den != (0, 0))
jn = mul(num, conj(den))  # j = jn / N(den); rational iff the w-coordinate of jn is 0
ok(f"w-coordinate of j * N(den) is nonzero ({len(str(abs(jn[1])))} digits)", jn[1] != 0)
# second route: j(lambda) = j(mu) iff mu in the S3-orbit of lambda; j rational iff conj(a) is in
# the orbit of a.  Each orbit relation, cleared of denominators, is an identity in O.
orbit_rel = {
    "abar = a": sub(ABAR, A),
    "abar = 1 - a": sub(ABAR, sub(ONE, A)),
    "abar = 1/a": sub(mul(ABAR, A), ONE),
    "abar = 1/(1 - a)": sub(mul(ABAR, sub(ONE, A)), ONE),
    "abar = a/(a - 1)": sub(mul(ABAR, AM1), A),
    "abar = (a - 1)/a": sub(mul(ABAR, A), AM1),
}
ok("conj(a) is not in the S3-orbit {a, 1-a, 1/a, 1/(1-a), a/(a-1), (a-1)/a}",
   all(v != (0, 0) for v in orbit_rel.values()))

# ---------------------------------------------------------------- claim 6
section("Claim 6: Tate orders prime to 7")
o_num = ord_at_pi(num, PI)
o_den = ord_at_pi(den, PI)
ordj = o_num - o_den
print(f"    ord_v_pi(256 (a^2-a+1)^3) = {o_num}, ord_v_pi(a^2 (a-1)^2) = {o_den}")
ok(f"ord_v_pi(j) = {ordj} (expected -30), so ord_v_pi(q) = 30", ordj == -30)
ok("30 is prime to 7", gcd(30, 7) == 1)

x = sympy.symbols("x")
DIVS = sympy.divisors(EXP)
blocks = {}
prod = ONE
for d in DIVS:
    coeffs = sympy.Poly(sympy.cyclotomic_poly(d, x), x).all_coeffs()[::-1]
    v = (0, 0)
    pk = ONE
    for co in coeffs:
        v = add(v, (int(co) * pk[0], int(co) * pk[1]))
        pk = mul(pk, PI)
    blocks[d] = v
    prod = mul(prod, v)
ok("prod_{d | 15} Phi_d(pi) = pi^15 - 1 exactly", prod == AM1)
NB = {d: abs(norm(blocks[d])) for d in DIVS}
ok("prod_d N(Phi_d(pi)) = |N(a - 1)|", math.prod(NB.values()) == abs(NAM1))


def iroot7(n):
    """floor(n^(1/7)) by integer Newton iteration."""
    if n < 2:
        return n
    r = 1 << ((n.bit_length() + 6) // 7)
    while True:
        s = (6 * r + n // r**6) // 7
        if s >= r:
            break
        r = s
    while r**7 > n:
        r -= 1
    while (r + 1) ** 7 <= n:
        r += 1
    return r


BND = {}
for d in DIVS:
    b = iroot7(NB[d])
    BND[d] = b
    ok(f"N_{d} = N(Phi_{d}(pi)): {len(str(NB[d]))} digits, seventh-root bound B_{d} = {b}"
       " (own Newton = sympy.integer_nthroot)",
       b == sympy.integer_nthroot(NB[d], 7)[0] and b**7 <= NB[d] < (b + 1) ** 7)

# pairwise gcds of the blocks
pair_primes = set()
for i, d in enumerate(DIVS):
    for e in DIVS[i + 1:]:
        g = gcd(NB[d], NB[e])
        fg = sympy.factorint(g)
        pair_primes |= set(fg)
        print(f"    gcd(N_{d}, N_{e}) = {g} {fg if g > 1 else ''}")
print(f"    primes dividing two blocks: {sorted(pair_primes)}")

# direct orders at places above 3 (inert) and 5 (ramified), and above 2 and 7 for information
ord3 = mult(3, c)  # the place above 3 is 3O
ok(f"order of pi^15 - 1 at the inert place above 3 = v_3(content) = {ord3}, and"
   f" v_3(N(a - 1)) = {mult(3, NAM1)} = 2 * that", mult(3, NAM1) == 2 * ord3)
ord5 = mult(5, NAM1)  # the place (sqrt5) has degree one
print(f"    order of pi^15 - 1 at the ramified place above 5 = v_5(N(a - 1)) = {ord5}")
for r, o in ((3, ord3), (5, ord5)):
    ok(f"order at the place above {r} is 0 or prime to 7", o == 0 or o % 7 != 0)
print(f"    (residues: pi = {(PI[0] % 3, PI[1] % 3)} mod 3 in the w-basis,"
      f" pi = {(PI[0] + PI[1] * 3) % 5} mod sqrt5 [w = 3 mod sqrt5])")
for r in sorted(pair_primes - {2, 7, 3, 5}):
    vr = mult(r, NAM1)
    ok(f"shared prime {r}: v_r(N(a - 1)) = {vr} not a positive multiple of 7", vr % 7 != 0 or vr == 0)


# ---- seventh-power search in the blocks (and the controls), two methods over one sieve
def base_primes(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, isqrt(n) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0].astype(np.int64)


def segments(B, seg=1 << 23):
    bp = base_primes(isqrt(B) + 1)
    lo = 2
    while lo <= B:
        hi = min(lo + seg, B + 1)
        s = np.ones(hi - lo, dtype=bool)
        for q in bp:
            q = int(q)
            if q * q >= hi:
                break
            st = max(q * q, ((lo + q - 1) // q) * q)
            s[st - lo::q] = False
        yield np.nonzero(s)[0].astype(np.int64) + lo
        lo = hi


def limbs32(n):
    out = []
    while n:
        out.append(n & 0xFFFFFFFF)
        n >>= 32
    return out[::-1] or [0]


R_ctrl = sympy.prevprime(BND[15] + 1)
M_ctrl = sympy.prevprime(10**6)
S_ctrl = sympy.prevprime(10**8)
targets = []  # (label, N, bound)
for d in DIVS:
    targets.append((f"N_{d}", NB[d], BND[d]))
targets.append((f"control N_15*{R_ctrl}^7", NB[15] * R_ctrl**7, BND[15]))
targets.append((f"control N_15*{M_ctrl}^7", NB[15] * M_ctrl**7, BND[15]))
targets.append((f"control N_15*{S_ctrl}^6", NB[15] * S_ctrl**6, BND[15]))
BMAX = max(t[2] for t in targets)
assert BMAX < 2**31, "base 2^32 limbs need q < 2^31"
LIMBS = [np.array(limbs32(t[1]), dtype=np.int64) for t in targets]
divA = [set() for _ in targets]
accB = [1 for _ in targets]
counted = [0 for _ in targets]
CHUNK = 4096
t1 = time.time()
for qs in segments(BMAX):
    lo = int(qs[0]) if len(qs) else BMAX + 1
    for i, (lab, n, b) in enumerate(targets):
        if lo > b:
            continue
        qq = qs[qs <= b]
        counted[i] += len(qq)
        # method A: vectorised Horner remainders
        r = np.zeros(len(qq), dtype=np.int64)
        for limb in LIMBS[i]:
            r = ((r << 32) | limb) % qq
        for q in qq[r == 0].tolist():
            divA[i].add(int(q))
        # method B: product of the primes, reduced mod n, chunk by chunk
        ql = qq.tolist()
        acc = accB[i]
        for k in range(0, len(ql), CHUNK):
            acc = acc * (math.prod(ql[k:k + CHUNK]) % n) % n
        accB[i] = acc
print(f"    sieve + both methods: {time.time() - t1:.1f} s")

flagged_blocks = []
for i, (lab, n, b) in enumerate(targets):
    g = gcd(n, accB[i])
    divB = set(sympy.factorint(g)) if g > 1 else set()
    pc = int(sympy.primepi(b))
    ok(f"{lab}: {counted[i]} primes <= {b} tested (= sympy.primepi)", counted[i] == pc)
    ok(f"{lab}: method A and method B find the same prime divisors <= bound", divA[i] == divB)
    ms = {q: mult(q, n) for q in sorted(divA[i])}
    print(f"      prime divisors <= bound with multiplicity: {ms}")
    seventh = {q: m for q, m in ms.items() if m >= 7}
    if lab.startswith("N_"):
        bad = {q: m for q, m in seventh.items() if q not in (2, 7)}
        ok(f"{lab}: no prime r outside {{2, 7}} with r^7 | {lab}", bad == {})
        flagged_blocks.append(bad)
    elif lab.endswith("^7"):
        q0 = R_ctrl if str(R_ctrl) in lab else M_ctrl
        ok(f"positive control detected: {q0} with multiplicity {seventh.get(q0)} >= 7",
           seventh.get(q0, 0) >= 7)
    else:
        ok(f"negative control: {S_ctrl} found with multiplicity {ms.get(S_ctrl)} = 6 and not flagged",
           ms.get(S_ctrl) == 6 and S_ctrl not in seventh)

# assemble claim 6 for all primes r not in {2, 7}
ok("every prime outside {2, 3, 5, 7} divides at most one block (pairwise gcds)",
   pair_primes <= {2, 3, 5, 7})
ok("hence v_r(N(a - 1)) <= 6 for every prime r outside {2, 3, 5, 7}; at 3 and 5 it is "
   f"{mult(3, NAM1)} and {mult(5, NAM1)}", all(not b for b in flagged_blocks)
   and mult(3, NAM1) < 7 and mult(5, NAM1) < 7)
# consistency with claim 3 on the primes actually found: exactly one place above each divides a - 1
found = sorted(set().union(*divA[:len(DIVS)]) - {2, 7})
cons = True
for r in found:
    if r == 5 or r % 5 in (2, 3):  # 5 ramified / inert: no place may divide a - 1
        cons &= mult(r, NAM1) == 0
    else:
        hits = [s for s in roots_w(r) if residue(AM1, s, r) == 0]
        cons &= len(hits) == 1
ok(f"for each of the {len(found)} small prime divisors found {found}: exactly one place above it"
   " divides a - 1 (consistent with claim 3)", cons)

# ---------------------------------------------------------------- claim 7
section("Claim 7: mod-7 image witnesses at degree-one good places")


def count_points(q, lam):
    sq = [0] * q
    for y in range(q):
        sq[y * y % q] += 1
    return 1 + sum(sq[(t * (t - 1) * (t - lam)) % q] for t in range(q))


SQ7 = {1, 2, 4}
wit = {}
rows = []
for q in sympy.primerange(3, 2000):
    if q in (2, 5, 7, P) or q % 5 not in (1, 4):
        continue
    for s in roots_w(q):
        lam = residue(A, s, q)
        if lam in (0, 1):
            continue
        aq = q + 1 - count_points(q, lam)
        assert aq * aq <= 4 * q, "Hasse bound"
        t7, d7 = aq % 7, (aq * aq - 4 * q) % 7
        u7 = (aq * aq * pow(q, -1, 7)) % 7
        rows.append((q, s, aq, t7, d7, u7))
        if d7 != 0 and d7 not in SQ7:
            wit.setdefault("Borel", (q, s, aq, t7, d7, u7))
            if t7 != 0:
                wit.setdefault("split Cartan normalizer", (q, s, aq, t7, d7, u7))
        if t7 != 0 and d7 in SQ7:
            wit.setdefault("nonsplit Cartan normalizer", (q, s, aq, t7, d7, u7))
        if u7 not in (0, 1, 2, 4):
            wit.setdefault("exceptional", (q, s, aq, t7, d7, u7))
    if len(wit) == 4:
        break
print("    first good degree-one places (q, w mod q, a_q, a_q mod 7, disc mod 7, a_q^2/q mod 7):")
for r_ in rows[:8]:
    print("     ", r_)
for k in ("Borel", "split Cartan normalizer", "nonsplit Cartan normalizer", "exceptional"):
    ok(f"not contained in any {k} subgroup: witness (q, w mod q, a_q, a_q mod 7, disc mod 7, u) = {wit.get(k)}",
       k in wit)
# cross-check one witness with a Legendre-symbol count
q0, s0, aq0 = wit["Borel"][:3]
lam0 = residue(A, s0, q0)
leg = sum(sympy.legendre_symbol((t * (t - 1) * (t - lam0)) % q0, q0) if (t * (t - 1) * (t - lam0)) % q0 else 0
          for t in range(q0))
ok(f"a_{q0} recomputed as -sum Legendre symbols = {-leg}", -leg == aq0)

# ---------------------------------------------------------------- claim 8
section("Claim 8: local profile at p")
ordq = 2 * oa  # ord_v_pi(q) = -ord_v_pi(j) = 2*ord(a)
ok("ord_v_pi(q) = 30 (= -ord_v_pi(j))", ordq == 30 == -ordj)
e_g = 1  # good reduction at the other place, p prime to 105: unramified (Neron-Ogg-Shafarevich)
ok("e_g = 1 at the good place (p prime to 105 = 3*5*7)", e_g == 1 and gcd(P, 105) == 1)
e_b = 105 // gcd(105, ordq)
ok(f"e_b = 105/gcd(105, 30) = {e_b} (expected 7)", e_b == 7)
ok("tame: p does not divide e_b, and e_b <= p - 2", P % e_b != 0 and e_b <= P - 2)
ok("different exponent of K_b (tame) = e_b - 1 = 6", e_b - 1 == 6)
qord = Fr(e_b * ordq, 2 * L)
ok(f"order of q^(1/(2l)) in the uniformizer of K_b = e_b*30/14 = {qord} (expected 15)", qord == 15)
print(f"    (reduction at v_pi is {'split' if P % 4 == 1 else 'non-split'} multiplicative:"
      f" -1 is {'a' if P % 4 == 1 else 'not a'} square mod p; this does not change e_b)")

# ---------------------------------------------------------------- claim 9
section("Claim 9: margins (units of log p, l* = 3)")
ls = (L - 1) // 2
ordq_root = Fr(ordq, 2 * L)  # ord_p of q^(1/(2l)) at the bad place: 15/7
Q = (Fr(0) + ordq_root) / 2
dbar = (Fr(0) + Fr(e_b - 1, e_b)) / 2
U = sum(-Fr(j * j) * ordq_root * Fr(1, 2 ** (j + 1)) for j in range(1, ls + 1)) / ls
U2 = sum(-Fr(j * j) * Q * Fr(1, 2**j) for j in range(1, ls + 1)) / ls
Bex = sum((j + 1) * dbar - j * j * Q + 1 for j in range(1, ls + 1)) / ls
Bfin = Fr(L + 1, 4) * ((1 + Fr(4, L)) * dbar - Fr(1, 6) * (2 * L * Q) + Fr(4, L))
print(f"    Q = {Q}, dbar = {dbar}, U = {U}, B_exact = {Bex}, B_final = {Bfin}")
ok("Q = 15/14", Q == Fr(15, 14))
ok("dbar = 3/7", dbar == Fr(3, 7))
ok("U = -15/16 (also = (1/3) sum -j^2 Q 2^-j)", U == Fr(-15, 16) == U2)
ok("B_exact = -19/7", Bex == Fr(-19, 7))
ok("B_final = -123/49", Bfin == Fr(-123, 49))
ok(f"U - B_final = {U - Bfin} (expected 1233/784) > 0", U - Bfin == Fr(1233, 784) and U - Bfin > 0)
ok(f"U - B_exact = {U - Bex} (expected 199/112) > 0", U - Bex == Fr(199, 112) and U - Bex > 0)

print()
print(f"runtime {time.time() - T0:.1f} s")
print("OK" if not fails else f"FAIL ({len(fails)}): {fails}")
sys.exit(0 if not fails else 1)
