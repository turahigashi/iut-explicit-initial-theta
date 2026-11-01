#!/usr/bin/env python3
"""Independent re-check (sympy, written separately from certify_datum.py) of the
arithmetic of the datum D_18 of the note,  F0 = Q(sqrt5), l = 7, E0: y^2 = x(x-1)(x-a), a = pi^18,
pi = 14164 + 5825*sqrt5 (norm p = 30965771).

Different methods from certify_datum.py on purpose:
  * primality by sympy.isprime, square roots of 5 by sympy.sqrt_mod;
  * j(E0) computed as an element of Q(sqrt5) with sympy, irrationality = nonzero sqrt5 part;
  * cyclotomic blocks from sympy.cyclotomic_poly and polynomial arithmetic in sympy;
  * seventh-power-freeness by sympy.primerange + sympy.multiplicity over the same bound,
    plus a direct factorization attempt for the small blocks;
  * Frobenius traces by counting points on y^2 = f(x) over F_q directly (sum over y);
  * local invariants from the Tate-curve description, recomputed with Fractions.
"""
from fractions import Fraction as F
from math import gcd

import sympy
from sympy import sqrt, Rational, expand, cyclotomic_poly, symbols, Poly, isprime, sqrt_mod

P_ = 30965771
A_, B_ = 14164, 5825
N = 18
L = 7
fails = []


def ok(name, cond):
    print(("  [ok] " if cond else "  [FAIL] ") + name)
    if not cond:
        fails.append(name)


s5 = sqrt(5)
pi = A_ + B_ * s5
pibar = A_ - B_ * s5
ok("p prime (sympy)", isprime(P_))
ok("norm(pi) = p", expand(pi * pibar) == P_)
ok("p > 2^12*3^3*5*2*7 = e*_mod*l (source)", P_ > 2**12 * 3**3 * 5 * 2 * 7)
ok("p > 2^14*3^3*5*2*7 (enlarged constant)", P_ > 2**14 * 3**3 * 5 * 2 * 7)
a = expand(pi**N)
abar = expand(pibar**N)
ok("7 divides neither N(a) nor N(1-a) (good reduction above l = 7)",
   int(expand(a * abar)) % 7 != 0 and int(expand((1 - a) * (1 - abar))) % 7 != 0)

# j-invariant of the Legendre curve, as an element of Q(sqrt5)
j = 256 * (a**2 - a + 1) ** 3 / (a**2 * (a - 1) ** 2)
jbar = 256 * (abar**2 - abar + 1) ** 3 / (abar**2 * (abar - 1) ** 2)
diff = sympy.nsimplify(sympy.radsimp(expand(j - jbar)))
ok("j(E0) is not rational (j - jbar != 0)", diff != 0)

# reduction at the two places above p: residues via a square root of 5 mod p
roots = sorted(sqrt_mod(5, P_, all_roots=True))
ok("5 has two square roots mod p", len(roots) == 2)
res = {r: (A_ + B_ * r) % P_ for r in roots}
r_pi = [r for r in roots if res[r] == 0]
ok("pi vanishes at exactly one place above p", len(r_pi) == 1)
r_bar = [r for r in roots if r not in r_pi][0]
a_at_bar = pow((A_ + B_ * r_bar) % P_, N, P_)
ok("a mod the conjugate place is not 0, 1", a_at_bar not in (0, 1))
print("    a mod v_pibar =", a_at_bar)

# cyclotomic blocks
x = symbols("x")
divs = sympy.divisors(N)
prod = 1
norms = {}
for d in divs:
    ph = Poly(cyclotomic_poly(d, x), x)
    v = expand(ph.as_expr().subs(x, pi))
    vbar = expand(ph.as_expr().subs(x, pibar))
    nv = int(expand(v * vbar))
    norms[d] = abs(nv)
    prod = expand(prod * v)
ok("prod Phi_d(pi) = pi^18 - 1", expand(prod - (a - 1)) == 0)

# seventh-power-freeness, outside 2 and 7, by trial division up to the seventh root
for d in divs:
    n = norms[d]
    bound = sympy.integer_nthroot(n, 7)[0]
    bad = []
    for q in sympy.primerange(2, bound + 1):
        if n % q == 0 and sympy.multiplicity(q, n) >= 7 and q not in (2, 7):
            bad.append(q)
    ok(f"N(Phi_{d}(pi)) ({len(str(n))} digits): no seventh power of a prime outside 2*7 (bound {bound})",
       bad == [])
    if len(str(n)) <= 30:
        print("    factorization:", sympy.factorint(n))

# overlaps at 3 (inert): the order of a - 1 at the place above 3
v3 = sympy.multiplicity(3, int(abs(expand((a - 1) * (abar - 1)))))
ok("v_3(N(a-1)) even (3 inert)", v3 % 2 == 0)
ok("order of a - 1 at the place above 3 is 0 or prime to 7", (v3 // 2) == 0 or (v3 // 2) % 7 != 0)
print("    order at 3:", v3 // 2)


# Frobenius at small degree-one places, by direct point counting
def count_points(q, lam):
    sq = {}
    for y in range(q):
        sq[y * y % q] = sq.get(y * y % q, 0) + 1
    return 1 + sum(sq.get((t * (t - 1) * (t - lam)) % q, 0) for t in range(q))


found_irred = None
for q in sympy.primerange(11, 400):
    if q % 5 not in (1, 4):
        continue
    for r in sorted(sqrt_mod(5, q, all_roots=True)):
        lam = pow((A_ + B_ * r) % q, N, q)
        if lam in (0, 1):
            continue
        aq = q + 1 - count_points(q, lam)
        disc = (aq * aq - 4 * q) % 7
        if disc != 0 and pow(disc, 3, 7) == 6:  # nonresidue mod 7
            found_irred = (q, r, aq)
            break
    if found_irred:
        break
ok("a degree-one good place with Frobenius irreducible mod 7", found_irred is not None)
print("    witness (q, sqrt5 mod q, a_q):", found_irred)
ok("Tate order 2N = 36 at v_pi prime to 7", gcd(2 * N, 7) == 1)

# local invariants at p (Tate curve): K_b = Q_p(zeta_420, q^(1/105)), q of order 2N = 36
e_b = F(105, gcd(105, 2 * N)).numerator
ok("e_b = 35", e_b == 35)
ok("tame and I* empty: e_b <= p - 2", e_b <= P_ - 2)
qq = F(2 * N, 2 * L)
ok("ord_p of the 2l-th root of q at b = 18/7", qq == F(18, 7))
ok("qOrd_b = e_b * 18/7 = 90", e_b * qq == 90)
dbar = (F(0) + F(e_b - 1, e_b)) / 2
Q = (F(0) + qq) / 2
lstar = (L - 1) // 2
union = sum(-F(jj * jj) * Q * F(1, 2**jj) for jj in range(1, lstar + 1)) / lstar
Bexact = sum((jj + 1) * dbar - jj * jj * Q + 1 for jj in range(1, lstar + 1)) / lstar
logq = 2 * L * Q
Bfinal = F(L + 1, 4) * ((1 + F(4, L)) * dbar - F(1, 6) * logq + F(4, L))
ok("margin over the exact bound = 677/280", union - Bexact == F(677, 280))
ok("margin over the final displayed bound = 4323/1960", union - Bfinal == F(4323, 1960))
print("    dbar =", dbar, " Q =", Q, " union >=", union, " Bexact =", Bexact, " Bfinal =", Bfinal)
print("OK" if not fails else f"FAIL {fails}")
raise SystemExit(0 if not fails else 1)
