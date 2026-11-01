#!/usr/bin/env python3
"""Independent re-check (sympy, sharing no code with certify_wide.py or certify_datum.py) of the datum D_3
of the note:

    F0 = Q(sqrt5), l = 7, E0: y^2 = x(x-1)(x-a), a = pi^6 / pibar^30, pi = 14164 + 5825*sqrt5 (norm p = 30965771).

Different methods on purpose:
  * arithmetic of Q(sqrt5) through sympy expressions; j(E0) irrational as a nonzero sqrt5 part;
  * the factorization of X^6 - Y^6 found by sympy.factor (not from a table of cyclotomic polynomials);
  * the seventh-power check of the two 75-digit norms by the wheel program seventh_power_wheel.c (trial
    division by every integer prime to 210, 64-bit limbs and 128-bit reduction), the 38-digit norms by
    sympy.factorint;
  * common places of two factors compared through sympy.sqrt_mod;
  * the Frobenius trace by counting points;
  * the gaps by enumerating all summands (v_0, ..., v_j) and taking minima and averages directly, and the
    final display from its formula in IUT IV, Thm 1.10, Step (v).
"""
import os
import subprocess
import sys
import tempfile
from fractions import Fraction as Fr
from itertools import product
from math import ceil, gcd

import sympy
from sympy import sqrt, expand, isprime, sqrt_mod, integer_nthroot, symbols

P_ = 30965771
A_, B_ = 14164, 5825
L = 7
fails = []


def ok(name, cond):
    print(("  [ok] " if cond else "  [FAIL] ") + name)
    if not cond:
        fails.append(name)


s5 = sqrt(5)
pi = A_ + B_ * s5
pib = A_ - B_ * s5
ok("p prime", isprime(P_))
ok("norm(pi) = p", expand(pi * pib) == P_)
ok("p > 2^14*3^3*5*2*7", P_ > 2**14 * 3**3 * 5 * 2 * 7)


def coords(z):
    z = expand(z)
    c0 = z.subs(s5, 0)
    c1 = expand((z - c0) / s5)
    return sympy.Rational(c0), sympy.Rational(c1)


def norm(z):
    c0, c1 = coords(z)
    return c0 * c0 - 5 * c1 * c1


a = pi**6 / pib**30
abar = pib**6 / pi**30
# a in coordinates: a = pi^36 / p^30
ac = coords(expand(pi**36))
ac = (ac[0] / sympy.Integer(P_) ** 30, ac[1] / sympy.Integer(P_) ** 30)
abc = (ac[0], -ac[1])
ok("a = pi^36/p^30 equals pi^6/pibar^30", sympy.simplify(expand((ac[0] + ac[1] * s5) * pib**30 - pi**6)) == 0)


def jinv(c):
    x = c[0] + c[1] * s5
    return 256 * (x**2 - x + 1) ** 3 / (x**2 * (x - 1) ** 2)


jd = sympy.radsimp(expand(jinv(ac) - jinv(abc)))
ok("j(E0) is not rational", sympy.nsimplify(jd) != 0)

X, Y = symbols("X Y")
fac = sympy.factor_list(X**6 - Y**6)
pieces = [f for f, e in fac[1]]
ok("X^6 - Y^6 factors into four forms over Q", len(pieces) == 4 and all(e == 1 for f, e in fac[1]))
Yv = pib**5
vals = [expand(f.subs({X: pi, Y: Yv})) for f in pieces]
norms = [abs(int(norm(v))) for v in vals]
num = expand(pi**6 - Yv**6)
Nnum = abs(int(norm(num)))
prod_ = 1
for nv in norms:
    prod_ *= nv
ok("product of the norms of the four forms = N(pi^6 - pibar^30)", prod_ == Nnum)
ok("p does not divide N(numerator of 1 - a)", Nnum % P_ != 0)
ok("7 does not divide N(numerator of 1 - a)", Nnum % 7 != 0)
print("    digits of the four norms:", [len(str(nv)) for nv in norms])

small = [nv for nv in norms if len(str(nv)) < 50]
large = [nv for nv in norms if len(str(nv)) >= 50]
ok("two norms of < 50 digits and two of >= 50", len(small) == 2 and len(large) == 2)
for nv in small:
    f = sympy.factorint(nv)
    print("    factorint:", f)
    ok("small norm: no odd prime to a seventh power", all(e < 7 for q, e in f.items() if q != 2))

src = os.path.join(os.path.dirname(os.path.abspath(__file__)), "seventh_power_wheel.c")
tmp = tempfile.mkdtemp(prefix="w7_")
exe = os.path.join(tmp, "w7")
subprocess.run(["gcc", "-O2", "-pthread", "-o", exe, src], check=True)
bound = max(integer_nthroot(nv, 7)[0] for nv in large)
threads = sys.argv[sys.argv.index("--threads") + 1] if "--threads" in sys.argv else "8"
out = subprocess.run([exe, str(bound), threads] + [str(nv) for nv in large], check=True,
                     capture_output=True, text=True).stdout
divs = {0: [], 1: []}
tested = None
for line in out.splitlines():
    w = line.split()
    if w[0] == "DIV":
        divs[int(w[1])].append(int(w[2]))
    elif w[0] == "TESTED":
        tested = int(w[1])
print("    wheel bound:", bound, " integers tested:", tested)
for i, nv in enumerate(large):
    ds = sorted(divs[i])
    primes = [q for q in ds if isprime(q)]
    exps = {q: sympy.multiplicity(q, nv) for q in primes}
    print(f"    large norm {i}: prime divisors up to the bound {exps}")
    ok(f"large norm {i}: no odd prime up to its seventh root to a seventh power",
       all(e < 7 for q, e in exps.items() if q != 2) and integer_nthroot(nv, 7)[0] <= bound)

# common places of two forms: only above primes dividing 6
bad = []
for i in range(4):
    for k in range(i + 1, 4):
        g = gcd(norms[i], norms[k])
        for q in sympy.factorint(g):
            if q in (2, 3):
                continue
            if q % 5 in (1, 4):
                for r in sqrt_mod(5, q, all_roots=True):
                    ri = [int((coords(v)[0] + coords(v)[1] * r) % q) for v in (vals[i], vals[k])]
                    if ri == [0, 0]:
                        bad.append((i, k, q, r))
            else:
                bad.append((i, k, q))
ok("two forms share a place only above 2 or 3", bad == [])
v2 = sympy.multiplicity(2, Nnum)
v3 = sympy.multiplicity(3, Nnum)
ok("above 3: order of 1 - a prime to 7 (v_3 even, half not divisible by 7 unless 0)", v3 % 2 == 0 and (v3 == 0 or (v3 // 2) % 7))
print(f"    v_2 = {v2}, v_3 = {v3}")


def count_points(q, lam):
    sq = {}
    for y in range(q):
        sq[y * y % q] = sq.get(y * y % q, 0) + 1
    return 1 + sum(sq.get((t * (t - 1) * (t - lam)) % q, 0) for t in range(q))


found = None
for q in sympy.primerange(11, 800):
    if q % 5 not in (1, 4) or q == 7:
        continue
    for r in sorted(sqrt_mod(5, q, all_roots=True)):
        num_q = pow((A_ + B_ * r) % q, 36, q)
        lam = num_q * pow(pow(P_, 30, q), -1, q) % q
        if lam in (0, 1):
            continue
        aq = q + 1 - count_points(q, lam)
        d = (aq * aq - 4 * q) % 7
        if d != 0 and pow(d, 3, 7) == 6:
            found = (q, r, aq)
            break
    if found:
        break
ok("mod-7 witness by point counting", found is not None)
print("    witness:", found)

# profile from the Tate curve
T = {"b1": 12, "b2": 60}
ok("Tate orders prime to 7", all(t % 7 for t in T.values()))
e = {b: 105 // gcd(105, t) for b, t in T.items()}
D = {b: e[b] - 1 for b in T}
rho = {b: Fr(t, 14) for b, t in T.items()}
qOrd = {b: e[b] * rho[b] for b in T}
ok("profile e = (35, 7), qOrd = (30, 30)", (e["b1"], e["b2"], qOrd["b1"], qOrd["b2"]) == (35, 7, 30, 30))
# gaps by enumeration over summands, equal weights
places = ["b1", "b2"]
gaps = []
stepv = []
union = []
for j in (1, 2, 3):
    tot_u = Fr(0)
    tot_s = Fr(0)
    cnt = 0
    for summand in product(places, repeat=j + 1):
        cnt += 1
        tot_u += -(j * j) * min(rho[summand[t]] for t in range(1, j + 1))
        tot_s += -(j * j) * rho[summand[j]] + sum(Fr(D[v], e[v]) for v in summand) + 1
    union.append(tot_u / cnt)
    stepv.append(tot_s / cnt)
    gaps.append(union[-1] - stepv[-1])
beta = (Fr(D["b1"], e["b1"]) + Fr(D["b2"], e["b2"])) / 2
logq = Fr(T["b1"] + T["b2"], 2)
final = Fr(L + 1, 4) * ((1 + Fr(4, L)) * beta - Fr(1, 6) * logq + Fr(4, L))
excess = sum(union) / 3 - final
print("    union lower bounds:", union, " Step (v) label bounds:", stepv)
print("    gaps:", gaps, " final display:", final, " excess:", excess)
ok("gaps = (-99/35, -11/35, 242/35)", gaps == [Fr(-99, 35), Fr(-11, 35), Fr(242, 35)])
ok("excess over the final display = 241/245", excess == Fr(241, 245))
lam = 9 * rho["b2"]
dI = 3 * Fr(D["b1"], e["b1"]) + Fr(D["b2"], e["b2"])
coef = -lam + dI + 1 + ceil(9 * rho["b1"])
ok("summand collision coefficient = -129/5", coef == Fr(-129, 5))
print("OK" if not fails else f"FAIL {fails}")
raise SystemExit(0 if not fails else 1)
