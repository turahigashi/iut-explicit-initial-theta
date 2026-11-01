#!/usr/bin/env python3
"""Complete factorizations with primality certificates (standard library only).

For the datum D_3 of the note (F0 = Q(sqrt5), pi = 14164 + 5825 sqrt5, p = N(pi) = 30965771,
a = pi^6 / pibar^30), the numerator of 1 - a is -prod_{d | 6} Phi_d(pi, pibar^5) with the homogeneous
cyclotomic forms Phi_d.  This program checks that each of the four norms N(Phi_d(pi, pibar^5)) equals the
product of the prime powers listed below, so that no odd prime divides it to the seventh power.  The same
is checked for N(1 - a) = 2^2 * 11^2 * R of the datum D_2 (a = pi * pibar^6), whose prime R is used in
Section 5 of the note.

A listed factor below 10^10 is proved prime by trial division.  A listed factor of at least 10^10 must
carry a Lucas (Pratt) certificate in pratt_certificates.json: a witness a and the prime factors of n - 1
with multiplicity, such that the factors multiply to n - 1, a^(n-1) = 1 (mod n), a^((n-1)/q) != 1 (mod n)
for every listed q, and every listed q is itself certified or below 10^10 and prime.  The file is not
trusted: every certificate in it is checked.

    python3 checks/check_pratt_factorizations.py
Exit status 0 iff every check passes.
"""
import json
import os
import sys
from math import isqrt, prod

if not __debug__:
    raise SystemExit("Run with assertions enabled (do not use python -O).")

SMALL = 10**10
HERE = os.path.dirname(os.path.abspath(__file__))
fails = []


def ok(name, cond):
    print(("  [ok]   " if cond else "  [FAIL] ") + name)
    if not cond:
        fails.append(name)
    return cond


def is_prime_small(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    for i in range(3, isqrt(n) + 1, 2):
        if n % i == 0:
            return False
    return True


# ---------------------------------------------------------------- certificates
certs = {int(k): v for k, v in json.load(open(os.path.join(HERE, "pratt_certificates.json"))).items()}
print(f"== {len(certs)} certificates")
for n in sorted(certs):
    a, fs = certs[n]["a"], certs[n]["factors"]
    good = n >= SMALL and prod(fs) == n - 1 and pow(a, n - 1, n) == 1
    good = good and all(pow(a, (n - 1) // q, n) != 1 for q in set(fs))
    good = good and all(q in certs or (q < SMALL and is_prime_small(q)) for q in set(fs))
    ok(f"certificate for {n} ({len(str(n))} digits, witness {a})", good)


def is_certified_prime(q):
    return q in certs if q >= SMALL else is_prime_small(q)


# ---------------------------------------------------------------- Z[sqrt5]
def mul(x, y):
    return (x[0] * y[0] + 5 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def neg(x):
    return (-x[0], -x[1])


def power(x, n):
    r = (1, 0)
    for _ in range(n):
        r = mul(r, x)
    return r


def norm(x):
    return x[0] * x[0] - 5 * x[1] * x[1]


PI = (14164, 5825)
PIBAR = (14164, -5825)
P = 30965771
ok("N(pi) = 30965771", norm(PI) == P)


def check_factorization(label, n, fac):
    print(f"== {label}: {len(str(n))} digits")
    ok(f"{label} = {' * '.join(f'{q}^{e}' if e > 1 else str(q) for q, e in fac)}",
       prod(q**e for q, e in fac) == n)
    ok(f"{label}: every listed factor is prime (trial division below 10^10, certificate above)",
       all(is_certified_prime(q) for q, _ in fac))
    ok(f"{label}: the listed factors are distinct", len({q for q, _ in fac}) == len(fac))
    return fac


# D_3: the four homogeneous cyclotomic forms at (pi, pibar^5)
X, Y = PI, power(PIBAR, 5)
forms = {
    1: add(X, neg(Y)),
    2: add(X, Y),
    3: add(add(mul(X, X), mul(X, Y)), mul(Y, Y)),
    6: add(add(mul(X, X), neg(mul(X, Y))), mul(Y, Y)),
}
num = add(power(X, 6), neg(power(Y, 6)))  # pi^6 - pibar^30
ok("D_3: prod_{d | 6} Phi_d(pi, pibar^5) = pi^6 - pibar^30",
   mul(mul(forms[1], forms[2]), mul(forms[3], forms[6])) == num)
FACT_D3 = {
    1: [(2, 2), (5, 2), (29, 1), (1301, 1), (7546302221502292729989416349739, 1)],
    2: [(2, 8), (19, 1), (149, 1), (19801, 1), (1984003939995100146692750879, 1)],
    3: [(17, 2), (1291, 1), (166911169, 1), (26746145815244461, 1),
        (486685363594452319041420748071613404758945479, 1)],
    6: [(19, 1), (61, 1), (118621, 1), (154072586477232178581475729, 1),
        (38269129828752271745435515342932155533891, 1)],
}
for d in (1, 2, 3, 6):
    fac = check_factorization(f"D_3: |N(Phi_{d}(pi, pibar^5))|", abs(norm(forms[d])), FACT_D3[d])
    ok(f"D_3: no odd prime to the seventh power in N(Phi_{d})", all(e < 7 for q, e in fac if q != 2))

# D_2: N(1 - a), a = pi * pibar^6 (an element of Z[sqrt5])
a2 = mul(PI, power(PIBAR, 6))
n2 = norm(add((1, 0), neg(a2)))
R = 56406340220143710508313748934073550973772664592051
check_factorization("D_2: |N(1 - a)|", abs(n2), [(2, 2), (11, 2), (R, 1)])

print("OK" if not fails else f"FAIL ({len(fails)}): {fails}")
sys.exit(0 if not fails else 1)
