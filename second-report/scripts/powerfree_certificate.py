#!/usr/bin/env python3
"""Executable 89th-power-free certificate for the fourteen-level datum.

Three independent reviews reconstructed this computation and asked that it be shipped
rather than described as external.  It is finite and small -- the largest search bound
is 24,856 -- so there is no reason for it to live outside the bundle.

  pi = 41 + 26i,  Norm(pi) = 2357,  a = pi^472,  B = Norm(1 - a).

B factors over Z[i] into nine cyclotomic blocks.  Blockwise 89th-power-freeness gives
it for B itself provided no rational prime contributes to two blocks with total
valuation >= 89; only 2 and 5 can occur twice, and their totals are 9 and 2.

  python3 scripts/powerfree_certificate.py            # human-readable
  python3 scripts/powerfree_certificate.py --json     # machine-readable

Exit 0 iff every check passes.  Standard library only.
"""
from __future__ import annotations
import json, sys
from math import gcd

ELL_MIN = 89                                   # smallest level in the window


def mul(x, y):  return (x[0]*y[0] - x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def sub(x, y):  return (x[0]-y[0], x[1]-y[1])
def nrm(x):     return x[0]*x[0] + x[1]*x[1]


def pw(x, n):
    r = (1, 0)
    while n:
        if n & 1: r = mul(r, x)
        x = mul(x, x); n >>= 1
    return r


def divexact(x, y):
    """Exact division in Z[i]; returns None if y does not divide x."""
    d = nrm(y)
    num = mul(x, (y[0], -y[1]))
    if num[0] % d or num[1] % d: return None
    return (num[0]//d, num[1]//d)


def val(n, q):
    v = 0
    while n % q == 0: n //= q; v += 1
    return v


def kth_root_floor(n, k):
    """floor(n ** (1/k)) by integer bisection -- no floats."""
    lo, hi = 0, 1
    while hi ** k <= n: hi *= 2
    while lo < hi:
        m = (lo + hi + 1) // 2
        if m ** k <= n: lo = m
        else: hi = m - 1
    return lo


def primes_upto(n):
    if n < 2: return []
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]: sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
    return [i for i in range(2, n + 1) if sieve[i]]


def divisors(n):
    return sorted(d for d in range(1, n + 1) if n % d == 0)


def mobius(n):
    m, res = n, 1
    q = 2
    while q * q <= m:
        if m % q == 0:
            m //= q
            if m % q == 0: return 0
            res = -res
        q += 1
    return -res if m > 1 else res


def build_blocks(pi, N):
    """Blocks of pi^N - 1, from Phi_d(X) = prod_{e|d} (X^e - 1)^{mu(d/e)} evaluated at
    pi by EXACT Gaussian division -- no hand-derived cyclotomic formulas."""
    def cyc_at(d):
        num, den = (1, 0), (1, 0)
        for e in divisors(d):
            m = mobius(d // e)
            t = sub(pw(pi, e), (1, 0))
            if m == 1:   num = mul(num, t)
            elif m == -1: den = mul(den, t)
        q = divexact(num, den)
        assert q is not None, f"Phi_{d}(pi) not integral"
        return q

    blocks = {f"Phi_{d}": cyc_at(d) for d in divisors(N) if d != N}
    # Phi_N splits over Z[i] as G_+ G_- with G_pm = (X^{N/4} -+ i)/(X^2 -+ i)... the
    # exact split is found by dividing Phi_N by the two candidate factors and keeping
    # whichever divides exactly; both must, and their product must be Phi_N.
    phiN = cyc_at(N)
    h = N // 4
    Xh, X2 = pw(pi, h), pw(pi, 2)
    gp = divexact((Xh[0], Xh[1] + 1), (X2[0], X2[1] - 1))
    gm = divexact((Xh[0], Xh[1] - 1), (X2[0], X2[1] + 1))
    assert gp is not None and gm is not None, "G_pm not Gaussian integers"
    assert mul(gp, gm) == phiN, "G_+ G_- != Phi_N"
    blocks["G_plus"], blocks["G_minus"] = gp, gm

    prod = (1, 0)
    for b in blocks.values(): prod = mul(prod, b)
    target = sub(pw(pi, N), (1, 0))
    assert prod == target, "blocks do not multiply to X^N - 1"
    return blocks, abs(nrm(target))


def self_test() -> int:
    """Negative control supplied by external review (round 15).

    Two synthetic blocks of norm 17^44 and 17^46: each is 89th-power free on its own,
    but their product is 17^90, which is not.  The pairwise gcd is 17^44.  The earlier
    version of this script tested a hard-coded prime list that omitted 17 and returned
    PASS.  The check below must return FAIL.
    """
    A, B = (17 ** 22, 0), (17 ** 23, 0)
    g = gcd(abs(nrm(A)), abs(nrm(B)))
    shared, m, d = set(), g, 2
    while d * d <= m:
        while m % d == 0: shared.add(d); m //= d
        d += 1
    if m > 1: shared.add(m)
    prod_val = val(abs(nrm(A)) * abs(nrm(B)), 17)
    caught = (17 in shared) and prod_val >= ELL_MIN
    print(f"  synthetic blocks 17^22, 17^23:  gcd factors -> {sorted(shared)}")
    print(f"  v_17(product) = {prod_val} >= {ELL_MIN} ? {prod_val >= ELL_MIN}")
    print(f"  SELF-TEST: the unknown shared prime is {'CAUGHT' if caught else 'MISSED'}")
    return 0 if caught else 1


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    pi, N = (41, 26), 472
    blocks, B = build_blocks(pi, N)
    out = {"pi": list(pi), "N": N, "ell_min": ELL_MIN,
           "B_digits": len(str(B)), "blocks": [], "pair_gcds": {}, "shared": {}}
    ok = True

    # (1) each block norm is 89th-power free, by exhaustive sieve to its own bound
    tested_total = 0
    for name, b in blocks.items():
        n = abs(nrm(b))
        bound = kth_root_floor(n, ELL_MIN)
        hits = [q for q in primes_upto(bound) if n % (q ** ELL_MIN) == 0]
        tested_total += len(primes_upto(bound))
        ok &= not hits
        out["blocks"].append({"name": name, "norm_digits": len(str(n)),
                              "root_bound": bound, "power_factors": hits})

    # (2) which rational primes can meet two blocks at all
    names = list(blocks)
    shared = set()
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            g = gcd(abs(nrm(blocks[names[i]])), abs(nrm(blocks[names[j]])))
            out["pair_gcds"][f"{names[i]}|{names[j]}"] = g
            # FAIL-CLOSED.  An earlier version tested a hard-coded list (2,3,5,7,11,13)
            # and would have PASSED while ignoring a gcd with a larger prime factor
            # (external review, round 15).  Factor the gcd completely instead.
            if g > 1:
                m, d = g, 2
                while d * d <= m:
                    while m % d == 0:
                        shared.add(d); m //= d
                    d += 1
                if m > 1: shared.add(m)
    # (3) their TOTAL valuations in B must stay below ell
    for q in sorted(shared):
        v = val(B, q)
        out["shared"][str(q)] = v
        ok &= v < ELL_MIN
    # every gcd must be fully accounted for by the primes we then bound
    for key, g in out["pair_gcds"].items():
        m = g
        for q in shared:
            while m % q == 0: m //= q
        if m != 1:
            ok = False
            out.setdefault("unaccounted_gcd", {})[key] = m
    out["overall_result"] = "PASS" if ok else "FAIL"
    out["primes_tested"] = tested_total
    out["limitation"] = ("Establishes 89th-power-freeness of B, which is SUFFICIENT for "
                         "the order condition at the remaining bad places.  It is not a "
                         "construction of fourteen initial Theta-data.")

    if "--json" in sys.argv:
        print(json.dumps(out, indent=2))
    else:
        print(f"B = Norm(pi^{N} - 1) has {out['B_digits']} digits; nine blocks")
        for b in out["blocks"]:
            print(f"  {b['name']:<9} norm {b['norm_digits']:>4}d  sieve to {b['root_bound']:>6}"
                  f"  {ELL_MIN}th-power factors: {b['power_factors'] or 'none'}")
        print(f"  primes tested (with multiplicity across blocks): {tested_total:,}")
        print(f"  primes meeting two blocks: {sorted(shared)}")
        for q, v in out["shared"].items():
            print(f"    v_{q}(B) = {v}   < {ELL_MIN} ? {int(v) < ELL_MIN}")
        print(f"RESULT: {out['overall_result']}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
