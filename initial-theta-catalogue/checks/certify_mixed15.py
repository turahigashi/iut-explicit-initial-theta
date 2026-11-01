#!/usr/bin/env python3
"""Search for and certify the datum D_15 of the note: an explicit datum in which, at every rational prime, at most one of the
places of F0 = Q(sqrt5) above it has multiplicative reduction with q in the support (bad share <= 1/2
everywhere), together with a split prime p > e*_mod * l at which the term with iota vanishes and the
two places above p are one good and one bad.

    F0 = Q(sqrt5),  l = 7,  E0: y^2 = x(x-1)(x-a),  a = pi^N,  N = 15,
    pi in Z[sqrt5] of norm p (or -pi),  p prime,  p = +-1 mod 5,  p > 30965760.

Why N = 15: N odd, so no prime r is forced to divide both places by Fermat's little theorem (r - 1 and
r^2 - 1 are even, N is odd; the only forced prime is r = 2, whose residue field F_4 has F_4^* of order
3 | 15, and the places above 2 divide 2l and are outside the support of q); 7 does not divide N, so the
Tate order 2N at v_pi is prime to l; e_b = 105/gcd(105, 30) = 7; the margin against the final displayed
bound of Step (v) is (13/48)N - 19/7 + 11/(7 e_b) = 1233/784 (in units of log p).

Bad share. For an odd rational prime r != 5, a place of Q(sqrt5) above r divides x = X + Y*sqrt5 for
every place above r iff r | gcd(X, Y) (split: (r) = rr', both divide iff r | x; inert: (r) is the only
place). The ramified place (sqrt5) divides x iff 5 | X. The places with q-order > 0 lie above p (v_pi
only, since a = pi^N) and above the primes dividing a - 1 (Legendre form; places above 2 and 7 divide
2l = 14 and are outside the support of q). Hence: if gcd(A - 1, B) has no prime factor other than 2 and
7 and 5 does not divide A - 1, then at every rational prime at most one of two places (weight 1 each)
is bad, or the only place is good, i.e. the bad share is 0 or 1/2 everywhere.

All checks of certify_datum.screen (primality, split, threshold, good reduction at v_pibar and above 7,
j irrational, Tate order, seventh-power-free cyclotomic blocks, mod-7 witnesses, local profile, margins)
are run on the selected candidate with N = 15, after the cheap checks above.

    python3 checks/certify_mixed15.py                 # search and certify
    python3 checks/certify_mixed15.py --out rec.json  # also write a record
Exit status 0 iff every check passes for the selected candidate.
"""
from __future__ import annotations

import json
import os
import sys
from fractions import Fraction as F
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import certify_datum as cd  # noqa: E402  (no side effects on import: main() is guarded)

if not __debug__:
    raise SystemExit("Run with assertions enabled (do not use python -O).")

EXP_N = 15


def prime_factors(n: int) -> list[int]:
    n = abs(n)
    out, d = [], 2
    while d * d <= n:
        while n % d == 0:
            out.append(d)
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out.append(n)
    return sorted(set(out))


def cheap(p: int, pi, N: int) -> dict:
    """The bad-share conditions and the cheap conditions of the first checks; no sieve."""
    A = cd.power(pi, N)
    x = (A[0] - 1, A[1])
    g = gcd(x[0], x[1])
    gp = prime_factors(g)
    r5 = cd.tonelli(5, p)
    r_pi = r5 if cd.residue(pi, r5, p) == 0 else (p - r5) % p
    r_bar = (p - r_pi) % p
    a_bar = cd.residue(A, r_bar, p)
    n1a = cd.norm(cd.sub(cd.ONE, A))
    orbit_hit = (cd.conj(A) == A or cd.mul(cd.conj(A), A) == cd.ONE or cd.conj(A) == cd.sub(cd.ONE, A)
                 or cd.mul(cd.conj(A), cd.sub(cd.ONE, A)) == cd.ONE
                 or cd.mul(cd.conj(A), cd.sub(A, cd.ONE)) == A or cd.mul(cd.conj(A), A) == cd.sub(A, cd.ONE))
    return {
        "gcd": g,
        "gcd_primes": gp,
        "gcd_ok": all(r in (2, 7) for r in gp),
        "sqrt5_divides_a_minus_1": x[0] % 5 == 0,
        "a_mod_vpibar_ok": a_bar not in (0, 1),
        "seven_good": cd.norm(A) % 7 != 0 and n1a % 7 != 0,
        "p_not_in_a_minus_1": cd.val(abs(n1a), p) == 0,
        "j_irrational": not orbit_hit,
    }


def passes(c: dict) -> bool:
    return (c["gcd_ok"] and not c["sqrt5_divides_a_minus_1"] and c["a_mod_vpibar_ok"] and c["seven_good"]
            and c["p_not_in_a_minus_1"] and c["j_irrational"])


def main():
    args = sys.argv[1:]
    out = args[args.index("--out") + 1] if "--out" in args else None
    fixed = int(args[args.index("--p") + 1]) if "--p" in args else None
    sign = int(args[args.index("--sign") + 1]) if "--sign" in args else None
    rejected = []
    chosen = None
    for p, pi in cd.candidates(cd.THRESHOLD if fixed is None else fixed - 1):
        if fixed is not None and p != fixed:
            raise SystemExit(f"--p {fixed} is not a prime = +-1 mod 5")
        for s in ((1, -1) if sign is None else (sign,)):
            cand = (s * pi[0], s * pi[1])
            c = cheap(p, cand, EXP_N)
            if passes(c):
                chosen = (p, cand, s, c)
                break
            rejected.append({"p": p, "sign": s, "gcd_primes": c["gcd_primes"],
                             "sqrt5": c["sqrt5_divides_a_minus_1"], "seven_good": c["seven_good"],
                             "a_mod_vpibar_ok": c["a_mod_vpibar_ok"], "j_irrational": c["j_irrational"]})
        if chosen or fixed is not None:
            break
        if len(rejected) >= 2000:
            raise SystemExit("no candidate among the first 2000")
    if chosen is None:
        raise SystemExit("the fixed candidate fails the cheap checks: " + json.dumps(rejected[-2:]))
    p, pi, s, c = chosen
    print(f"candidate p = {p}, pi = {pi[0]} + {pi[1]}*sqrt5 (sign {s}), N = {EXP_N}; "
          f"{len(rejected)} rejected before it by the cheap checks", flush=True)
    cd.FAIL.clear()
    cd.LOG.clear()
    cd.check("gcd of the coefficients of a - 1 has no prime factor other than 2 and 7", c["gcd_ok"], True)
    cd.check("sqrt5 divides a - 1 (must be False: the ramified place above 5 is good)",
             c["sqrt5_divides_a_minus_1"], False)
    rec = cd.screen(p, pi, EXP_N, True)
    rec["sign"] = s
    rec["gcd_a_minus_1"] = c["gcd"]
    rec["gcd_primes"] = c["gcd_primes"]
    rec["bad_share_everywhere_at_most_half"] = c["gcd_ok"] and not c["sqrt5_divides_a_minus_1"]
    # expected values of the local profile and margins for N = 15
    cd.check("e_b = 7", rec["e_b"], 7)
    cd.check("qOrd_b in the uniformizer of K_b = 15", rec["qOrd_b_uniformizer"], 15)
    cd.check("different exponent at b = 6", rec["D_b_different_exponent"], 6)
    cd.check("averaged lower bound for the hull = -15/16", F(rec["union_lower"]), F(-15, 16))
    cd.check("exact procession-normalized bound = -19/7", F(rec["B_exact"]), F(-19, 7))
    cd.check("final displayed bound (iota = 0) = -123/49", F(rec["B_final"]), F(-123, 49))
    cd.check("margin against the final displayed bound = 1233/784", F(rec["margin_final"]), F(1233, 784))
    rec["rejected_before_count"] = len(rejected)
    rec["rejected_before_sample"] = rejected[:40]
    rec["threshold_source_e_star_mod_times_l"] = cd.THRESHOLD_SOURCE
    rec["threshold_enlarged_times_l"] = cd.THRESHOLD_ENLARGED
    rec["checks_total"] = len(cd.LOG)
    rec["checks_failed"] = list(cd.FAIL)
    rec["log"] = list(cd.LOG)
    if out:
        with open(out, "w") as fh:
            json.dump(rec, fh, indent=2, default=str)
            fh.write("\n")
    print("\n".join(cd.LOG))
    for k in ("e_b", "ord_qq_b", "qOrd_b_uniformizer", "dbar", "Q", "union_lower", "B_exact", "B_final",
              "margin_exact", "margin_final", "sieve_limit", "primes_sieved", "max_exponent_per_block",
              "mod7_witnesses", "gcd_a_minus_1", "gcd_primes"):
        print(f"  {k}: {rec[k]}")
    print("OK" if not cd.FAIL else f"FAIL: {cd.FAIL}")
    sys.exit(0 if not cd.FAIL else 1)


if __name__ == "__main__":
    main()
