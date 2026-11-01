#!/usr/bin/env python3
"""Screen and certify the arithmetic of an explicit datum with mixed reduction at a
split prime p > e*_mod * l, where the term with iota in IUT IV, Theorem 1.10, Step (v)
vanishes (iota_p = 0).

    F0 = Q(sqrt5),  l = 7,  E0: y^2 = x(x-1)(x-a),  a = pi^N,  N = 18,
    pi in Z[sqrt5] of norm p,  p prime,  p = +-1 mod 5,
    p > 30965760 = 2^14*3^3*5*2*7  (> e*_mod * l = 7741440 of the source).

What this program checks (standard library only, exact integer and rational arithmetic):
  (1) p is prime and splits in Q(sqrt5); pi has norm p; p > e*_mod * l = 7741440,
      with e_mod = 2 (the maximal ramification index of Q(sqrt5) over Q), and also
      p > 2^14*3^3*5*e_mod*l = 30965760 (a larger, more conservative constant).
  (2) a = pi^N has order N at v_pi and is neither 0 nor 1 modulo v_pibar
      (multiplicative reduction at v_pi, good reduction at v_pibar).
  (3) j(E0) is not rational: the six Legendre orbit comparisons between a and its
      conjugate fail, so the field of moduli is F0.
  (4) The Tate order 2N at v_pi is prime to l = 7.
  (5) Every selected bad place has Tate order prime to 7: pi^N - 1 is the product of
      the cyclotomic blocks Phi_d(pi), d | N; each block norm is seventh-power-free
      (exhaustive check of all primes up to the floor of its seventh root); a prime
      ideal can divide two blocks only above a prime dividing N, and those totals are
      computed directly.
  (6) Witnesses for the mod-7 Galois image: Frobenius characteristic polynomials at
      small good degree-one places (irreducible, etc.), as in the first report.
  (7) The local profile at p: e_g = 1, e_b = 105 / gcd(105, 2N), tame, d_b = 1 - 1/e_b,
      ord_p(q_b) = 2N, ord_p(underline-underline q_b) = 2N/(2l) = N/l.
  (8) The comparison with the final displayed bound of Step (v), procession-normalized,
      at this prime (iota = 0), against the averaged lower bound for the hull in the variant
      of Remark 5 of the note with permutations moving the label 0 and without rounding
      (lower bound at the good place: units part >= 0).

What this program does NOT check: the geometric constructions of an initial Theta-datum
beyond the listed arithmetic (cores, compatible section, cusp, lattice), the cited
theorems, the identification of these quantities with the source's possible images,
or the readings under which the comparisons of the note apply.

    python3 checks/certify_datum.py            # screen and certify
    python3 checks/certify_datum.py --json     # machine-readable
Exit status 0 iff every check passes for the selected prime.
"""
from __future__ import annotations

import json
import sys
from fractions import Fraction as F
from math import gcd, isqrt

if not __debug__:
    raise SystemExit("Run with assertions enabled (do not use python -O).")

L_LEVEL = 7
E_MOD = 2
E_STAR_MOD = 2**12 * 3**3 * 5 * E_MOD          # [IUTchIV] Thm 1.10, (R4): e*_mod
THRESHOLD_SOURCE = E_STAR_MOD * L_LEVEL         # iota_p = 0 iff p > e*_mod * l (Step (iii))
# A more conservative constant uses 2^14 in place of 2^12 (as when F is enlarged to its Galois
# closure). We take p above both thresholds so that iota_p = 0 under either constant.
THRESHOLD_ENLARGED = 2**14 * 3**3 * 5 * E_MOD * L_LEVEL
THRESHOLD = max(THRESHOLD_SOURCE, THRESHOLD_ENLARGED)
EXP_N = 18
FAIL: list[str] = []
LOG: list[str] = []


def check(name, got, want):
    ok = got == want
    LOG.append(f"  [{'ok' if ok else 'FAIL'}] {name}: {got}" + ("" if ok else f"  (expected {want})"))
    if not ok:
        FAIL.append(name)
    return ok


# ------------------------------------------------------------------ Z[sqrt5]
def mul(x, y):
    return (x[0] * y[0] + 5 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def sub(x, y):
    return (x[0] - y[0], x[1] - y[1])


def conj(x):
    return (x[0], -x[1])


def norm(x):
    return x[0] * x[0] - 5 * x[1] * x[1]


def power(x, n):
    r, b = (1, 0), x
    while n:
        if n & 1:
            r = mul(r, b)
        b = mul(b, b)
        n >>= 1
    return r


ONE = (1, 0)


def is_prime(n: int) -> bool:
    """Deterministic Miller-Rabin for n < 3.3e24 (bases 2..37)."""
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for q in small:
        if n % q == 0:
            return n == q
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for b in small:
        x = pow(b, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def primes_up_to(m: int) -> list[int]:
    sieve = bytearray([1]) * (m + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, isqrt(m) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i in range(m + 1) if sieve[i]]


def kth_root_floor(n: int, k: int) -> int:
    lo, hi = 0, 1
    while hi**k <= n:
        hi *= 2
    while lo < hi:
        m = (lo + hi + 1) // 2
        if m**k <= n:
            lo = m
        else:
            hi = m - 1
    return lo


def val(n: int, q: int) -> int:
    assert n != 0
    v = 0
    while n % q == 0:
        n //= q
        v += 1
    return v


def find_pi(p: int):
    """An element of Z[sqrt5] of norm +p (searching small b)."""
    for b in range(0, 200000):
        t = p + 5 * b * b
        a = isqrt(t)
        if a * a == t:
            return (a, b)
        t = 5 * b * b - p
        if t >= 0:
            a = isqrt(t)
            if a * a == t:  # norm -p; multiply by the unit 2 + sqrt5 of norm -1
                return mul((a, b), (2, 1))
    return None


def max_prime_exponent(n: int, plist: list[int], limit: int, bound: int, report: bool = False):
    """Largest exponent of a prime <= bound dividing n (a prime > bound has exponent < 7
    when bound = floor(n^(1/7))). plist must be all primes <= limit, and bound <= limit.
    Returns (prime, exponent[, primes with exponent >= 7])."""
    assert bound <= limit, "sieve list does not cover the bound"
    best_q, best_e, offenders = 0, 0, []
    for q in plist:
        if q > bound:
            break
        if n % q == 0:
            e = val(n, q)
            if e > best_e:
                best_q, best_e = q, e
            if e >= 7:
                offenders.append(q)
    return (best_q, best_e, offenders) if report else (best_q, best_e)


def residue(x, r, p):
    return (x[0] + x[1] * r) % p


def cyclotomic(d: int) -> list[int]:
    """Coefficients (low degree first) of the d-th cyclotomic polynomial."""
    num = [-1] + [0] * (d - 1) + [1]  # x^d - 1
    for e in range(1, d):
        if d % e == 0:
            den = cyclotomic(e)
            # exact division num / den
            q = [0] * (len(num) - len(den) + 1)
            r = num[:]
            for i in range(len(q) - 1, -1, -1):
                c = r[i + len(den) - 1] // den[-1]
                assert c * den[-1] == r[i + len(den) - 1]
                q[i] = c
                for k, dk in enumerate(den):
                    r[i + k] -= c * dk
            assert all(v == 0 for v in r), (d, e)
            num = q
    return num


def evaluate(poly, x):
    r = (0, 0)
    for c in reversed(poly):
        r = add(mul(r, x), (c, 0))
    return r


def legendre(n, p):
    n %= p
    return 0 if n == 0 else (1 if pow(n, (p - 1) // 2, p) == 1 else -1)


def screen(p: int, pi, N: int, verbose: bool) -> dict:
    """All arithmetic checks for one candidate; returns a record."""
    rec: dict = {"p": p, "pi": list(pi), "N": N}
    check("p is prime", is_prime(p), True)
    check("p = +-1 mod 5 (split in Q(sqrt5))", p % 5 in (1, 4), True)
    check("Norm(pi) = p", norm(pi), p)
    check("e*_mod * l (source, 2^12) = 7741440", THRESHOLD_SOURCE, 7741440)
    check("enlarged constant (2^14) times l = 30965760", THRESHOLD_ENLARGED, 30965760)
    check("p > e*_mod * l (iota_p = 0 in the source)", p > THRESHOLD_SOURCE, True)
    check("p > 2^14*3^3*5*e_mod*l (iota_p = 0 for the enlarged constant)", p > THRESHOLD_ENLARGED, True)
    # general square root of 5 mod p by Tonelli-Shanks
    r5 = tonelli(5, p)
    check("5 is a square mod p", r5 is not None and r5 * r5 % p == 5, True)
    r_pi = r5 if residue(pi, r5, p) == 0 else (p - r5) % p
    r_bar = (p - r_pi) % p
    check("pi vanishes at its place", residue(pi, r_pi, p), 0)
    check("pi is a unit at the conjugate place", residue(pi, r_bar, p) != 0, True)
    A = power(pi, N)
    rec["a_digits"] = [len(str(abs(A[0]))), len(str(abs(A[1])))]
    check("Norm(a) = p^N", norm(A), p**N)
    a_bar_res = residue(A, r_bar, p)
    rec["a_mod_vpibar"] = a_bar_res
    check("a mod v_pibar is not 0 or 1 (good reduction)", a_bar_res not in (0, 1), True)
    # v_p(Norm(1 - a)) = 0, so v_pi(1-a) = 0 and v_pibar(1-a) = 0
    check("v_p(Norm(1-a)) = 0", val(norm(sub(ONE, A)), p), 0)
    # good reduction above l = 7 as in the datum of the first report (7 is inert in Q(sqrt5)):
    # no place above 7 divides a or 1 - a (the discriminant 16 a^2 (1-a)^2 is a unit there)
    check("7 does not divide Norm(a)", norm(A) % L_LEVEL != 0, True)
    check("7 does not divide Norm(1-a) (good reduction above l)", norm(sub(ONE, A)) % L_LEVEL != 0, True)
    # (3) j irrational
    orbit = {
        "abar == a": conj(A) == A,
        "abar == 1/a": mul(conj(A), A) == ONE,
        "abar == 1-a": conj(A) == sub(ONE, A),
        "abar == 1/(1-a)": mul(conj(A), sub(ONE, A)) == ONE,
        "abar == a/(a-1)": mul(conj(A), sub(A, ONE)) == A,
        "abar == (a-1)/a": mul(conj(A), A) == sub(A, ONE),
    }
    for k, v in orbit.items():
        check(f"orbit comparison {k}", v, False)
    # (4) Tate order at v_pi
    check("Tate order 2N at v_pi prime to 7", gcd(2 * N, L_LEVEL), 1)
    # (5) blocks
    divisors = [d for d in range(1, N + 1) if N % d == 0]
    blocks = {d: evaluate(cyclotomic(d), pi) for d in divisors}
    prod = ONE
    for d in divisors:
        prod = mul(prod, blocks[d])
    check("product of cyclotomic blocks = pi^N - 1", prod, sub(A, ONE))
    norms = {d: abs(norm(blocks[d])) for d in divisors}
    check("every block norm is nonzero", all(v != 0 for v in norms.values()), True)
    bounds = {d: kth_root_floor(norms[d], 7) for d in divisors}
    big = max(bounds.values())
    rec["block_norm_digits"] = {d: len(str(norms[d])) for d in divisors}
    rec["sieve_bounds"] = bounds
    plist = primes_up_to(big)
    rec["primes_sieved"] = len(plist)
    rec["sieve_limit"] = big
    # positive controls on the same code path: a planted seventh power must be found,
    # and a planted sixth power must not be reported as a seventh power
    d0 = max(divisors, key=lambda d: bounds[d])
    planted7 = max_prime_exponent(norms[d0] * 13**7, plist, big, bounds[d0])
    planted6 = max_prime_exponent(13**6 * 17**3, plist, big, kth_root_floor(13**6 * 17**3, 7))
    check("sieve control: planted 13^7 is found", planted7[1] >= 7 and planted7[0] == 13, True)
    check("sieve control: 13^6 * 17^3 has no seventh power", planted6[1] < 7, True)
    worst = {}
    for d in divisors:
        q_at, e_at, offenders = max_prime_exponent(norms[d], plist, big, bounds[d], report=True)
        worst[d] = {"max_exponent": e_at, "at": q_at,
                    "seventh_powers_at": offenders}
        bad = [q for q in offenders if q not in (2, L_LEVEL)]
        check(f"block Phi_{d}(pi): no prime outside 2*7 to a seventh power in the norm", bad, [])
    rec["max_exponent_per_block"] = worst
    # overlaps: only primes dividing N; 2, 3 and 7 are inert in Q(sqrt5) (f = 2), 5 is ramified (e = 2, f = 1)
    for q in sorted({q for q in (2, 3, 5, 7) if N % q == 0}):
        vn = val(abs(norm(sub(A, ONE))), q)
        if q == 5:
            check("5 is ramified in Q(sqrt5)", legendre(5, q), 0)
            vp = vn  # f = 1: v_5(Norm x) = ord_(sqrt5)(x)
        else:
            check(f"{q} is inert in Q(sqrt5)", legendre(5, q) if q > 2 else -1, -1)
            assert vn % 2 == 0
            vp = vn // 2
        rec[f"v_{q}(pi^N - 1)"] = vp
        if q != 2:
            check(f"place above {q}: order of pi^N - 1 not divisible by 7 (or zero)",
                  vp == 0 or vp % 7 != 0, True)
    # (6) mod-7 witnesses at small degree-one good places
    data = []
    for q in range(11, 4000):
        if not is_prime(q) or q % 5 not in (1, 4) or q in (p,):
            continue
        r = tonelli(5, q)
        for root in sorted({r, (q - r) % q}):
            av = residue(A, root, q)
            if av in (0, 1):
                continue
            ap = -sum(legendre(x * (x - 1) * (x - av), q) for x in range(q))
            assert ap * ap <= 4 * q, (q, ap)
            data.append((q, root, ap))
        if len(data) >= 60:
            break
    QR7 = {(x * x) % L_LEVEL for x in range(1, L_LEVEL)}
    W = {}
    for (q, root, ap) in data:
        t7 = ap % 7
        dd = (ap * ap - 4 * q) % 7
        isQR, isNR = dd in QR7, (dd != 0 and dd not in QR7)
        if "Borel" not in W and isNR:
            W["Borel"] = (q, root, ap, dd)
        if "splitN" not in W and t7 != 0 and isNR:
            W["splitN"] = (q, root, ap, dd)
        if "nonsplitN" not in W and t7 != 0 and isQR:
            W["nonsplitN"] = (q, root, ap, dd)
        if "exc" not in W and q % 7 != 0:
            tt = (ap * ap * pow(q, -1, 7)) % 7
            if tt not in (0, 1, 2, 4):
                W["exc"] = (q, root, ap, tt)

    def roots_mod_l(qq, aq):
        return {x for x in range(L_LEVEL) if (x * x - aq * x + qq) % L_LEVEL == 0}

    for k in ("Borel", "splitN", "nonsplitN", "exc"):
        check(f"mod-7 witness excluding {k}", W.get(k) is not None, True)
    if "Borel" in W:
        wq, _, wap, _ = W["Borel"]
        check("Borel witness: characteristic polynomial irreducible mod 7", len(roots_mod_l(wq, wap)), 0)
    rec["mod7_witnesses"] = {k: list(v) for k, v in W.items()}
    # (7) local profile at p
    ordq = 2 * N
    e_b = 105 // gcd(105, ordq)
    rec["e_g"], rec["e_b"] = 1, e_b
    check("e_b <= p - 2 (tame, I* empty)", e_b <= p - 2, True)
    d_b = 1 - F(1, e_b)
    qq = F(ordq, 2 * L_LEVEL)
    rec["ord_q_b"], rec["ord_qq_b"], rec["d_b"] = ordq, str(qq), str(d_b)
    check("e_b * ord(qq_b) is an integer (qOrd in the uniformizer of K_b)", (e_b * qq).denominator, 1)
    rec["qOrd_b_uniformizer"] = int(e_b * qq)
    rec["D_b_different_exponent"] = e_b - 1
    # (8) comparison, normalized by log p, iota = 0, l* = 3
    dbar = (0 + d_b) / 2
    Q = qq / 2  # weighted average of ord(qq) over the two places (equal weights)
    lstar = (L_LEVEL - 1) // 2
    js = range(1, lstar + 1)
    union_lower = sum(-F(j * j) * qq * F(1, 2 ** (j + 1)) for j in js) / lstar
    B_exact = sum((j + 1) * dbar - j * j * Q + 1 for j in js) / lstar
    l = L_LEVEL
    logD, logQ, logS = dbar, 2 * Q * l, F(1)  # log(q_{v_Q}) = weighted avg of ord_p(q_v) = 2l*Q
    B_final = F(l + 1, 4) * ((1 + F(4, l)) * logD - F(1, 6) * logQ + F(4, l) * logS)
    check("B_final >= B_exact (the source's two weakenings)", B_final >= B_exact, True)
    rec["dbar"], rec["Q"] = str(dbar), str(Q)
    rec["union_lower"], rec["B_exact"], rec["B_final"] = str(union_lower), str(B_exact), str(B_final)
    rec["margin_exact"] = str(union_lower - B_exact)
    rec["margin_final"] = str(union_lower - B_final)
    check("averaged lower bound for the hull exceeds the exact procession-normalized bound", union_lower > B_exact, True)
    check("averaged lower bound for the hull exceeds the final displayed bound (iota = 0)", union_lower > B_final, True)
    return rec


def tonelli(n: int, p: int):
    n %= p
    if n == 0:
        return 0
    if pow(n, (p - 1) // 2, p) != 1:
        return None
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(n, q, p), pow(n, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r


def candidates(start: int):
    """Primes p > start, p = +-1 mod 5, with an element pi of Z[sqrt5] of norm p,
    in increasing order of p."""
    p = start
    while True:
        p += 1
        if p % 5 not in (1, 4) or not is_prime(p):
            continue
        pi = find_pi(p)
        assert pi is not None, p  # class number one and the unit 2 + sqrt5 of norm -1
        yield p, pi


def main():
    args = sys.argv[1:]
    as_json = "--json" in args
    out = args[args.index("--out") + 1] if "--out" in args else None
    fixed = int(args[args.index("--p") + 1]) if "--p" in args else None
    rejected = []
    rec = None
    for p, pi in candidates(THRESHOLD if fixed is None else fixed - 1):
        if fixed is not None and p != fixed:
            raise SystemExit(f"--p {fixed} is not a prime = +-1 mod 5")
        FAIL.clear()
        LOG.clear()
        rec = screen(p, pi, EXP_N, True)
        if not FAIL or fixed is not None:
            break
        rejected.append({"p": p, "failed": list(FAIL)})
        if len(rejected) >= 500:
            raise SystemExit("no candidate among the first 500")
    assert rec is not None
    rec["threshold_source_e_star_mod_times_l"] = THRESHOLD_SOURCE
    rec["threshold_enlarged_times_l"] = THRESHOLD_ENLARGED
    rec["rejected_before"] = rejected
    rec["checks_total"] = len(LOG)
    rec["checks_failed"] = list(FAIL)
    rec["log"] = list(LOG)
    if out:
        with open(out, "w") as fh:
            json.dump(rec, fh, indent=2, default=str)
            fh.write("\n")
    if as_json:
        print(json.dumps(rec, indent=2, default=str))
    else:
        p, pi = rec["p"], rec["pi"]
        print(f"selected p = {p}, pi = {pi[0]} + {pi[1]}*sqrt5, N = {EXP_N}")
        print(f"rejected before it: {rejected}")
        print("\n".join(LOG))
        for k in ("e_b", "ord_qq_b", "qOrd_b_uniformizer", "dbar", "Q", "union_lower", "B_exact",
                  "B_final", "margin_exact", "margin_final", "sieve_limit", "primes_sieved",
                  "max_exponent_per_block", "mod7_witnesses"):
            print(f"  {k}: {rec[k]}")
        print("OK" if not FAIL else f"FAIL: {FAIL}")
    sys.exit(0 if not FAIL else 1)


if __name__ == "__main__":
    main()
