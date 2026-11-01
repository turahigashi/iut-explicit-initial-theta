#!/usr/bin/env python3
"""Certify the datum D_3 of the note: two bad places above one split prime whose q-orders differ
widely, so that, under the readings stated in the note, the lower bounds for the hull exceed not only
the bound of Step (v) of IUT IV Thm 1.10 at one tuple but also its displayed bounds at p: the weighted
average bound for the label 3 and the final display.

    F0 = Q(sqrt5),  l = 7,  E0: y^2 = x(x-1)(x-a),  a = (pi / pibar^k)^n = pi^(n(k+1)) / p^(kn),
    pi = 14164 + 5825 sqrt5 of prime norm p = 30965771,  (n, k) = (6, 5) by default.

At v_pi the parameter a has a zero of order n, at v_pibar a pole of order kn; both places above p are
multiplicative, with Tate orders 2n and 2kn.  The numerator of 1 - a = (pibar^(kn) - pi^n) / pibar^(kn)
factors as the homogeneous cyclotomic forms Phi_d(pi, pibar^k), d | n, whose norms are checked to have no
seventh power of a prime: primes up to the seventh root of each norm are tested, by trial division in
Python for the small norms and by the segmented sieve seventh_power_sieve.c (compiled to a temporary
directory) for the large ones, with a planted control.

Checks (exact integer and rational arithmetic; helpers reused from certify_datum.py):
  (1) p prime, split, N(pi) = p, above both thresholds for iota_p = 0;
  (2) a pibar^(kn) = pi^n (the representation of a), pi a unit at v_pibar and pibar a unit at v_pi;
  (3) p does not divide N(pibar^(kn) - pi^n) (1 - a a unit above p), 7 divides neither norm;
  (4) the product of the forms Phi_d(pi, pibar^k) is pi^n - pibar^(kn); pairwise gcds of their norms
      involve only primes dividing n; no norm has a seventh power of a prime; the order of 1 - a at the
      places above 2 and 3 (both inert) is computed;
  (5) the six Legendre orbit comparisons between abar and a fail (field of moduli F0);
  (6) the Tate orders 2n, 2kn are prime to 7; a mod-7 witness (Frobenius irreducible at a good place);
  (7) the local profile e = 105/gcd(105, T), different e - 1, qOrd = e T / 14 (integer), tame;
  (8) the gaps, in units of log p, of the averaged lower bound for the hull (permutations fixing 0,
      without rounding: the first variant of Remark 5 of the note) over the Step (v) bounds:
        gap_j = j^2 (rho2 - rho1)(1/2 - 2^-j) - (j+1) betabar - 1   (label j, weighted average bound),
        average over j = 1, 2, 3, and the excess over the final display (average minus (betabar + 1)/7);
      and the collision coefficient at the summand (b1, b1, b1, b2) for j = 3;
  (9) whether sqrt(a) and sqrt(1 - a) change the profile (the field of a tower).

    python3 checks/certify_wide.py [--n N --k K] [--threads T] [--json OUT]
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from fractions import Fraction as F
from math import ceil, gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import certify_datum as cd  # noqa: E402

if not __debug__:
    raise SystemExit("Run with assertions enabled (do not use python -O).")

P_ = 30965771
PI = (14164, 5825)
L = 7
FAIL: list[str] = []
LOG: list[str] = []


def check(name, got, want):
    ok = got == want
    LOG.append(f"  [{'ok' if ok else 'FAIL'}] {name}: {got}" + ("" if ok else f"  (expected {want})"))
    if not ok:
        FAIL.append(name)
    return ok


def hom_cyclotomic(d, X, Y):
    """Phi_d(X, Y) = sum_i c_i X^i Y^(phi(d) - i) in Z[sqrt5]."""
    c = cd.cyclotomic(d)
    m = len(c) - 1
    s = (0, 0)
    for i, ci in enumerate(c):
        t = cd.mul(cd.power(X, i), cd.power(Y, m - i))
        s = cd.add(s, (ci * t[0], ci * t[1]))
    return s


# Q(sqrt5) with rational coordinates, for the orbit comparisons
def qm(x, y):
    return (x[0] * y[0] + 5 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def qs(x, y):
    return (x[0] - y[0], x[1] - y[1])


def qinv(x):
    n = x[0] * x[0] - 5 * x[1] * x[1]
    assert n != 0
    return (x[0] / n, -x[1] / n)


def sieve_large(numbers, bound, threads, planted):
    """Primes <= bound dividing the numbers, by the C sieve; also run on a planted control."""
    src = os.path.join(os.path.dirname(os.path.abspath(__file__)), "seventh_power_sieve.c")
    tmp = tempfile.mkdtemp(prefix="s7_")
    exe = os.path.join(tmp, "s7")
    subprocess.run(["gcc", "-O2", "-pthread", "-o", exe, src], check=True)
    args = [exe, str(bound), str(threads)] + [format(x, "x") for x in numbers + [planted]]
    out = subprocess.run(args, check=True, capture_output=True, text=True).stdout
    divs = {i: [] for i in range(len(numbers) + 1)}
    count = None
    for line in out.splitlines():
        w = line.split()
        if w[0] == "DIV":
            divs[int(w[1])].append(int(w[2]))
        elif w[0] == "COUNT":
            count = int(w[1])
        elif w[0] == "BOUND":
            assert int(w[1]) == bound
    return divs, count


def main():
    args = sys.argv[1:]
    n = int(args[args.index("--n") + 1]) if "--n" in args else 6
    k = int(args[args.index("--k") + 1]) if "--k" in args else 5
    threads = int(args[args.index("--threads") + 1]) if "--threads" in args else 8
    out = args[args.index("--json") + 1] if "--json" in args else None
    p, pi = P_, PI
    pibar = cd.conj(pi)
    rec: dict = {"p": p, "pi": list(pi), "n": n, "k": k, "a": "pi^n / pibar^(kn)"}
    # (1)
    check("p is prime", cd.is_prime(p), True)
    check("p = +-1 mod 5 (split in Q(sqrt5))", p % 5 in (1, 4), True)
    check("p = 3 mod 4 (Q_p(sqrt-1) unramified quadratic)", p % 4, 3)
    check("Norm(pi) = p", cd.norm(pi), p)
    check("p > e*_mod * l = 7741440", p > cd.THRESHOLD_SOURCE, True)
    check("p > 30965760", p > cd.THRESHOLD_ENLARGED, True)
    r5 = cd.tonelli(5, p)
    r_pi = r5 if cd.residue(pi, r5, p) == 0 else (p - r5) % p
    r_bar = (p - r_pi) % p
    check("pi vanishes at v_pi", cd.residue(pi, r_pi, p), 0)
    check("pibar vanishes at v_pibar", cd.residue(pibar, r_bar, p), 0)
    check("pibar is a unit at v_pi", cd.residue(pibar, r_pi, p) != 0, True)
    check("pi is a unit at v_pibar", cd.residue(pi, r_bar, p) != 0, True)
    # (2) a = A / p^(kn), A = pi^(n(k+1))
    A = cd.power(pi, n * (k + 1))
    den = p ** (k * n)
    check("a * pibar^(kn) = pi^n  (A pibar^(kn) = pi^n p^(kn))",
          cd.mul(A, cd.power(pibar, k * n)) == (cd.power(pi, n)[0] * den, cd.power(pi, n)[1] * den), True)
    rec["ord_a_v_pi"] = n
    rec["ord_a_v_pibar"] = -k * n
    # (3)
    Y = cd.power(pibar, k)
    num = cd.sub(cd.power(pibar, k * n), cd.power(pi, n))  # numerator of 1 - a
    Nnum = abs(cd.norm(num))
    check("p does not divide N(pibar^(kn) - pi^n)", Nnum % p != 0, True)
    check("7 does not divide N(a) = p^(n - kn)", p % 7 != 0, True)
    check("7 does not divide N(pibar^(kn) - pi^n)", Nnum % 7 != 0, True)
    # (4) cyclotomic factorization
    divisors = [d for d in range(1, n + 1) if n % d == 0]
    factors = {d: hom_cyclotomic(d, pi, Y) for d in divisors}
    prod = cd.ONE
    for d in divisors:
        prod = cd.mul(prod, factors[d])
    check("prod_{d|n} Phi_d(pi, pibar^k) = pi^n - pibar^(kn)", prod, cd.sub(cd.power(pi, n), cd.power(Y, n)))
    norms = {d: abs(cd.norm(factors[d])) for d in divisors}
    tot = 1
    for d in divisors:
        tot *= norms[d]
    check("product of the norms = N(numerator)", tot, Nnum)
    # Two factors can share a place only above a prime dividing n.  A common prime factor of two norms
    # may lie under different places when it splits, so the places are compared, not the norms.
    bad_common = []
    gcd_report = {}
    for i, d1 in enumerate(divisors):
        for d2 in divisors[i + 1:]:
            g = gcd(norms[d1], norms[d2])
            qs_ = [q for q in range(2, 10**6) if g % q == 0 and cd.is_prime(q)]
            rest = g
            for q in qs_:
                rest //= q ** cd.val(rest, q)
            assert rest == 1, "gcd with a large prime factor: extend the search"
            gcd_report[f"{d1},{d2}"] = qs_
            for q in qs_:
                if n % q == 0:
                    continue
                if q % 5 in (1, 4):  # split: compare the two places
                    r = cd.tonelli(5, q)
                    for root in {r, (q - r) % q}:
                        if cd.residue(factors[d1], root, q) == 0 and cd.residue(factors[d2], root, q) == 0:
                            bad_common.append((d1, d2, q, root))
                else:  # inert or ramified: one place
                    bad_common.append((d1, d2, q))
    rec["pairwise_norm_gcd_primes"] = gcd_report
    check("two factors share a place only above a prime dividing n", bad_common, [])
    rec["factor_norm_digits"] = {str(d): len(str(norms[d])) for d in divisors}
    small_bound = 0
    large = []
    for d in divisors:
        b = cd.kth_root_floor(norms[d], 7)
        if b <= 10**7:
            small_bound = max(small_bound, b)
        else:
            large.append(d)
    plist = cd.primes_up_to(max(small_bound, 100))
    seventh = {}
    for d in divisors:
        if d in large:
            continue
        b = cd.kth_root_floor(norms[d], 7)
        q_at, e_at, offenders = cd.max_prime_exponent(norms[d], plist, max(small_bound, 100), b, report=True)
        offenders = [q for q in offenders if q != 2]  # the place above 2 is not selected (treated below)
        seventh[d] = {"bound": b, "max_exponent": [q_at, e_at], "offenders": offenders, "method": "python"}
        check(f"N(Phi_{d}): no seventh power of an odd prime (primes up to {b})", offenders, [])
    if large:
        lb = max(cd.kth_root_floor(norms[d], 7) for d in large)
        planted_q = lb  # the largest prime not above the bound
        while not cd.is_prime(planted_q):
            planted_q -= 1
        rec["sieve_planted_prime"] = planted_q
        planted = norms[large[0]] * planted_q ** 7
        divs, count = sieve_large([norms[d] for d in large], lb, threads, planted)
        check("sieve control: the planted prime is found", planted_q in divs[len(large)], True)
        rec["sieve_count_primes"] = count
        rec["sieve_bound"] = lb
        for i, d in enumerate(large):
            b = cd.kth_root_floor(norms[d], 7)
            exps = {q: cd.val(norms[d], q) for q in divs[i] if q <= b}
            offenders = [q for q, e in exps.items() if e >= 7 and q != 2]
            seventh[d] = {"bound": b, "prime_divisors_up_to_bound": exps, "offenders": offenders,
                          "method": "C sieve", "primes_enumerated": count}
            check(f"N(Phi_{d}): no seventh power of an odd prime (primes up to {b}, C sieve)", offenders, [])
    rec["seventh_power_check"] = {str(d): v for d, v in seventh.items()}
    for q in (2, 3):
        vq = cd.val(Nnum, q) if Nnum % q == 0 else 0
        rec[f"v_{q}(N(numerator))"] = vq
        check(f"{q} is inert in Q(sqrt5)", q % 5 in (2, 3), True)
        check(f"N(numerator): even valuation at the inert prime {q}", vq % 2, 0)
        if q == 3:
            check("order of 1 - a at the place above 3 is prime to 7", (vq // 2) % 7 != 0 or vq == 0, True)
        if q == 2:
            # not selected; the pole of j = 256 (a^2-a+1)^3 / (a^2 (a-1)^2) there has order 2 ord(1-a) - 8
            ord2 = vq // 2
            rec["ord_1_minus_a_above_2"] = ord2
            rec["pole_order_j_above_2"] = 2 * ord2 - 8
            check("above 2 (not selected): order of 1 - a and pole order of j prime to 7",
                  (ord2 % 7 != 0, (2 * ord2 - 8) % 7 != 0), (True, True))
    # (5) orbit comparisons, in Q(sqrt5)
    aq = (F(A[0], den), F(A[1], den))
    abar = (aq[0], -aq[1])
    one = (F(1), F(0))
    oma = qs(one, aq)
    orbit = {
        "abar == a": abar == aq,
        "abar == 1/a": abar == qinv(aq),
        "abar == 1-a": abar == oma,
        "abar == 1/(1-a)": abar == qinv(oma),
        "abar == a/(a-1)": abar == qm(aq, qinv(qs(aq, one))),
        "abar == (a-1)/a": abar == qm(qs(aq, one), qinv(aq)),
    }
    for key, v in orbit.items():
        check(f"orbit comparison {key}", v, False)
    # (6)
    T1, T2 = 2 * n, 2 * k * n
    check("Tate orders 2n, 2kn prime to 7", (T1 % 7 != 0, T2 % 7 != 0), (True, True))
    witness = None
    for q in range(11, 4000):
        if not cd.is_prime(q) or q % 5 not in (1, 4) or q == p or q == 7:
            continue
        r = cd.tonelli(5, q)
        for root in sorted({r, (q - r) % q}):
            av = cd.residue(A, root, q) * pow(den % q, -1, q) % q
            if av in (0, 1):
                continue
            ap = -sum(cd.legendre(x * (x - 1) * (x - av), q) for x in range(q))
            assert ap * ap <= 4 * q
            dd = (ap * ap - 4 * q) % 7
            if dd != 0 and dd not in {1, 2, 4}:
                witness = (q, root, ap, dd)
                break
        if witness:
            break
    check("mod-7 witness: Frobenius characteristic polynomial irreducible", witness is not None, True)
    rec["mod7_witness"] = list(witness or ())
    # (7) profile
    prof = []
    for T in (T1, T2):
        e = 105 // gcd(105, T)
        check(f"Tate order {T}: qOrd = e T / 14 is an integer", (e * T) % 14, 0)
        prof.append((e, e - 1, e * T // 14, F(T, 14)))
        check(f"Tate order {T}: tame, e <= p - 2", e <= p - 2, True)
    (e1, D1, q1, r1), (e2, D2, q2, r2) = prof
    rec.update({"e_b1": e1, "D_b1": D1, "qOrd_b1": q1, "rho_b1": str(r1),
                "e_b2": e2, "D_b2": D2, "qOrd_b2": q2, "rho_b2": str(r2)})
    # (8) gaps (units of log p)
    beta = (F(D1, e1) + F(D2, e2)) / 2
    delta = r2 - r1
    gaps = [j * j * delta * (F(1, 2) - F(1, 2**j)) - (j + 1) * beta - 1 for j in (1, 2, 3)]
    avg = sum(gaps) / 3
    final = avg - (beta + 1) / 7
    union = [-(j * j) * (r1 + delta * F(1, 2**j)) for j in (1, 2, 3)]
    stepv = [(j + 1) * beta - j * j * (r1 + r2) / 2 + 1 for j in (1, 2, 3)]
    check("gap_j = union_j - stepv_j", gaps, [u - s for u, s in zip(union, stepv)])
    procession = sum(stepv) / 3
    final_display = F(L + 1, 4) * ((1 + F(4, L)) * beta - F(1, 6) * (T1 + T2) / 2 + F(4, L))
    check("final display - procession bound = (betabar + 1)/7", final_display - procession, (beta + 1) / 7)
    rec.update({"betabar": str(beta), "rho_gap": str(delta), "union_lower_bounds": [str(x) for x in union],
                "stepv_label_bounds": [str(x) for x in stepv], "gaps": [str(x) for x in gaps],
                "average_gap": str(avg), "procession_bound": str(procession),
                "final_display": str(final_display), "excess_over_final_display": str(final)})
    check("label 3: gap > 0 (weighted average upper bound of Step (v) exceeded)", gaps[2] > 0, True)
    check("average over labels: excess over the final display > 0", final > 0, True)
    lam = 9 * r2
    dI = 3 * F(D1, e1) + F(D2, e2)
    coef = -lam + dI + 1 + ceil(9 * r1)
    rec["summand_collision_coefficient_j3"] = str(coef)
    check("summand (b1,b1,b1,b2), j = 3: -lambda + d_I + 1 + ceil(9 rho1) < 0", coef < 0, True)
    # (9) field of a tower
    check("n even and kn even, so sqrt(a) = pi^(n/2) / pibar^(kn/2) lies in F0", (n % 2, (k * n) % 2), (0, 0))
    rec["tower_same_profile"] = (n % 2 == 0 and (k * n) % 2 == 0)
    rec["checks_total"] = len(LOG)
    rec["checks_failed"] = list(FAIL)
    rec["log"] = list(LOG)
    print(f"p = {p}, pi = {pi[0]} + {pi[1]}*sqrt5, a = pi^{n} / pibar^{k * n}")
    print("\n".join(LOG))
    for key in ("e_b1", "D_b1", "qOrd_b1", "rho_b1", "e_b2", "D_b2", "qOrd_b2", "rho_b2", "factor_norm_digits",
                "pairwise_norm_gcd_primes", "ord_1_minus_a_above_2", "pole_order_j_above_2", "sieve_planted_prime",
                "sieve_bound", "sieve_count_primes", "v_2(N(numerator))", "v_3(N(numerator))", "mod7_witness",
                "betabar", "rho_gap", "union_lower_bounds", "stepv_label_bounds", "gaps", "average_gap",
                "procession_bound", "final_display", "excess_over_final_display",
                "summand_collision_coefficient_j3", "tower_same_profile"):
        print(f"  {key}: {rec.get(key)}")
    for d, v in seventh.items():
        print(f"  seventh-power check Phi_{d}: bound {v['bound']}, method {v['method']}, offenders {v['offenders']}")
    if out:
        with open(out, "w") as fh:
            json.dump(rec, fh, indent=2, default=str)
            fh.write("\n")
    print("OK" if not FAIL else f"FAIL: {FAIL}")
    sys.exit(0 if not FAIL else 1)


if __name__ == "__main__":
    main()
