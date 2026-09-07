#!/usr/bin/env python3
"""Check the explicit Hensel/CRT arithmetic in Appendix D for three N values.

This standard-library program verifies the complete CRT conditions and local
orders for N = 1, 106, 211.  It does not prove the existence of infinitely many
seventh-power-free values, certify any individual sample as seventh-power-free,
or verify the geometric constructions or hypothesis (SA).  The infinite-family
argument is the mathematical counting proof in Appendix D.

Run from the project directory:
    python3 scripts/check_crt_family.py
"""

import json
from math import gcd


if not __debug__:
    raise SystemExit("Run with assertions enabled (do not use python -O).")

P = 211


def valuation(n, p):
    """Return the exponent of p in a nonzero integer n."""
    assert n != 0 and p > 1
    exponent = 0
    while n % p == 0:
        n //= p
        exponent += 1
    return exponent


def crt(congruences):
    """Return the least nonnegative solution and the product modulus."""
    solution, modulus = 0, 1
    for residue, next_modulus in congruences:
        assert gcd(modulus, next_modulus) == 1
        digit = ((residue - solution) * pow(modulus, -1, next_modulus)) % next_modulus
        solution += modulus * digit
        modulus *= next_modulus
        assert 0 <= solution < modulus
    assert all((solution - residue) % m == 0 for residue, m in congruences)
    return solution, modulus


def check_family(N):
    assert N >= 1 and N % 105 == 1

    # Start at the root 65 modulo p and lift through modulus p^(N+1).
    # The extra digit is required to obtain order exactly N.
    root, modulus = 65, P
    assert (root * root - 5) % modulus == 0
    for _ in range(N):
        error = (root * root - 5) // modulus
        digit = (-error * pow(2 * root, -1, P)) % P
        root += modulus * digit
        modulus *= P
        assert 0 <= root < modulus
        assert (root * root - 5) % modulus == 0
    assert modulus == P ** (N + 1) and root % P == 65

    congruences = [
        (root + P ** N, modulus),
        (0, 8),
        (2, 3),
        (2, 5),
        (2, 19),
        (6, 11),
    ]
    A0, M = crt(congruences)
    assert M == 25080 * P ** (N + 1)

    # One positive sample in the progression, not a certified power-free value.
    sample_x = 1
    A = A0 + M * sample_x
    assert all((A - residue) % m == 0 for residue, m in congruences)
    assert (A - root - P ** N) % P ** (N + 1) == 0
    first_norm = A * A - 5
    second_norm = (A - 1) ** 2 - 5
    f_value = first_norm * second_norm
    assert f_value > 0 and f_value % P ** N == 0
    G = f_value // P ** N

    assert valuation(first_norm, P) == N
    assert valuation(second_norm, P) == 0
    assert valuation(f_value, P) == N
    assert (first_norm // P ** N) % P == 130
    assert second_norm % P == 82
    assert G % P == 110
    assert (A + 65) % P == 130
    assert (130 * 130 - 130 + 1) % P == 102

    v2G = valuation(G, 2)
    assert v2G == 2
    # The excluded primes are read off the congruence moduli rather than retyped:
    # the list was a bare tuple and any entry could be perturbed unnoticed
    # (mutation test, 2026-09-07).
    odd_moduli = sorted({m for _, m in congruences if m % 2 and m != modulus})
    assert odd_moduli == [3, 5, 11, 19], odd_moduli
    assert all(G % q != 0 for q in (*odd_moduli, P))
    assert gcd(2 * N, 105) == 1

    return {
        "N": N,
        "hensel_modulus_exponent": N + 1,
        "hensel_root_mod_211": root % P,
        "all_six_CRT_conditions": "PASS",
        "A0_decimal_digits": len(str(A0)),
        "progression_modulus_is_25080_times_211_to_N_plus_1": True,
        "sample_x": sample_x,
        "v211_first_norm": valuation(first_norm, P),
        "v211_second_norm": valuation(second_norm, P),
        "v211_f": valuation(f_value, P),
        "v2_G": v2G,
        "G_mod211": G % P,
        "G_is_unit_at_3_5_11_19_211": True,
        "sample_G_seventh_power_free_certified": False,
    }


def main():
    results = [check_family(N) for N in (1, 106, 211)]
    print(json.dumps({
        "scope": "Finite Hensel/CRT and local-order checks only.",
        "samples": results,
        "infinite_existence_proof": "Appendix D; not established by these finite checks.",
        "individual_seventh_power_free_sample": "Not certified.",
    }, indent=2))
    print("PASS: all three samples satisfy the stated CRT and local-order conditions.")
    print("No individual sample has been certified seventh-power-free.")
    print("EXIT:0")


if __name__ == "__main__":
    main()
