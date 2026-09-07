#!/usr/bin/env python3
"""Exact finite checks for the Tate-degree normalization bridge.

These checks verify rational identities and finite tuple sums.  They do not
establish the source-admissibility hypothesis (SA), compute the actual hull,
or turn either SS approximation into a theorem about that hull.
"""
from fractions import Fraction as F
from itertools import product
import json


def ceil(q):
    return -(-q.numerator // q.denominator)


def main():
    if not __debug__:
        raise SystemExit("Run without -O: assertion checks must be enabled.")

    # An arbitrary finite-extension degree partition.  Each pair lists the
    # relative e and f above a base place; the local degree sums are identical.
    base_degree = 5
    base_places = [(1, 2, F(7)), (3, 1, F(0))]
    above = [[(1, 3), (3, 1)], [(2, 1), (1, 4)]]
    extension_degree = 6
    # The partition is arbitrary, but the sentence above claims the local degree
    # sums agree; that claim was not checked, so any entry could be perturbed and
    # the example silently stopped illustrating it (mutation test, 2026-09-07).
    assert sum(e * f for e, f, _ in base_places) == base_degree
    assert all(sum(e * f for e, f in blk) == extension_degree for blk in above)
    assert len(above) == len(base_places)
    before = sum(F(e * f, base_degree) * tau for e, f, tau in base_places)
    after = F(0)
    for (e, f, tau), partition in zip(base_places, above):
        assert sum(er * fr for er, fr in partition) == extension_degree
        for er, fr in partition:
            # v_w(q) = e_w * ord_p(q); log N(w)/log p = f_w.
            ew, fw = e * er, f * fr
            vwq = ew * tau
            after += vwq * fw / (base_degree * extension_degree)
    assert before == after

    # Raw IUT weights times the rank of each local tensor factor give the
    # product of base-field local degrees, after the displayed normalization.
    for k in range(1, 5):
        for t in product(range(2), repeat=k):
            d = [2, 3]
            relative = [6, 10]
            raw, rank, target = F(1, 5**k), 1, F(1, 5**k)
            for i in t:
                raw /= relative[i]
                rank *= d[i] * relative[i]
                target *= d[i]
            assert raw * rank == target

    stages = []
    native_slope = seed_slope = zero_fixed_slope = F(0)
    for j in (1, 2, 3):
        tuples = list(product((0, 1), repeat=j + 1))
        weights = [F(1, 2 ** (j + 1))] * len(tuples)
        assert sum(weights) == 1
        marginal = sum(w for w, t in zip(weights, tuples) if t[j])
        all_bad = sum(w for w, t in zip(weights, tuples) if all(t))
        except_zero_bad = sum(w for w, t in zip(weights, tuples) if all(t[1:]))
        assert marginal == F(1, 2)
        assert all_bad == F(1, 2 ** (j + 1))
        assert except_zero_bad == F(1, 2 ** j)
        native_slope += F(j * j, 21) * marginal
        seed_slope += F(j * j, 21) * all_bad
        zero_fixed_slope += F(j * j, 21) * except_zero_bad
        stages.append({"j": j, "tuples": len(tuples),
                       "bad_slot_weight": str(marginal),
                       "all_bad_weight": str(all_bad)})
    assert native_slope == F(1, 3)
    assert seed_slope == F(1, 16)
    assert zero_fixed_slope == F(1, 8)
    assert native_slope - seed_slope == F(13, 48)
    assert native_slope - F(1, 14) == F(11, 42)
    assert F(1, 14) - seed_slope == F(1, 112)

    samples = []
    for n in (1, 106, 211, 946):
        assert n % 105 == 1
        depth = sum(F(ceil(F(j*j*n, 7)), 3 * 2**(j+1)) for j in (1, 2, 3))
        assert depth == F(n, 16) + F(5, 48)
        lower = -F(53, 35) - depth
        samples.append({"N": n, "D_p/log_p": str(F(n)),
                        "bad_theta_order": str(F(n, 7)),
                        "Q_p/log_p": str(F(n, 14)), "lower/log_p": str(lower)})

    # Finite checks of the general formula (the proof uses the sum of squares).
    for ell in (3, 5, 7, 13, 29, 101):
        m = (ell - 1) // 2
        beta = sum(F(j*j, 2*ell*m) for j in range(1, m+1))
        assert beta == F(ell+1, 24)
    print(json.dumps({"scope": "Exact finite rational checks; SA not verified by this script",
                      "base_change_before": str(before), "base_change_after": str(after),
                      "stages": stages, "native_slope": str(native_slope),
                      "seed_slope": str(seed_slope),
                      "coefficient_difference": str(native_slope-seed_slope),
                      "SS_1_6_Tate_slope": "1/14", "samples": samples,
                      "status": "PASS"}, indent=2))


if __name__ == "__main__":
    main()
