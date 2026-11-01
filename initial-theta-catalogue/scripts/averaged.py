#!/usr/bin/env python3
"""Weighted-average comparisons at p in Step (v) of IUT IV, Thm 1.10 (displays on pp. 28-29).

Applies when p > e*_mod * l (so the s^<= terms vanish, IV pp. 23, 25) and the places of F_mod above p
have degree one, hence equal weights. Uses the closed forms of catalogue.py for the places.
  displayed average bound at stage j : B_j = (j+1) dbar - j^2 rhobar + 1
  displayed final bound at p          : F   = (l+1)/4 * ((1 + 4/l) dbar - mbar/6 + 4/l),  mbar = 2 l rhobar
  lower bound for the hull at a tuple v: -min_t c(v_t), t over the labels a permutation may bring to j:
       t in 1..j  (permutations fixing 0, reading (L))  or  t in 0..j (all labels, reading (L^0));
       c(b) = ceil(j^2 rho_b) (rounded, from (1.3)) or j^2 rho_b (identity components); c(g) = 0 (reading (M_g)).
"""
from fractions import Fraction as Fr
from itertools import product
from math import ceil
from catalogue import DATA, d

EMOD_STAR_L7 = 7741440   # e*_mod * l for a quadratic F_mod and l = 7 (IV p. 22)


def averaged(l, p, places, labels='fix0', rounded=True):
    assert p > EMOD_STAR_L7 and l == 7
    ls = (l - 1) // 2
    n = len(places)
    dbar = sum(d(e) for _, _, e, _ in places) / n
    rhobar = sum(r for _, _, _, r in places) / n
    L, B = [], []
    for j in range(1, ls + 1):
        ts = range(1, j + 1) if labels == 'fix0' else range(0, j + 1)
        def c(pl):
            if pl[1] == 'good':
                return Fr(0)
            x = j * j * pl[3]
            return Fr(ceil(x)) if rounded else x
        tot = Fr(0)
        for tup in product(places, repeat=j + 1):
            tot += -min(c(tup[t]) for t in ts)
        L.append(tot / n ** (j + 1))
        B.append((j + 1) * dbar - j * j * rhobar + 1)
    Lbar = sum(L) / ls
    F = Fr(l + 1, 4) * ((1 + Fr(4, l)) * dbar - 2 * l * rhobar / 6 + Fr(4, l))
    return L, B, Lbar, F


def fmt(x):
    return f'{x.numerator}' if x.denominator == 1 else f'{x.numerator}/{x.denominator}'


if __name__ == '__main__':
    for name in ('D_2', 'D_3', 'D_18', 'D_15'):
        l, p, places = DATA[name]
        for labels, rounded in (('fix0', True), ('fix0', False), ('all', False)):
            L, B, Lbar, F = averaged(l, p, places, labels, rounded)
            per = ', '.join(f'j={j+1}: {fmt(L[j])} vs {fmt(B[j])} (margin {fmt(L[j]-B[j])})' for j in range(3))
            print(f'{name:7s} labels={labels:4s} rounded={str(rounded):5s} | {per} | '
                  f'average {fmt(Lbar)} vs final {fmt(F)} (margin {fmt(Lbar - F)} = {float(Lbar - F):.4f})')
    # cross-checks: Table 3 and Remark 5 of the note
    L, B, Lbar, F = averaged(*DATA['D_3'], 'fix0', True)
    assert L == [-3, Fr(-15, 2), Fr(-95, 8)] and B == [Fr(9, 35), Fr(-229, 35), Fr(-647, 35)]
    assert L[2] - B[2] == Fr(1851, 280) and F == Fr(-1956, 245) and Lbar - F == Fr(3089, 5880)
    L, B, Lbar, F = averaged(*DATA['D_3'], 'fix0', False)
    assert L[2] - B[2] == Fr(242, 35) and Lbar - F == Fr(241, 245)
    L, B, Lbar, F = averaged(*DATA['D_18'], 'fix0', True)
    assert B == [Fr(24, 35), Fr(-94, 35), Fr(-302, 35)] and F == Fr(-816, 245) and Lbar - F == Fr(2687, 2940)
    L, B, Lbar, F = averaged(*DATA['D_18'], 'fix0', False)
    assert Lbar - F == Fr(1059, 980)
    L, B, Lbar, F = averaged(*DATA['D_15'], 'all', False)
    assert Lbar == Fr(-15, 16) and sum(B) / 3 == Fr(-19, 7) and F == Fr(-123, 49)
    assert Lbar + Fr(19, 7) == Fr(199, 112) and Lbar - F == Fr(1233, 784)
    print('CROSS-CHECKS: D_3 1851/280, 3089/5880, 241/245; D_18 2687/2940, 1059/980; D_15 1233/784 reproduced')
