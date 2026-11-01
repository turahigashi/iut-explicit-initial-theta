#!/usr/bin/env python3
"""Per-component comparisons in Step (v) of IUT IV, Thm 1.10, for the explicit data.

For a rational prime p and the places of F_mod above it, each place has
  e   : ramification index of K at the place (tame with e <= p - 2, checked),
  rho : ord_p of the 2l-th root of q at the place (0 at a good place),
  d   = (e - 1)/e : the different exponent (ord_p normalized).
For a stage j (1 <= j <= l*) and a tuple v = (v_0, ..., v_j) of places, Step (v) uses
  bound(v) = -j^2 rho(v_j) + d_I + 1,   d_I = sum_i d(v_i)          (units of log p).
Readings of the note (all conditional):
  (L)      label permutations fixing 0 act on possible images before the hull is taken;
  (L^0)    the same, with permutations moving 0 also admitted;
  (M_b)    q_b^{j^2} times a lattice containing 1 is a possible image at a bad place b;
  (M_g)    at a good place the theta value is a unit.
Elements and lower bounds for the hull component (margin = hull bound - bound(v); > 0 means
non-containment):
  BB    (needs two bad places with rho_s < rho_l, j >= 2, permutation fixing 0):
        y = theta_{b_s} at a label i0 in 1..j-1, 1 elsewhere; hull >= -ceil(j^2 rho_s)  [(M_b), (L)]
  GB    (good to bad, unit): y = 1;                 hull >= 0                        [(M_g), (L)]
  GB_L  (good to bad, the log-unit lattice);        hull >= -sum_i 1/e_i             [(SA) of First-full, Thm 8.1]
For j = 1 the good-to-bad comparison needs a permutation moving the label 0, i.e. (L^0).
The maximizing tuples are explicit: v_j at the place with the larger rho, the theta factor at the
source place, all other factors at a place of least d (a good place if there is one).
"""
from fractions import Fraction as Fr
from itertools import product
from math import ceil

DATA = {
    # name: (l, p, [(place, kind, e, rho)])
    'D_211':  (7, 211,      [('g', 'good', 1, Fr(0)), ('b', 'bad', 105, Fr(29, 7))]),
    'D_109':  (7, 109,      [('g', 'good', 1, Fr(0)), ('b', 'bad', 105, Fr(29, 7))]),
    'D_2':    (7, 30965771, [('b1', 'bad', 105, Fr(1, 7)), ('b2', 'bad', 35, Fr(6, 7))]),
    'D_3':    (7, 30965771, [('b1', 'bad', 35, Fr(6, 7)), ('b2', 'bad', 7, Fr(30, 7))]),
    'D_18':   (7, 30965771, [('g', 'good', 1, Fr(0)), ('b', 'bad', 35, Fr(18, 7))]),
    'D_15':   (7, 30965819, [('g', 'good', 1, Fr(0)), ('b', 'bad', 7, Fr(15, 7))]),
}
LEVELS_2357 = (89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157)
for _l in LEVELS_2357:
    DATA[f'D_2357(l={_l})'] = (_l, 2357, [('g', 'good', 1, Fr(0)), ('b', 'bad', 15 * _l, Fr(472, _l))])


def d(e):
    return Fr(e - 1, e)


def margins(l, p, places, j):
    """Closed-form maxima over tuples at stage j. Returns {kind: (margin, tuple)}."""
    assert all(e <= p - 2 for _, _, e, _ in places), 'I* nonempty: (1) does not apply'
    dmin_place = min(places, key=lambda x: d(x[2]))
    res = {}
    bads = [x for x in places if x[1] == 'bad']
    goods = [x for x in places if x[1] == 'good']
    if goods and bads:
        b = max(bads, key=lambda x: x[3])
        g = goods[0]
        tup = [g] * j + [b]
        bound = -j * j * b[3] + sum(d(x[2]) for x in tup) + 1
        res['GB'] = (Fr(0) - bound, tup)
        res['GB_L'] = (-sum(Fr(1, x[2]) for x in tup) - bound, tup)
    if len(bads) >= 2 and j >= 2:
        bl = max(bads, key=lambda x: x[3])
        bs = min(bads, key=lambda x: x[3])
        if bs[3] < bl[3]:
            tup = [dmin_place] + [bs] + [dmin_place] * (j - 2) + [bl]
            bound = -j * j * bl[3] + sum(d(x[2]) for x in tup) + 1
            res['BB'] = (-ceil(j * j * bs[3]) - bound, tup)
    return res


def brute(l, p, places, j):
    """Enumerate all tuples (small j only) to cross-check margins()."""
    res = {}
    for tup in product(places, repeat=j + 1):
        vj = tup[j]
        bound = -j * j * vj[3] + sum(d(x[2]) for x in tup) + 1
        for i0 in range(0, j):
            src = tup[i0]
            cands = []
            if src[1] == 'bad' and vj[1] == 'bad' and src[3] < vj[3] and i0 >= 1:
                cands.append(('BB', -ceil(j * j * src[3])))
            if src[1] == 'good' and vj[1] == 'bad':
                cands.append(('GB', Fr(0)))
                cands.append(('GB_L', -sum(Fr(1, x[2]) for x in tup)))
            for key, hull in cands:
                m = hull - bound
                if key not in res or m > res[key]:
                    res[key] = m
    return res


def fmt(x):
    return f'{x.numerator}' if x.denominator == 1 else f'{x.numerator}/{x.denominator}'


if __name__ == '__main__':
    for name, (l, p, places) in DATA.items():
        ls = (l - 1) // 2
        rhos = {x[3] for x in places}
        print(f'== {name}  l={l} p={p}  places={[(x[0], x[1], x[2], fmt(x[3])) for x in places]}  '
              f'rho constant above p: {len(rhos) == 1}')
        stages = range(1, ls + 1) if ls <= 3 else (1, 2, 3, ls)
        for j in stages:
            for key, (m, tup) in sorted(margins(l, p, places, j).items()):
                flag = 'NON-CONTAINMENT' if m > 0 else 'contained'
                print(f'  j={j:2d} {key:5s} tuple={tuple(x[0] for x in tup) if len(tup) <= 6 else "(g,...,g,b)"}'
                      f' margin={fmt(m)} ({float(m):.4f})  {flag}')
        if name.startswith('D_2357'):
            # first stage at which the lattice version is positive, and first for the unit version
            first = {k: next((j for j in range(1, ls + 1) if margins(l, p, places, j)[k][0] > 0), None)
                     for k in ('GB', 'GB_L')}
            print(f'  first positive stage: {first}')
    # cross-checks: closed form = brute force for l = 7 data
    for name in ('D_211', 'D_109', 'D_2', 'D_3', 'D_18', 'D_15'):
        l, p, places = DATA[name]
        for j in (1, 2, 3):
            mf = {k: v[0] for k, v in margins(l, p, places, j).items()}
            mb = brute(l, p, places, j)
            assert mf == mb, (name, j, mf, mb)
    # values published earlier, and further consistency checks
    l, p, pl = DATA['D_2']
    tup = [pl[0], pl[0], pl[0], pl[1]]
    bnd = -9 * pl[1][3] + sum(d(x[2]) for x in tup) + 1
    assert bnd == Fr(-97, 35) and -2 - bnd == Fr(27, 35)                 # [Note, Thm 5]
    l, p, pl = DATA['D_211']
    for j, want in ((1, Fr(8, 7)), (2, Fr(88, 7))):                        # [First]: 8/7 (j = 1), 88/7 (j = 2)
        assert margins(l, p, pl, j)['GB_L'][0] == want
    l, p, pl = DATA['D_3']
    tup = [pl[0], pl[0], pl[0], pl[1]]
    bnd = -9 * pl[1][3] + sum(d(x[2]) for x in tup) + 1
    assert bnd == Fr(-169, 5) and -ceil(9 * pl[0][3]) - bnd == Fr(129, 5)  # D_3, tuple (b1, b1, b1, b2), j = 3
    l, p, pl = DATA['D_18']
    assert margins(l, p, pl, 2)['GB'][0] == Fr(291, 35)    # D_18, j = 2
    print('CROSS-CHECKS: closed form = enumeration (l = 7, j <= 3); 27/35 [Note], 8/7 and 88/7 [First] reproduced; 129/5, 291/35 consistent')
