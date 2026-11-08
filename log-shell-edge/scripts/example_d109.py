"""Example 7.3: the six bad places of the explicit initial Theta-datum D109.

The place data (prime, ramification index e, orders of a and 1 - a, ord of q, membership in V^bad_mod) are read from
the program iut_compute.py of the walkthrough (folder iut-walkthrough/program of the same repository); it needs sympy.
The datum has E_0: y^2 = x(x-1)(x-a) over F_0 = Q(i), F = F_0(sqrt(-1), E_0[15]) and K = F(E_0[7]) (catalogue,
Section 3).  At each bad place w the reduction is split multiplicative (the tangents at the node are +-sqrt(-1)
when ord_w(a) > 0, with p = 1 mod 4, and +-1 when ord_w(1 - a) > 0), so by Tate's uniformization
K_v = Q_p(mu_420, q^(1/105)).  Since ord_w(q) is prime to 105, K_v is totally ramified of degree 105 over the
unramified extension Q_p(mu_420): e = 105 and f = the order of p modulo 420.  For the place above 109 used in the
table of Section 5 of "Three tiers of indeterminacy" the script also prints the exponent lo(m) used in the proof of
Theorem 7.1.

Usage:  python3 example_d109.py [path to iut-walkthrough/program]
"""
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
PROGRAM = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, '..', '..', 'iut-walkthrough', 'program')
sys.path.insert(0, PROGRAM)
import iut_compute as ic


def order_mod(a, m):
    k, x = 1, a % m
    while x != 1 % m:
        x, k = x * a % m, k + 1
    return k


def ceil(x):
    return -((-x.numerator) // x.denominator)


dt = ic.InitialThetaData('D109', factor_seconds=1)
print(f'D109: l = {dt.ell}, l* = {dt.ell_star}; the places of V^bad_mod (walkthrough program):')
print('prime | ord_w(a) | ord_w(1-a) | ord_w(q) | p mod 4 | e | f = ord of p mod 420 | [K_v:Q_p] | small')
from math import gcd
for v in dt.bad:
    p, e = v.prime, v.e
    oa, o1 = v.ord_a or 0, v.ord_1ma or 0
    oq = 2 * oa if oa > 0 else 2 * o1                  # ord_w(j) = -2 ord_w(a) or -2 ord_w(1 - a)
    assert v.weight == Fr(1, 2) and oq == v.ord_q_w and (oa > 0) != (o1 > 0)
    assert p % 4 == 1 or oa == 0                        # split multiplicative reduction over F_0,w = Q_p
    assert gcd(oq, 105) == 1 and e == 105 // gcd(105, oq)
    f = order_mod(p, 420)
    small = e <= p - 2
    assert small
    print(f'{p} | {oa} | {o1} | {oq} | {p % 4} | {e} | {f} | {e * f} ({"even" if e * f % 2 == 0 else "odd"}) | {small}')
v = next(w for w in dt.bad if w.prime == 109)
e, rq = v.e, Fr(v.rq)
print(f'place above 109: e = {e}, ord_p(qbb) = {rq}')
print('j | lambda | m = e*lambda | m mod e | lo(m) | lo(m)/e | ceil(lambda) - (e-1)/e')
for j in range(1, dt.ell_star + 1):
    lam = j * j * rq
    m = lam * e
    assert m.denominator == 1 and lam.denominator != 1
    m = int(m)
    lo = e * ((m - 1) // e) + 1
    assert Fr(lo, e) == ceil(lam) - Fr(e - 1, e)
    print(f'{j} | {lam} | {m} | {m % e} | {lo} | {Fr(lo, e)} | {ceil(lam) - Fr(e - 1, e)}')
