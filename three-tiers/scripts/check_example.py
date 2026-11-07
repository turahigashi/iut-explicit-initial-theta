"""Brute-force check of the exact hull at a small place, in the smallest case.
k = Q_5(sqrt5), pi = sqrt5, e = 2, p = 5 (e <= p-2).  Packet T = k (x) k ~ k x k via
x(x)y -> (x*y, x*sigma(y)).  (R_I)~ = O x O.  R_I = O(x)O = {(u,v): u = v mod pi}.
Log-shell I = pi^{1-e} O = pi^{-1} O, so (x)I = pi^{-1}O (x) pi^{-1}O (a unit multiple of 5^{-1} R_I).
Work in coordinates: an element of k x k is a pair of elements a + b*pi (a,b in Q_5).
A Z_5-lattice is given by a 4x4 basis matrix over Q (5-adic content is what matters).

Claim (paper): for theta = pi^m in the factor 1, kappa = max{k : theta*(O x O) <= 5^k (x)I} = ceil(m/2),
so the span of all GL((x)I)-images is 5^ceil(lambda) (x)I, lambda = m/2.
We test kappa by linear algebra over Q with 5-adic valuations.
"""
from fractions import Fraction as F
import itertools

def v5(x):
    x = F(x)
    if x == 0: return 10**9
    n, d, c = x.numerator, x.denominator, 0
    while n % 5 == 0: n //= 5; c += 1
    while d % 5 == 0: d //= 5; c -= 1
    return c

# element of k = a + b*pi as vector (a,b); multiplication by pi: (a,b) -> (5b, a)
def mul_pi(v, n=1):
    a, b = v
    for _ in range(n): a, b = 5*b, a
    return (a, b)
def mul_mpi(v, n=1):  # multiplication by -pi (= sigma(pi))
    a, b = v
    for _ in range(n): a, b = -5*b, -a
    return (a, b)

# basis of O x O as Z_5-module, coordinates in Q^4: (a1,b1,a2,b2)
OxO = [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
# R = O(x)O = image of x(x)y: basis of O (x) O = {1(x)1, 1(x)pi, pi(x)1, pi(x)pi} ->
#   1(x)1 -> (1,1); 1(x)pi -> (pi, -pi); pi(x)1 -> (pi, pi); pi(x)pi -> (5, -5)
def emb(x, y):  # x,y in k as (a,b): x(x)y -> (x*y, x*sigma(y))
    def mul(u, w):  # (u0+u1 pi)(w0+w1 pi) = u0w0 + 5 u1w1 + (u0w1+u1w0) pi
        return (u[0]*w[0] + 5*u[1]*w[1], u[0]*w[1] + u[1]*w[0])
    sy = (y[0], -y[1])
    p1, p2 = mul(x, y), mul(x, sy)
    return (p1[0], p1[1], p2[0], p2[1])
one, pi = (1, 0), (0, 1)
R = [emb(a, b) for a in (one, pi) for b in (one, pi)]

def solve(B, v):
    """coordinates of v in basis B (4x4 over Q), Gaussian elimination"""
    n = 4
    M = [[F(B[j][i]) for j in range(n)] + [F(v[i])] for i in range(n)]
    for c in range(n):
        r = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[r] = M[r], M[c]
        piv = M[c][c]
        M[c] = [x / piv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] for i in range(n)]

def contained(gens, B, scale_v5):
    """is span_Z5(gens) inside 5^scale_v5 * span_Z5(B)?"""
    for g in gens:
        co = solve(B, g)
        if any(v5(c) < scale_v5 for c in co): return False
    return True

# theta*(O x O) for theta = pi^m placed in factor 1: theta = 1 (x) pi^m -> (pi^m, (-pi)^m)
def theta_OxO(m):
    out = []
    for b in OxO:
        x1, x2 = (b[0], b[1]), (b[2], b[3])
        y1 = mul_pi(x1, m); y2 = mul_mpi(x2, m)
        out.append((y1[0], y1[1], y2[0], y2[1]))
    return out

# (x)I = pi^{-1}O (x) pi^{-1}O, spanned by emb(pi^{-1} x_a, pi^{-1} x_b); pi^{-1} = pi/5
piinv_one = (F(0), F(1, 5)); piinv_pi = (F(1), F(0))      # pi^{-1}*1 = pi/5,  pi^{-1}*pi = 1
TI = [emb(a, b) for a in (piinv_one, piinv_pi) for b in (piinv_one, piinv_pi)]
def kappa(m):
    gens = theta_OxO(m)
    best = None
    for k in range(-10, 30):
        if contained(gens, TI, k): best = k               # gens inside 5^k * (x)I ?
    return best

import math
ok = True
for m in range(0, 13):
    lam = F(m, 2)
    kap = kappa(m)
    ceil_l = math.ceil(lam); floor_l = math.floor(lam)
    print(f"m={m:2d} lambda={str(lam):>4}  kappa={kap}  ceil={ceil_l}  floor={floor_l}  "
          f"container exponent floor -> gap kappa-floor = {kap - floor_l}")
    ok &= (kap == ceil_l)
print("kappa == ceil(lambda) for all m:", ok)
