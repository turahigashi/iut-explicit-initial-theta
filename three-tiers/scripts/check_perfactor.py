"""k = Q_5(sqrt5), pi^2 = 5, e = 2.  T = k (x) k (tensor coordinates, basis x_a (x) x_b, x_0 = 1, x_1 = pi).
Compute, for theta = 1 (x) pi^m, the hull (componentwise min pi-valuation in k x k) of the union of images of
theta*(R_I)~ under (a) per-factor maps g0 (x) g1 with g_i in GL(I) (I = pi^{-1}O, the log-shell), random samples;
(b) the exact value for all of GL((x)I) (orbit lemma): valuation 2*ceil(m/2) - 2 in each component.
Also report: IV container hull valuation 2*floor(m/2) - 2, and the region itself: m.
"""
from fractions import Fraction as F
import random, math
random.seed(20261108)
P = 5
def v5(x):
    x = F(x)
    if x == 0: return 10**9
    n, d, c = x.numerator, x.denominator, 0
    while n % P == 0: n //= P; c += 1
    while d % P == 0: d //= P; c -= 1
    return c
# element of k: (a, b) = a + b*pi.  pi-adic valuation: v_pi(a + b pi) = min(2 v5(a), 2 v5(b) + 1)
def vpi(z):
    a, b = z
    return min(2 * v5(a) if a != 0 else 10**9, 2 * v5(b) + 1 if b != 0 else 10**9)
def kmul(u, w): return (u[0]*w[0] + 5*u[1]*w[1], u[0]*w[1] + u[1]*w[0])
def sigma(u): return (u[0], -u[1])
# tensor element: dict {(a,b): coeff} over basis x_a (x) x_b
X = [(F(1), F(0)), (F(0), F(1))]   # x_0 = 1, x_1 = pi as elements of k
def to_kxk(t):
    """x(x)y -> (x*y, x*sigma(y)), extended linearly"""
    c1 = (F(0), F(0)); c2 = (F(0), F(0))
    for (a, b), c in t.items():
        p1 = kmul(X[a], X[b]); p2 = kmul(X[a], sigma(X[b]))
        c1 = (c1[0] + c * p1[0], c1[1] + c * p1[1]); c2 = (c2[0] + c * p2[0], c2[1] + c * p2[1])
    return c1, c2
def tmul(s, t):
    out = {}
    for (a, b), c in s.items():
        for (cc, d), e in t.items():
            xa = kmul(X[a], X[cc]); xb = kmul(X[b], X[d])   # products in each factor, as a + b pi
            for i, ci in enumerate(xa):
                for j, cj in enumerate(xb):
                    if ci and cj:
                        out[(i, j)] = out.get((i, j), F(0)) + c * e * ci * cj
    return out
def tadd(*ts):
    out = {}
    for t in ts:
        for k_, v in t.items(): out[k_] = out.get(k_, F(0)) + v
    return out
def tscale(c, t): return {k_: c * v for k_, v in t.items()}
one = {(0, 0): F(1)}
pi_x_1 = {(1, 0): F(1)}
one_x_pi = {(0, 1): F(1)}
pi_x_piinv = tscale(F(1, 5), {(1, 1): F(1)})          # pi (x) pi^{-1} = (1/5) pi (x) pi
e1 = tscale(F(1, 2), tadd(one, pi_x_piinv)); e2 = tscale(F(1, 2), tadd(one, tscale(F(-1), pi_x_piinv)))
assert to_kxk(e1) == ((1, 0), (0, 0)) and to_kxk(e2) == ((0, 0), (1, 0))
normal_basis = [e1, tmul(pi_x_1, e1), e2, tmul(pi_x_1, e2)]   # Z_5-basis of (R_I)~ = O x O
# per-factor maps: g in GL(I), I = span{1, pi^{-1}} = span{(1,0), (0,1/5)} in basis {1, pi}
Pm = [[F(1), F(0)], [F(0), F(1, 5)]]                       # columns: basis of I in coordinates (a, b)
Pinv = [[F(1), F(0)], [F(0), F(5)]]
def matmul(A, B): return [[sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def rand_gl2_z5():
    while True:
        h = [[F(random.randint(-30, 30)) for _ in range(2)] for _ in range(2)]
        det = h[0][0] * h[1][1] - h[0][1] * h[1][0]
        if det != 0 and v5(det) == 0: return h
def g_on_k(g, u):  # u = (a, b) coordinates in basis {1, pi}
    return (g[0][0] * u[0] + g[0][1] * u[1], g[1][0] * u[0] + g[1][1] * u[1])
def apply_pf(g0, g1, t):
    out = {}
    for (a, b), c in t.items():
        ga = g_on_k(g0, X[a]); gb = g_on_k(g1, X[b])
        for i, ci in enumerate(ga):
            for j, cj in enumerate(gb):
                if ci and cj: out[(i, j)] = out.get((i, j), F(0)) + c * ci * cj
    return out
for m in range(0, 9):
    theta = {(0, m % 2): F(5) ** (m // 2)}                  # 1 (x) pi^m = 5^{m//2} * 1 (x) pi^{m%2}
    region = [tmul(theta, b) for b in normal_basis]
    vreg = [min(vpi(to_kxk(t)[c]) for t in region) for c in (0, 1)]
    best = [10**9, 10**9]
    for _ in range(400):
        g0 = matmul(matmul(Pm, rand_gl2_z5()), Pinv); g1 = matmul(matmul(Pm, rand_gl2_z5()), Pinv)
        for t in region:
            im = apply_pf(g0, g1, t)
            c1, c2 = to_kxk(im)
            best[0] = min(best[0], vpi(c1)); best[1] = min(best[1], vpi(c2))
    lam = F(m, 2)
    exactL = 2 * math.ceil(lam) - 2; cont = 2 * math.floor(lam) - 2
    print(f"m={m} lambda={str(lam):>3}  region v={vreg}  per-factor sampled hull v={best}  "
          f"exact(all phi) v={exactL}  IV container v={cont}")
