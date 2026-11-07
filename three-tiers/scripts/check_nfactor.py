"""n-factor check for k = Q_5(sqrt5) (pi^2 = 5, e = 2, small since e <= p-2 = 3).
T = k^{(x) n} ~ k^{2^{n-1}}: x_0 (x) x_1 (x) ... (x) x_{n-1} -> ( x_0 * prod_i s_i(x_i) )_{s in {1,sigma}^{n-1}}.
(R_I)~ = O^{2^{n-1}} (componentwise).  (x)I = span of images of pi^{-1}u_0 (x) ... (x) pi^{-1}u_{n-1}, u in {1, pi}.
theta = pi^m in the LAST factor.  Region = theta * (R_I)~.
Checks: (1) kappa = max{k : region <= 5^k (x)I} == ceil(m/2);
        (2) sampled per-factor GL(I)^n images: componentwise min pi-valuation of the union == 2*ceil(m/2) - n
            (the claimed exact hull mu*(R_I)~, mu = 5^ceil * prod pi_i^{-1});  IV container gives 2*floor(m/2) - n.
"""
from fractions import Fraction as F
import itertools, random, math, sys
random.seed(7)
P = 5
def v5(x):
    x = F(x)
    if x == 0: return 10**9
    n, d, c = x.numerator, x.denominator, 0
    while n % P == 0: n //= P; c += 1
    while d % P == 0: d //= P; c -= 1
    return c
def vpi(z):
    a, b = z
    return min(2 * v5(a) if a != 0 else 10**9, 2 * v5(b) + 1 if b != 0 else 10**9)
def kmul(u, w): return (u[0]*w[0] + 5*u[1]*w[1], u[0]*w[1] + u[1]*w[0])
def sig(u): return (u[0], -u[1])
ONE, PI, PIINV = (F(1), F(0)), (F(0), F(1)), (F(0), F(1, 5))
def emb(xs):
    n = len(xs); out = []
    for s in itertools.product((0, 1), repeat=n - 1):
        z = xs[0]
        for i, si in enumerate(s):
            z = kmul(z, sig(xs[i + 1]) if si else xs[i + 1])
        out.extend(z)
    return tuple(out)
def solve(B, v):
    n = len(v)
    M = [[F(B[j][i]) for j in range(n)] + [F(v[i])] for i in range(n)]
    for c in range(n):
        r = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[r] = M[r], M[c]
        piv = M[c][c]; M[c] = [x / piv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]; M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] for i in range(n)]
def contained(gens, B, k):
    return all(min(v5(c) for c in solve(B, g)) >= k for g in gens)
def run(n, mmax=7, samples=150):
    ncomp = 2 ** (n - 1)
    TI = [emb([kmul(PIINV, u) for u in us]) for us in itertools.product((ONE, PI), repeat=n)]
    # region basis: theta * O^{ncomp}: theta in last factor -> component c: pi^m or (-pi)^m depending on sigma on last factor
    ok = True
    for m in range(0, mmax + 1):
        th = [None] * ncomp
        for ci, s in enumerate(itertools.product((0, 1), repeat=n - 1)):
            t = ONE
            for _ in range(m): t = kmul(t, sig(PI) if s[-1] else PI)
            th[ci] = t
        region = []
        for ci in range(ncomp):
            for u in (ONE, PI):
                vec = [F(0)] * (2 * ncomp)
                z = kmul(th[ci], u); vec[2*ci], vec[2*ci+1] = z
                region.append(tuple(vec))
        kap = max(k for k in range(-6, 12) if contained(region, TI, k))
        # per-factor sampling: g_i in GL(I), I = span{pi^{-1}, 1}; act on tensor coordinates via pure tensors of basis
        # represent region elements back in tensor coordinates: solve in basis of all pure tensors x_a (x)...
        PT = [emb(list(us)) for us in itertools.product((ONE, PI), repeat=n)]
        Pm = [[F(1), F(0)], [F(0), F(1, 5)]]; Pinv = [[F(1), F(0)], [F(0), F(5)]]
        def mm(A, B): return [[sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
        def rgl():
            while True:
                h = [[F(random.randint(-25, 25)) for _ in range(2)] for _ in range(2)]
                d = h[0][0]*h[1][1] - h[0][1]*h[1][0]
                if d != 0 and v5(d) == 0: return mm(mm(Pm, h), Pinv)
        coords = [solve(PT, r) for r in region]            # tensor coordinates of region generators
        idx = list(itertools.product((0, 1), repeat=n))
        best = [10**9] * ncomp
        for _ in range(samples):
            gs = [rgl() for _ in range(n)]
            for co in coords:
                out = [F(0)] * (2 * ncomp)
                for c, us in zip(co, idx):
                    if c == 0: continue
                    imgs = [(gs[i][0][us[i]], gs[i][1][us[i]]) for i in range(n)]   # g_i applied to basis vector x_{us[i]}
                    e = emb(imgs)
                    out = [o + c * x for o, x in zip(out, e)]
                for ci in range(ncomp):
                    best[ci] = min(best[ci], vpi((out[2*ci], out[2*ci+1])))
        exact = 2 * math.ceil(F(m, 2)) - n; cont = 2 * math.floor(F(m, 2)) - n
        good = (kap == math.ceil(F(m, 2))) and all(b == exact for b in best)
        ok &= good
        print(f"n={n} m={m}: kappa={kap} (ceil {math.ceil(F(m,2))})  sampled hull v={sorted(set(best))}  exact={exact}  IV container={cont}  {'OK' if good else 'MISMATCH'}")
    return ok
res = all(run(n) for n in (2, 3))
print('all OK:', res)
