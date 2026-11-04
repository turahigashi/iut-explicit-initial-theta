"""Random check of the factor lemma: span of {g(theta*I) : g in GL(I)} = p^kappa * I, kappa = max{k: theta I in p^k I}.
Work in I-coordinates: theta*I has the rows of the matrix T (coordinates of theta*b_i); g acts on coordinates by
an invertible integer matrix with unit determinant mod p.  Accumulate the span and compare with p^kappa * Z^e."""
import sys, random
from fractions import Fraction as Fr
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from shell_lattice import shell, kappa, coords, echelon, vp

def rand_gl(e, p, rng):
    while True:
        # product of random transvections, permutations and unit diagonals: always in GL_e(Z_(p))
        g = [[Fr(int(i == j)) for j in range(e)] for i in range(e)]
        for _ in range(3 * e):
            a, b = rng.sample(range(e), 2)
            t = rng.randrange(-p * p, p * p)
            for r in range(e):           # column op: col_b += t * col_a
                g[r][b] += t * g[r][a]
        for r in range(e):
            u = rng.choice([x for x in range(1, p * p) if x % p])
            g[r] = [u * x for x in g[r]]
        return g

def matmul_row(v, g):
    e = len(v)
    return [sum(v[i] * g[i][j] for i in range(e)) for j in range(e)]

def run(p, e, thetas, trials=6, seed=1):
    rng = random.Random(seed)
    L, I = shell(p, e)
    for name, th in thetas(L):
        k = kappa(L, I, th)
        T = [coords(I, L.mul(th, b), e) for b in I]
        rows = list(T)
        for _ in range(trials):
            g = rand_gl(e, p, rng)
            rows += [matmul_row(t, g) for t in T]
        E = echelon(rows, p, e)
        diag = [vp(E[t][t], p) for t in range(e)]
        # the span equals p^k Z^e iff the echelon diagonal has valuation k everywhere and all entries have val >= k
        ok = all(d == k for d in diag) and all(x == 0 or vp(x, p) >= k for r in E for x in r)
        t = Fr(L.vw(th), e)
        print(f"  {name:>14}: ord_p = {str(t):>6}  floor = {t.numerator // t.denominator:>2}  kappa = {k:>2}   "
              f"ind2/log p = {str(t - k):>6}   span == p^kappa I : {ok}")

def thetas(L):
    out = []
    for m in [1, 2, L.e - 1, L.e, L.e + 1, 2 * L.e + 1]:
        out.append((f"w^{m}", L.wpow(m)))
        u = L.wpow(0); u[1 % L.e] += 1                      # 1 + w
        out.append((f"(1+w) w^{m}", L.mul(u, L.wpow(m))))
    return out

if __name__ == "__main__":
    for p, e in [(11, 3), (3, 4), (5, 6)]:
        print(f"p={p} e={e}")
        run(p, e, thetas)
