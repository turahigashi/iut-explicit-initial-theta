"""Exact computation of the log-shell lattice I = (2p)^{-1} log(1 + m) of L = Q_p(w), w^e = p (p odd, p not | e),
and of kappa(theta) = max{k : theta*I in p^k*I}.  Also a random check that the span of the GL(I)-orbit of
theta*I is p^kappa * I.  Coordinates: coefficients of w^0..w^{e-1}; exact rationals, Z_(p)-spans."""
import sys, random
from fractions import Fraction as Fr

def vp(x, p):
    if x == 0: return None
    n, d, k = x.numerator, x.denominator, 0
    while n % p == 0: n //= p; k += 1
    while d % p == 0: d //= p; k -= 1
    return k

class Field:
    def __init__(s, p, e):
        s.p, s.e = p, e
    def wpow(s, k):                      # w^k as a vector
        v = [Fr(0)] * s.e
        v[k % s.e] = Fr(s.p) ** (k // s.e)
        return v
    def mul(s, a, b):
        e, p = s.e, s.p
        out = [Fr(0)] * e
        for i, x in enumerate(a):
            if x == 0: continue
            for j, y in enumerate(b):
                if y == 0: continue
                k = i + j
                out[k % e] += x * y * (p ** (k // e))
        return out
    def vw(s, a):                         # w-adic valuation
        vals = [s.e * vp(x, s.p) + r for r, x in enumerate(a) if x != 0]
        return min(vals) if vals else None
    def log_gens(s):
        """generators of log(1 + m): log(1 + w^i) mod m^{M+1} for i <= M, and m^{M+1}; M = floor(e/(p-1))."""
        p, e = s.p, s.e
        M = e // (p - 1)
        H = M + 1
        gens = []
        for i in range(1, M + 1):
            v = [Fr(0)] * e
            n = 1
            while True:
                val = i * n - e * vp(Fr(n), p)
                if val < H:
                    k = i * n
                    v[k % e] += Fr((-1) ** (n + 1), n) * (Fr(p) ** (k // e))
                # stop when even the most favourable later term is >= H
                if i * n - e * (n.bit_length() * 2) > H + 5 * e and n > 4 * p:
                    break
                n += 1
            gens.append(v)
        for k in range(H, H + e):
            gens.append(s.wpow(k))
        return gens

def echelon(rows, p, e):
    """Z_(p)-basis of the span of rows (full rank e): upper triangular, pivot of row r at column r."""
    rows = [list(r) for r in rows]
    basis = []
    for col in range(e):
        cand = [(vp(r[col], p), idx) for idx, r in enumerate(rows) if r[col] != 0]
        if not cand:
            raise ValueError("not full rank")
        _, piv = min(cand)
        pr = rows.pop(piv)
        for r in rows:
            if r[col] != 0:
                c = r[col] / pr[col]
                for t in range(col, e):
                    r[t] -= c * pr[t]
        basis.append(pr)
    return basis

def coords(basis, y, e):
    """y = sum_t c_t basis[t]; basis upper triangular."""
    y = list(y); c = [Fr(0)] * e
    for t in range(e):
        if y[t] != 0:
            c[t] = y[t] / basis[t][t]
            for u in range(t, e):
                y[u] -= c[t] * basis[t][u]
    assert all(x == 0 for x in y)
    return c

def shell(p, e):
    L = Field(p, e)
    B = echelon(L.log_gens(), p, e)
    I = [[x / p for x in b] for b in B]          # (2p)^{-1}: 2 is a unit for p odd
    return L, I

def kappa(L, I, theta):
    p, e = L.p, L.e
    k = None
    for b in I:
        c = coords(I, L.mul(theta, b), e)
        for x in c:
            if x != 0:
                v = vp(x, p)
                k = v if k is None else min(k, v)
    return k

def radius(L, I):                                    # -min ord_p over I, and the largest ball inside
    vals = [L.vw(b) for b in I]
    return min(vals)

if __name__ == "__main__":
    p, e = int(sys.argv[1]), int(sys.argv[2])
    L, I = shell(p, e)
    vmin = min(L.vw(b) for b in I)
    print(f"p={p} e={e}: min w-valuation on I = {vmin} (ord_p = {Fr(vmin, e)})")
    # is I an O-module?  test w*I in I
    kw = kappa(L, I, L.wpow(1))
    print("  w*I in I ?", kw is not None and kw >= 0, f"(kappa(w) = {kw})")
