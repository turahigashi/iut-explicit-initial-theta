#!/usr/bin/env python3
"""Section 8: lattice facts for the fields with e = p - 1 and mu_p in K.

These are the cyclotomic boundary (p odd, K = Q_p(zeta_p) K_0 with K_0/Q_p unramified of degree f,
pi = zeta_p - 1) and, for p = 2, the fields unramified over Q_2 (pi = 2, rho = zeta_2 - 1 = -2).
O_K = O_{K_0}[pi] is computed exactly modulo p^PREC (integer arithmetic, standard library only).

Checked for each field:
  (L1) log(1 + pi z) = pi (z - z^p) mod m^2 for every residue representative z     (Lemma 8.5(a), proof)
  (L2) Lambda/m^2 = pi * ker Tr_{kappa/F_p}, of order q/p, so [m : Lambda] = p           (Lemma 8.5(a))
  (L3) v(log(1 + x)) = v(x) on m^2 (basis elements and random elements), so log U^(2) = m^2
  (L4) Tr(m^j) = p^ceil(j/e) Z_p for 0 <= j <= 2e + 1, and Tr(Lambda) = p Z_p for p odd   (Lemma 8.5(b))
  (L5) the least valuation w of Lambda - {0} is 2 if f = 1 and 1 if f >= 2              (Lemma 8.5(c))
  (L6) (1 + x)^p is in U^(p) for x in m; the classes of (1 + pi z)^p in U^(p)/U^(p+1) are exactly the
       classes 1 + rho^p A with Tr(A mod m) = 0, so 1 + rho^p A with Tr(A mod m) != 0 is not a p-th
       power in K                                                                        (Lemma 8.2, e_1 = 1)
  (L7) a_K(m) = m - min v(S_K(m)) for S_K(m) as in Theorem 8.9 (resp. 8.11), against the case formula
  (L8) the log-shell (2p)^{-1} log O^x compared with O_K
"""
import itertools
import random

PREC = 10   # every printed statement concerns valuations < e * PREC; results are exact modulo p^PREC
GUARD = 8   # extra p-adic digits carried while dividing by n in the logarithm series


def binom(n, k):
    r = 1
    for i in range(k):
        r = r * (n - i) // (i + 1)
    return r


def cyclo_eisenstein(p):
    """((X + 1)^p - 1)/X, coefficients from low to high degree; its root is zeta_p - 1."""
    return [binom(p, k) for k in range(1, p + 1)]


def vp(n, p, cap):
    n %= p ** cap
    if n == 0:
        return cap
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


class Field:
    def __init__(self, name, p, g, E):
        self.name, self.p, self.g, self.E = name, p, g, E
        self.f, self.e = len(g) - 1, len(E) - 1
        self.d, self.q = self.e * self.f, p ** (len(g) - 1)
        self.M = p ** (PREC + GUARD)
        assert g[-1] == 1 and E[-1] == 1
        # g is irreducible mod p (degree <= 3: no root in F_p); E is Eisenstein
        assert self.f <= 3 and all(sum(c * x ** i for i, c in enumerate(g)) % p for x in range(p)) or self.f == 1
        assert E[0] % p == 0 and E[0] % (p * p) != 0 and all(c % p == 0 for c in E[1:-1])

    # ---- K_0 = Z_p[theta]/(g), elements are lists of f integers
    def k0mul(self, a, b):
        f, M = self.f, self.M
        prod = [0] * (2 * f - 1)
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    prod[i + j] += ai * bj
        for k in range(2 * f - 2, f - 1, -1):
            c = prod[k]
            if c:
                prod[k] = 0
                for t in range(f):
                    prod[k - f + t] -= c * self.g[t]
        return [x % M for x in prod[:f]]

    def k0pow(self, a, n):
        r = [1] + [0] * (self.f - 1)
        for _ in range(n):
            r = self.k0mul(r, a)
        return r

    def k0trace(self, a):
        tot = 0
        for i in range(self.f):
            b = [0] * self.f
            b[i] = 1
            tot += self.k0mul(a, b)[i]
        return tot % self.M

    # ---- O_K = O_{K_0}[pi], elements are lists of e lists of f integers (coefficient of theta^i pi^j)
    def zero(self):
        return [[0] * self.f for _ in range(self.e)]

    def one(self):
        x = self.zero()
        x[0][0] = 1
        return x

    def from_k0(self, c):
        x = self.zero()
        x[0] = [v % self.M for v in c]
        return x

    def mono(self, a, b, i):
        """p^a pi^b theta^i with 0 <= b < e."""
        x = self.zero()
        x[b][i] = self.p ** a
        return x

    def add(self, x, y):
        return [[(u + v) % self.M for u, v in zip(r, s)] for r, s in zip(x, y)]

    def sub(self, x, y):
        return [[(u - v) % self.M for u, v in zip(r, s)] for r, s in zip(x, y)]

    def scal(self, x, c):
        return [[(u * c) % self.M for u in r] for r in x]

    def mul(self, x, y):
        e, f = self.e, self.f
        prod = [[0] * f for _ in range(2 * e - 1)]
        for i in range(e):
            if any(x[i]):
                for j in range(e):
                    if any(y[j]):
                        c = self.k0mul(x[i], y[j])
                        row = prod[i + j]
                        for t in range(f):
                            row[t] += c[t]
        for k in range(2 * e - 2, e - 1, -1):
            c = prod[k]
            if any(c):
                prod[k] = [0] * f
                for t in range(e):
                    s = self.E[t]
                    if s:
                        row = prod[k - e + t]
                        for u in range(f):
                            row[u] -= s * c[u]
        return [[v % self.M for v in row] for row in prod[:e]]

    def power(self, x, n):
        r = self.one()
        for _ in range(n):
            r = self.mul(r, x)
        return r

    def pi(self):
        if self.e == 1:
            return self.scal(self.one(), -self.E[0])   # pi = -E_0 = p
        x = self.zero()
        x[1][0] = 1
        return x

    def val(self, x):
        """v_K(x) with v_K(pi) = 1, capped at e * PREC."""
        best = self.e * PREC
        for j, row in enumerate(x):
            v = min(vp(c, self.p, PREC) for c in row)
            if v < PREC:
                best = min(best, self.e * v + j)
        return best

    def res(self, y, j):
        """For v(y) >= j: the residue of y/(p^a pi^b), j = a e + b, as a tuple in F_q (fixed unit factor)."""
        a, b = divmod(j, self.e)
        pa = self.p ** a
        assert all(c % pa == 0 for c in y[b])
        return tuple((c // pa) % self.p for c in y[b])

    def log1p(self, x):
        assert self.val(x) >= 1
        p, e = self.p, self.e
        nmax = 2 * e * PREC + 2 * e + 10
        total, pw = self.zero(), self.one()
        for n in range(1, nmax + 1):
            pw = self.mul(pw, x)
            k, n1 = 0, n
            while n1 % p == 0:
                n1 //= p
                k += 1
            assert k <= GUARD
            inv = pow(n1, -1, self.M)
            t = self.scal(pw, inv if n % 2 else -inv)
            if k:
                pk = p ** k
                assert all(c % pk == 0 for row in t for c in row)
                t = [[c // pk for c in row] for row in t]
            total = self.add(total, t)
        return total

    def trace(self, x):
        tot = 0
        for j in range(self.e):
            for i in range(self.f):
                b = self.zero()
                b[j][i] = 1
                tot += self.mul(x, b)[j][i]
        return tot % self.M

    def residue_reps(self):
        for a in itertools.product(range(self.p), repeat=self.f):
            yield list(a)

    def lattice_basis(self, j):
        """A Z_p-basis of m^j (j >= 0)."""
        out = []
        for b in range(self.e):
            a = max(0, -(-(j - b) // self.e))
            for i in range(self.f):
                out.append(self.mono(a, b, i))
        return out


def check_field(F, rng):
    p, e, f, q = F.p, F.e, F.f, F.q
    print("=== %s: p = %d, e = %d, f = %d, d = %d" % (F.name, p, e, f, F.d))
    pi = F.pi()
    rho = pi if p > 2 else F.scal(pi, -1)
    zeta = F.add(F.one(), rho)
    assert zeta != F.one() and F.val(F.sub(F.power(zeta, p), F.one())) >= e * PREC
    print("  1 + rho is a nontrivial p-th root of unity (mu_p in K), rho = %s" % ("pi" if p > 2 else "-2"))

    reps = list(F.residue_reps())
    kertr = {tuple(z) for z in reps if F.k0trace(z) % p == 0}
    assert len(kertr) == q // p

    # (L1), (L2)
    logs = {}
    for z in reps:
        zz = F.from_k0(z)
        L = F.log1p(F.mul(pi, zz))
        frob = F.from_k0(F.k0pow(z, p))
        D = F.sub(L, F.mul(pi, F.sub(zz, frob)))
        assert F.val(L) >= 1 and F.val(D) >= 2, (z, F.val(L), F.val(D))
        logs[tuple(z)] = L
    print("  (L1) log(1 + pi z) = pi (z - z^p) mod m^2 for all %d residue representatives z: OK" % q)
    S = {F.res(L, 1) for L in logs.values()}
    T = {F.res(F.mul(pi, F.sub(F.from_k0(z), F.from_k0(F.k0pow(z, p)))), 1) for z in reps}
    assert S == T == kertr
    print("  (L2) Lambda/m^2 = pi * ker Tr_{kappa/F_p}: %d classes = q/p, so [m : Lambda] = p: OK" % len(S))

    # (L3)
    cnt = 0
    for lev in range(2, 2 * e + 3):
        a, b = divmod(lev, e)
        for i in range(f):
            x = F.mono(a, b, i)
            assert F.val(F.log1p(x)) == F.val(x) == lev
            cnt += 1
    for _ in range(6):
        x = F.zero()
        for j in range(e):
            x[j] = [rng.randrange(F.M) for _ in range(f)]
        x = F.mul(x, F.mono(*divmod(2, e), 0))       # random element of m^2
        assert F.val(F.log1p(x)) == F.val(x)
        cnt += 1
    print("  (L3) v(log(1 + x)) = v(x) for %d elements x of m^2: OK" % cnt)

    # (L4)
    out = []
    for j in range(0, 2 * e + 2):
        tmin = min(vp(F.trace(x), p, PREC) for x in F.lattice_basis(j))
        assert tmin == -(-j // e)
        out.append(tmin)
    lam_gens = F.lattice_basis(2) + list(logs.values())
    tlam = min(vp(F.trace(x), p, PREC) for x in lam_gens)
    if p > 2:
        assert tlam == 1
        print("  (L4) v_p Tr(m^j), j = 0..%d: %s = ceil(j/e); Tr(Lambda) = p Z_p: OK" % (2 * e + 1, out))
    else:
        assert tlam == 2            # m^2 <= Lambda <= m with traces in 4 Z_2 (not used in the note)
        print("  (L4) v_p Tr(m^j), j = 0..%d: %s = ceil(j/e); Tr(Lambda) = 4 Z_2 (p = 2): OK" % (2 * e + 1, out))

    # (L5)
    w = 1 if any(F.res(L, 1) != (0,) * f for L in logs.values()) else 2
    assert w == (2 if f == 1 else 1)
    print("  (L5) least valuation of Lambda - {0}: w = %d: OK" % w)

    # (L6)
    pw_classes = set()
    for z in reps:
        P = F.power(F.add(F.one(), F.mul(pi, F.from_k0(z))), p)
        assert F.val(F.sub(P, F.one())) >= p
        pw_classes.add(F.res(F.sub(P, F.one()), p))
    for _ in range(6):
        x = F.zero()
        for j in range(e):
            x[j] = [rng.randrange(F.M) for _ in range(f)]
        x = F.mul(x, pi)                                  # random element of m
        assert F.val(F.sub(F.power(F.add(F.one(), x), p), F.one())) >= p
    assert pw_classes == kertr
    rp = F.power(rho, p)
    bad = 0
    for A in reps:
        c = F.res(F.mul(rp, F.from_k0(A)), p)
        if F.k0trace(A) % p:
            assert c not in pw_classes
            bad += 1
        else:
            assert c in pw_classes
    print("  (L6) (1 + x)^p in U^(p) for x in m; classes of (1 + pi z)^p in U^(p)/U^(p+1) = ker Tr (%d);"
          % len(pw_classes))
    print("       1 + rho^p A is not a p-th power mod U^(p+1) exactly when Tr(A mod m) != 0 (%d of %d): OK"
          % (bad, q))

    # (L7)  S_K(m) = m^m if r = 1 and p^n Lambda if r >= 2 (m = n e + r, 1 <= r <= e); min v(p^n Lambda) = n e + w
    vals = []
    for m in range(1 - e, 2 * e + 1):
        n, r = divmod(m - 1, e)
        r += 1
        a = 0 if r == 1 else m - (n * e + w)
        if r >= 2:
            assert a == ((m - 2) % e if f == 1 else (m - 1) % e)
        vals.append(a)
    print("  (L7) a_K(m) for m = %d..%d: %s" % (1 - e, 2 * e, vals))
    print("       a_K(1..e) = %s" % vals[e:2 * e])

    # (L8)
    if p == 2:
        same = (w == 2)       # (1/4) Lambda = O_K iff Lambda = 4 O_K = m^2
        print("  (L8) log-shell (1/4) log O^x %s O_K" % ("=" if same else "!="))
        assert same == (f == 1)
    else:
        print("  (L8) log-shell (2p)^{-1} log O^x = p^{-1} Lambda, least valuation %d - e = %d" % (w, w - e))
    print()


FIELDS = [
    ("Q_3(zeta_3)", 3, [0, 1], cyclo_eisenstein(3)),
    ("Q_5(zeta_5)", 5, [0, 1], cyclo_eisenstein(5)),
    ("Q_7(zeta_7)", 7, [0, 1], cyclo_eisenstein(7)),
    ("Q_3(zeta_3) Q_9", 3, [1, 0, 1], cyclo_eisenstein(3)),
    ("Q_3(zeta_3) Q_27", 3, [1, -1, 0, 1], cyclo_eisenstein(3)),
    ("Q_5(zeta_5) Q_25", 5, [-2, 0, 1], cyclo_eisenstein(5)),
    ("Q_2", 2, [0, 1], [-2, 1]),
    ("Q_4 (unramified over Q_2, f = 2)", 2, [1, 1, 1], [-2, 1]),
    ("Q_8 (unramified over Q_2, f = 3)", 2, [1, 1, 0, 1], [-2, 1]),
]

if __name__ == "__main__":
    rng = random.Random(20261108)
    for name, p, g, E in FIELDS:
        check_field(Field(name, p, g, E), rng)
    print("all checks passed")
