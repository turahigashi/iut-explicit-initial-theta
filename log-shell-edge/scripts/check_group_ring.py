"""Steps (2)-(4) and (6) of the proof of Theorem 6.5, in finite models.

The group G = <s, t | t^n = 1, s^f = t^u, s t s^-1 = t^q> (n prime to p) models the image of the tame quotient
(s ~ sigma, t ~ tau), R = F_p[G], and chi0 : G -> F_p^x is a nontrivial character.  M_1 is the free R-module on
xb_1, xb_2, xb_3, and M_2 = M_1 (+) Lambda^2(M_1): the first summand is the image of the p-th power map, the second
that of the commutator pairing B (diagonal G-action), as for a free pro-p group and p odd.  We check:
  (a) e' = (1/n) sum_k chi0(t)^-k t^k is a central idempotent with t e' = chi0(t) e';
  (b) theta = -s + chi0(s) e' satisfies theta R = R theta = I_0 = ker(eps_chi0)        [step (2)];
  (c) the adjoint rule B(a u, v) = B(u, a^dag v) mod I_0 Lambda^2, a^dag = sum a_g chi0(g) g^-1   [step (2)];
  (d) c = (rho0 - chi0(rho0)) / (1 - chi0(rho0)) has eps(c) = 1 and c in I_0, and eps(mu) = eps(nu) = 0 [step (3)];
  (e) E = Q(psi xb) - Q(xb), for Q(xb) = [s = 1] xb_1^(p) + B(xb_1, delta xb_1) + B(xb_2, xb_3) and
      psi: xb_1 -> xb_1 + c xb_2, xb_3 -> xb_3 + mu xb_1 + nu xb_2, lies in I_0 M_2 and theta zeta = -E is solved
      orbit by orbit, although E != 0                                                       [step (4)];
  (f) on coinvariants xb_1 -> xb_1 + eps(c) xb_2 = xb_1 + xb_2 and xb_3 -> xb_3                  [step (6)].
Exact arithmetic over F_p; standard library only; fixed seed.
"""
import itertools
import random
from collections import defaultdict


def make_group(n, f, q, u):
    assert pow(q, f, n) == 1 % n and (q * u - u) % n == 0, 'invalid parameters'
    els = [(i, j) for i in range(f) for j in range(n)]
    qinv = pow(q, -1, n) if n > 1 else 0

    def mul(a, b):
        (i1, j1), (i2, j2) = a, b
        jj = (j1 * pow(qinv, i2, n) + j2) % n if n > 1 else 0     # s^i1 t^j1 s^i2 t^j2
        ii = i1 + i2
        if ii >= f:
            ii -= f
            jj = (u + jj) % n if n > 1 else 0
        return (ii, jj)

    e = (0, 0)
    for a, b, c in itertools.product(els, repeat=3):
        assert mul(mul(a, b), c) == mul(a, mul(b, c)), 'not associative'
    inv = {a: next(b for b in els if mul(a, b) == e) for a in els}
    s, t = (1 % f, 0) if f > 1 else (0, u % n if n > 1 else 0), (0, 1 % n if n > 1 else 0)
    return els, mul, inv, e, s, t


def run(p, n, f, q, u, trials, rnd):
    assert n % p != 0
    els, mul, inv, one, s, t = make_group(n, f, q, u)
    chars = [(cs, ct) for cs in range(1, p) for ct in range(1, p)
             if pow(ct, n, p) == 1 and pow(ct, q, p) == ct and pow(cs, f, p) == pow(ct, u, p) and (cs, ct) != (1, 1)]
    if not chars:
        return None
    out = []
    for cs, ct in chars:
        chi = {g: pow(cs, g[0], p) * pow(ct, g[1], p) % p for g in els}
        assert all(chi[mul(g, h)] == chi[g] * chi[h] % p for g in els for h in els), 'not a character'
        out.append(check_character(p, n, els, mul, inv, one, s, t, chi, trials, rnd))
    return len(els), out


def check_character(p, n, els, mul, inv, one, s, t, chi, trials, rnd):
    def clean(d):
        return {k: v % p for k, v in d.items() if v % p}

    def rmul(a, b):
        r = defaultdict(int)
        for g, x in a.items():
            for h, y in b.items():
                r[mul(g, h)] += x * y
        return clean(r)

    def radd(*xs, signs=None):
        r = defaultdict(int)
        for k, a in enumerate(xs):
            sg = 1 if signs is None else signs[k]
            for g, x in a.items():
                r[g] += sg * x
        return clean(r)

    def scal(c, a):
        return clean({g: c * x for g, x in a.items()})

    def dag(a):
        return clean({inv[g]: x * chi[g] for g, x in a.items()})

    def eps(a):
        return sum(a.values()) % p

    def eps0(a):
        return sum(x * chi[g] for g, x in a.items()) % p

    def rank(rows):
        rows = [r[:] for r in rows]
        rk, col, m = 0, 0, len(rows[0]) if rows else 0
        while rk < len(rows) and col < m:
            piv = next((i for i in range(rk, len(rows)) if rows[i][col] % p), None)
            if piv is None:
                col += 1
                continue
            rows[rk], rows[piv] = rows[piv], rows[rk]
            iv = pow(rows[rk][col], -1, p)
            rows[rk] = [x * iv % p for x in rows[rk]]
            for i in range(len(rows)):
                if i != rk and rows[i][col] % p:
                    fct = rows[i][col]
                    rows[i] = [(x - fct * y) % p for x, y in zip(rows[i], rows[rk])]
            rk += 1
            col += 1
        return rk

    def solve(A, bvec):
        """solve A x = b over F_p (A square list of rows); return x or None"""
        m = len(A)
        M = [A[i][:] + [bvec[i]] for i in range(m)]
        where, r = [-1] * m, 0
        for c in range(m):
            piv = next((i for i in range(r, m) if M[i][c] % p), None)
            if piv is None:
                continue
            M[r], M[piv] = M[piv], M[r]
            iv = pow(M[r][c], -1, p)
            M[r] = [x * iv % p for x in M[r]]
            for i in range(m):
                if i != r and M[i][c] % p:
                    fct = M[i][c]
                    M[i] = [(x - fct * y) % p for x, y in zip(M[i], M[r])]
            where[c] = r
            r += 1
        if any(all(x % p == 0 for x in M[i][:m]) and M[i][m] % p for i in range(m)):
            return None
        return [M[where[c]][m] if where[c] >= 0 else 0 for c in range(m)]

    idx = {g: i for i, g in enumerate(els)}
    G = len(els)
    # (a) e'
    tpow = [one]
    for _ in range(n - 1):
        tpow.append(mul(tpow[-1], t))
    ninv, ct = pow(n, -1, p), chi[t]
    ep = clean({tpow[k]: ninv * pow(ct, -k, p) for k in range(n)})
    assert rmul(ep, ep) == ep, "e' is not idempotent"
    assert rmul({s: 1}, ep) == rmul(ep, {s: 1}) and rmul({t: 1}, ep) == rmul(ep, {t: 1}), "e' is not central"
    assert rmul({t: 1}, ep) == scal(ct, ep), "t e' != chi0(t) e'"
    assert eps0(ep) == 1
    # (b) theta R = R theta = I_0
    b = chi[s]
    theta = radd({s: 1}, scal(b, ep), signs=[-1, 1])
    assert eps0(theta) == 0, 'theta not in I_0'
    right = [[rmul(theta, {g: 1}).get(h, 0) for h in els] for g in els]
    left = [[rmul({g: 1}, theta).get(h, 0) for h in els] for g in els]
    assert rank(right) == G - 1 and rank(left) == G - 1, 'theta R != I_0'
    Lmat = [[rmul(theta, {g: 1}).get(h, 0) for g in els] for h in els]       # matrix of a -> theta a on R
    # modules
    basis = [(i, g) for i in (1, 2, 3) for g in els]
    order = {bv: k for k, bv in enumerate(basis)}

    def act(r, m):
        o = defaultdict(int)
        for g, x in r.items():
            for (i, h), y in m.items():
                o[(i, mul(g, h))] += x * y
        return clean(o)

    def madd(*ms):
        o = defaultdict(int)
        for m in ms:
            for k, v in m.items():
                o[k] += v
        return clean(o)

    def B(u_, v_):
        o = defaultdict(int)
        for a_, x in u_.items():
            for b_, y in v_.items():
                if a_ == b_:
                    continue
                if order[a_] < order[b_]:
                    o[(a_, b_)] += x * y
                else:
                    o[(b_, a_)] -= x * y
        return clean(o)

    def gpair(g, pr):
        (i, a_), (j, b_) = pr
        A_, B_ = (i, mul(g, a_)), (j, mul(g, b_))
        return ((A_, B_), 1) if order[A_] < order[B_] else ((B_, A_), -1)

    pairs = [(x, y) for x in basis for y in basis if order[x] < order[y]]
    orbit_of, orbits, seen = {}, [], set()
    for pr in pairs:
        if pr in seen:
            continue
        orb = sorted({gpair(g, pr)[0] for g in els}, key=lambda w: (order[w[0]], order[w[1]]))
        for w in orb:
            seen.add(w)
            orbit_of[w] = len(orbits)
        vals = defaultdict(set)                       # chi0-equivariant functional normalised at pr
        for g in els:
            w, sg = gpair(g, pr)
            vals[w].add(sg * chi[g] % p)
        functional = None if any(len(v) > 1 for v in vals.values()) else {w: next(iter(v)) for w, v in vals.items()}
        orbits.append((orb, functional))

    def in_I0_wedge(w2):
        for orb, fn in orbits:
            if fn is not None and sum(w2.get(w, 0) * fn[w] for w in orb) % p:
                return False
        return True

    def in_I0_free(m1):
        coords = defaultdict(dict)
        for (i, g), v in m1.items():
            coords[i][g] = v
        return all(eps0(cd) == 0 for cd in coords.values())

    def theta_on_orbit(orb):
        pos = {w: k for k, w in enumerate(orb)}
        A = [[0] * len(orb) for _ in orb]
        for k, w in enumerate(orb):
            for g, x in theta.items():
                w2, sg = gpair(g, w)
                A[pos[w2]][k] = (A[pos[w2]][k] + x * sg) % p
        return A

    theta_mats = {}
    nonzero_E = 0
    for _ in range(trials):
        # (c) adjoint rule
        a = clean({g: rnd.randrange(p) for g in els})
        u_ = clean({bv: rnd.randrange(p) for bv in basis})
        v_ = clean({bv: rnd.randrange(p) for bv in basis})
        diff = madd(B(act(a, u_), v_), {k: -x for k, x in B(u_, act(dag(a), v_)).items()})
        assert in_I0_wedge(diff), 'adjoint rule fails'
        # (d) c, mu, nu
        rho0 = rnd.choice([g for g in els if chi[g] != 1])
        k = pow((1 - chi[rho0]) % p, -1, p)
        c = clean({rho0: k, one: -chi[rho0] * k}) if rho0 != one else None
        assert eps(c) == 1 and eps0(c) == 0, 'c'
        delta = clean({g: rnd.randrange(p) for g in els})
        cd = dag(c)
        mu = scal(-1, rmul(cd, radd(delta, dag(delta), signs=[1, -1])))
        nu = scal(-1, rmul(rmul(cd, delta), c))
        assert eps(mu) == 0 and eps(nu) == 0, 'eps(mu), eps(nu)'
        # (e) E for s = 1 (with the p-th power term) and for s >= 2 (without it)
        x1, x2, x3 = {(1, one): 1}, {(2, one): 1}, {(3, one): 1}
        px1 = madd(x1, act(c, x2))
        px3 = madd(x3, act(mu, x1), act(nu, x2))
        for s1 in (1, 0):
            Ep = madd({kk: s1 * v for kk, v in px1.items()}, {kk: -s1 * v for kk, v in x1.items()})
            Ew = madd(B(px1, act(delta, px1)), B(x2, px3), {kk: -v for kk, v in B(x1, act(delta, x1)).items()},
                      {kk: -v for kk, v in B(x2, x3).items()})
            assert in_I0_free(Ep) and in_I0_wedge(Ew), 'E not in I_0 M_2'
            if Ep or Ew:
                nonzero_E += 1
            # theta zeta = -E: free part coordinate by coordinate, wedge part orbit by orbit
            coords = defaultdict(dict)
            for (i, g), v in Ep.items():
                coords[i][g] = v
            for cd_ in coords.values():
                assert solve(Lmat, [(-cd_.get(h, 0)) % p for h in els]) is not None, 'theta zeta = -E (free part)'
            touched = defaultdict(dict)
            for w, v in Ew.items():
                touched[orbit_of[w]][w] = v
            for oi, part in touched.items():
                orb = orbits[oi][0]
                if oi not in theta_mats:
                    theta_mats[oi] = theta_on_orbit(orb)
                assert solve(theta_mats[oi], [(-part.get(w, 0)) % p for w in orb]) is not None, 'theta zeta = -E'
        # (f) coinvariants
        assert eps(c) == 1 and eps(mu) == 0 and eps(nu) == 0
    return f'chi0(s)={chi[s]} chi0(t)={chi[t]}: {trials} trials ok, E != 0 in {nonzero_E} of {2 * trials}'


MODELS = [  # (p, n, f, q, u): |G| = n f
    (3, 2, 2, 1, 1), (3, 4, 2, 3, 0), (5, 4, 1, 1, 0), (5, 2, 3, 1, 1), (7, 3, 2, 2, 0), (7, 6, 2, 5, 3),
    (11, 5, 2, 4, 0), (13, 4, 2, 3, 0), (13, 3, 3, 1, 1), (11, 10, 2, 9, 5), (7, 9, 3, 4, 0)]
rnd = random.Random(20261108)
count = 0
for prm in MODELS:
    res = run(*prm, trials=6, rnd=rnd)
    if res is None:
        print(prm, 'no nontrivial character')
        continue
    order_G, lines = res
    abelian = prm[3] % prm[1] == 1 % prm[1]
    print(f'p={prm[0]} n={prm[1]} f={prm[2]} q={prm[3]} u={prm[4]}  |G|={order_G} '
          f'{"abelian" if abelian else "nonabelian"}, {len(lines)} nontrivial characters')
    for ln in lines:
        print('   ', ln)
        count += 1
print(f'{count} (group, character) pairs checked')
