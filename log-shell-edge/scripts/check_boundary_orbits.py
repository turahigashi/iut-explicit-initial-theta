#!/usr/bin/env python3
"""Section 8: orbits in V = Lambda/p Lambda in finite models (Lemmas 8.7, 8.8 and Proposition 8.13).

Only elements whose action on V is stated in the note are used, and only facts that do not depend on the
unknown remaining elements of Gamma_K are concluded: the orbits of the subgroup generated here are already
as large as the invariant data allow, so they are the orbits of Gamma_K.

(b) cyclotomic boundary, d = (p - 1) f even.  V has basis [z], [y_2], ..., [y_d]; tau = coefficient of [y_2]
    (Tr/p mod p up to a unit); R = F_p[z]; U = span([y_3], ..., [y_d]) with the pairs (y_3, y_4), (y_5, y_6), ...
    Generators: symplectic transvections of U fixing [z], [y_2] (Kondo26, Lemma 3.3), and the mixing map M of
    Lemma 8.8: [y_2] -> [y_2] + alpha [z] + [y_4], [y_3] -> [y_3] - alpha [z] - [y_4] (y_1 = alpha z; every
    alpha in F_p is tried).
(a) odd degree d >= 3, K small.  V has basis [y_1], [y_2], ..., [y_d]; tau = coefficient of [y_1];
    W = span([y_2], ..., [y_d]) with the pairs (y_2, y_3), (y_4, y_5), ...
    Generators: symplectic transvections of W fixing [y_1] (Kondo26, Lemma 3.3), and a map phi with
    phi([y_1]) = [y_1] + [y_2] (Theorem 6.5); only phi([y_1]) is used, so phi is taken to fix W.
Standard library only.
"""
import itertools
from fractions import Fraction


def vec_add(u, v, p):
    return tuple((a + b) % p for a, b in zip(u, v))


def vec_scale(u, c, p):
    return tuple((a * c) % p for a in u)


def apply(mat_cols, x, p):
    """mat_cols[k] is the image of the k-th basis vector."""
    out = [0] * len(x)
    for k, c in enumerate(x):
        if c:
            col = mat_cols[k]
            for i in range(len(out)):
                out[i] += c * col[i]
    return tuple(v % p for v in out)


def unit(n, k):
    v = [0] * n
    v[k] = 1
    return tuple(v)


def symplectic_form(n, start, p):
    """<b_i, b_j> on coordinates start..n-1 with pairs (start, start+1), ...: <b_a, b_{a+1}> = -1."""
    def form(u, v):
        s = 0
        for a in range(start, n - 1, 2):
            s += -(u[a] * v[a + 1]) + u[a + 1] * v[a]
        return s % p
    return form


def transvection(n, vvec, form, p):
    cols = []
    for k in range(n):
        b = unit(n, k)
        c = form(b, vvec)
        cols.append(vec_add(b, vec_scale(vvec, c, p), p))
    return cols


def transvection_gens(n, start, p):
    form = symplectic_form(n, start, p)
    idx = list(range(start, n))
    vs = [unit(n, i) for i in idx]
    vs += [vec_add(unit(n, i), unit(n, j), p) for i, j in itertools.combinations(idx, 2)]
    return [transvection(n, v, form, p) for v in vs], form


def orbits(points, gens, p):
    seen, out = set(), []
    for x in points:
        if x in seen:
            continue
        orb, stack = {x}, [x]
        while stack:
            y = stack.pop()
            for g in gens:
                z = apply(g, y, p)
                if z not in orb:
                    orb.add(z)
                    stack.append(z)
        seen |= orb
        out.append(frozenset(orb))
    return out


def span(vectors, n, p):
    """Row-reduce; return the dimension of the span."""
    rows = [list(v) for v in vectors]
    rank, col = 0, 0
    while rank < len(rows) and col < n:
        piv = next((i for i in range(rank, len(rows)) if rows[i][col] % p), None)
        if piv is None:
            col += 1
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], -1, p)
        rows[rank] = [(a * inv) % p for a in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][col] % p:
                c = rows[i][col]
                rows[i] = [(a - c * b) % p for a, b in zip(rows[i], rows[rank])]
        rank += 1
        col += 1
    return rank


def all_vectors(n, p):
    return [tuple(v) for v in itertools.product(range(p), repeat=n)]


def check_cyclotomic(p, d):
    f = d // (p - 1)
    print("=== (b) cyclotomic boundary model: p = %d, d = %d (f = %d, e = %d)" % (p, d, f, p - 1))
    n = d                                          # coordinates: 0 = [z], 1 = [y_2], 2.. = [y_3], ..., [y_d]
    sp, form = transvection_gens(n, 2, p)
    U = [x for x in all_vectors(n, p) if x[0] == 0 and x[1] == 0]
    Unz = [x for x in U if any(x)]
    if d >= 4:
        orbU = orbits(Unz, sp, p)
        assert len(orbU) == 1
        print("  the transvections act transitively on U - {0} (%d vectors)" % len(Unz))
        # Lemma 8.7: the only Sp-invariant line in ker tau is F_p[z]
        kertau = [x for x in all_vectors(n, p) if x[1] == 0 and any(x)]
        lines = {frozenset(vec_scale(x, c, p) for c in range(1, p)) for x in kertau}
        inv = [L for L in lines if all(apply(g, next(iter(L)), p) in L for g in sp)]
        assert len(inv) == 1 and unit(n, 0) in inv[0]
        print("  (Lemma 8.7) Sp-invariant lines in ker tau: %d, namely F_p[z]: OK" % len(inv))
    for alpha in range(p):
        gens = list(sp)
        if d >= 4:
            cols = [unit(n, k) for k in range(n)]
            z, y2, y3, y4 = unit(n, 0), unit(n, 1), unit(n, 2), unit(n, 3)
            cols[1] = vec_add(vec_add(y2, vec_scale(z, alpha, p), p), y4, p)
            cols[2] = vec_add(y3, vec_scale(vec_add(vec_scale(z, alpha, p), y4, p), p - 1, p), p)
            gens.append(cols)
            for g in gens:                          # R and tau are preserved
                assert apply(g, unit(n, 0), p) == unit(n, 0)
                assert all(apply(g, unit(n, k), p)[1] == (1 if k == 1 else 0) for k in range(n))
        # orbits on V/R (drop the [z] coordinate)
        quot = [(0,) + x for x in itertools.product(range(p), repeat=n - 1)]

        def proj(x):
            return (0,) + x[1:]
        gens_q = [[proj(c) for c in g] for g in gens]
        orb_q = orbits(quot, gens_q, p)
        expect = [(1, 0)] + ([(p ** (d - 2) - 1, 0)] if d >= 4 else []) + [(p ** (d - 2), s) for s in range(1, p)]
        got = sorted((len(o), next(iter(o))[1]) for o in orb_q)
        assert got == sorted(expect), (got, expect)
        if alpha == 0:
            print("  orbits on V/R: {0}, U - {0}, and {tau = s} for s != 0 (sizes %s): OK"
                  % sorted(len(o) for o in orb_q))
        if p ** d > 5000:
            continue
        V = all_vectors(n, p)
        orb = orbits(V, gens, p)
        Rset = {vec_scale(unit(n, 0), c, p) for c in range(p)}
        # Lemma 8.8: R together with the orbit of any x with tau(x) != 0 spans V
        for o in orb:
            x = next(iter(o))
            if x[1] and d >= 4:
                assert span(list(o) + [unit(n, 0)], n, p) == n
        # Proposition 8.13(b): the union of the translates of I = R + F_p v (tau(v) != 0) is R u {tau != 0}
        target = Rset | {x for x in V if x[1]}
        idx = {x: i for i, o in enumerate(orb) for x in o}
        tgt = {i for i, o in enumerate(orb) if o <= target}
        assert set().union(*[orb[i] for i in tgt]) == target       # target is a union of orbits
        for v in V:
            if v[1] != 1:
                continue
            I = {vec_add(vec_scale(unit(n, 0), c, p), vec_scale(v, t, p), p) for c in range(p) for t in range(p)}
            assert {idx[x] for x in I} == tgt
        # and of R + span(v, u) with 0 != u in U is all of V
        if d >= 4:
            I2 = {vec_add(vec_add(vec_scale(unit(n, 0), c, p), vec_scale(unit(n, 1), t, p), p),
                          vec_scale(unit(n, 2), s, p), p) for c in range(p) for t in range(p) for s in range(p)}
            assert {idx[x] for x in I2} == set(range(len(orb)))
        meas = Fraction(len(target), p ** d)
        assert meas == 1 - Fraction(1, p) + Fraction(1, p ** (d - 1))
        if d >= 4:
            a, b = unit(n, 1), vec_add(vec_scale(unit(n, 1), p - 1, p), unit(n, 2), p)
            assert a in target and b in target and vec_add(a, b, p) not in target
        if alpha == 0:
            print("  (Lemma 8.8) R + span of the orbit of any x with tau(x) != 0 is V: OK")
            print("  (Prop. 8.13(b)) union for R + span([y_2], [y_3]): V; union for R + F_p v, tau(v) != 0 "
                  "(all %d such v): R u {tau != 0}, relative measure %s = 1 - 1/p + p^(1-d)%s: OK"
                  % (p ** (d - 1), meas, ", not additive" if d >= 4 else ""))
            if f == 1:
                print("      f = 1: q(m^e) = R + F_p [p] is of the second kind; q(m^r), 2 <= r < e, of the first")
            else:
                print("      f >= 2: every q(m^r), 2 <= r <= e, meets U - {0}, so only the first kind occurs")
    print("  (all alpha in F_p tried)")
    print()


def check_odd(p, d):
    small_f1 = d <= p - 2
    print("=== (a) odd degree model: p = %d, d = %d (small K with f = 1, e = d: %s)"
          % (p, d, "exists" if small_f1 else "none, only e < d occurs"))
    n = d                                          # coordinates: 0 = [y_1], 1.. = [y_2], ..., [y_d]
    sp, form = transvection_gens(n, 1, p)
    phi = [unit(n, k) for k in range(n)]
    phi[0] = vec_add(unit(n, 0), unit(n, 1), p)
    gens = sp + [phi]
    V = all_vectors(n, p)
    orb = orbits(V, gens, p)
    got = sorted((len(o), next(iter(o))[0]) for o in orb)
    expect = sorted([(1, 0), (p ** (d - 1) - 1, 0)] + [(p ** (d - 1), t) for t in range(1, p)])
    assert got == expect, (got, expect)
    print("  orbits on V: {0}, W - {0}, and {tau = t} for t != 0 (sizes %s): OK" % sorted(len(o) for o in orb))
    target = {x for x in V if x[0]} | {tuple([0] * n)}
    idx = {x: i for i, o in enumerate(orb) for x in o}
    tgt = {i for i, o in enumerate(orb) if o <= target}
    assert set().union(*[orb[i] for i in tgt]) == target
    for v in V:
        if v[0] != 1:
            continue
        line = {vec_scale(v, t, p) for t in range(p)}
        assert {idx[x] for x in line} == tgt
    I2 = {vec_add(vec_scale(unit(n, 0), t, p), vec_scale(unit(n, 1), s, p), p) for t in range(p) for s in range(p)}
    assert {idx[x] for x in I2} == set(range(len(orb)))
    meas = Fraction(len(target), p ** d)
    assert meas == 1 - Fraction(1, p) + Fraction(1, p ** d)
    a, b = unit(n, 0), vec_add(vec_scale(unit(n, 0), p - 1, p), unit(n, 1), p)
    assert a in target and b in target and vec_add(a, b, p) not in target
    print("  (Prop. 8.13(a)) union for a line F_p v with tau(v) != 0 (all %d such lines): {0} u {tau != 0}; "
          "relative measure %s = 1 - 1/p + p^(-d); not additive; a plane meeting W gives V: OK"
          % (p ** (d - 1), meas))
    print()


if __name__ == "__main__":
    for p, d in [(3, 2), (3, 4), (5, 4), (3, 6), (7, 6)]:
        check_cyclotomic(p, d)
    for p, d in [(3, 3), (5, 3), (7, 3), (5, 5), (7, 5)]:
        check_odd(p, d)
    print("all checks passed")
