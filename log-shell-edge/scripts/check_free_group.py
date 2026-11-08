"""Section 4: the free-group automorphisms used to move the pairs of the presentation.

Words in a free group are lists of (generator, +1/-1).  For the maps Z, H, J of Lemma 4.3 and
the pair maps of Lemma 4.2 the script checks that the stated inverse composes to the identity,
that the boundary word is fixed as an element, that M = (J o H) o Z o (J o H)^-1 fixes a, and that
the abelianizations are the matrices stated in Section 4.3.  Standard library only.
"""


def reduce(w):
    out = []
    for g, e in w:
        if out and out[-1][0] == g and out[-1][1] == -e:
            out.pop()
        else:
            out.append((g, e))
    return out


def inv(w):
    return [(g, -e) for g, e in reversed(w)]


def mul(*ws):
    return reduce([x for w in ws for x in w])


def gen(g):
    return [(g, 1)]


def comm(u, v):
    return mul(u, v, inv(u), inv(v))


def apply(phi, w):
    out = []
    for g, e in w:
        img = phi.get(g, gen(g))
        out += img if e == 1 else inv(img)
    return reduce(out)


def compose(phi, psi):
    """phi after psi"""
    gens = set(phi) | set(psi)
    return {g: apply(phi, psi.get(g, gen(g))) for g in gens}


GENS = 'abcd'
a, b, c, d = (gen(g) for g in GENS)
R, Q = comm(a, b), comm(c, d)
delta2 = mul(R, Q)
k = mul(inv(b), c, d, inv(c))

Z = {'a': mul(a, k), 'b': mul(inv(k), b, k), 'c': mul(inv(k), c), 'd': d}
Zi = {'a': mul(a, inv(k)), 'b': mul(k, b, inv(k)), 'c': mul(k, c), 'd': d}
H = {'a': mul(R, c, inv(R)), 'b': mul(R, d, inv(R)), 'c': a, 'd': b}
Hi = {'a': c, 'b': d, 'c': mul(inv(Q), a, Q), 'd': mul(inv(Q), b, Q)}
J = {'a': mul(a, b, inv(a)), 'b': inv(a), 'c': c, 'd': d}
Ji = {'a': inv(b), 'b': mul(b, a, inv(b)), 'c': c, 'd': d}
Psi, Psii = compose(J, H), compose(Hi, Ji)
M = compose(Psi, compose(Z, Psii))
Ta = {'b': mul(b, a)}                      # b -> ba
Tai = {'b': mul(b, inv(a))}
Td = {'c': mul(c, inv(d))}                 # c -> c d^-1
Tdi = {'c': mul(c, d)}
Ud = compose(M, compose(Tai, Tdi))         # induces T_{a+d} T_a^-1 T_d^-1
Ai = {'a': mul(a, b)}                      # pair maps of Lemma 4.2(i)
Bi = {'b': mul(b, a)}
D, C = comm(c, d), comm(a, b)
S = {'a': c, 'b': d, 'c': mul(inv(D), a, D), 'd': mul(inv(D), b, D)}
Si = {'a': mul(C, c, inv(C)), 'b': mul(C, d, inv(C)), 'c': a, 'd': b}


def is_identity(phi):
    return all(apply(phi, gen(g)) == gen(g) for g in GENS)


def ab(w):
    v = [0, 0, 0, 0]
    for g, e in w:
        v[GENS.index(g)] += e
    return v


def ab_matrix(phi):
    """columns = images of a, b, c, d"""
    cols = [ab(phi.get(g, gen(g))) for g in GENS]
    return [[cols[j][i] for j in range(4)] for i in range(4)]


FORM = {('a', 'b'): -1, ('b', 'a'): 1, ('c', 'd'): -1, ('d', 'c'): 1}


def pair(x, y):
    return sum(x[i] * y[j] * FORM.get((GENS[i], GENS[j]), 0) for i in range(4) for j in range(4))


def transvection(v):
    """matrix of T_v(x) = x + <x, v> v"""
    cols = []
    for i in range(4):
        e = [0, 0, 0, 0]
        e[i] = 1
        t = pair(e, v)
        cols.append([e[j] + t * v[j] for j in range(4)])
    return [[cols[j][i] for j in range(4)] for i in range(4)]


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(4)) for j in range(4)] for i in range(4)]


def matinv_unipotent(A):
    # A = I + N with N^2 = 0 for the transvections used here
    N = [[A[i][j] - (1 if i == j else 0) for j in range(4)] for i in range(4)]
    return [[(1 if i == j else 0) - N[i][j] for j in range(4)] for i in range(4)]


checks = []


def check(name, ok):
    checks.append((name, ok))
    print(('ok   ' if ok else 'FAIL ') + name)


check('Z(k) = k', apply(Z, k) == k)
for name, f, fi in [('Z', Z, Zi), ('H', H, Hi), ('J', J, Ji), ('swap of two pairs', S, Si),
                    ('a -> ab', Ai, {'a': mul(a, inv(b))}), ('b -> ba', Bi, {'b': mul(b, inv(a))})]:
    check(f'{name}: stated inverse composes to the identity on both sides',
          is_identity(compose(f, fi)) and is_identity(compose(fi, f)))
for name, f, word in [('Z', Z, delta2), ('H', H, delta2), ('J', J, delta2), ('swap of two pairs', S, delta2),
                      ('a -> ab', Ai, R), ('b -> ba', Bi, R), ('c -> c d^-1', Td, Q)]:
    check(f'{name} fixes the boundary word as an element', apply(f, word) == word)
check('M(a) = a', apply(M, a) == a)
check('M fixes delta_2 = [a,b][c,d]', apply(M, delta2) == delta2)
check('the word inducing U_d fixes a and delta_2', apply(Ud, a) == a and apply(Ud, delta2) == delta2)
A, B_, Cv, Dv = [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]
dmb = [Dv[i] - B_[i] for i in range(4)]
apd = [A[i] + Dv[i] for i in range(4)]
check('Z^ab = T_{d-b}', ab_matrix(Z) == transvection(dmb))
check('Psi^ab: a->c, b->d, c->b, d->-a', [ab(Psi[g]) for g in GENS] == [Cv, Dv, B_, [-1, 0, 0, 0]])
check('Psi^ab preserves the form',
      all(pair(ab(Psi[x]), ab(Psi[y])) == pair(ab(gen(x)), ab(gen(y))) for x in GENS for y in GENS))
check('M^ab = T_{a+d}', ab_matrix(M) == transvection(apd))
check('(b -> ba)^ab = T_a', ab_matrix(Bi) == transvection(A))
check('(c -> c d^-1)^ab = T_d', ab_matrix(Td) == transvection(Dv))
Ud_mat = matmul(transvection(apd), matmul(matinv_unipotent(transvection(A)), matinv_unipotent(transvection(Dv))))
formula = []
for i in range(4):
    e = [0, 0, 0, 0]
    e[i] = 1
    xa, xd = pair(e, A), pair(e, Dv)
    formula.append([e[j] + xa * Dv[j] + xd * A[j] for j in range(4)])
formula = [[formula[j][i] for j in range(4)] for i in range(4)]
check('U_d = T_{a+d} T_a^-1 T_d^-1 equals x -> x + <x,a> d + <x,d> a', Ud_mat == formula)
check('the word inducing U_d has abelianization U_d', ab_matrix(Ud) == formula)
print(f'{sum(ok for _, ok in checks)}/{len(checks)} checks passed')
