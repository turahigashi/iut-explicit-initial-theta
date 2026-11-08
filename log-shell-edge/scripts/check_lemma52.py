"""Lemma 5.2 (even degree): the d images x, T_a x, U_{y_3} x, ..., U_{y_d} x form a basis.

Basis y_1, ..., y_d of Lambda with the alternating form <y_1,y_2> = <y_3,y_4> = ... = -1 (and <y_2,y_1> = 1 etc.),
a = y_1, b = y_2, T_v(x) = x + <x,v> v and U_w(x) = x + <x,a> w + <x,w> a.  For x = alpha a + u b + w_0
the proof shows that the determinant of the d vectors (rows, in the basis y_1..y_d) is a unit times u^d; here we
check with exact integers that it equals -u^d for d = 2, 4, ..., 12 and random integral x, and that T_a and U_w
preserve the form.  Standard library only; fixed seed.
"""
import random
from fractions import Fraction


def form(d):
    J = [[0] * d for _ in range(d)]
    for i in range(0, d, 2):
        J[i][i + 1], J[i + 1][i] = -1, 1
    return J


def pair(J, x, y):
    return sum(x[i] * J[i][j] * y[j] for i in range(len(x)) for j in range(len(y)))


def det(M):
    M = [[Fraction(v) for v in row] for row in M]
    n, s = len(M), Fraction(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            s = -s
        s *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            M[r] = [M[r][k] - f * M[c][k] for k in range(n)]
    return s


def unit(d, i):
    v = [0] * d
    v[i] = 1
    return v


def T(J, v, x):
    t = pair(J, x, v)
    return [x[i] + t * v[i] for i in range(len(x))]


def U(J, a, w, x):
    s, t = pair(J, x, a), pair(J, x, w)
    return [x[i] + s * w[i] + t * a[i] for i in range(len(x))]


def matrix_of(f, d):
    cols = [f(unit(d, i)) for i in range(d)]
    return [[cols[j][i] for j in range(d)] for i in range(d)]


def preserves(J, M):
    d = len(M)
    return all(sum(M[k][i] * J[k][l] * M[l][j] for k in range(d) for l in range(d)) == J[i][j]
               for i in range(d) for j in range(d))


rnd = random.Random(20261108)
total = 0
for d in range(2, 13, 2):
    J = form(d)
    a, b = unit(d, 0), unit(d, 1)
    ws = [unit(d, i) for i in range(2, d)]
    assert preserves(J, matrix_of(lambda x: T(J, a, x), d)), 'T_a is not symplectic'
    for w in ws:
        assert preserves(J, matrix_of(lambda x, w=w: U(J, a, w, x), d)), 'U_w is not symplectic'
    for _ in range(200):
        x = [rnd.randint(-50, 50) for _ in range(d)]
        u = x[1]
        rows = [x, T(J, a, x)] + [U(J, a, w, x) for w in ws]
        D = det(rows)
        assert D == -u ** d, (d, x, D)
        assert T(J, a, x) == [x[i] + u * a[i] for i in range(d)]      # <x,a> = u
        total += 1
    print(f'd = {d}: T_a and U_w (w = y_3..y_d) preserve the form; det = -u^{d} for 200 random x')
print(f'{total} determinants checked')
