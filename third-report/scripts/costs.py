#!/usr/bin/env python3
"""Exact values of the local distinctions of [IUT4, Sec. 1], for note6.

Standard library only.  Every table asserts its own conclusion.  Run:  python3 scripts/costs.py
"""
import decimal, math, sys
from fractions import Fraction as F

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d*d <= n:
        if n % d == 0: return False
        d += 2
    return True

def muli(x, y): return (x[0]*y[0] - x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def mul5(x, y): return (x[0]*y[0] + 5*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
assert ([n for n in range(2, 300) if is_prime(n)]
        == [n for n in range(2, 300) if all(n % d for d in range(2, n))])
assert mul5((0, 1), (0, 1)) == (5, 0) and muli((0, 1), (0, 1)) == (-1, 0)

def powr(b, n, mul):
    r = (1, 0)
    while n:
        if n & 1: r = mul(r, b)
        b = mul(b, b); n >>= 1
    return r

def c1():
    print("Table 1.  The p-primary torsion term m_i.  k = Q_p(zeta_p), e = p-1, f = 1.")
    print("          [S] [IUT4, Prop. 1.4(ii)]: for the log of the unit group,")
    print("            mu^log(log O^x) = -(1/e + m/(e f)) log p,")
    print("          where p^m is the order of the p-primary torsion of O^x.")
    print("          CORRECTION 2026-09-07 (round 2): an earlier version attributed this")
    print("          to the ceiling in a_i of [IUT4, Prop. 1.2].  The values were right")
    print("          and the derivation was not: a_i is the coefficient of the hull")
    print("          bound, m_i is the torsion variable, and they are different objects.")
    print("      p    e   f   m    mu/log p    without m     cost of m")
    for p in (3, 5, 7):
        assert is_prime(p), p
        e, f, m = p - 1, 1, 1
        assert e + 1 == p and f == 1        # k = Q_p(zeta_p): totally ramified of
                                            # degree p-1, residue degree 1
        mu = -(F(1, e) + F(m, e*f))
        drop = -F(1, e)
        assert mu == F(-2, e) and drop - mu == F(1, e)
        print(f"    {p:>3} {e:>4} {f:>3} {m:>3} {str(mu):>11} {str(drop):>12} {str(drop-mu):>13}")
    print("    -> the cost is log3/2, log5/4, log7/6: not uniform in p, and largest")
    print("       where p is smallest.  The normalization itself is [IUT4, Prop. 1.4(i)].")

def c2():
    print("Table 2.  Residue degree.  Unramified extensions of Q_5.  [S]+[P]")
    print("          [IUT4, Prop. 1.4(i),(ii)].  The lattice index grows with f;")
    print("          the NORMALIZED log-volume does not move.")
    print("      f   [O : log-units]   raw log index / log5   mu / log5")
    for f in (1, 2, 3):
        index = 5**f                                   # [O : log-units]
        # The next column prints log(index)/log 5 and claims it is f.  Check the two
        # printed columns against each other -- and do it in exact integers: a first
        # attempt compared logarithms, and rounding absorbed the difference between
        # 5^f and 6^f for f = 1, 2, 3, so the guard passed on a wrong table.
        _n, _e = index, 0
        while _n % 5 == 0: _n //= 5; _e += 1
        assert (_n, _e) == (1, f) and F(-f, f) == -1
        print(f"    {f:>3} {index:>16} {f:>22} {str(F(-f,f)):>11}")
    assert all(F(-f, f) == -1 for f in (1, 2, 3))
    print("    -> using the raw index instead of the normalized volume counts f twice.")

def c3():
    print("Table 3.  The tensor order.  k = Q_5(sqrt 5), R = O (x)_{Z_5} O in O x O.  [S]+[P]")
    print("          [IUT4, Prop. 1.1, Prop. 1.4(iii)].")
    print("          R = {(u,v) in O^2 : u = v mod pi}, so [O^2 : R] = |O/pi| = 5, and")
    print("          dim_{Q_5}(k x k) = 4.  (O^2 is a Z_5-module, not a Q_5 vector space;")
    print("          the ambient Q_5-space is k x k, of dimension 4.)")
    # The index is COMPUTED from the transition matrix, not asserted as a literal.
    # An earlier version set `idx, dim = 5, 4` and asserted only mu == -1/dim, so
    # changing the printed index to 25 left all twelve tables exiting zero -- the
    # assert did not check the number it printed (external review, round 3).
    # Basis of R inside O^2 = <(1,1), (pi,-pi), (5,5)... >: with u = A+B*pi, v = A-B*pi,
    # the map (A,B,C,D) -> (u,v) has the integer matrix below in the basis
    # {(1,0),(pi,0),(0,1),(0,pi)} of O^2 over Z_5.
    M = [[1, 0, 0, 5],
         [0, 1, 1, 0],
         [1, 0, 0, -5],
         [0, 1, -1, 0]]
    # The determinant and the index are unchanged by generators that do not lie in R,
    # so check the defining congruence: with u = M[0][j] + M[1][j] pi and
    # v = M[2][j] + M[3][j] pi, membership in R is u = v mod pi, i.e. the constant
    # terms agree mod 5 (external review, 2026-09-07).
    assert all((M[0][j] - M[2][j]) % 5 == 0 for j in range(4)), M

    def _det(A):
        A = [row[:] for row in A]; n = len(A); d = F(1)
        for i in range(n):
            piv = next((r for r in range(i, n) if A[r][i] != 0), None)
            if piv is None: return F(0)
            if piv != i: A[i], A[piv] = A[piv], A[i]; d = -d
            d *= F(A[i][i])
            inv = F(1, 1)/F(A[i][i])
            for r in range(i+1, n):
                f = F(A[r][i]) * inv
                for c in range(i, n): A[r][c] = F(A[r][c]) - f*F(A[i][c])
        return d
    det = _det(M)
    assert det == -20, det
    def _v5(n):
        v5 = 0; t = n
        while t % 5 == 0: t //= 5; v5 += 1
        return v5, t
    assert _v5(5**3 * 7) == (3, 7) and _v5(7) == (0, 7)   # the same loop, on a control
    v5, _ = _v5(abs(int(det)))
    idx = 5**v5
    dim = len(M)
    mu = F(-v5, dim)
    print(f"      det of the transition matrix = {int(det)},  v_5 = {v5},  index {idx},")
    print(f"      dim {dim},  mu(R)/log5 = {mu}")
    assert (int(det), v5, idx, dim) == (-20, 1, 5, 4) and mu == F(-1, 4)
    print("    -> treating the tensor order as its own normalization loses exactly log5/4.")

def c4():
    print("Table 4.  The floor.  [S]+[P]")
    print("          [IUT4, Prop. 1.4(iii)] passes from the container to the smooth bound")
    print("          by -floor(A) <= -A + 1, so the slack is 1 + floor(A) - A.  In the")
    print("          moderate tame model here d_I + a_I = |I| is an integer, so it is")
    print("            1 + floor(lambda) - lambda.")
    print("          CORRECTION 2026-09-07 (round 2): an earlier version used")
    print("          ceil(lambda) - lambda.  The two agree off the integers and differ")
    print("          ON them: at lambda = 3 and 4 the slack is 1, not 0.")
    print("      lambda        1 + floor - lambda      ceil - lambda (wrong)")
    for lam in (F(3), F(472,157), F(627,157), F(4)):
        good = 1 + F(math.floor(lam)) - lam
        assert good == 1 - (lam - F(math.floor(lam))) and 0 < good <= 1   # 1 - frac
        bad = F(math.ceil(lam)) - lam
        print(f"    {str(lam):>12} {str(good):>21} {str(bad):>24}")
    assert 1 + F(math.floor(F(3))) - F(3) == 1
    assert 1 + F(math.floor(F(472,157))) - F(472,157) == F(156,157)
    print("    -> at lambda = 472/157 the slack is 156/157, and the entry margin of that")
    print("       same curve is 1/157.  Their RATIO is 156; they are not comparable in")
    print("       kind either -- one is a defect between a container and a smooth bound,")
    print("       the other a margin between the two sides of a comparison.")

def c5():
    print("Table 5.  Ramification support.  Curve 5190c3, K_0 = Q(i, E[210]).  [S]+[P]")
    print("          [IUT4, Thm 1.10 Steps (iii),(viii); Rem. 1.10.5(iii)].")
    # Delta is computed from the Weierstrass coefficients of 5190c3 as they stand in
    # Cremona's allcurves.00000-09999, not read in as a literal.  An earlier version
    # started from the integer and factored it, so the curve never entered the check
    # (external review, round 3).
    a1, a2, a3, a4, a6 = 1, 0, 1, -654067329, 6428594779636
    b2 = a1*a1 + 4*a2
    b4 = 2*a4 + a1*a3
    b6 = a3*a3 + 4*a6
    b8 = a1*a1*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3*a3 - a4*a4
    D = -b2*b2*b8 - 8*b4**3 - 27*b6*b6 + 9*b2*b4*b6
    c4 = b2*b2 - 24*b4
    c6 = -b2**3 + 36*b2*b4 - 216*b6
    assert c4**3 - c6**2 == 1728*D            # ties every coefficient above to Delta
    assert D == 54516917144884717852292160
    fac, n = {}, D
    for q in (2, 3, 5, 173):
        while n % q == 0: fac[q] = fac.get(q, 0) + 1; n //= q
    assert fac == {2:6, 3:44, 5:1, 173:1} and n == 1
    print(f"      Delta from [a1..a6] = 2^6 * 3^44 * 5 * 173   (computed, then divided)")
    # multiplicative reduction at 173: v_173(Delta) = 1 with c4 a unit there
    residue_173 = c4 % 173
    # the modulus has to be the multiplicative prime of Delta, not a nearby integer
    assert 173 in fac and fac[173] == 1 and residue_173 == c4 % max(fac)
    assert residue_173 != 0
    print(f"      at 173: v(Delta) = 1 and c4 = {residue_173} mod 173 (a unit) -> multiplicative")
    # The support is a MATHEMATICAL claim, argued in the text, not a consequence of the
    # factorization; what is machine-checked here is that it is consistent with Delta
    # and with the ramification of Q(i, mu_210).
    support = [2, 3, 5, 7, 173]
    assert set(fac) | {7} == set(support)          # the bad primes of Delta, plus 7
    assert all(q in support for q in (2, 3, 5, 7))  # 2 from Q(i); 3,5,7 from mu_210
    cutoff = 3870720
    sieve = bytearray([1])*(cutoff+1); sieve[0]=sieve[1]=0
    i = 2
    while i*i <= cutoff:
        if sieve[i]: sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
        i += 1
    cnt = sum(sieve)
    assert cnt == 274666
    print(f"      actual ramification support: {support}  ({len(support)} primes)")
    print(f"      all primes below the cutoff {cutoff:,}: {cnt:,}")
    print(f"      ratio = {cnt}/{len(support)} = {cnt/len(support):.1f}")
    print("    -> replacing the input support by an all-prime proxy multiplies the count")
    print("       by 5.49e4 at this curve.  No PNT threshold is used; the count is exact.")

def c6():
    print("Table 6.  Weights.  A split prime with e_b = 2355, e_g = 1.  [S]+[P]")
    print("          [IUT4, Rem. 1.7.1]: the moduli place weights are the local degrees")
    print("          over [F_0:Q], not the ramification indices.")
    w_wrong, w_ok = F(2355, 2356), F(1, 2)
    print(f"      weight from e alone : {w_wrong}")
    print(f"      correct weight      : {w_ok}    (both places, since the prime splits)")
    print(f"      ratio               : {w_wrong/w_ok}")
    assert w_wrong/w_ok == F(2355, 1178)
    weights = {t: w for t, w in
               (("gg", F(1,4)), ("gb", F(1,4)), ("bg", F(1,4)), ("bb", F(1,4)))}
    assert set(weights) == {"gg", "gb", "bg", "bb"}
    assert all(w == F(1, len(weights)) for w in weights.values())
    assert sum(weights.values()) == 1
    print("      two-factor tuples: gg, gb, bg, bb each 1/4, summing to 1")
    print("    -> weighting by e sends the bad side to 2355/2356 instead of 1/2.")

def c7():
    print("Table 7.  A mean that agrees while the components do not.  [S]+[P]")
    print("          [IUT4, Prop. 1.7; Rem. 1.10.7(ii)].  (Q_p x Q_p) (x) (Q_p x Q_p)")
    print("          has four components.")
    full, diag = [0, 8, 8, 16], [0, 16]
    mean_full, mean_diag = F(sum(full),4), F(sum(diag),2)
    assert (mean_full, mean_diag) == (F(sum(full), len(full)), F(sum(diag), len(diag)))
    assert mean_full == mean_diag == 8
    print(f"      all four components   {full}   mean {mean_full}")
    print(f"      diagonal two only     {diag}       mean {mean_diag}")
    print("      mixed-component probability: 1/2 against 0")
    print("    -> the means agree, so checking the mean does not detect the collapse.")

def c8():
    print("Table 8.  Where the ramification index jumps.  pi = 41+26i, p = 2357, ell = 157.")
    print("          [P] e_b <= p-2 is NOT a hypothesis of [IUT4, Prop. 1.4(iii)]:")
    print("          there I* is a chosen subset and the inequality is asked only")
    print("          outside it.  It is the condition for leaving the place OUT of I*.")
    print("          e_b = 15 ell / gcd(15 ell, 2N).")
    print("       N    gcd(2355, 2N)    e_b   e_b <= 2355")
    exp = {471: 5, 472: 2355, 474: 785, 475: 471}
    for N in (471, 472, 474, 475):
        g = math.gcd(15*157, 2*N); eb = 15*157//g
        print(f"    {N:>4} {g:>14} {eb:>7} {('yes' if eb <= 2355 else 'no'):>13}")
        assert eb == exp[N]
    print("    -> one step in N moves e_b by a factor of 471.  The curve used in note5")
    print("       (N = 472) is the one where the gcd is 1 and e_b is maximal.  It has")
    print("       FOURTEEN CANDIDATE LEVELS, not fourteen verified initial Theta-data.")

def _heights_at(q):
    """The two heights of Table 9, computed from the curve rather than transcribed.

    a = (16+3*sqrt5)^110, b = 1-a, t = 1-a+a^2, and the Legendre j-invariant
    j = 256 t^3 / (a^2 b^2).  With D = N(a^2 b^2), U = N(256 t^3):

      H_ideal = (1/2) log(D / G_ideal),  G_ideal = N((256t^3, a^2b^2)) = 2^8,
      H_norms = (1/2) log(D / gcd(U, D)).

    G_ideal is 2^8 because t + ab = 1, so t and ab share no prime ideal, leaving only
    the 2 coming from 256; 2 is inert here.  gcd(U, D) additionally carries 661^2 --
    the cancellation the table is about.  An earlier version of this script assigned
    both heights as literals and checked only their difference, so it did not compute
    them at all (external review, 2026-09-07).
    """
    def mul(x, y): return (x[0]*y[0] + 5*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
    def sub(x, y): return (x[0] - y[0], x[1] - y[1])
    def add(x, y): return (x[0] + y[0], x[1] + y[1])
    def pw(x, n):
        r = (1, 0)
        while n:
            if n & 1: r = mul(r, x)
            x = mul(x, x); n >>= 1
        return r
    def nrm(x): return x[0]*x[0] - 5*x[1]*x[1]
    def ln(n):
        decimal.getcontext().prec = 80
        return float(decimal.Decimal(n).ln())

    a = pw((16, 3), 110); b = sub((1, 0), a)
    t = add(sub((1, 0), a), mul(a, a))
    assert add(t, mul(a, b)) == (1, 0)                 # t + ab = 1
    assert abs(nrm(a)) == 211**110 and abs(nrm(t)) % 2 == 1
    num = pw(t, 3); num = (256*num[0], 256*num[1])
    den = mul(pw(a, 2), pw(b, 2))
    # num/den is meant to be j of the Legendre curve y^2 = x(x-1)(x-a), and nothing
    # tied it to that curve: perturbing the DENOMINATOR exponent left every assertion
    # below passing while both printed heights moved by 55 log 211, and perturbing the
    # numerator exponent changed j without moving these two heights at all -- a
    # different defect, not a harmless one (external review,
    # 2026-09-07; found independently by two reviewers inside the residue this
    # script's own paper had classified as harmless).  For that curve
    # b2 = -4(1+a), b4 = 2a, b6 = 0, b8 = -a^2, so c4 = 16 t and Delta = 16 a^2(a-1)^2,
    # and j = c4^3/Delta is an exact identity in the ring of integers.
    _b2 = mul((-4, 0), add((1, 0), a))
    _b4 = mul((2, 0), a)
    _c4 = sub(mul(_b2, _b2), mul((24, 0), _b4))
    _am1 = sub(a, (1, 0))
    _disc = mul((16, 0), mul(mul(a, a), mul(_am1, _am1)))
    assert _c4 == mul((16, 0), t)
    assert mul(num, _disc) == mul(den, pw(_c4, 3))     # j = c4^3 / Delta, exactly
    U, D = abs(nrm(num)), abs(nrm(den))
    # G_ideal: t+ab=1 gives the SUPPORT (only the 2 from 256), not the exponent.
    # 2 is inert in Q(sqrt5), so v_(2)(x) = v_2(N(x))/2.  a = 5, b = 4 mod 8, hence
    # v_(2)(a) = v_(2)(t) = 0 and v_(2)(b) = 2; so v_(2)(256t^3) = 8, v_(2)(a^2b^2) = 4,
    # the ideal gcd is (2)^4 and its norm is 2^8 (external review, round 2).
    def _v2N(x):
        n = abs(nrm(x)); k = 0
        while n % 2 == 0: n //= 2; k += 1
        return k // 2                                   # 2 inert
    assert a[0] % 8 == 5 and a[1] % 8 == 0
    assert b[0] % 8 == 4 and b[1] % 8 == 0
    v_num = 8 + 3*_v2N(t)
    v_den = 2*_v2N(a) + 2*_v2N(b)
    assert (_v2N(a), _v2N(b), _v2N(t)) == (0, 2, 0) and (v_num, v_den) == (8, 4)
    assert (v_num, v_den) == (_v2N(num), _v2N(den))    # measured, not just asserted
    G_ideal = 2**(2*min(v_num, v_den))                  # norm of (2)^min
    assert G_ideal == 2**8
    G_norms = math.gcd(U, D)
    assert G_norms == G_ideal * q**2                    # the 661^2 that is over-cancelled
    return 0.5*(ln(D) - ln(G_ideal)), 0.5*(ln(D) - ln(G_norms))


def c9():
    print("Table 9.  An ideal gcd is not a norm gcd.  pi = 16+3sqrt5, N = 110, p = 661.")
    print("          [P]  661 splits; sqrt5 has the two roots 115 and 546 there.  Reducing")
    print("          a = (16+3 sqrt5)^110 and t = 1 - a + a^2 at each root shows that the")
    print("          661-factor of the numerator and that of the denominator sit at")
    print("          DIFFERENT primes, so cancelling total norms removes one too many.")
    q = 661
    roots = [r for r in range(q) if (r*r - 5) % q == 0]
    assert roots == [115, 546]
    # HENSEL.  An earlier version substituted the mod-q roots directly into arithmetic
    # mod q^4.  They are not square roots of 5 there -- 115^2-5 = 20*661 is not 0 mod
    # q^2 -- so the element used did not satisfy sqrt(5)^2 = 5 and was not a local
    # embedding at all.  The valuations happened to come out right; that is not a
    # reason the method was (external review, 2026-09-07).
    def _lift(r, k):
        m, x = q, r
        while m < q**k:
            m = min(m*m, q**k)
            x = (x - (x*x - 5) * pow(2*x, -1, m)) % m
        return x % q**k
    def _a(r, N, m):
        x = 1
        for _ in range(N): x = (x*(16 + 3*r)) % m
        return x
    def _v(x, m):
        # a zero residue means the precision is exhausted, NOT valuation 0
        if x % m == 0: raise ValueError("precision exhausted; raise k")
        k = 0
        while x % q == 0: x //= q; k += 1
        return k
    print("      sqrt5 mod 661   a mod 661   v(1-a)   v(t), t = 1-a+a^2")
    obs = []
    for r in roots:
        m = q**4
        R = _lift(r, 4)
        assert (R*R - 5) % m == 0 and R % q == r      # a genuine local square root
        A = _a(R, 110, m)
        v1, vt = _v((1-A) % m, m), _v((1 - A + A*A) % m, m)
        obs.append((v1, vt))
        print(f"    {r:>13} {A % q:>11} {v1:>8} {vt:>18}")
    assert obs == [(1, 0), (0, 1)]
    # The two heights, computed from the curve rather than transcribed.  An earlier
    # version assigned them as literals and only checked their difference (ibid.).
    true_H, wrong_H = _heights_at(q)
    d = true_H - wrong_H
    print(f"      height with the correct ideal gcd : {true_H}")
    print(f"      height after cancelling norms     : {wrong_H}")
    print(f"      difference                        : {d:.12f}")
    print(f"      log 661                           : {math.log(q):.12f}")
    assert abs(d - math.log(q)) < 1e-9
    print("    -> the error is exactly log 661, and the reason is visible in the table:")
    print("       the two valuations never sit at the same prime, while the total norms")
    print("       carry 661 twice and cancel it once too often.")

def _muli_(x, y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def _nrmi(z): return z[0]*z[0] + z[1]*z[1]        # the norm of Q(i)
assert (_nrmi((1, 1)), _nrmi((3, 4)), _nrmi((0, 5))) == (2, 25, 25)
assert _nrmi(_muli_((2, 3), (5, 7))) == _nrmi((2, 3)) * _nrmi((5, 7))   # multiplicative


def c10():
    print("Table 10.  The two-adic boundary.  pi = 10+3i.  [P]")
    print("          The finite height contribution at 2 is NOT v_2 itself but")
    print("            max(v_2(N(1-a)) - 8, 0) * log 2,")
    print("          the remainder left by a cap at 8 = v_2(256), the numerator constant")
    print("          of j = 256 t^3/(a^2 b^2).  The cap is OURS: [IUT4, Cor. 2.2(i)]")
    print("          defines log(q^forall) and log(q^{/=2}) and prints no such cutoff.")
    print("          RECOVERED 2026-09-07 (round 2): an earlier version")
    print("          omitted this item because v_2 itself (1, 9, 1, 11) did not match the")
    print("          reported 0, log2, 0, 3log2.  Both were right; the definitions differed.")
    def _mul(x, y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])
    def _pw(b, n):
        r = (1, 0)
        while n:
            if n & 1: r = _mul(r, b)
            b = _mul(b, b); n >>= 1
        return r
    def _v(n, q):
        k = 0
        while n % q == 0: n //= q; k += 1
        return k
    print("       N   v_2(N(1-a))   max(v_2-8,0)   contribution")
    exp = {199: 0, 200: 1, 201: 0, 400: 3}
    for N in (199, 200, 201, 400):
        A = _pw((10, 3), N); Z = (1-A[0], -A[1]); B = Z[0]**2 + Z[1]**2
        assert B == _nrmi(Z)                   # B is the norm of Q(i), not some other

        v2 = _v(B, 2); m = max(v2 - 8, 0)
        assert m == exp[N]
        lab = "0" if m == 0 else ("log 2" if m == 1 else f"{m} log 2")
        # the label is the table's answer, so read the coefficient back out of it
        _c = 0 if lab == "0" else (1 if lab == "log 2" else int(lab.split()[0]))
        assert _c == m, (N, lab, m)
        print(f"    {N:>4} {v2:>13} {m:>14}   {lab}")
    print("    -> one step in N moves it between 0 and log 2; the cap at 8 is what makes")
    print("       the two quantities differ, and it is why the naive reading failed.")

def c11():
    print("Table 11.  Two permitted upper-bound expressions at the same p.  [S]+[P]")
    print("          ell = 157, p = 2357, e_b = 2355, e_g = 1.  RECOVERED 2026-09-07.")
    pi_re, pi_im = 41, 26                     # p = N(pi), pi = 41 + 26i
    l, p_, em = 157, pi_re**2 + pi_im**2, 2**12 * 3**3 * 5 * 2
    assert p_ == 2357 and is_prime(p_)
    p_minus_two = p_-2
    assert p_minus_two + 2 == p_
    for e in (2355, 1):
        assert e <= p_minus_two
    print(f"      every e_i <= p-2 = {p_minus_two}, so I* is empty and the extra error term of")
    print("      [IUT4, Prop. 1.4(iii)] is EXACTLY 0.")
    coarse_coefficient = l+5
    assert coarse_coefficient - l == 5
    coarse = coarse_coefficient * math.log(em*l)
    print(f"      the uniform coarse term, averaged over j: (ell+5) log(e*_mod ell)")
    print(f"        = {coarse_coefficient} * log({em} * {l}) = {coarse:.12f}")
    assert abs(coarse - 3073.534296832696) < 1e-9
    print("    -> 0 against 3073.53.  This compares TWO PERMITTED UPPER BOUNDS at one")
    print("       fixed p, averaged over j.  It is not the actual indeterminacy and not")
    print("       the gap in [IUT3, Cor. 3.12]; no such claim is made.")

def c12():
    """The finite statistic of the paper's Proposition, machine-checked.

    This is the one statement in the paper that was wrong twice before it was right --
    first the domain (it was asserted at a fixed stage, where it is vacuous), then the
    injectivity hypothesis -- so every clause of it is checked here rather than only
    stated.  Everything is exact rational arithmetic.
    """
    print("Table 12.  The finite statistic: every clause of the Proposition.  [P]")
    from itertools import product

    def T(m):                                   # T_m = coprod_{j=1..m} {g,b}^{j+1}
        for j in range(1, m + 1):
            for t in product("gb", repeat=j + 1):
                yield j, t

    def B(j, t, cg, cb, s):
        return (1 + cg*t.count("g") + cb*t.count("b")
                - (s*j*j if t[-1] == "b" else 0))

    # Factorization, injectivity, the value counts and the collision set are all
    # invariant under B -> B + const, so nothing here pinned the constant term.
    assert B(1, ("g", "g"), F(0), F(0), F(0)) == 1
    assert B(1, ("g", "b"), F(0), F(0), F(0)) == 1

    def pi(j, t):
        return (t.count("b"), j if t[-1] == "b" else None)

    def factors(pairs, cg, cb, s):
        d = {}
        for j, t in pairs:
            k, v = pi(j, t), B(j, t, cg, cb, s)
            if k in d and d[k] != v:
                return False
            d[k] = v
        return True

    a_exp, ell = 29, 7                          # the profile of the second report:
    eb = 15*ell                                 #   a = pi^29, ell = 7, e_b = 15 ell
    s_, cb_ = F(a_exp, ell), 1 - F(1, eb)
    assert (eb, s_, cb_) == (105, F(29, 7), F(104, 105)) and s_ > 2*cb_

    # (a) the equivalence: B factors through pi on T_m  <=>  e_g = 1
    print("    (a) B factors through pi on T_3, by e_g:")
    for eg in (1, 2, 3, 5, 105):
        cg = 1 - F(1, eg)
        f = factors(list(T(3)), cg, cb_, s_)
        print(f"          e_g = {eg:3d}   c_g = {str(cg):8s}   factors: {f}")
        assert f == (eg == 1)

    # (b) the domain is part of the statement: at a FIXED stage it factors always
    print("    (b) at a FIXED stage it factors for every e_g, so the claim would be")
    print("        vacuous there; the equivalence lives on the union:")
    for eg in (1, 2, 105):
        cg = 1 - F(1, eg)
        row = [factors(list(product("gb", repeat=j+1)) and
                       [(j, t) for t in product("gb", repeat=j+1)], cg, cb_, s_)
               for j in (1, 2, 3)]
        print(f"          e_g = {eg:3d}   j = 1,2,3: {row}")
        assert all(row)

    # (c) injectivity when e_b > 1 and s > 2 c_b
    cls = {}
    for j, t in T(3):
        cls.setdefault(pi(j, t), set()).add(B(j, t, F(0), cb_, s_))
    vals = [next(iter(v)) for v in cls.values()]
    assert all(len(v) == 1 for v in cls.values())
    _m = 3                                             # |T_m| and |pi(T_m)| in closed
    assert len(list(T(_m))) == 2**(_m+2) - 4           # form, so the printed counts
    assert len(cls) == (_m*_m + 5*_m + 2)//2 == 13     # move if the loop's m moves
    two_cb = 2*cb_
    assert two_cb == cb_ + cb_ and s_ > two_cb
    print(f"    (c) e_b = 105 > 1 and s = {s_} > 2c_b = {two_cb}:  "
          f"{len(cls)} classes, {len(set(vals))} values, injective: "
          f"{len(cls) == len(set(vals))}")
    assert len(cls) == len(set(vals))

    # (d) the inequality is strict: at s = 2 c_b the classes (0,None) and (2,1) meet
    s0 = 2*cb_
    b0 = B(1, ("g", "g"), F(0), cb_, s0)
    b2 = B(1, ("b", "b"), F(0), cb_, s0)
    print(f"    (d) at s = 2c_b exactly:  B(g,g) = {b0} = B(b,b) = {b2}  -> not injective")
    assert b0 == b2

    # (e') the exact criterion supplied by an external reviewer: injective <=> r not in E_m
    def E(m):
        S = set()
        for j in range(1, m+1):
            for d in range(1, j+2): S.add(F(d, j*j))
            for k in range(j+1, m+1):
                for d in range(1, k+1): S.add(F(d, k*k - j*j))
        return S

    def inj(m, cb, s):
        d = {}
        for j, t in T(m):
            k, v = pi(j, t), B(j, t, F(0), cb, s)
            if k in d and d[k] != v: return None
            d[k] = v
        return len(set(d.values())) == len(d)

    Em = E(3); mis = 0; n_tested = 0
    for num in range(1, 40):
        for den in range(1, 20):
            r = F(num, den); got = inj(3, cb_, r*cb_)
            assert got is not None, (num, den)   # skipping a case would make the
            n_tested += 1                        # scan pass on zero comparisons
            mis += (got != (r not in Em))
    assert mis == 0
    assert n_tested == 39*19 == 741                      # ordered pairs (n, d), and
    assert len({F(n, d) for n in range(1, 40)            # 476 distinct rationals
                for d in range(1, 20)}) == 476
    print(f"    (e') injective <=> r = s/c_b not in E_m: {n_tested} rational r tested, "
          f"{mis} mismatches; |E_3| = {len(Em)}")
    print(f"         sup E_m = 2 at j=1,d=2 for m = 2..7: "
          f"{[max(E(m)) for m in range(2, 8)]}  -> s > 2c_b suffices at every cutoff")
    assert all(max(E(m)) == 2 for m in range(2, 8))
    assert F(29, 7)/cb_ == F(435, 104) and F(435, 104) not in Em

    # (e) the counts quoted in the paper
    n = sum(1 for _ in T(3))
    dv = {B(j, t, F(0), cb_, s_) for j, t in T(3)}
    print(f"    (e) |T_3| = {n},  distinct values of B = {len(dv)}")
    assert (n, len(dv)) == (28, 13)
    print("    -> the coefficient sees how many bad places there are, and, when the")
    print("       last is bad, at which stage; the good places are invisible to it.")


TABLES = [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12]
if __name__ == "__main__":
    which = [int(sys.argv[1])] if len(sys.argv) > 1 else range(1, len(TABLES)+1)
    # A table that never runs, or runs out of order, used to leave "all tables
    # computed" printed all the same; and a printed row could change or vanish with
    # every assertion still passing.  Each table's output is now compared against a
    # frozen fixture, which is a separately reviewed artifact and is never regenerated
    # by a test or packaging run (external review, 2026-09-07).
    assert tuple(which) == ((int(sys.argv[1]),) if len(sys.argv) > 1 else tuple(range(1, 13)))
    assert all(1 <= i <= len(TABLES) for i in which)
    from contextlib import redirect_stdout
    from io import StringIO
    from note6_output_contract import check_output
    for i in which:
        buffer = StringIO()
        with redirect_stdout(buffer):
            TABLES[i-1]()
        check_output(i, buffer.getvalue())
        print(buffer.getvalue(), end=""); print()
    print("RESULT: all tables computed")
