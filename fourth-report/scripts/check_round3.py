"""Exact certificates for the corrected stage margins and selected Tate degrees.

Uses binary powering in Z[sqrt(5)] and rational atanh-series intervals.
Does not implement IUT, p-adic logarithms, or prove admissibility of pi^n families.
Run with Python 3 and assertions enabled; stdout gives the complete certificate.
"""
from fractions import Fraction as Q
from math import gcd


def quadratic_product(x, y):
    a, b = x
    c, d = y
    return a*c + 5*b*d, a*d + b*c


def quadratic_power(x, n):
    ans = (1, 0)
    while n:
        if n & 1:
            ans = quadratic_product(ans, x)
        x = quadratic_product(x, x)
        n >>= 1
    return ans


def valuation(n, p):
    assert n > 0 and p > 1
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def near_one_log_interval(y, terms=60):
    """For 1 <= y <= 2, rigorous positive-series interval for log(y)."""
    assert 1 <= y <= 2
    z = (y - 1) / (y + 1)
    partial = 2*sum((z**(2*k+1))/Q(2*k+1) for k in range(terms))
    tail = 2*z**(2*terms+1)/(Q(2*terms+1)*(1-z*z))
    return partial, partial+tail


def log_interval(x):
    """Positive rational x >= 1, range reduced using exact powers of two."""
    x = Q(x)
    assert x >= 1
    exponent = 0
    while x >= 2:
        x /= 2
        exponent += 1
    a, b = near_one_log_interval(x)
    l2, u2 = near_one_log_interval(Q(2))
    return a+exponent*l2, b+exponent*u2


# The two routines above produce the RIGOROUS enclosures that the height
# comparison below rests on, and neither had a self-test: the factor 2 of the
# atanh series, both exponents in it, and the range reduction could each be
# perturbed with every downstream assertion still passing (mutation test,
# 2026-09-07).
# The anchor is a SECOND, independent series: for 0 < u <= 1 the partial sums of
# log(1+u) = u - u^2/2 + u^3/3 - ... alternate around the true value, so consecutive
# partial sums bracket it.  This is rational throughout -- the script certifies
# with no floating point, and the self-test must not be the one place that does.
def _alt_log_bracket(y, terms=400):
    u = Q(y) - 1
    assert 0 <= u <= 1
    s_n = sum((-1)**(k+1) * u**k / Q(k) for k in range(1, terms+1))
    s_n1 = s_n + (-1)**(terms+2) * u**(terms+1) / Q(terms+1)
    return (s_n, s_n1) if s_n <= s_n1 else (s_n1, s_n)

for _y in (Q(1), Q(5, 4), Q(3, 2), Q(7, 4), Q(2)):
    _lo, _hi = near_one_log_interval(_y)
    _a, _b = _alt_log_bracket(_y)
    assert _lo <= _hi and _a <= _b
    # Both intervals contain log(y), so the narrower must sit inside the wider.
    # Intersection alone is too weak: shrinking the atanh tail bound makes the
    # enclosure non-rigorous while still meeting the other interval.
    if _b - _a <= _hi - _lo:
        assert _lo <= _a and _b <= _hi, _y
    else:
        assert _a <= _lo and _hi <= _b, _y
for _x in (1, Q(3, 2), 2, Q(5, 2), 7, 45, 211, Q(1234, 7)):
    _lo, _hi = log_interval(_x)
    assert _lo <= _hi, _x
    assert _hi - _lo < Q(1, 10**12), _x                   # and the enclosure is narrow
for _u, _v in ((2, 3), (7, 211), (Q(3, 2), 5)):                   # log(uv) = log u + log v,
    _a, _b = log_interval(_u * _v)                                # checked between the
    _c, _d = log_interval(_u)                                     # enclosures, with no
    _e, _f = log_interval(_v)                                     # floating point at all
    assert _c + _e <= _b and _a <= _d + _f, (_u, _v)


def decimal_enclosure(interval, digits=12):
    """Outward-rounded decimal endpoints with integer arithmetic."""
    lo, hi = interval
    scale = 10**digits
    a = (lo.numerator*scale)//lo.denominator
    b = -((-hi.numerator*scale)//hi.denominator)
    return f"({a//scale}.{a%scale:0{digits}d}, {b//scale}.{b%scale:0{digits}d})"


assert decimal_enclosure((Q(1, 2), Q(1, 2)), 3) == "(0.500, 0.500)"
assert decimal_enclosure((Q(1, 3), Q(2, 3)), 4) == "(0.3333, 0.6667)"   # rounded outward


if not __debug__:      # an assert cannot guard against -O: it is itself removed,
    raise SystemExit(  # so every check below would vanish and the run still PASS
        "Run with assertions enabled (do not use python -O).")
A29, B29 = quadratic_power((16, 3), 29)
norm_a = A29*A29 - 5*B29*B29
R = (A29-1)**2 - 5*B29*B29
assert A29 == 1067261374298406947765593518710042015056
assert B29 == 477293796532903168691016059805411153867
assert gcd(A29, B29) == 1
assert gcd(A29-1, B29) == 3
assert norm_a == 211**29
assert R == 25362449986390845063221249700759698691829298140087354726503101384580
assert {p:valuation(R,p) for p in (2,3,5,7)} == {2:2,3:2,5:1,7:0}
assert A29 % 5 == 1
assert [(A29+B29*r)%59 for r in (8,51)] == [58,1]
assert [(A29+B29*r)%211 for r in (65,146)] == [0,26]
print("EXPLICIT pi^29 CERTIFICATE")
print("A29 =", A29)
print("B29 =", B29)
print("gcd(A29,B29) =", gcd(A29,B29))
print("gcd(A29-1,B29) =", gcd(A29-1,B29))
print("Norm(a) =", norm_a)
print("R=Norm(1-a) =", R)
_PS = (2, 3, 5, 7)
print(f"v_p(R), p={','.join(map(str,_PS))} =", {p: valuation(R, p) for p in _PS})
_Q59, _RTS = 59, (8, 51)
assert all((r*r - 5) % _Q59 == 0 for r in _RTS)          # they really are sqrt(5) mod 59
print(f"{_Q59} residues at sqrt5={','.join(map(str,_RTS))} =",
      [(A29 + B29*r) % _Q59 for r in _RTS])

# H_all = log(Norm(a)*R/4); H_ns = log(45), in degree-normalized F0 convention.
Hall = log_interval(Q(norm_a*R, 4))
Hns = log_interval(45)
ratio = (Hns[0]/Hall[1], Hns[1]/Hall[0])
_LO, _HI = Q(123, 10000), Q(124, 10000)
assert _LO < ratio[0] <= ratio[1] < _HI
assert 1 - ratio[1] > 1 - _HI
print("SELECTED TATE-DIVISOR CONTRIBUTIONS (outside 2,7; 1/[F0:Q])")
print("H_all = 29 log(211) + log(R/4) in", decimal_enclosure(Hall))
print("H_ns = log(45) in", decimal_enclosure(Hns))
print("H_ns/H_all in", decimal_enclosure(ratio, 15))
def _dec4(q):                                      # integer formatting, no floats
    n = q.numerator * 10**4 // q.denominator
    assert Q(n, 10**4) == q, q
    return f"{n // 10**4}.{n % 10**4:04d}"
print(f"CERTIFIED {_dec4(_LO)} < H_ns/H_all < {_dec4(_HI)}")
print(f"CERTIFIED discarded fraction > {_dec4(1 - _HI)}")

print("CORRECTED STAGE CERTIFICATES")
s = Q(29,7)
for j, es, want in [(1,[1,105],Q(8,7)),(2,[105,1,105],Q(88,7)),(3,[105,105,1,105],Q(226,7))]:
    assert len(es)==j+1 and all(e <= 211-2 for e in es)
    aI = sum(Q(1,e) for e in es)
    dI = len(es)-aI
    lam = j*j*s
    upper = -lam+dI+1
    seed = -aI
    assert seed-upper == want == j*j*s-(j+2)
    floor = lam.numerator//lam.denominator-(j+1)
    print(f"j={j}: lambda={lam}, dI={dI}, aI={aI}, seed={seed}, upper={upper}, margin={want}, exponent={floor}")
assert -Q(116,7)+Q(208,105)+1 == -Q(1427,105)
assert Q(14)*(2+2)/Q(2*2) == 14
print("j=2 positivity threshold: ord_p(q_Tate) > 14 (not 56)")

print("FAMILY DISTINCTION")
print("A29+B29*sqrt5 is the explicit example, with odd nonsplit bad primes exactly 3,5.")
print("For a=T-sqrt5 and T=2 mod5,19, the deterministic theorem instead gives H_ns=0.")
print("The theorem proving those classifications is written separately; finite checks are not its proof.")
print("PASS: all integer and rational assertions. No floating-point pass/fail.")
