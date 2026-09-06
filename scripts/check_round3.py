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


def decimal_enclosure(interval, digits=12):
    """Outward-rounded decimal endpoints with integer arithmetic."""
    lo, hi = interval
    scale = 10**digits
    a = (lo.numerator*scale)//lo.denominator
    b = -((-hi.numerator*scale)//hi.denominator)
    return f"({a//scale}.{a%scale:0{digits}d}, {b//scale}.{b%scale:0{digits}d})"


assert __debug__, "Assertions must remain enabled."
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
print("v_p(R), p=2,3,5,7 =", {p:valuation(R,p) for p in (2,3,5,7)})
print("59 residues at sqrt5=8,51 =", [(A29+B29*r)%59 for r in (8,51)])

# H_all = log(Norm(a)*R/4); H_ns = log(45), in degree-normalized F0 convention.
Hall = log_interval(Q(norm_a*R, 4))
Hns = log_interval(45)
ratio = (Hns[0]/Hall[1], Hns[1]/Hall[0])
assert Q(123,10000) < ratio[0] <= ratio[1] < Q(124,10000)
assert 1-ratio[1] > Q(9876,10000)
print("SELECTED TATE-DIVISOR CONTRIBUTIONS (outside 2,7; 1/[F0:Q])")
print("H_all = 29 log(211) + log(R/4) in", decimal_enclosure(Hall))
print("H_ns = log(45) in", decimal_enclosure(Hns))
print("H_ns/H_all in", decimal_enclosure(ratio, 15))
print("CERTIFIED 0.0123 < H_ns/H_all < 0.0124")
print("CERTIFIED discarded fraction > 0.9876")

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
