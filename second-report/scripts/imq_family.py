#!/usr/bin/env python3
"""The three facts used in the existence family, and the excluded densities
(second report, sections 5 and 6).  Standard library only.

f(T) = (T^2+1)((T-1)^2+1) = T^4 - 2T^3 + 3T^2 - 2T + 2 = Norm(a)Norm(1-a) for a = T - i.
"""
import sys

def f(A): return (A*A + 1) * ((A-1)**2 + 1)
def val(n, q):
    k = 0
    while n % q == 0: n //= q; k += 1
    return k
def primes(n):
    s = bytearray([1])*n; s[0:2] = b'\0\0'
    for i in range(2, int(n**.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n) if s[i]]

fails = []
def check(ok, label, extra=""):
    print(f"  {'OK ' if ok else 'FAIL'}  {label}{('   ' + extra) if extra else ''}")
    if not ok: fails.append(label)

print("=== the polynomial ===")
coeffs = [1, -2, 3, -2, 2]
check(all(f(A) == sum(c*A**(4-i) for i, c in enumerate(coeffs)) for A in range(-50, 50)),
      "f(T) = T^4 - 2T^3 + 3T^2 - 2T + 2 on -50..49")
# disc(f): the two quadratic factors have discriminant -4 each, resultant
# Res(T^2+1, (T-1)^2+1) = product over roots i,-i of ((r-1)^2+1) = 5*... computed directly
res = 1
for r in (1j, -1j):
    res *= ((r-1)**2 + 1)
res = int(round(res.real))
disc = (-4)*(-4)*res*res
check(disc == 400, "disc(f) = disc(T^2+1) * disc((T-1)^2+1) * Res^2 = 400",
      f"Res = {res}, disc = {disc}")

print("\n=== (i) v_2(f(A)) = 1 for every A ===")
check(all(val(f(A), 2) == 1 for A in range(-2000, 2000)),
      "v_2(f(A)) = 1 on -2000..1999, so 2^7 never divides f(A)")
check(all(((A*A+1) % 8 == 2) if A % 2 else (((A-1)**2+1) % 8 == 2) for A in range(-2000, 2000)),
      "the odd factor is 2 mod 8 and the other factor is odd")

print("\n=== (ii) q = 3 mod 4 never divides f(A) ===")
bad = [q for q in primes(4000) if q % 4 == 3
       and any(f(A) % q == 0 for A in range(q))]
check(not bad, "no prime q = 3 mod 4 below 4000 divides any f(A)",
      "" if not bad else f"counterexamples {bad[:5]}")
print("      (reason: q | f(A) forces A^2 = -1 or (A-1)^2 = -1 mod q, impossible for q = 3 mod 4)")

print("\n=== (iii) 7 never divides f(A): the residue-characteristic exclusion is automatic ===")
check(all(f(A) % 7 != 0 for A in range(7)), "7 does not divide f(A) for any A mod 7",
      f"values {sorted({f(A) % 7 for A in range(7)})}")
check(7 % 4 == 3, "because 7 = 3 mod 4, so (ii) already excludes residue characteristic 7")
print("      This does NOT give the Tate-order condition at pi: that still needs 7 not | N.")

print("\n=== excluded densities, compared as the same quantity ===")
P = primes(3_000_000)
d_qi = sum(4.0/q**7 for q in P if q >= 13 and q % 4 == 1)
badM = {2, 3, 5, 11, 19, 211}                       # primes dividing M in the first report
d_q5 = sum(4.0/q**7 for q in P if q not in badM)
check(abs(d_qi - 7.38e-8)/7.38e-8 < 5e-3,
      "Q(i):    sum over q >= 13, q = 1 mod 4 of 4/q^7", f"= {d_qi:.4e}")

# --- the bound the proposition actually uses, PROVED rather than approximated -------
# A truncated positive sum is a LOWER bound, so the float check above does not
# establish the "<=" in the proof (internal check, round 15).  Here it is exactly:
# a finite rational partial sum over the primes up to 100, plus an integral tail that
# over-counts by summing over ALL integers n > 100.
from fractions import Fraction as Fr
_part = 4 * sum(Fr(1, q**7) for q in P if 13 <= q <= 100 and q % 4 == 1)
_tail = Fr(4, 6 * 100**6)                      # 4 * int_100^inf x^-7 dx = 2/(3*10^12)
_tot  = _part + _tail
check(_tail == Fr(2, 3 * 10**12), "tail bound 4*int_100^inf x^-7 dx = 2/(3*10^12)")
check(_tot <= Fr(738, 10**10),
      "EXACT: 4*sum_{q>=13, q=1 mod 4} q^-7 <= 7.38e-8",
      f"= {float(_tot):.15e}  (margin {float(Fr(738,10**10) - _tot):.4e})")
check(abs(d_q5 - 4.93e-6)/4.93e-6 < 5e-3,
      "Q(sqrt5): sum over q not dividing M of 4/q^7 ", f"= {d_q5:.4e}")
print(f"  ratio = {d_q5/d_qi:.1f}")
check(abs(d_q5/d_qi - 66.8) < 0.5, "the honest ratio is 66.8, not 194")
share = (4.0/7**7)/d_q5
check(abs(share - 0.985) < 5e-3, "the single term 4/7^7 is 98.5% of the first density",
      f"4/7^7 = {4.0/7**7:.3e}, share = {share:.4f}")
print(f"  (the integral majorant used in the first report is 1/69984 = {1/69984:.4e};")
print( "   it is not the prime sum, and must not be compared with one)")

print("\n" + "=" * 46)
print(f"RESULT: {'PASS - all checks hold' if not fails else 'FAIL: ' + '; '.join(fails)}")
sys.exit(1 if fails else 0)
