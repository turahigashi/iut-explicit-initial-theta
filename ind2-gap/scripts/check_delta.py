"""Independent re-check of Delta(D) bounds for the note (lower: frac; upper: IV Prop 1.2(i) constants a, b)."""
import sys, math
from fractions import Fraction as Fr
import os
HERE = os.path.dirname(os.path.abspath(__file__))
PROGRAM = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, '..', '..', 'iut-walkthrough', 'program')
sys.path.insert(0, PROGRAM)
import iut_compute as ic

def fl(x): return x.numerator // x.denominator
def frac(x): return x - fl(x)
def ceil(x): return -fl(-x)

def a_const(p, e):  # IUT IV Prop 1.2: a = (1/e) ceil(e/(p-2)) (p>2), 2 (p=2)
    return Fr(2) if p == 2 else Fr(ceil(Fr(e, p - 2)), e)
def b_const(p, e):  # b = floor(log(p e/(p-1))/log p) - 1/e
    x = math.log(p * e / (p - 1)) / math.log(p)
    return Fr(math.floor(x)) - Fr(1, e)

res = {}
for name in [n for n in ic.DATA if n != 'D2357']:
    dt = ic.InitialThetaData(name, factor_seconds=1)
    ell, ls = dt.ell, dt.ell_star
    s = Fr(ell * (ell + 1), 12)
    lo = up = absq = 0.0
    nsmall = nnon = 0
    for v in dt.bad:
        p, e, w, rq = v.prime, v.e, v.weight, v.rq
        ab = a_const(p, e) + b_const(p, e)
        small = (p != 2) and (e <= p - 2)
        assert ab == 0 or not small, (name, p, e, ab)
        if small: nsmall += 1
        else: nnon += 1
        s_lo = s_up = Fr(0)
        for j in range(1, ls + 1):
            t = j * j * rq
            assert frac(t) > 0
            s_lo += frac(t)
            s_up += t - fl(t - ab)
        lo += float(w) * float(s_lo / ls) * math.log(p)
        up += float(w) * float(s_up / ls) * math.log(p)
        absq += float(w) * float(rq) * math.log(p)   # |log q| of the q-pilot (q-bar = q^{1/2l}), as in iut_compute
    main = float(s - 1) * absq
    res[name] = (lo, up, absq, main, nsmall, nnon)
    print(f"{name}: bad={nsmall} small + {nnon} not small  Delta in [{lo:.4f}, {up:.4f}]  |log q|={absq:.4f}  (s-1)|log q|={main:.4f}  ratio [{lo/main:.3f}, {up/main:.3f}]")

# class-number average check
def h_minus(l):  # class number of Q(sqrt(-l)) for l = 3 mod 4 prime, l > 3
    return -sum((pow(a, (l - 1) // 2, l) == 1 and 1 or -1) * a for a in range(1, l)) // l
for l in [7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83, 5, 13, 17, 29, 37, 41]:
    ls = (l - 1) // 2
    for n in range(1, l):
        avg = sum(Fr((j * j * n) % l, l) for j in range(1, ls + 1)) / ls
        chi = 1 if pow(n, (l - 1) // 2, l) == 1 else -1
        pred = Fr(1, 2) - (Fr(chi * h_minus(l), l - 1) if l % 4 == 3 else 0)
        assert avg == pred, (l, n, avg, pred)
print("class-number label average formula: OK for", "7 11 19 23 31 43 47 59 67 71 79 83 (3 mod 4) and 5 13 17 29 37 41 (1 mod 4), all n")
print("h(-l):", {l: h_minus(l) for l in [7, 11, 19, 23, 31, 43, 47]})
