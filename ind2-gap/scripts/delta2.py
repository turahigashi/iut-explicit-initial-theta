"""Delta(D) of lana's Gap.lean, from the closed form of the (Ind2)-term.

ind2Term(i, p, c) = (ord_p(theta) - kappa(theta)) * log p,  theta = qbar_v^{j^2} at v = c(j),
kappa(theta) = max{k : theta * I_v  in  p^k * I_v}  (I_v the log-shell of K_v).
 - always  kappa <= floor(ord theta)          ->  term >= frac(ord theta) * log p
 - small places (p odd, e <= p-2; I_v an O_v-module) ->  kappa = floor(ord theta), term = frac(ord theta) * log p
 - otherwise  kappa >= floor(ord theta) - mu, mu <= max(0, ceil(rho - rho' - frac)),
   rho = outer radius of I_v (program's log_shell_radius), rho' = inner radius 1 + [p=2] - n0/e,
   n0 = floor(e/(p-1)) + 1   (log(1+m^n) = m^n for n > e/(p-1)).
Delta(D) = (1/l*) sum_{j=1}^{l*} sum_{v in V_mod^bad} w_v * term_v(j)."""
import sys, math
from fractions import Fraction as Fr
import os
HERE = os.path.dirname(os.path.abspath(__file__))
PROGRAM = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, '..', '..', 'iut-walkthrough', 'program')
sys.path.insert(0, PROGRAM)
import iut_compute as ic

def floor(x): return x.numerator // x.denominator
def frac(x): return x - floor(x)
def ceil(x): return -floor(-x)

names = sys.argv[2:] or [n for n in ic.DATA if n != 'D2357']
for name in names:
    dt = ic.InitialThetaData(name, factor_seconds=1)
    ls = dt.ell_star
    lo = up = Fr(0)        # in units of sum of rational multiples of log p: keep per-prime coefficients
    lo_f = up_f = 0.0
    absq = 0.0
    rows = []
    for v in dt.bad:
        p, e = v.prime, v.e
        small = (p != 2) and (e is not None) and (e <= p - 2)
        rho = ic.log_shell_radius(p, e)
        n0 = e // (p - 1) + 1
        rho_in = 1 + (1 if p == 2 else 0) - Fr(n0, e)
        s_lo = s_up = Fr(0)
        for j in range(1, ls + 1):
            t = j * j * v.rq
            r = frac(t)
            assert r > 0, (name, p, j, t)         # l does not divide ord(q): never an integer
            mu = 0 if small else max(0, ceil(rho - rho_in - r))
            s_lo += r
            s_up += r + mu
        c_lo = float(v.weight) * float(s_lo / ls) * math.log(p)
        c_up = float(v.weight) * float(s_up / ls) * math.log(p)
        lo_f += c_lo; up_f += c_up
        absq += float(v.weight) * float(v.rq) * math.log(p)   # |log q| of the q-pilot (q-bar = q^{1/2l}), as in iut_compute
        rows.append((v.name, p, e, v.rq, v.weight, small, s_lo / ls, c_lo, c_up))
    print(f"== {name}  l={dt.ell}  l*={ls}  |V_bad|={len(dt.bad)}  |log q|={absq:.4f}")
    print(f"   Delta in [{lo_f:.4f}, {up_f:.4f}]" + ("  (exact)" if abs(lo_f - up_f) < 1e-12 else ""))
    for r in rows:
        print(f"   {r[0]:>6} p={r[1]:<6} e={r[2]:<4} ord_p(qbar)={str(r[3]):<8} w={str(r[4]):<4} "
              f"small={'yes' if r[5] else 'no ':3}  avg_j frac={str(r[6]):<8} ({float(r[6]):.4f})  "
              f"term in [{r[7]:.4f}, {r[8]:.4f}]")
