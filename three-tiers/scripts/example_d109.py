"""Table of Section 5: the exact room, the container and the bound of IUT IV, Prop. 1.2(iii),
at the bad place of the datum D109 above p = 109, for the component with every factor at that place.

The place data (ramification index e and ord_p of q-double-bar) are read from the program
iut_compute.py of the walkthrough (folder iut-walkthrough/program of the same repository).
All values are in units of log p; exact rational arithmetic.

Usage:  python3 example_d109.py [path to iut-walkthrough/program]
"""
import math, os, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
PROGRAM = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, '..', '..', 'iut-walkthrough', 'program')
sys.path.insert(0, PROGRAM)
import iut_compute as ic

def floor(x): return x.numerator // x.denominator
def ceil(x): return -((-x.numerator) // x.denominator)

dt = ic.InitialThetaData('D109', factor_seconds=1)
P = 109
above = [v for v in dt.places if v.prime == P]
print(f"D109: l = {dt.ell}, l* = {dt.ell_star}; places of F_mod above {P}:")
for v in above:
    print(f"  {v.name}: good={v.good}  e={v.e}  in V_bad={v.in_Vbad}  ord_p(qbb)={v.rq}")
assert all(v.e is not None and v.e <= P - 2 for v in above), "not small"
bad = [v for v in above if v.in_Vbad]
assert len(bad) == 1
v = bad[0]
e, rq = v.e, F(v.rq)
print(f"bad place {v.name}: e = {e} <= p - 2 = {P - 2}: small; ord_p(qbb) = {rq}")
lp = math.log(P)
print("j | lambda | d_I | exact | container | IV bound | container-exact | bound-exact")
for j in range(1, dt.ell_star + 1):
    lam = j * j * rq
    assert (lam * e).denominator == 1 and lam.denominator != 1      # lambda in (1/e)Z, not an integer
    dI = F((j + 1) * (e - 1), e)
    exact = dI - (ceil(lam) - lam)
    cont = dI + (lam - floor(lam))
    bound = dI + 1
    m = int(lam * e)                                                 # pi-adic order of the theta value
    assert m - ((m - 1) % e) == e * ceil(lam) + 1 - e                # the pivot exponent loE(m)
    print(f"{j} | {lam} | {dI} | {exact} ({float(exact)*lp:.3f}) | {cont} ({float(cont)*lp:.3f}) | "
          f"{bound} ({float(bound)*lp:.3f}) | {cont - exact} | {bound - exact}")
