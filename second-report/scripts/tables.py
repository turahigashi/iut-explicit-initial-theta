#!/usr/bin/env python3
"""The numbers in the tables paper.  Standard library only.

Two things here are INPUTS, not derivations, and each says so where it is printed:
the counts of the Cremona sweep and the local Tate order ord_3(q) = 44 at the two
curves it returns (Table 12).  Everything else is computed from the data.

Each table is printed with the source locator of the quantity it tabulates.  No
statement here depends on a reading of the theory; where a quantity's *significance*
does, that is said in the paper, not here.

    python3 scripts/tables.py            all tables
    python3 scripts/tables.py 3          table 3 only
"""
from fractions import Fraction as F
import math, sys

# ---------- the two data ----------------------------------------------------
def mul5(x, y): return (x[0]*y[0] + 5*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def muli(x, y): return (x[0]*y[0] - x[1]*y[1], x[0]*y[1] + x[1]*y[0])

def datum(mul, pi, N):
    a = (1, 0)
    for _ in range(N): a = mul(a, pi)
    return a

A5 = datum(mul5, (16, 3), 29)                       # first report,  F_mod = Q(sqrt5)
AI = datum(muli, (10, 3), 29)                       # second report, F_mod = Q(i)
N5 = abs((1-A5[0])**2 - 5*A5[1]**2)
NI = (1-AI[0])**2 + AI[1]**2

def factor_small(n, primes):
    f = []
    for q in primes:
        k = 0
        while n % q == 0: n //= q; k += 1
        if k: f.append((q, k))
    return f, n

SMALL = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
         21577, 80621]

def primes_upto(n):
    s = bytearray([1])*n; s[0:2] = b'\0\0'
    for i in range(2, int(n**.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n) if s[i]]

# ---------- tables ----------------------------------------------------------
def t1():
    print("Table 1.  The two data.  [P]  Def 3.1 is [IUT1, Def. 3.1].")
    for nm, a, Nm, p, base in (("Q(sqrt5), pi=16+3sqrt5", A5, N5, 211, "sqrt5"),
                               ("Q(i),     pi=10+3i",     AI, NI, 109, "i")):
        f, c = factor_small(Nm, SMALL)
        print(f"  {nm}")
        print(f"    Norm(a) = {p}^29 ({len(str(abs(a[0]**2 - (5 if base=='sqrt5' else -1)*a[1]**2)))} digits)")
        print(f"    Norm(1-a): {len(str(Nm))} digits = " +
              " * ".join(f"{q}^{k}" if k > 1 else str(q) for q, k in f) +
              f" * C,  C has {len(str(c))} digits")
        print(f"    e_g = 1,  e_b = 105,  ord_p(qbb) = 29/7,  ord_p(q) = 58,  ell = 7")

def t2():
    print("Table 2.  Stage margins.  [P] from [IUT4, Prop. 1.4(iii)] with I* empty;")
    print("          margin = j^2 s - (j+2), s = ord_p(qbb).  Positive iff ord_p(q) > 2 ell (j+2)/j^2.")
    s = F(29, 7)
    print("      j    j^2 s      margin      threshold ord_p(q) >")
    for j in (1, 2, 3):
        print(f"    {j:>3} {str(j*j*s):>8} {str(j*j*s-(j+2)):>10} {str(F(2*7*(j+2), j*j)):>22}")

def t3():
    print("Table 3.  Where the explicit data on record sit.  [P]")
    print("          ord_p(q) = -v_p(j).  Entry condition at j=1 (ell=7): ord_p(q) > 42.")
    print("      datum                          p   ord_p(q)   s=ord/(2*7)   margin  regime")
    for nm, p, o in (("Dupuy-Hilado E11a1 (Q)", 11, 5), ("Cremona 14a1 (Q)", 7, 3),
                     ("Cremona 15a1 (Q)", 5, 4),        ("Cremona 37a1 (Q)", 37, 1),
                     ("first report (Q(sqrt5))", 211, 58), ("second report (Q(i))", 109, 58)):
        s = F(o, 14); m = s - 3
        print(f"    {nm:28s} {p:>5} {o:>9}   {str(s):>11} {float(m):>8.2f}  "
              f"{'NONTRIVIAL' if m > 0 else 'vacuous'}")
    print("    WARNING.  For the four curves over Q the margin formula's own hypotheses fail:")
    # CORRECTED 2026-09-07 (external review, round 19).  An earlier version applied
    # THIS datum's torsion level 105 to curves that do not have it.  [IUT1, Def 3.1(b)]
    # makes E[6] rational over F, so at the reference level 7 the field K contains
    # E[42]; both primes are prime to 42, with Tate orders 5 and 1.
    for _nm, _p, _oq in (("11a1", 11, 5), ("37a1", 37, 1)):
        _eb = 42 // math.gcd(42, _oq)
        assert _eb == 42 and _eb > _p - 2
        print(f"      {_nm}: e_b >= 42/gcd(42,{_oq}) = {_eb} > p-2 = {_p-2}"
              f"   [not 105/gcd(105,{_oq}); 105 is THIS datum's level]")
    print("      14a1: p = ell;   15a1: p divides the torsion level 15;")
    print("      37a1: e > p-2.  Their entries are formula values, not licensed comparisons.")
    print("      Over F_mod = Q there is in any case no mixed place [First, Cor. 3(i)].")

def t4():
    print("Table 4.  Tuple types at a split prime.  [S]+[P]")
    print("          [IUT4, Thm 1.10, Step (v)] fixes lambda by the status of the LAST")
    print("          index v_j alone.  ASCII TRANSCRIPTION (the source's typography is")
    print("          not reproduced here):  'lambda' to be 0 if v_j in V^good;")
    print("          'lambda' to be ord of qbb_{v_j}^{j^2} if v_j in V^bad,")
    print("          where qbb = q^(1/(2 ell)) is the DOUBLE-UNDERLINED q of")
    print("          [IUT1, Ex. 3.2(iv)] -- not q itself.  (An earlier version of this")
    print("          line printed q, naming a quantity 2*ell times larger than the one")
    print("          the arithmetic below actually uses.)")
    print("          d_I = (j+1) - sum_i 1/e_{t_i};  bound = -lambda + d_I + 1;")
    print("          co(t) = -sum_i 1/e_{t_i}  (the COEFFICIENT expression; the packet")
    print("          log_p(R_I^x) lies below co(t)*log p by max(k-1,0)(e-1)/(2e)*log p")
    print("          for k bad entries -- ZERO for k=0,1; 52/105 for k=2, 104/105 for")
    print("          k=3 at e_b=105.  The plain (k-1) form is negative at k=0.)")
    print("")
    print("          CORRECTION 2026-09-07 (external review).  An earlier version put")
    print("          lambda = j^2 s on EVERY type, including the all-good ones, and")
    print("          reported a single 'mixed' row.  Both are fixed: lambda carries the")
    print("          indicator 1{t_j = b}, and tuples are listed individually, since")
    print("          (g,b) and (b,g) have the same co and different bounds.")
    s_ = F(29, 7); eg, eb = 1, 105
    print("       j  tuple      co(t)       bd(t)     co - bd")
    seen = {}
    for j, ts in ((1, ["gg","gb","bg","bb"]), (2, ["ggg","gbb","bbg","bbb"])):
        for t in ts:
            inv = sum(F(1, eg) if c == "g" else F(1, eb) for c in t)
            dI = F(j+1) - inv
            lam = F(j*j)*s_ if t[-1] == "b" else F(0)
            bound = -lam + dI + 1
            d = -inv - bound
            seen[(j, t)] = d
            print(f"    {j:>4}  {t:<9} {str(-inv):>9} {str(bound):>12} {str(d):>13}")
        print("")
    assert seen[(1,"gb")] == seen[(1,"bb")] == F(8,7)
    assert seen[(1,"gg")] == seen[(1,"bg")] == F(-3)
    assert seen[(2,"gbb")] == seen[(2,"bbb")] == F(88,7)
    assert seen[(2,"ggg")] == seen[(2,"bbg")] == F(-4)
    print("    -> the difference is 8/7 (j=1), 88/7 (j=2) EXACTLY for the tuples whose")
    print("       last entry is bad, and -3, -4 for those whose last entry is good.")
    print("       So it is constant on each of the two classes, not on all types; and")
    print("       'mixed' does not name a value, since (g,b) and (b,g) differ.")

def t5():
    print("Table 5.  Five conditions, and data in the original family that meet all of them.")
    print("          (1) [First, sec.6] entry: ord_p(q) = 2N > 6 ell")
    print("          (2) [IUT4, Cor. 2.2(ii), (C1)]: ell >= sqrt(H_all),  H_all = log of")
    print("              the product of q-parameters over ALL bad places.  (An earlier")
    print("              version said SELECTED here; (C1) is stated for H_all.)")
    print("          (3) [P] non-vacuity of the ell-term, in units of log p:")
    print("              (ell+1)N/24 > (ell+5)*log(e*_mod ell)/log p     <- BOTH sides in log p")
    print("              CORRECTION 2026-09-07: an earlier version compared the left side")
    print("              (log p units) with the right side in nats.  Fixed; two rows moved.")
    print("          (4) [P] e_b = 15 ell/gcd(15 ell, ord) <= p-2: the condition under")
    print("              which the place may be left OUT of I* in [IUT4, Prop. 1.4(iii)]")
    print("              -- NOT a hypothesis for the estimate to apply (see note below)")
    print("          (5) [IUT1, Def. 3.1(c)]: ell prime to the order of the q-parameter")
    print("              *** THE COLUMN BELOW TESTS ONLY THE DESIGNATED PLACE ***, where")
    print("              the order is 2N, so the check is ell not dividing 2N.  At the")
    print("              REMAINING bad places the condition needs v_p(1-a) prime to ell,")
    print("              for which power-freeness of Norm(1-a) is sufficient; that is an")
    print("              separate computation -- scripts/powerfree_certificate.py, which")
    print("              ships here -- not this column.  (Continued:)")
    print("     H_all = N log p + log N(1-a) - min(v_2, 8) log 2      <- (C1) uses this")
    print("     H_sel = N log p + log N(1-a) - v_2 log 2 - v_ell log ell  <- selected places")
    print("     CORRECTION 2026-09-07 (round 2): H_sel dropped the place over 7 for every")
    print("     row; it must drop the place over THAT ROW's ell.  At N=114, ell=37 one has")
    print("     v_37 = 2, so the two heights differ there by 2 log 37; they agree only at")
    print("     N=29, where ell = 7 and v_7 = 0.")
    em = 2**12*3**3*5*2; LP = math.log(211)
    def mul5(x, y): return (x[0]*y[0] + 5*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
    def val(n, q):
        k = 0
        while n % q == 0: n //= q; k += 1
        return k
    print("        N    ell     H_all  sqrt(H)    e_b   (1)(2)(3)(4)(5)     H_sel")
    for N, l in ((29,7), (114,37), (160,53), (480,73), (480,79)):
        a = (1,0)
        for _ in range(N): a = mul5(a, (16,3))
        Nom = abs((1-a[0])**2 - 5*a[1]**2)
        # [IUT4, Cor. 2.2(ii)] (C1) is stated for H_all = log(q^forall), which keeps every
        # nonarchimedean place; the cancellation at 2 is capped at 8.  The SELECTED-place
        # height (dropping 2 and ell outright) is a different number and is printed too.
        Hsel = N*LP + math.log(Nom) - val(Nom,2)*math.log(2) - val(Nom,l)*math.log(l)
        H = N*LP + math.log(Nom) - min(val(Nom,2), 8)*math.log(2)
        ordq = 2*N; eb = 15*l//math.gcd(15*l, ordq)
        c = (ordq > 6*l, l >= math.sqrt(H),
             (l+1)*N/24 > (l+5)*math.log(em*l)/LP,      # BOTH sides in units of log p
             eb <= 209, ordq % l != 0)
        print(f"    {N:>5} {l:>6} {H:>9.2f} {math.sqrt(H):>9.3f} {eb:>6}    " +
              " ".join(" o " if x else " X " for x in c) +
              (" <-all5" if all(c) else "       ") + f" {Hsel:>10.2f}")
    print("     N=29, ell=7 fails (2) and (3).  The other four rows meet all five.")
    print("     (c) HEIGHT.  An earlier version put H_sel in the column used for (2).")
    print("         (C1) is stated for H_all = log(q^forall); the two differ at N=160")
    print("         and N=480 (v_2 = 12, v_7 = 2 there).  The verdicts do not change.")
    print("     The first of the rows LISTED here at which all five hold is N=114, ell=37.")
    print("     This is not monotone in N: at N=116, ell=37 one has e_b = 555 > 209, so")
    print("     condition (4) fails there even though (1) (2) (3) (5) hold.")
    print("")
    print("     CORRECTION 2026-09-07 (external review).  Two errors are fixed here.")
    print("     (a) UNITS.  Condition (3) compared a left side in units of log p with a")
    print("         right side in nats.  Dividing the right side by log p moves N=114 and")
    print("         N=160 from X to o, and the first all-five point from N=480 to N=114.")
    print("     (b) STATUS OF (4).  e_b <= p-2 is NOT a hypothesis of [IUT4, Prop 1.4(iii)].")
    print("         There I* is a CHOSEN subset and the condition p-2 >= e_i is required")
    print("         only for i NOT in I*.  Thm 1.10 Step (v) takes I* to be exactly the set")
    print("         with e_{v_i} > p-2, and (R4) absorbs those into 4(j+1)*ell*_mod -- the")
    print("         same iota-term tabulated in Table 9.  So the estimate applies either")
    print("         way; (4) is the condition under which an index may be left OUT of I*,")
    print("         i.e. the condition for the error-free form of the bound.")
    print("     An earlier version also used e_b = 15 ell without the gcd and omitted (5).")

def t6():
    print("Table 6.  Coefficients of [IUT4, Thm 1.10] at ell = 7.  [S] printed in the source.")
    l = 7; ls = (l-1)//2; s = F(29, 7)
    print(f"    per-stage coefficient on log(q) (UNROOTED):  j^2/(2 ell) = " +
          ", ".join(str(F(j*j, 2*l)) for j in range(1, ls+1)))
    avg = sum(F(j*j, 2*l) for j in range(1, ls+1))/ls
    print(f"    average over j:  (2 ell*+1)(ell*+1)/(12 ell) = {avg} = (ell+1)/24 = {F(l+1,24)}")
    print(f"    q-side coefficient 1/(2 ell) = {F(1,2*l)};  ratio 12/(ell(ell+1)) = {F(12,l*(l+1))}")
    print("    (On the ROOTED log(qbb) = log(q)/(2 ell) the same coefficients read j^2.)")
    # An earlier version printed a "set-valued diameter" row carrying a locator that is
    # not in this report's bibliography.  The row is used nowhere in the paper, so it is
    # removed rather than given a source it does not have.  (The retired locator is not
    # repeated here: scripts/check_no_drift.py greps for it, and a comment quoting it
    # would trip that guard exactly as a real relapse would.)


def t7():
    print("Table 7.  Local degrees and tensor orders.  [P]")
    print("          f_g = 24 is the Frobenius order of X^2-24X+211 mod 3,5,7 (orders 4,3,8; lcm 24).")
    print("          [IUT3, Prop. 3.2] (which is what [IUT4, Thm 1.10] cites here;")
    print("          Thm 3.11(i)(a) is cited only for the notation): EACH FACTOR, BEFORE")
    print("          tensoring, is a direct sum over the places of V over v_Q -- here 2.")
    print("          (Confirmed at [IUT4, Thm 1.10, proof, Step (iv)], author PDF p.27.")
    print("          This is the count BEFORE tensoring: it is neither the number of")
    print("          tuple components after tensoring nor the split into field factors.)")
    eg, eb, fg, fb = 1, 105, 24, 2
    ag, ab = eg*fg, eb*fb
    print(f"    a_g = e_g f_g = {ag},  a_b = e_b f_b = {ab},  lcm = {math.lcm(ag,ab)}")
    for nm, es in (("(g,g)", [ag,ag]), ("(g,b)", [ag,ab]), ("(b,b)", [ab,ab])):
        n = 1
        for e in es: n *= e
        print(f"      N_t{nm} = {n}" + (f"   -> cylinder weight 1/(N_t 2^2) = 1/{n*4}" if nm=="(g,b)" else ""))
    print("    tensor order:  (g,b) is MAXIMAL (good side unramified) -> normalized gain 0;")
    print(f"                   (b,b) is not:  gain (e-1)/(2e) = {F(eb-1,2*eb)} log p")
    print("    -> a structural difference that only a mixed profile produces.")

def t8():
    print("Table 8.  Container and seed exponents, and the floor slack.  [P]")
    print("          RESTRICTED to tuples whose LAST entry is bad, so lambda = j^2 s.")
    print("          If the last entry is good then lambda = 0 by [IUT4, Thm 1.10,")
    print("          Step (v)] and none of the columns below applies.")
    print("          [IUT4, Thm 1.10, Step (v)] container p^(floor(lambda)-|I|);")
    print("          [IUT4, Prop. 1.4(iii)] bound -lambda+d_I+1, whose floor leaves slack (A).")
    s = F(29, 7); eg, eb = 1, 105
    print("      j   lambda=j^2 s   container floor(l)-|I|   seed ceil(l)   slack (A)")
    for j in (1, 2, 3):
        lam = F(j*j)*s
        dI = F(j+1) - (F(1,eg) + F(j,eb)); aI = F(1,eg) + F(j,eb)
        x = lam - dI - aI; A = 1 - (x - math.floor(x))
        print(f"    {j:>3} {str(lam):>12} {math.floor(lam)-(j+1):>21} {math.ceil(lam):>14} "
              f"{str(F(A).limit_denominator(1000)):>11}")

def t9():
    print("Table 9.  The ratio of the two terms of the averaged upper bound.  [P]")
    print("          [IUT4, Thm 1.10, Step (v)] carries the term 4 iota_vQ ell*_mod with")
    print("          ell*_mod = log(e*_mod ell), iota = 1 when p <= e*_mod ell.")
    l = 7; em = 2**12 * 3**3 * 5 * 2; Lp = math.log(211)
    Ls = math.log(em*l)
    print(f"    e*_mod ell = {em*l:,},  ell*_mod = {Ls:.3f} nat = {Ls/Lp:.3f} log p")
    print(f"    procession average of the term: (ell+5) ell*_mod = {(l+5)*Ls/Lp:.2f} log p")
    print(f"    the q-signal at 211:            (ell+1)/24 * 29 = {float(F(l+1,24)*29):.3f} log p")
    print(f"    ratio = {((l+5)*Ls/Lp)/float(F(l+1,24)*29):.12f}   <- both sides in log p")
    print(f"    (printed without the log p in the denominator it would be "
          f"{((l+5)*Ls)/float(F(l+1,24)*29):.6f}; that form is wrong)")
    print("    -> at these parameters the iota-term is about 3.7x the q-term.  BOTH are")
    print("       terms INSIDE the same upper bound: this says nothing about the distance")
    print("       between that bound and any actual value, nor whether the estimate holds.")


def t10():
    print("Table 10.  The probability measure of [DH-PS, Sec. 7.1] on our datum.  [S]+[P]")
    print("          The measure is stated twice in that paper.  Sec. 1 (p.2) gives the")
    print("          numerator as [F_0,v : Q_p]; Sec. 7.1 (p.22) gives the denominator as")
    print("          [F_0:Q]^(j+1).  Together they determine it, and the degree formula")
    print("          sum_{v|p} [F_0,v : Q_p] = [F_0 : Q] makes it a probability measure.")
    l = 7; F0deg = 2                       # F_0 = Q(sqrt 5) or Q(i); 211 resp. 109 splits
    locdeg = [1, 1]                        # two places above p, each of local degree 1
    assert sum(locdeg) == F0deg, "degree formula"
    jmax = (l - 1)//2
    print(f"    ell = {l},  j runs 1..{jmax};  [F_0:Q] = {F0deg}, places above p: "
          f"{len(locdeg)} of local degree {locdeg}")
    print("      j   tuples 2^(j+1)   Pr per tuple   mass at this j")
    tot = F(0); ntup = 0
    for j in range(1, jmax + 1):
        n = len(locdeg)**(j + 1)
        pr = F(2, l - 1) * F(1, F0deg)**(j + 1)
        tot += n*pr; ntup += n
        print(f"    {j:>3} {n:>15} {str(pr):>14} {str(n*pr):>15}")
    print(f"    total tuples = {ntup},  total mass = {tot}")
    assert tot == 1 and ntup == 28, "not normalised"
    print("    -> normalised; the mixed j=1 tuple carries 1/12.")
    print("    Reading the Sec. 7.1 numerator literally as a K-completion degree instead")
    print("    gives masses far above 1; the Sec. 1 statement fixes the intended field.")


def t11():
    print("Table 11.  Fourteen levels on one curve, and the window that produces them.  [P]")
    print("          L = Q(i), pi = 41+26i (Norm 2357, prime, = 1 mod 4 so split),")
    print("          a = pi^472, E: y^2 = x(x-1)(x-a), F = L(E[15]), K_ell = F(E[ell]).")
    p_, N = 41**2 + 26**2, 472
    assert p_ == 2357 and all(p_ % d for d in range(2, 49)) and p_ % 4 == 1
    ordq = 2*N
    # H_all computed here, not transcribed.  Convention: log of the product of the
    # q-parameters over ALL nonarchimedean places, i.e. [IUT4, Cor. 2.2(i)]'s
    # log(q^forall) -- this INCLUDES the place over 2, as does H_all in Table 5.
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
    _a = _pw((41, 26), N); _z = (1-_a[0], -_a[1]); _Nm = _z[0]**2 + _z[1]**2
    # Table 5's H_sel drops 2 and ell entirely; its H_all and Cor. 2.2(i) keep them:
    # here ord(q) = 2 at the ramified place (1+i) of Q(i), whose normalized
    # contribution is 2*log2/e = log2.  ell = 89..157 does not divide Norm(1-a).
    H = (N*math.log(p_) + math.log(_Nm)
         - _v(_Nm, 2)*math.log(2)          # remove the raw 2-part of the norm
         + math.log(2))                    # add back the place over 2, weight log2
    assert abs(H - 7324.751610927228) < 1e-9, H
    lo, hi = math.sqrt(H), F(N, 3)              # (2) ell >= sqrt(H);  margin>0 <=> ell < N/3
    pr = [q for q in range(2, 200) if q > 1 and all(q % d for d in range(2, int(q**0.5)+1))]
    win = [q for q in pr if lo <= q < hi]
    print(f"    ord_p(q) = 2N = {ordq};  H = {H};  sqrt(H) = {lo:.3f};  N/3 = {float(hi):.3f}")
    print(f"    window sqrt(H) <= ell < N/3 contains {len(win)} primes")
    print("      ell   e_b = 15 ell/gcd   e_b <= p-2   margin (j=1) = s-3")
    for l in win:
        s_ = F(ordq, 2*l); eb = 15*l//math.gcd(15*l, ordq)
        print(f"    {l:>5} {eb:>16} {('o' if eb <= p_-2 else 'X'):>12} {str(s_-3):>20}")
    assert len(win) == 14 and win[0] == 89 and win[-1] == 157
    assert all(_Nm % l for l in win), "some ell divides Norm(1-a)"
    # The two rational primes that can appear in more than one cyclotomic block, and
    # their total valuations in B = Norm(1-a).  Both are below 89, which is what lets
    # blockwise 89th-power-freeness give 89th-power-freeness of B itself.  Computed
    # here rather than transcribed (external review, 2026-09-07).
    v2b, v5b = _v(_Nm, 2), _v(_Nm, 5)
    assert (v2b, v5b) == (9, 2) and max(v2b, v5b) < win[0]
    print(f"    shared primes across blocks: v_2(B) = {v2b}, v_5(B) = {v5b}; both < "
          f"{win[0]} = the smallest ell in the window,")
    print("      which is why blockwise 89th-power-freeness gives it for B itself.")
    print("      (The exhaustive sieve over each block is run by")
    print("       scripts/powerfree_certificate.py, shipped here; its inputs -- the")
    print("       nine norms, the 36 pair gcds and the nine 89th-root bounds, largest")
    print("       24,856 -- are in lean/LargeImaginaryDatum.lean.)")
    print("    [IUT1, Def. 3.1(c)] also needs ell prime to the residue characteristics of")
    print("    the bad places; those lie over p AND over every prime dividing Norm(1-a).")
    print("    Checked: none of the fourteen divides Norm(1-a).")
    assert F(ordq, 2*157) - 3 == F(1, 157)
    assert 15*157 == p_ - 2
    print("    -> the window closes at ell = 157 from two conditions at once:")
    print(f"       margin (1/157, the last positive one) and e_b = 15*157 = {15*157} = p-2.")
    print("    Order condition of [IUT1, Def. 3.1(c)] at the bad places:")
    def _mul(x, y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])
    def _pow(b, n):
        r = (1, 0)
        while n:
            if n & 1: r = _mul(r, b)
            b = _mul(b, b); n >>= 1
        return r
    A = _pow((41, 26), N); Z = (1-A[0], -A[1]); NN = Z[0]**2 + Z[1]**2
    digits = len(str(NN))
    divs = [k for k in range(1, N+1) if N % k == 0]
    # CORRECTION 2026-09-07 (round 2).  The nine blocks are NOT "the eight cyclotomic
    # factors with Phi_4 split".  They are Phi_1, Phi_2, Phi_4, Phi_8, Phi_59, Phi_118,
    # Phi_236 kept whole, together with G_+ = (X^118 + i)/(X^2 - i) and
    # G_- = (X^118 - i)/(X^2 + i), whose product is Phi_472.  Phi_4 is not split.
    blocks = [1, 1, 2, 4, 58, 58, 116, 116, 116]     # degrees of the nine blocks
    nfac = len(blocks)
    assert digits == 1592 and len(divs) == 8 and nfac == 9 and sum(blocks) == N
    print(f"      Norm(1-a) has {digits} digits; a direct 157th-power bound is about "
          f"10^{digits/157:.2f}")
    print(f"      472 = 8*59 has {len(divs)} divisors.  The reduction uses {nfac} blocks:")
    print(f"      Phi_1, Phi_2, Phi_4, Phi_8, Phi_59, Phi_118, Phi_236 kept whole, plus")
    print(f"      G_+ = (X^118+i)/(X^2-i) and G_- = (X^118-i)/(X^2+i), with G_+G_- = Phi_472.")
    print(f"      Degrees {blocks} sum to {sum(blocks)} = N; that is "
          f"{nfac*(nfac-1)//2} pairwise gcds to clear.")
    print("      (The sieve is not run in THIS script; it is run by")
    print("       scripts/powerfree_certificate.py, shipped here.  Its inputs -- the")
    print("       nine norms, the 36 pair gcds and the nine 89th-root bounds, largest")
    print("       24,856 -- are in lean/LargeImaginaryDatum.lean, whose header states")
    print("       that having them does not by itself prove power-freeness;")
    print("       it is not recomputed here.)")


def t12():
    print("Table 12.  The whole tabulated record, not a sample.  [P]")
    print("          Cremona tables of conductor < 10^4 (64687 curves), swept for a")
    print("          SINGLE place of multiplicative reduction with ord_p(q) > 42.")
    print("      (These counts are TRANSCRIBED from an external sweep of Cremona's")
    print("       allcurves.00000-09999, not recomputed here.  ord_3(q) = 44 is likewise")
    print("       taken from that sweep as an INPUT: the Weierstrass coefficients are not")
    print("       read here, so this is the arithmetic that follows FROM 44, not a")
    print("       re-derivation OF 44.)")
    print("      hits with ord_p(q) > 42            80")
    print("      of which the place lies above 2    78   <- excluded by [IUT1, Def. 3.1]")
    print("      remaining (5160j1, 5190c3)          2   place above 3, ord_3(q) = 44")
    l, ordq, p_ = 7, 44, 3
    s_ = F(ordq, 2*l)
    print(f"    at ell = {l}:  s = {s_},  margin = {s_-3} > 0   -> the threshold IS reached")
    # The residue characteristic 3 DIVIDES the torsion level 15*ell = 105, so the
    # prime-to-p ramification formula of [IUT4, Prop. 1.8(vii)] does not apply here
    # at all; an earlier version of this table printed the number it would have given.
    assert 15*l % p_ == 0
    print(f"    p = {p_} divides the torsion level 15*ell = {15*l}, so the prime-to-p")
    print("      ramification formula does not apply at this place.")
    # Independent lower bound, valid whatever that formula would have said: full
    # 3-torsion plus the Weil pairing puts mu_3 in K, and zeta_3 - 1 is a root of the
    # Eisenstein polynomial T^2 + 3T + 3, so Q_3(mu_3)/Q_3 is totally ramified of
    # degree 2.  Hence 2 | e.  (Check the Eisenstein polynomial by expanding
    # (u+1)^2 + (u+1) + 1, the minimal polynomial of zeta_3 evaluated at u = z - 1.)
    assert all((u+1)**2 + (u+1) + 1 == u*u + 3*u + 3 for u in range(-9, 10))
    assert 3 % 3 == 0 and (3 % 9) != 0          # Eisenstein at 3: 3 | 3, 3 | 3, 9 not| 3
    print("      mu_3 c K by the Weil pairing, and zeta_3 - 1 is a root of the Eisenstein")
    print("      polynomial T^2 + 3T + 3, so e(Q_3(mu_3)/Q_3) = 2 and therefore 2 | e.")
    assert p_ - 2 == 1 < 2
    print(f"      In particular e >= 2 > {p_-2} = p-2, so the index cannot be left outside")
    print("      I*; the I* = empty shortcut of [IUT4, Prop. 1.4(iii)] is unavailable here.")
    print("      The proposition itself still applies, with this index placed in I*.")
    print("    -> the entry threshold alone is not a filter; it is one of five conditions.")

def t13():
    print("Table 13.  Residue degrees at 109, and the mixed tensor there.  [P]")
    print("      (An earlier version of the abstract attributed these to an external")
    print("       certificate of the first report.  That report is about 211 and says")
    print("       nothing about 109; the values are computed here instead.)")
    # The two places above 109 in Q(i): i |-> r with r^2 = -1.
    P = 109
    rs = [r for r in range(P) if (r*r + 1) % P == 0]
    def leg(t):
        t %= P
        return 0 if t == 0 else (1 if pow(t, (P-1)//2, P) == 1 else -1)
    good = bad = None
    for r in rs:
        a = pow((10 + 3*r) % P, 29, P)
        if a in (0, 1):
            bad = (r, a)
        else:
            pts = 1 + sum(1 + leg(x*(x-1)*(x-a)) for x in range(P))
            good = (r, a, pts, P + 1 - pts)
    assert bad and good and sorted(rs) == [33, 76]
    print(f"    places above 109:  i = {bad[0]} -> a = {bad[1]} (multiplicative);"
          f"  i = {good[0]} -> a = {good[1]} (good)")
    print(f"    at the good place: {good[2]} points, a_109 = {good[3]}")
    ap = good[3]
    # Frobenius phi satisfies phi^2 = ap*phi - 109 and acts on E[m] through Z[phi]/m.
    # The order in that RING equals the order of the action only when phi mod m is not
    # scalar, and that has to be checked rather than assumed: here disc = ap^2 - 4P is
    # -432 = -2^4 * 3^3, so it vanishes mod 3 and the ring computation proves nothing
    # at m = 3 (external review, 2026-09-07).  m = 5, 7 are settled by the discriminant;
    # m = 3 is settled below on the curve itself.
    disc = ap*ap - 4*P
    assert disc == -432 and disc % 3 == 0 and disc % 5 != 0 and disc % 7 != 0
    def mul(A, B, m):
        (u1, v1), (u2, v2) = A, B
        return ((u1*u2 - v1*v2*P) % m, (u1*v2 + u2*v1 + v1*v2*ap) % m)
    def order_on(m):
        A, phi, n = (1, 0), (0, 1), 0
        while True:
            n += 1
            A = mul(A, phi, m)
            if A == (1 % m, 0):
                return n
            assert n <= 1000
    orders = {}
    for m in (5, 7):
        # disc is a nonzero square-free-of-m unit: the characteristic polynomial has
        # distinct roots mod m, so phi mod m is regular semisimple, hence non-scalar,
        # hence {1, phi} acts faithfully and the ring order IS the matrix order.
        orders[m] = order_on(m)
    # m = 3.  Mod 3 the characteristic polynomial is (X+1)^2, so phi is either -I
    # (order 2) or a non-scalar Jordan block (order 6); the ring returns 6 either way.
    # Decide it on the curve: psi_3 for y^2 = x^3 + Ax^2 + Bx + C is
    #   3x^4 + 4Ax^3 + 6Bx^2 + 12Cx + (4AC - B^2).
    ag = good[1]
    A_, B_, C_ = -(1 + ag), ag, 0
    psi3 = [3, 4*A_, 6*B_, 12*C_, 4*A_*C_ - B_*B_]
    nr = next(d for d in range(2, P) if pow(d, (P-1)//2, P) == P - 1)   # non-residue
    def ev2(co, x):                        # evaluate over F_P^2 = F_P[t]/(t^2 - nr)
        r = (0, 0)
        for c in co:
            r = ((r[0]*x[0] + nr*r[1]*x[1]) % P, (r[0]*x[1] + r[1]*x[0]) % P)
            r = ((r[0] + c) % P, r[1])
        return r
    roots2 = sum(1 for u in range(P) for v in range(P) if ev2(psi3, (u, v)) == (0, 0))
    # One x-root over F_{P^2} means E(F_{P^2})[3] = Z/3, so Frob^2 != 1 on E[3]; the
    # order-2 option is excluded and the Jordan block, of order 6, is the one.
    assert roots2 == 1
    orders[3] = 6
    print(f"    disc = {disc} vanishes mod 3 only; at m = 3 the ring order is not")
    print(f"      decisive, so E[3] is counted directly: psi_3 has {roots2} root over")
    print(f"      F_(109^2), i.e. E(F_(109^2))[3] = Z/3, so Frob^2 != 1 and the order is 6.")
    print(f"      (#E(F_(109^2)) = {112*108} is divisible by 27, so counting points"
          " cannot decide it.)")
    fg = 1
    for v in orders.values():
        fg = fg*v//math.gcd(fg, v)
    print(f"    order of Frobenius on E[3], E[5], E[7]: "
          f"{orders[3]}, {orders[5]}, {orders[7]}  ->  f_g = lcm = {fg}")
    def order_mod(a, n):
        k, x = 1, a % n
        while x != 1:
            x = x*a % n; k += 1
        return k
    fb = order_mod(P, 105)                 # Tate place: unramified of this degree
    print(f"    f_b = ord(109 mod 105) = {fb}")
    eg, eb = 1, 105
    comps = math.gcd(fg, fb)
    per = fg*fb//math.gcd(fg, fb) * eg * eb
    print(f"    mixed tensor: {fg*eg} * {fb*eb} = {fg*eg*fb*eb} = {comps} components"
          f" of degree {per}")
    assert (fg, fb, comps, per) == (12, 6, 6, 1260)
    assert fg*eg*fb*eb == comps*per == 7560 == 12*630
    print("    -> f_g = 12, f_b = 6 here, against 24 and 2 at 211 (Table 1).")


TABLES = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13]
if __name__ == "__main__":
    which = [int(sys.argv[1])] if len(sys.argv) > 1 else range(1, len(TABLES)+1)
    for i in which:
        TABLES[i-1](); print()
    print("RESULT: all tables computed")
