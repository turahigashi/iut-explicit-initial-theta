#!/usr/bin/env python3
"""The additive bridge: in a + b = c the exponent of a prime in one term reappears as the depth (distance to 1)
of the ratio of the other two, and so as the p-adic valuation of its logarithm.

triples_rows()  four well-known abc triples: for each odd prime p with p^e || (one term), e >= 2, the p-adic
                valuation of log_p(ratio of the other two) computed from the series, and the primes in the ratio.
data_rows()     the seven initial Theta-data (Legendre form over a quadratic field, local data as published with
                the note [TC]): over the same set V^bad of places as the program of [TC] (ord_v(q) > 0, not above
                2, 3, 5 or ell, ord_v(q) not divisible by ell), the bridge depth d_v = ord_v(q)/2, the gaps
                (j^2 - 1) d_v for the labels j = 1, ..., ell*, and the label-averaged gap summed with the weights
                f_v log p_v / [F:Q], that is (k - 1)/2 times sum ord_v(q) f_v log p_v / [F:Q]. It is compared with
                the wall (k - 1)Q of Corollary 3.12, Q = |log qq| = sum ord_v(q) f_v log p_v / (2 ell [F:Q])
                (the q-pilot is qq = q^(1/(2 ell))): the gap is exactly ell times the wall."""
import os
from math import log

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = ["D211", "D109", "D2", "D3", "D18", "D15", "D2357"]
TRIPLES = [(2, 3**10 * 109, 23**5), (11**2, 3**2 * 5**6 * 7**3, 2**21 * 23), (1, 2 * 3**7, 5**4 * 7),
           (283, 5**11 * 13**2, 2**8 * 3**8 * 17**3)]


def factor(n):
    out, d = {}, 2
    n = abs(n)
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def vp(n, p):
    if n == 0:
        return 10**9
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def vp_log(num, den, p, prec):
    """v_p(log_p(num/den)) for an odd prime p and num/den = 1 mod p, from the series log(1+y) = sum (-1)^(n+1) y^n/n
    computed modulo p^prec (exact as long as the answer is below prec)."""
    extra = 12
    M = p ** (prec + extra)
    y = (num * pow(den, -1, M) - 1) % M
    assert y % p == 0
    s, yn = 0, 1
    for n in range(1, 6 * prec + 20):
        yn = (yn * y) % M
        e = vp(n, p)
        m = n // p**e
        t = (yn // p**e) * pow(m, -1, M)        # y^n is divisible by p^n, so by p^e
        s = (s + (t if n % 2 else -t)) % M
    s %= p**prec
    return vp(s, p) if s else prec


def triples_rows():
    rows = []
    for a, b, c in TRIPLES:
        assert a + b == c
        rad = 1
        for q in factor(a * b * c):
            rad *= q
        quality = log(c) / log(rad)
        items = []
        for name, x in (("a", a), ("b", b), ("c", c)):
            for p, e in sorted(factor(x).items()):
                if p == 2 or e < 2:
                    continue
                if name == "a":
                    num, den, ratio = b, c, "b/c"
                elif name == "b":
                    num, den, ratio = a, c, "a/c"
                else:
                    num, den, ratio = -a, b, "−a/b"
                lv = vp_log(num, den, p, e + 6)
                others = sorted(set(factor(num)) | set(factor(den)))
                items.append(dict(p=p, e=e, term=name, ratio=ratio, vlog=lv, primes=others))
        rows.append(dict(a=a, b=b, c=c, rad=rad, quality=quality, items=items))
    return rows


def read_datum(name):
    ell, unf, field, places = None, 0, "", []
    with open(os.path.join(HERE, "..", "data", name + ".txt"), encoding="utf-8") as fh:
        for line in fh:
            if line.startswith("# local data"):
                field = line.split("over F = ")[1].strip()
            t = line.split()
            if not t or t[0].startswith("#"):
                continue
            if t[0] == "ell":
                ell = int(t[1])
            elif t[0] == "unfactored":
                unf = int(t[1])
            elif t[0] == "place":
                places.append(dict(label=t[1], p=int(t[2]), f=int(t[3]), e=int(t[4]), oq=int(t[5])))
    return ell, unf, field, places


def data_rows():
    rows = []
    for name in DATA:
        ell, unf, field, places = read_datum(name)
        ls = (ell - 1) // 2
        k = ell * (ell + 1) / 12
        deg = 2                                               # the seven fields are quadratic
        bad = [v for v in places if v["oq"] > 0 and v["p"] not in (2, 3, 5, ell) and v["oq"] % ell]
        for v in bad:
            assert v["oq"] % 2 == 0, (name, v)
            v["d"] = v["oq"] // 2
            v["vol"] = v["d"] * v["f"] * log(v["p"])
        top = max(bad, key=lambda v: v["vol"])
        S = sum(v["oq"] * v["f"] * log(v["p"]) for v in bad)
        Q = S / (2 * ell * deg)
        gaps = {j: (j * j - 1) * top["d"] for j in range(1, ls + 1)}
        gap_total = (k - 1) / 2 * S / deg
        rows.append(dict(name=name, field=field, ell=ell, ls=ls, k=k, unfactored=unf, nbad=len(bad), top=top,
                         gaps=gaps, S=S, Q=Q, wall=(k - 1) * Q, gap_total=gap_total))
        assert abs(gap_total - ell * (k - 1) * Q) < 1e-9 * gap_total
    return rows


if __name__ == "__main__":
    for r in triples_rows():
        print(f"{r['a']} + {r['b']} = {r['c']}   rad = {r['rad']}   quality = {r['quality']:.4f}")
        for it in r["items"]:
            print(f"   p = {it['p']}: p^{it['e']} || {it['term']};  v_p(log_p({it['ratio']})) = {it['vlog']};"
                  f"  the ratio is a product of powers of {it['primes']}")
            assert it["vlog"] == it["e"]
    print()
    for r in data_rows():
        t = r["top"]
        print(f"{r['name']}: F = {r['field']}, ell = {r['ell']}, ell* = {r['ls']}, k = {r['k']:.4f}"
              f"{'  (unfactored cofactor: the places above it are not counted)' if r['unfactored'] else ''}")
        print(f"   places in V^bad: {r['nbad']};  sum of ord_q f log p = {r['S']:.4f};  Q = |log qq| = {r['Q']:.4f}")
        print(f"   largest bridge region: place {t['label']} (p has {len(str(t['p']))} digits, f = {t['f']}),"
              f" ord_q = {t['oq']}, depth d = {t['d']}")
        js = sorted(r["gaps"])
        show = js if len(js) <= 3 else [1, 2, js[-1]]
        print("   gaps (j^2-1) d: " + ", ".join(f"j={j}: {r['gaps'][j]} levels" for j in show))
        print(f"   label-averaged gap summed over V^bad (weights f log p / [F:Q]) = {r['gap_total']:.4f}"
              f" = ell x wall;  wall (k-1)Q = {r['wall']:.4f}")
