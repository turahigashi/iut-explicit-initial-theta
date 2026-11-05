#!/usr/bin/env python3
"""Write the local data of the seven initial Theta-data as plain text files, the common input of the two C programs.

The local data are acquired by the elementary program (elementary_height.py: valuations of the j-invariant of
y^2 = x(x-1)(x-a) over F = Q(sqrt D)), which does not use iut_compute.py. Every place above every prime dividing
N(a)N(1-a) is written, with its residue degree f, its ramification index e_F over Q_p, and ord_v(q) (0 when the
reduction is good). The same places are then compared with those of iut_compute.py (the program of the walkthrough),
prime by prime, as multisets of (f, e_F, ord q); the run stops if they differ.

Usage: python3 export_local_data.py <folder with elementary_height.py and iut_compute.py> <output folder>
From the folder two-computations/ (both programs are in ../reading-family/scripts):
    python3 scripts/export_local_data.py ../reading-family/scripts <output folder>
"""
import math
import os
import sys
from collections import Counter

src, outdir = sys.argv[1], sys.argv[2]
sys.path.insert(0, src)
import elementary_height as el  # noqa: E402
import iut_compute as ic  # noqa: E402


def classical_places(name):
    D, x, y, m, k, ell = el.CURVES[name]
    pi = el.Q(D, x, y)
    a = pi ** m * pi.conj() ** k
    b = 1 - a
    c = a * a - a + 1
    primes, rest = el.candidate_primes(a, b, el.KNOWN.get(name, []))
    rows = []
    for q in primes:
        K = 12 + 2 * max(abs(el.vq(a.norm(), q)), abs(el.vq(b.norm(), q)), abs(el.vq(c.norm(), q)))
        for nm, f, emb in el.places_over(D, q):
            e_F = 2 if f == 1 and emb is None else 1
            va, vb, vc = el.val(a, q, f, emb, K), el.val(b, q, f, emb, K), el.val(c, q, f, emb, K)
            ordj = 8 * e_F * (q == 2) + 3 * vc - 2 * va - 2 * vb
            rows.append((nm, q, f, e_F, max(-ordj, 0)))
    return D, ell, rows, rest


def main():
    os.makedirs(outdir, exist_ok=True)
    for name in el.CURVES:
        D, ell, rows, rest = classical_places(name)
        # comparison with the places of iut_compute.py (odd primes; it leaves out 2)
        dt = ic.InitialThetaData(name, factor_seconds=1)
        mine = Counter((p, f, e, o) for _, p, f, e, o in rows if p != 2)
        theirs = Counter((v.prime, v.f, v.e_base, v.ord_q_w) for v in dt.places)
        if mine != theirs:
            raise SystemExit(f"{name}: the local data differ: {sorted((mine - theirs).items())} / {sorted((theirs - mine).items())}")
        if bool(rest) != bool(dt.unfactored):
            raise SystemExit(f"{name}: the unfactored parts differ")
        path = os.path.join(outdir, name + ".txt")
        with open(path, "w") as fh:
            fh.write(f"# local data of the initial Theta-datum {name}: E: y^2 = x(x-1)(x-a) over F = Q(sqrt({D}))\n")
            fh.write("# written by export_local_data.py from elementary_height.py; the same as the places of iut_compute.py\n")
            fh.write(f"name {name}\nell {ell}\nD {D}\nunfactored {len(rest)}\n")
            fh.write("# place  prime  f  e_F  ord_q   (one line per place of F above a prime dividing N(a)N(1-a))\n")
            for nm, p, f, e, o in rows:
                fh.write(f"place {nm} {p} {f} {e} {o}\n")
        print(f"{name}: {len(rows)} places, {len(set(p for _, p, *_ in rows))} primes, unfactored {len(rest)}; "
              f"agrees with iut_compute.py")


if __name__ == "__main__":
    main()
