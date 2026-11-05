#!/usr/bin/env python3
"""Table 2 of the note: for which N each statement fails when q is replaced by q^N.

For a reading R with (Ind1)-axis r, split point x = x_r and remainder B_R, Theorem 3.3 gives
    Cor_R(D^N)  <=>  (x - 1) N a <= B_R,        IV_R(D^N)  <=>  (k - x) N a <= C - B_R,
and H(D^N) <=> (k - 1) N a <= C.  Here a, k, C and x are those of N = 1 (a and the theta part scale
with N, k, C and x do not), and B_R is replaced by its interval [B_lo, B_hi] at N = 1; by the scan of
scan_scale.py it moves by at most about 26 over N = 1..40.

Usage: python3 thresholds.py [D211 D109 ...]   (default: the six factored data)
"""
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iut_compute as ic  # noqa: E402
import iut_readings36 as r36  # noqa: E402

DEFAULT = ["D211", "D109", "D2", "D3", "D18", "D15"]


def thresholds(name):
    res = r36.evaluate(ic.InitialThetaData(name, factor_seconds=1))
    a, k, C = res["a"], res["k"], res["C"]
    wall = (k - 1) * a
    out = dict(name=name, a=a, k=k, C=C, wall=wall, N_H=C / wall)
    for r in ("V", "L", "L0"):
        x = res["loads"][r]["x"]
        rows = [row for row in res["rows"] if row["reading"][0] == r]
        B_lo = [row["B_lo"] for row in rows]
        B_hi = [row["B_hi"] for row in rows]
        hull = [row for row in rows if row["reading"][3] == "包"]
        d = dict(x=x, n=len(rows))
        if x > 1:
            # Cor fails for every N > B/((x-1)a); the latest start over the readings uses B_hi
            d["cor_fails_by"] = max(B_hi) / ((x - 1) * a)
            d["cor_fails_from_min"] = min(B_lo) / ((x - 1) * a)
        else:
            # x < 1: the load of Cor is negative; Cor holds for N >= -B/((1-x)a) when B < 0
            d["cor_holds_from"] = max(1, max(math.ceil(-b / ((1 - x) * a)) if b < 0 else 1 for b in B_lo))
            d["cor_hull_min_B"] = min(row["B_lo"] for row in hull)
        if k - x > 1e-9:
            d["iv_fails_range"] = ((C - max(B_hi)) / ((k - x) * a), (C - min(B_lo)) / ((k - x) * a))
        else:
            d["iv_all_N"] = all(b <= C for b in B_hi)
        out[r] = d
    return out


def main():
    names = sys.argv[1:] or DEFAULT
    print("Thresholds in N (remainders replaced by their interval at N = 1)")
    print(f"{'datum':<7}{'a':>9}{'wall':>10}{'C':>10}{'H fails':>10}   per (Ind1)-axis")
    for name in names:
        t = thresholds(name)
        print(f"{name:<7}{t['a']:9.3f}{t['wall']:10.3f}{t['C']:10.2f}  N > {t['N_H']:.2f}")
        for r in ("V", "L", "L0"):
            d = t[r]
            s = f"    {r:<3} x = {d['x']:.4f} ({d['n']} readings): "
            if "cor_fails_by" in d:
                s += f"Cor fails for every N > {d['cor_fails_by']:.2f} (in some reading already for N > {d['cor_fails_from_min']:.2f}); "
            else:
                s += (f"Cor holds for every N >= {d['cor_holds_from']} in all readings "
                      f"(least B_R of the hull readings {d['cor_hull_min_B']:.3f}); ")
            if "iv_fails_range" in d:
                lo, hi = d["iv_fails_range"]
                s += f"IV fails for N > {lo:.2f} to {hi:.2f} (least to largest over the readings)"
            else:
                s += "IV holds for every N" if d["iv_all_N"] else "IV fails in some reading"
            print(s)


if __name__ == "__main__":
    main()
