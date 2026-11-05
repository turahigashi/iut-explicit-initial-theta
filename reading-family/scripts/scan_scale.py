#!/usr/bin/env python3
"""q → q^N の族で、残り B_R が N によらない幅に収まることを多くの N で確かめる（ℓ の倍数の N は除く）。
出力：読みごとの B_R（下端・上端）の N についての最小・最大と幅、それに比べた N·a の伸び"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iut_compute as ic
import iut_readings36 as r36

names = sys.argv[1].split(",") if len(sys.argv) > 1 else ["D2", "D211"]
Nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 40
out = {}
for name in names:
    base = ic.InitialThetaData(name, factor_seconds=1)
    Ns = [N for N in range(1, Nmax + 1) if N % base.ell]
    rows = {}
    a1 = None
    for N in Ns:
        res = r36.evaluate(ic.InitialThetaData(name, factor_seconds=1, scale_q=N))
        if N == 1:
            a1 = res["a"]
        for r in res["rows"]:
            key = "・".join(r["reading"])
            d = rows.setdefault(key, dict(lo_min=1e300, lo_max=-1e300, hi_min=1e300, hi_max=-1e300))
            d["lo_min"] = min(d["lo_min"], r["B_lo"]); d["lo_max"] = max(d["lo_max"], r["B_lo"])
            d["hi_min"] = min(d["hi_min"], r["B_hi"]); d["hi_max"] = max(d["hi_max"], r["B_hi"])
    print(f"\n[{name}] N = {Ns[0]}…{Ns[-1]}（{len(Ns)} 個、ℓ = {base.ell} の倍数を除く）、a(N=1) = {a1:.4f}、"
          f"N·a の伸び {(Ns[-1] - Ns[0]) * a1:.1f}")
    print(f"  {'読み':<22}{'B_R 下端の範囲':>26}{'B_R 上端の範囲':>26}{'幅（最大）':>12}")
    wmax = 0
    for key, d in rows.items():
        w = max(d["lo_max"] - d["lo_min"], d["hi_max"] - d["hi_min"])
        wmax = max(wmax, w)
        print(f"  {key:<22}{d['lo_min']:>12.3f}〜{d['lo_max']:<12.3f}{d['hi_min']:>12.3f}〜{d['hi_max']:<12.3f}{w:>10.3f}")
    print(f"  幅の最大 {wmax:.3f}（N·a の伸びの {100 * wmax / ((Ns[-1] - Ns[0]) * a1):.2f}%）")
    out[name] = dict(Ns=Ns, a=a1, rows=rows, width_max=wmax)
json.dump(out, open("results36_scan.json", "w"), ensure_ascii=False, indent=1)
