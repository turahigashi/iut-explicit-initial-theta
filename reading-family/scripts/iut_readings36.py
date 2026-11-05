#!/usr/bin/env python3
"""系3.12（変種）と IV の上界を 36 通りの読みで計算し、高さの不等式の「荷」が二つの主張のどちらに載るかを出す。

読みの軸（2026-11-04 に数えた 36 通り）
  ① (Ind1)  V / L / L0         ラベル j のテータ値が乗りうる位置（iut_compute.placements）
  ② (Ind3)  容器 / 反復
  ③ (Ind2)  単数 / 格子
  ④ 包      あり / なし        可能な像の合併を正則包で置き換えるか。反復で包なしは純テンソルの合併で体積 0（−∞）なので除く
  ⑤ アルキメデス部分  小 / 大  IV 定理1.10 段階 (vii) の π^{j+1}·B_I ／ III 命題3.2(ii) の単位球（lana の log 殻）
  → 3 × (2×2 + 2) × 2 = 36

二つの主張と高さの不等式（a = |log q̲̲|、k = ℓ(ℓ+1)/12、U(D) は IV の手順の上界、C = U(D) + k·a）
  系3.12_R ：−a ≤ M_R            M_R = −|log Θ|_R（読み R での可能な像の合併の包の log 体積）
  IV_R     ：M_R ≤ U(D)
  高さ H   ：(k − 1)·a ≤ C
  a・k・U(D)・C は読みを受け取らない一つの手順で計算する（iut_height.py と同じ）。読みで変わるのは M_R だけ。

分解（このプログラムで確かめる）
  M_R = Θ_① + B_R
    Θ_① = (1/ℓ*) Σ_j Σ_p log p · E_T[ −min_{i∈P_①(j)} s_i(T) ]   テータ部分。① だけで決まる
    B_R ：残り（容器・単数部分・格子の丸め・包の欠損・アルキメデス部分）。q の位数を N 倍しても有界
  x_① = −Θ_①/a とおくと
    系3.12_R ⟺ (x_① − 1)·a ≤ B_R      （系3.12 の荷 (x−1)a）
    IV_R     ⟺ (k − x_①)·a ≤ C − B_R  （IV の荷 (k−x)a）
    荷の和 = (k−1)·a、予算の和 = C。足すと H になる
  x_V = k（IV の荷は 0）、x_L0 ≤ x_L ≤ k。等号は各素数の上の素点で q の位数がそろうとき

q を q^N にした族（iut_compute の scale_q）：Θ_① は N 倍、B_R は有界、U は −kNa + C（C は不変）。

使い方
  python3 iut_readings36.py --all                 # 7 データ × 36 通り
  python3 iut_readings36.py --data D2
  python3 iut_readings36.py --all --scale 2 3     # q → q^N の族での検査（テータ部分の N 倍・残りの有界性・U の形）
  python3 iut_readings36.py --all --json results36.json
"""
import argparse
import json
import math
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iut_compute as ic  # noqa: E402
import iut_patterns as ip  # noqa: E402
import iut_height as ih  # noqa: E402

AX1 = ["V", "L", "L0"]
AX2 = ["容器", "反復"]
AX3 = ["単数", "格子"]
AX4 = ["包", "包なし"]
AX5 = ["小", "大"]
READINGS = [(a, b, c, d, e) for a in AX1 for b in AX2 for c in AX3 for d in AX4 for e in AX5
            if not (b == "反復" and d == "包なし")]
assert len(READINGS) == 36


def flt(x):
    """浮動小数の量を LogSum に（キー 'num' は係数をそのまま数として足す）"""
    return ic.LogSum({'num': Fr(x)})


def log_int(n):
    """log n を素因数の log の有理係数の和で（正確）"""
    out = ic.LogSum()
    for q, m in __import__('sympy').factorint(n).items():
        out = out + ic.LogSum.log(q, m)
    return out


# ---------------------------------------------------------------------------------------------------------
# テータ部分 Θ_①
# ---------------------------------------------------------------------------------------------------------

def theta_prime(locs, j, P):
    """一つの素数での E_T[−min_{i∈P} s_i(T)]（log p の係数、正確）。位置 P 以外の因子は値に効かない"""
    m, npos = len(locs), len(P)
    total = Fr(0)
    for c in ip.compositions(npos, m):
        pc = Fr(ip.multinom(npos, c))
        for i in range(m):
            pc *= locs[i].w ** c[i]
        present = [i for i in range(m) if c[i] > 0]
        total += pc * (-min(locs[i].s(j) for i in present))
    return total


def theta_part(dt, r1, groups):
    ls = dt.ell_star
    tot = ic.LogSum()
    for j in range(1, ls + 1):
        P = ic.placements(r1, j)
        for p, locs in groups.items():
            tot = tot + ic.LogSum.log(p, theta_prime(locs, j, P))
    return tot * Fr(1, ls)


# ---------------------------------------------------------------------------------------------------------
# 36 通りの M_R（数えた素点だけ。区間 [下端, 上端]）
# ---------------------------------------------------------------------------------------------------------

def arch_large_excess(ls):
    """大きい球の包が π^{j+1}·B_I を超える分 ((m−1)/2)·log 2（m = j+1 因子）のラベル平均 = (ℓ*+1)/4·log 2（lana VcI.md §2(e)）"""
    return ic.LogSum.log(2, Fr(ls + 1, 4))


def arch_defect(ls):
    """大きい球そのもの（包なし）の、その包からの欠損 log(N!)/(2N)（N = 2^j）のラベル平均（lana VcI.md §2(e)）。浮動小数"""
    return flt(sum(math.lgamma(2 ** j + 1) / (2 * 2 ** j) for j in range(1, ls + 1)) / ls)


def shell_defect_max(dt, groups):
    """包なしの容器：⊗𝓘 そのものの log 体積は包より小さく、その差（殻の欠損）は 0 以上 d_I·log p + Σ_{I*}(3 + log e) 以下
    （lana VcI.lean の defectPacket_nonneg・defectPacket_tame_le・abs_shellDefect_add_orderVol_le と
    neg_sum_differentExponent_mul_log_le_orderVol）。成分の期待値は (j+1)·Σ_v w_v·(…) なので、そのラベル平均"""
    ls = dt.ell_star
    ex, fl = ic.LogSum(), 0.0
    for p, locs in groups.items():
        dsum = sum(L.w * Fr(L.e - 1, L.e) for L in locs)                       # 穏分岐の差積の位数（p ∤ e を仮定）
        star = sum(float(L.w) * (3 + math.log(L.e)) for L in locs if L.e > p - 2)
        for j in range(1, ls + 1):
            ex = ex + ic.LogSum.log(p, (j + 1) * dsum)
            fl += (j + 1) * star
    return ex * Fr(1, ls) + flt(fl / ls)


def all_mid(dt, groups):
    """36 通りの M_R の区間（数えた素点＋アルキメデス部分）。12 通りの包の計算（iut_patterns.rhs、π^{j+1}・小）から組み立てる"""
    ls = dt.ell_star
    base = {}
    for r1 in AX1:
        for r2 in AX2:
            for r3 in AX3:
                base[(r1, r2, r3)] = ip.rhs(dt, (r1, r2, r3), groups)
    sd = shell_defect_max(dt, groups)
    big, adef = arch_large_excess(ls), arch_defect(ls)
    out = {}
    for R in READINGS:
        r1, r2, r3, r4, r5 = R
        lo, hi = base[(r1, r2, r3)]
        if r4 == "包なし":                                      # 容器のみ
            u_lo, u_hi = base[(r1, "容器", "単数")]
            lo = u_lo - sd                                      # 合併は θ_i⊗𝓘 の一つを含む（単数でも格子でも）
            # 上端は同じ ②③ の包の上端のまま（合併はその包に含まれる）
        if r5 == "大":
            lo, hi = lo + big, hi + big
            if r4 == "包なし":
                lo, hi = lo - adef, hi - adef
        out[R] = (lo, hi)
    return out, base


# ---------------------------------------------------------------------------------------------------------
# 両端（読みに依らない一つの手順）：a、k、U(D)、C
# ---------------------------------------------------------------------------------------------------------

def ends(dt):
    """iut_height.compute と同じ手順で、渡したデータ（scale_q を含む）について −|log q̲̲| と U(D) を出す。
    U(D) = U_known + U_unknown + (ℓ+5)/4·log π。U_known は数えた素数での IV の上界（命題1.4(iii)、I* は正確な項）"""
    ell, ls = dt.ell, dt.ell_star
    e_star = 2 ** 12 * 3 ** 3 * 5 * 2
    ell_star_mod = math.log(e_star * ell)
    logq = sum(float(Fr(v.weight) * 2 * ell * v.rq) * math.log(v.prime) for v in dt.bad)
    lhs = -logq / (2 * ell)
    disc = ih.disc_quadratic(dt.D)
    ram = {int(q) for q in __import__('sympy').primefactors(abs(disc))}
    dst = {2, 3, 5, ell} | {v.prime for v in dt.bad} | ram
    small = {2, 3, 5, ell}
    by = {}
    for v in dt.places:
        by.setdefault(v.prime, []).append(v)
    known = sorted(p for p in dst if p not in small and p in by and all(v.e is not None for v in by[p]))
    unknown = sorted(p for p in dst if p not in known)
    U_known, logd_known, theta_sum = 0.0, 0.0, 0.0
    for p in known:
        pl = [ih.Place(v) for v in by[p]]
        c = ih.P_closed(pl, ell)
        U_known += c["room"] + c["theta"] + c["s"] + c["star_exact"]
        logd_known += c["logd"]
        theta_sum += c["theta"]
    log_dF = 0.5 * math.log(abs(disc))
    log_fF = sum(float(Fr(v.weight) / v.e_base) * math.log(v.prime) for v in dt.bad)
    logd_unknown = max(0.0, log_dF + log_fF + 2 * math.log(ell) + 21 - logd_known)
    U_unknown = (ell + 5) / 4 * logd_unknown + sum(math.log(p) for p in unknown) + \
        sum((ell + 5) * ell_star_mod for p in unknown if p <= e_star * ell)
    arch = (ell + 5) / 4 * math.log(math.pi)
    U = U_known + U_unknown + arch
    k = Fr(ell * (ell + 1), 12)
    a = -lhs
    return dict(a=a, k=k, U=U, C=U + float(k) * a, U_known=U_known, U_unknown=U_unknown, arch=arch,
                theta_sum=theta_sum, known=known, unknown=unknown)


# ---------------------------------------------------------------------------------------------------------
# 判定と荷
# ---------------------------------------------------------------------------------------------------------

def evaluate(dt):
    groups = ip.local_groups(dt)
    th = ic.Theater(dt, (1, 0))
    absq = th.degree(th.q_pilot())                       # a = |log q̲̲|（LogSum、正確）
    a = absq.value()
    E = ends(dt)
    assert abs(E["a"] - a) < 1e-9 * max(1.0, a), (E["a"], a)
    k = E["k"]
    # テータ部分
    theta = {r1: theta_part(dt, r1, groups) for r1 in AX1}
    counted_all_bad = all(v.prime in groups for v in dt.bad)
    if counted_all_bad:
        assert (theta["V"] + absq * k).c == {}, "Θ_V = −k·a が正確に成り立たない"
    for r1 in AX1:
        assert abs(theta[r1].value() - (-float(k) * a if r1 == "V" else theta[r1].value())) < 1e-6
    tV, tL, tL0 = (theta[r].value() for r in AX1)
    assert tV <= tL + 1e-9 <= tL0 + 2e-9, (tV, tL, tL0)
    assert tL0 <= 1e-12
    x = {r1: -theta[r1].value() / a for r1 in AX1}
    loads = {}
    for r1 in AX1:
        lc, li = (x[r1] - 1) * a, (float(k) - x[r1]) * a
        assert abs(lc + li - (float(k) - 1) * a) < 1e-9 * max(1.0, a * float(k))
        loads[r1] = dict(x=x[r1], load_cor=lc, load_iv=li, theta=theta[r1].value(), theta_exact=ic.ls_json(theta[r1]))
    # 36 通り
    mids, base = all_mid(dt, groups)
    extra_all = dt.cofactor_container_bound()
    rows = []
    for R in READINGS:
        lo, hi = mids[R]
        lo_v, hi_v = lo.value(), hi.value()
        assert lo_v <= hi_v + 1e-9, (R, lo_v, hi_v)
        r1 = R[0]
        extra = extra_all if ip.uses_shell(R[:3]) else ic.LogSum()
        ex = extra.value()
        # 系3.12_R：−a ≤ M_R（数えていない素点の寄与は 0 以上、分解していない因数の上は下限 extra）
        if -a <= lo_v + ex:
            cor = "成り立つ"
        elif -a <= hi_v + ex:
            cor = "決まらない"
        else:
            cor = "不足"
        cor_deficit = max(0.0, -a - (hi_v + ex))
        # IV_R：M_R ≤ U(D)。数えていない素数（θ = 1）での寄与は、どの読みでも IV のそこでの上界 U_unknown 以下
        #   （格子は θ = 1 で単数と同じ、反復と包なしは容器の包以下）。アルキメデス部分は M_R に入っている
        Um = E["U_known"] + E["arch"]                    # 数えた素数＋アルキメデス部分での IV の上界
        if hi_v <= Um:
            iv = "成り立つ"
        elif lo_v + ex > E["U"]:
            # 分解していない因数の上の素点は U(D) にも正の量を足す（段階 (ii) の評価が導手とともに増える分を含む）ので条件つき
            iv = "破れる（条件つき）" if dt.unfactored else "破れる"
        else:
            iv = "決まらない"
        B_lo, B_hi = lo_v - theta[r1].value(), hi_v - theta[r1].value()
        rows.append(dict(reading=list(R), lo=lo_v, hi=hi_v, extra=ex, cor=cor, cor_deficit=cor_deficit, iv=iv,
                         B_lo=B_lo, B_hi=B_hi, budget_iv_lo=E["C"] - B_hi, budget_iv_hi=E["C"] - B_lo,
                         lo_exact=ic.ls_json(lo), hi_exact=ic.ls_json(hi)))
    # 予算の和の検査（区間の端どうし）
    for r in rows:
        assert abs((r["B_lo"] + r["budget_iv_hi"]) - E["C"]) < 1e-6 and abs((r["B_hi"] + r["budget_iv_lo"]) - E["C"]) < 1e-6
    # q の位数がそろうか（各素数の上の、重みが正の素点で）
    equal = {p: len({L.s(1) for L in locs if L.w > 0}) == 1 for p, locs in groups.items()}
    return dict(name=dt.name, ell=dt.ell, ell_star=dt.ell_star, scale=float(dt.scale_q), a=a, k=float(k),
                wall=(float(k) - 1) * a, C=E["C"], U=E["U"], U_known=E["U_known"], U_unknown=E["U_unknown"],
                arch=E["arch"], loads=loads, rows=rows, counted_all_bad=counted_all_bad,
                equal_orders={str(p): v for p, v in equal.items()}, unfactored=bool(dt.unfactored),
                known_primes=E["known"], group_primes=sorted(groups))


MARK = {"成り立つ": "○", "決まらない": "？", "不足": "△", "破れる": "×", "破れる（条件つき）": "×*"}


def show(res):
    print(f"\n==================== {res['name']}（ℓ = {res['ell']}、q → q^{res['scale']:g}） ====================")
    if res["unfactored"]:
        print("  ※ 分解していない因数がある（その上の悪い素点は a にも M_R にも U(D) にも入っていない）。"
              "△ と ×* はその素点しだい（×* は IV が破れる側の不足）")
    if res.get("conditional"):
        print(f"  （{res['conditional']}）")
    print(f"  a = |log q̲̲| = {res['a']:.4f}   k = {res['k']:.4f}   壁 (k−1)·a = {res['wall']:.4f}")
    print(f"  U(D) = {res['U']:.4f}（数えた素数 {res['U_known']:.4f}＋数えていない素数 {res['U_unknown']:.4f}"
          f"＋アルキメデス {res['arch']:.4f}）   C = U + k·a = {res['C']:.4f}")
    print(f"  高さの不等式 H：(k−1)·a = {res['wall']:.4f} {'≤' if res['wall'] <= res['C'] else '>'} C = {res['C']:.4f}")
    eq = [p for p, v in res["equal_orders"].items() if not v]
    print(f"  q の位数がそろわない素数（重みが正の素点で）：{', '.join(eq) if eq else 'なし'}")
    print("  荷の分け方（① だけで決まる）：")
    print(f"    {'①':<4}{'x = −Θ/a':>10}{'系3.12 の荷 (x−1)a':>20}{'IV の荷 (k−x)a':>18}")
    for r1 in AX1:
        L = res["loads"][r1]
        print(f"    {r1:<4}{L['x']:>10.4f}{L['load_cor']:>20.4f}{L['load_iv']:>18.4f}")
    print(f"  36 通り（M_R は数えた素点＋アルキメデス部分。B_R = M_R − Θ_①）")
    print(f"    {'①':<3}{'②':<4}{'③':<4}{'④':<5}{'⑤':<3}{'M_R':>24}{'B_R（系3.12 の予算）':>26}  系3.12  IV")
    for r in res["rows"]:
        a1, a2, a3, a4, a5 = r["reading"]
        rng = f"{r['lo']:.3f}" if abs(r["hi"] - r["lo"]) < 5e-4 else f"{r['lo']:.3f}〜{r['hi']:.3f}"
        bud = f"{r['B_lo']:.3f}" if abs(r["B_hi"] - r["B_lo"]) < 5e-4 else f"{r['B_lo']:.3f}〜{r['B_hi']:.3f}"
        print(f"    {a1:<3}{a2:<4}{a3:<4}{a4:<5}{a5:<3}{rng:>24}{bud:>26}   {MARK[r['cor']]}      {MARK[r['iv']]}")


def summary(results):
    print("\n==================== まとめ：荷の分け方 x_①（V は k、L0 ≤ L ≤ k） ====================")
    print("  " + " " * 6 + "".join(f"{r['name']:>10}" for r in results))
    print("  " + "k".ljust(6) + "".join(f"{r['k']:>10.3f}" for r in results))
    for r1 in AX1:
        print("  " + r1.ljust(6) + "".join(f"{r['loads'][r1]['x']:>10.4f}" for r in results))
    print("\n==================== まとめ：判定（系3.12／IV。○ 成り立つ・？ 決まらない・△ 不足・× 破れる・×* 条件つきで破れる） ====================")
    print("  " + " " * 22 + "".join(f"{r['name']:>8}" for r in results))
    for k, R in enumerate(READINGS):
        row = f"  {R[0]:<3}{R[1]:<4}{R[2]:<4}{R[3]:<5}{R[4]:<3}  "
        row += "".join(f"{MARK[r['rows'][k]['cor']] + '／' + MARK[r['rows'][k]['iv']]:>7} " for r in results)
        print(row)


def scale_check(names, Ns):
    """q → q^N の族：Θ_① の N 倍（正確）、残り B_R の有界性、U(D^N) = −k·N·a + C（C は N によらない）"""
    print("\n==================== q → q^N の族での検査 ====================")
    ok = True
    out = []
    for name in names:
        base = evaluate(ic.InitialThetaData(name, factor_seconds=1))
        for N in Ns:
            dt = ic.InitialThetaData(name, factor_seconds=1, scale_q=N)
            res = evaluate(dt)
            # a と Θ は N 倍、C は不変
            a_ok = abs(res["a"] - N * base["a"]) < 1e-9 * res["a"]
            th_ok = all(abs(res["loads"][r1]["theta"] - N * base["loads"][r1]["theta"]) < 1e-7 * max(1, abs(res["loads"][r1]["theta"]))
                        for r1 in AX1)
            x_ok = all(abs(res["loads"][r1]["x"] - base["loads"][r1]["x"]) < 1e-9 for r1 in AX1)
            C_ok = abs(res["C"] - base["C"]) < 1e-6 * max(1, base["C"])
            # 残り B_R の動き
            dB = max(max(abs(r["B_lo"] - b["B_lo"]), abs(r["B_hi"] - b["B_hi"])) for r, b in zip(res["rows"], base["rows"]))
            exactB = [tuple(r["reading"]) for r, b in zip(res["rows"], base["rows"])
                      if abs(r["B_lo"] - b["B_lo"]) < 1e-9 and abs(r["B_hi"] - b["B_hi"]) < 1e-9]
            ok &= a_ok and th_ok and x_ok and C_ok
            print(f"  [{name}] N = {N}：a が N 倍 {a_ok}、Θ_① が N 倍 {th_ok}、x_① 不変 {x_ok}、C 不変 {C_ok}"
                  f"（C = {res['C']:.4f}）、B_R の動き最大 {dB:.4f}（変わらない読み {len(exactB)}/36）")
            out.append(dict(name=name, N=N, a=res["a"], C=res["C"], dB=dB, exactB=len(exactB),
                            cor=[r["cor"] for r in res["rows"]], iv=[r["iv"] for r in res["rows"]]))
        # 荷の向きの閾値（どの N で系3.12 と IV のどちらが先に破れるか）。B_R は N=1 の区間で代用（有界）
        print(f"  [{name}] 高さの不等式が破れる N の下限（q の位数だけを N 倍）：N > C/((k−1)a) = {base['C'] / base['wall']:.2f}")
        for r1 in AX1:
            L = base["loads"][r1]
            rr = [r for r in base["rows"] if r["reading"][0] == r1]
            Bmin, Bmax = min(r["B_lo"] for r in rr), max(r["B_hi"] for r in rr)
            if L["load_cor"] > 1e-12:
                nc = f"系3.12 は N > {Bmin / L['load_cor']:.2f}〜{Bmax / L['load_cor']:.2f} で破れる"
            else:
                nc = "系3.12 はどの N でも荷を持たない（x ≤ 1）"
            if L["load_iv"] > 1e-9:
                ni = f"IV は N > {(base['C'] - Bmax) / L['load_iv']:.2f}〜{(base['C'] - Bmin) / L['load_iv']:.2f} で破れる"
            else:
                ni = "IV は荷を持たない（x = k）"
            print(f"     {r1}：{nc}／{ni}")
    print("q → q^N の検査：" + ("すべて通った" if ok else "失敗あり"))
    return ok, out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", default="D2", choices=list(ic.DATA))
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--scale", nargs="*", type=int)
    ap.add_argument("--json")
    args = ap.parse_args()
    names = list(ic.DATA) if args.all else [args.data]
    if args.scale:
        ok, out = scale_check([n for n in names if n != "D2357"] or names, args.scale)
        if args.json:
            with open(args.json, "w") as f:
                json.dump(out, f, ensure_ascii=False, indent=1)
        sys.exit(0 if ok else 1)
    results = []
    for nm in names:
        res = evaluate(ic.InitialThetaData(nm, factor_seconds=1))
        if nm in ic.CONDITIONAL:
            res["conditional"] = ic.CONDITIONAL[nm]
        show(res)
        results.append(res)
    if len(results) > 1:
        summary(results)
    if args.json:
        with open(args.json, "w") as f:
            json.dump(results, f, ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
