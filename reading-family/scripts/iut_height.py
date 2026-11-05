#!/usr/bin/env python3
"""初期Θデータから、高さの不等式の両辺を IUT に従って計算する（IV 定理1.10 の証明の段階 (iv)〜(viii)）。

読みに依らない一つの手順。IV 定理1.10 の言明とその証明に沿う。

  左辺  −|log q̲̲| = −(1/2ℓ)·log 𝔮          log 𝔮 = Σ_{v ∈ 𝕍_mod^bad} w_v·ord_p(q_v)·log p（q-パラメータの因子の次数）
  右辺  −|log Θ| の上界 U(D) = Σ_{v_ℚ ∈ dst} P_{v_ℚ} + (ℓ+5)/4·log π        （段階 (v)(vi)(vii)(viii)）
    P_{v_ℚ}：ラベル j（1…ℓ*）と、p の上の素点の組 T = (v_0, …, v_j)（重み Π w）ごとに、命題1.4(iii) の局所評価
               B(T, j) = (−λ + 𝔡_I + 1)·log p + Σ_{i ∈ I*} (3 + log e_i)
             λ = ord(q̲̲_{v_j}^{j²})（i† = j、良い素点なら 0）、𝔡_I = Σ_i 𝔡_{v_i}（差積の位数）、I* = {i : e_{v_i} > p − 2}。
             組について加重平均し（命題1.7：i† の対称化は平均を変えない）、j について平均する。
             IV は I* の項を (R4) で 4(j+1)·ℓ*_mod·ι に置き換える（ι = [p ≤ e*_mod·ℓ]）。両方を出す。
    特別でない素数（K で不分岐）は 0（段階 (vi)）。アルキメデス部分は (j+1)·log π を平均して (ℓ+5)/4·log π（段階 (vii)）。

  2・3・5・ℓ の上の素点は局所体が分からないので、原典と同じく段階 (ii) の評価
      log 𝔡^K ≤ log 𝔡^{F_tpd} + log 𝔣^{F_tpd} + 2·log ℓ + 21
  から、分かっている素数の分を引いた残りで上から抑える（その素数は 𝕍^bad に入らないので λ = 0）。
  一覧のデータは Legendre 形 y² = x(x−1)(x−a) なので E[2] は F_mod 上有理で、F_tpd = F_mod。

  定理1.10 の形：(1/6)·log 𝔮 ≤ (1 + 20·d_mod/ℓ)·(log 𝔡^{F_tpd} + log 𝔣^{F_tpd}) + 20·(e*_mod·ℓ + η_prm)
  η_prm（命題1.6）は、η ≥ η_prm で π(η) ≤ 4η/(3 log η) となる正の実数。ここでは η_prm = 2 とし、
  η ≤ 10^7 の範囲を篩で確かめる（それ以上は Rosser–Schoenfeld の π(x) < 1.25506·x/log x による）。
使い方：python3 iut_height.py [--data D2 ...]
"""
import argparse
import itertools
import math
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iut_compute as ic  # noqa: E402


def prime_count_check(limit=10 ** 7):
    """η_prm = 2 の確認：2 ≤ η ≤ limit で π(η) ≤ 4η/(3 log η)（素数の直後だけ見れば足りる）"""
    sieve = bytearray([1]) * (limit + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, limit + 1, i)))
    count = 0
    for n in range(2, limit + 1):
        if sieve[n]:
            count += 1
            if count > 4 * n / (3 * math.log(n)):
                return False, n
    return True, limit


def disc_quadratic(D):
    return D if D % 4 == 1 else 4 * D


class Place:
    def __init__(self, v):
        self.v, self.name, self.p, self.e, self.w = v, v.name, v.prime, v.e, Fr(v.weight)
        self.bad = bool(v.in_Vbad)
        self.rq = Fr(v.rq) if self.bad else Fr(0)           # ord_p(q̲̲)
        assert self.e is not None
        assert self.p % self.e != 0 or self.e == 1, "穏分岐を仮定（p ∤ e）"
        self.d = Fr(self.e - 1, self.e)                      # 穏分岐の差積の位数（命題1.3(i) の等号）
        self.base_e = v.e_base


def local_bound_tuples(places, j, ell):
    """組 T ごとの命題1.4(iii) の局所評価の加重平均（数え上げ）。i† = j と、i† について対称化した値の両方"""
    p = places[0].p
    L = math.log(p)
    tot, tot_sym = 0.0, 0.0
    for T in itertools.product(places, repeat=j + 1):
        w = 1.0
        for v in T:
            w *= float(v.w)
        dI = sum(float(v.d) for v in T)
        star = sum(3 + math.log(v.e) for v in T if v.e > p - 2)
        lam = float(j * j * T[-1].rq)                        # i† = j（最後の位置）
        lam_sym = sum(float(j * j * v.rq) for v in T) / (j + 1)
        tot += w * ((-lam + dI + 1) * L + star)
        tot_sym += w * ((-lam_sym + dI + 1) * L + star)
    return tot, tot_sym


def P_closed(places, ell):
    """P_{v_ℚ} の閉じた式：(ℓ+5)/4·log 𝔡^K_p − (ℓ+1)/24·log 𝔮_p + log p + (ℓ+5)/4·Σ_{e > p−2} w·(3 + log e)"""
    p = places[0].p
    L = math.log(p)
    logd = sum(float(v.w * v.d) for v in places) * L
    logq = sum(float(v.w * 2 * ell * v.rq) for v in places) * L
    star = sum(float(v.w) * (3 + math.log(v.e)) for v in places if v.e > p - 2)
    return dict(logd=logd, logq=logq, room=(ell + 5) / 4 * logd, theta=-(ell + 1) / 24 * logq, s=L,
                star_exact=(ell + 5) / 4 * star)


def compute(name, check_enum=True):
    dt = ic.InitialThetaData(name, factor_seconds=1)
    ell, ls = dt.ell, dt.ell_star
    d_mod, e_mod = 2, 2                                       # F_mod = ℚ(√D)：次数 2、ある素数で分岐
    e_star = 2 ** 12 * 3 ** 3 * 5 * e_mod
    ell_star_mod = math.log(e_star * ell)
    # 左辺
    logq = sum(float(Fr(v.weight) * 2 * ell * v.rq) * math.log(v.prime) for v in dt.bad)
    lhs = -logq / (2 * ell)
    # 特別な素数（D6）：2・3・5・ℓ、𝕍^bad の下の素数、F_mod で分岐する素数
    disc = disc_quadratic(dt.D)
    ram = {int(q) for q in __import__('sympy').primefactors(abs(disc))}
    bad_primes = {v.prime for v in dt.bad}
    dst = {2, 3, 5, ell} | bad_primes | ram
    small = {2, 3, 5, ell}
    by = {}
    for v in dt.places:
        by.setdefault(v.prime, []).append(v)
    known = sorted(p for p in dst if p not in small and p in by and all(v.e is not None for v in by[p]))
    unknown = sorted(p for p in dst if p not in known)
    rows = []
    U_known = 0.0
    logd_known = 0.0
    for p in known:
        pl = [Place(v) for v in by[p]]
        assert abs(sum(float(v.w) for v in pl) - 1) < 1e-12
        c = P_closed(pl, ell)
        iota = 1 if p <= e_star * ell else 0
        star_iv = (ell + 5) * ell_star_mod * iota
        P_exact = c["room"] + c["theta"] + c["s"] + c["star_exact"]
        P_iv = c["room"] + c["theta"] + c["s"] + star_iv
        if check_enum and ls <= 4:
            avg = sum(local_bound_tuples(pl, j, ell)[0] for j in range(1, ls + 1)) / ls
            avg_sym = sum(local_bound_tuples(pl, j, ell)[1] for j in range(1, ls + 1)) / ls
            assert abs(avg - P_exact) < 1e-9 * max(1, abs(P_exact)), (p, avg, P_exact)
            assert abs(avg_sym - P_exact) < 1e-9 * max(1, abs(P_exact)), (p, avg_sym, P_exact)
        rows.append(dict(p=p, places=", ".join(f"{v.name}(e={v.e}{', 悪' if v.bad else ''})" for v in pl),
                         room=c["room"], theta=c["theta"], s=c["s"], star_exact=c["star_exact"], star_iv=star_iv,
                         P_exact=P_exact, P_iv=P_iv))
        U_known += P_exact
        logd_known += c["logd"]
    # 2・3・5・ℓ（と分からない素数）：段階 (ii) で差積を上から抑える
    log_dF = 0.5 * math.log(abs(disc))                       # log 𝔡^{F_tpd} = log 𝔡^{F_mod}
    log_fF = sum(float(Fr(v.weight) / v.e_base) * math.log(v.prime) for v in dt.bad)   # 導手（係数 1）
    logd_K_bound = log_dF + log_fF + 2 * math.log(ell) + 21
    logd_unknown = max(0.0, logd_K_bound - logd_known)
    U_unknown = (ell + 5) / 4 * logd_unknown + sum(math.log(p) for p in unknown) + \
        sum((ell + 5) * ell_star_mod for p in unknown if p <= e_star * ell)
    arch = (ell + 5) / 4 * math.log(math.pi)
    U = U_known + U_unknown + arch
    theta_total = sum(r["theta"] for r in rows)
    # 定理1.10 の形
    eta_prm = 2.0
    thm_lhs = logq / 6
    thm_rhs = (1 + 20 * d_mod / ell) * (log_dF + log_fF) + 20 * (e_star * ell + eta_prm)
    # 段階 (viii) の中間の上界（C_Θ·|log q̲̲| の上界）
    s_le = sum(1 for p in dst if p <= e_star * ell)
    viii = (ell + 1) / 4 * ((1 + 12 * d_mod / ell) * (log_dF + log_fF) + 2 * math.log(ell) + 56
                            - (1 - 12 / ell ** 2) * logq / 6 + 20 / 3 * ell_star_mod * s_le) - logq / (2 * ell)
    return dict(name=name, ell=ell, lhs=lhs, logq=logq, rows=rows, unknown=unknown, U_known=U_known,
                U_unknown=U_unknown, arch=arch, U=U, theta_total=theta_total, k_absq=(ell * (ell + 1) / 12) * (-lhs),
                logd_unknown=logd_unknown, logd_K_bound=logd_K_bound, log_dF=log_dF, log_fF=log_fF,
                thm_lhs=thm_lhs, thm_rhs=thm_rhs, viii=viii, unfactored=bool(dt.unfactored),
                e_star_l=e_star * ell)


def show(r):
    print(f"\n==================== {r['name']}（ℓ = {r['ell']}） ====================")
    if r["unfactored"]:
        print("  ※ N(1 − a) に分解していない因数がある。その上の悪い素点は log 𝔮 にも右辺にも入っていない（両辺とも不完全）")
    print(f"  左辺  −|log q̲̲| = −log 𝔮/(2ℓ) = {r['lhs']:.4f}      （log 𝔮 = {r['logq']:.4f}）")
    print(f"  右辺  −|log Θ| の上界 U(D)（段階 (v)〜(viii)）：")
    print(f"    {'素数':>8}  {'余地 (ℓ+5)/4·log𝔡':>18} {'テータ −(ℓ+1)/24·log𝔮':>22} {'+log p':>8} {'I* の項':>8} {'P':>10}   素点")
    for x in r["rows"]:
        print(f"    {x['p']:>8}  {x['room']:18.4f} {x['theta']:22.4f} {x['s']:8.4f} {x['star_exact']:8.4f} {x['P_exact']:10.4f}   {x['places']}")
    print(f"    分かっている素数の和 {r['U_known']:.4f}（テータの項の和 {r['theta_total']:.4f} = −k·|log q̲̲| = {-r['k_absq']:.4f}）")
    print(f"    2・3・5・ℓ の上（{', '.join(map(str, r['unknown']))}）：差積を段階 (ii) で抑えて ≤ {r['U_unknown']:.4f}"
          f"（log 𝔡^K の残り ≤ {r['logd_unknown']:.4f}、I* の項は (R4) の 4(j+1)·ℓ*_mod）")
    print(f"    アルキメデス部分 (ℓ+5)/4·log π = {r['arch']:.4f}")
    print(f"    U(D) = {r['U']:.4f}")
    ok = r["lhs"] <= r["U"]
    verdict = "成り立つ" if ok else ("決まらない（分解していない因数の上の素点の寄与が入っていない）" if r["unfactored"] else "成り立たない")
    print(f"  高さの不等式（データごと、IV の手順）：−|log q̲̲| = {r['lhs']:.4f} {'≤' if ok else '>'} U(D) = {r['U']:.4f}"
          f"  → {verdict}（差 {r['U'] - r['lhs']:.4f}）")
    gap, room = r['k_absq'] + r['lhs'], r['U'] + r['k_absq']
    print(f"    同じことを「差と余地」で：(k−1)·|log q̲̲| = {gap:.4f} {'≤' if gap <= room else '>'} 余地 U(D) + k·|log q̲̲| = {room:.4f}")
    print(f"  段階 (viii) の中間の上界（C_Θ·|log q̲̲| の上界）= {r['viii']:.1f}")
    ok2 = r["thm_lhs"] <= r["thm_rhs"]
    print(f"  定理1.10 の形：(1/6)·log 𝔮 = {r['thm_lhs']:.4f} {'≤' if ok2 else '>'} "
          f"(1+20d_mod/ℓ)(log𝔡+log𝔣) + 20(e*_mod·ℓ + η_prm) = {r['thm_rhs']:.4g}"
          f"（log 𝔡^F_tpd = {r['log_dF']:.4f}、log 𝔣^F_tpd = {r['log_fF']:.4f}、e*_mod·ℓ = {r['e_star_l']:,}）")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", nargs="*", default=list(ic.DATA))
    ap.add_argument("--skip-eta-check", action="store_true")
    args = ap.parse_args()
    if not args.skip_eta_check:
        ok, n = prime_count_check()
        print(f"η_prm = 2 の確認：2 ≤ η ≤ 10^7 で π(η) ≤ 4η/(3 log η)：{'成り立つ' if ok else '破れる（η = ' + str(n) + '）'}")
    for name in args.data:
        show(compute(name))


if __name__ == "__main__":
    main()
