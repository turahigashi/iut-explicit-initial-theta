#!/usr/bin/env python3
"""系3.12（変種）を 12 通りの読みで計算する。iut_compute.py（walkthrough の版 1.1.0。同じフォルダに同梱）の拡張で、元のコードは変えない。

読みの軸（どれも有限の選択肢）
  ① (Ind1) ラベル置換の範囲（p.175 の制限の読み、短報の 2×2 の読みの軸と同じもの）
       V  ：テータ値はラベル j の因子にとどまる（IV 定理1.10 段階 (v)、lana の「IV の読み」）
       L  ：0 を固定する置換（一覧の (L)、短報の (R)）
       L0 ：すべての位置（lana の「字義どおりの読み」）
  ② (Ind3) の読み
       容器：可能な像の台を log 殻のテンソル積 ⊗𝓘 全体とする（III 命題3.5 (ii)(a) の coric なパケット、lana の shell）
       反復：可能な像を、単数と、log-link を同じ回数 m′ だけ反復した実際の像の純テンソルに限る
             （容器は使わない）
  ③ (Ind2) の群
       単数：ℤ_p^× のスカラーと体の自己同型だけ（包を変えない）
       格子：各因子の log 殻 𝓘 を保つ ℤ_p 線形な自己同型すべて（lana の tensorAut。IV 命題1.2 の
             「⊗𝓘 を保つ任意の自己同型」でも値は同じ）

成分（因子ごとの素点の組 T = (v_0, …, v_j)、重み Π w）ごとの包の log 体積。log p を単位とする係数で書く。
P は ① で決まる位置の集合、s_t = ord_p(θ_t)（θ_t = q̲̲_{v_t}^{j²}、悪い素点以外では 0）、ρ = log 殻の半径、
μ = log(𝒪^×) の最小の付値（= 1 + δ − ρ）、δ = [p = 2]、n = j + 1、κ(X) = max{k : X ⊆ p^k·𝓘}。
  容器・単数：Σ_u ρ_u − min_{t∈P} s_t                                       （iut_compute.py の計算）
  容器・格子：Σ_u ρ_u − min_{t∈P} κ(θ_t𝓘)
  反復・単数：−(min_{t∈P} s_t + min(0, Σ_u μ_u))
  反復・格子：Σ_u ρ_u − min_{t∈P} min(κ(θ_t𝒪) + Σ_{u≠t} κ(𝒪_u), n(1+δ) + κ(θ_t𝓘))
根拠：
  ・包（b·O の交わり）は ℤ_p 上で生成する格子しか見ない。
  ・𝓘 を保つ GL(𝓘) は原始ベクトルに推移的に働くので、格子 X の GL(𝓘) 軌道が生成する格子は p^{κ(X)}·𝓘。
    因子ごとの GL の軌道は純テンソルの因子ごとに生成するので、⊗_u X_u の軌道は p^{Σ κ(X_u)}·(⊗𝓘)。
  ・単数倍は包と交換し、log 体積は付値の分だけずれる（lana の leastHull_units_smul・componentVol_units_smul）。
  ・反復の読みの像：m′ = 0 は単数（付値 0）、m′ = 1 は log(𝒪^×)（最小の付値 μ）、m′ ≥ 2 の像はその部分集合。
玉の素点（p 奇数・e ≤ p − 2）では κ(θ𝓘) = ⌊s⌋、κ(θ𝒪) = ⌊s + ρ⌋、κ(𝒪) = 0（𝓘 = p^{−1}𝔪）。
玉でない素点では κ は θ の単数部分と体に依るので、次の評価で上下から挟む（区間）：
  κ(θ𝓘) ∈ [max(⌊s − (a+b)⌋, ⌊s − (ρ − ρ′)⌋), ⌊s⌋]   a + b は IV 命題1.2(i) の定数（lana の logLatticeA + B）
  κ(θ𝒪) ∈ [max(⌊s + ρ′⌋, κ(θ𝓘) の下端), ⌊s + ρ⌋]     ρ′ = 1 + δ − n0/e（n0 = ⌊e/(p−1)⌋ + 1、内側の半径の下限）
  κ(𝒪)  ∈ [max(0, ⌊ρ′⌋), ⌊ρ⌋]

判定：−|log q̲̲| ≤ −|log Θ|（変種）を、右辺の下端・上端と比べる。数えていない素点（2・3・5・ℓ の上、分解して
いない因数の上）の寄与は 0 以上だが上界が無いので、「破れる」とは言わず、それらが足すべき量（不足）を出す。

使い方
  python3 iut_patterns.py --all            # 7 つのデータの 12 通り
  python3 iut_patterns.py --data D2
  python3 iut_patterns.py --check          # 旧版との一致・Δ(D) との一致・数え上げとの一致・模型の体での κ の区間
  python3 iut_patterns.py --all --json results_patterns.json
"""
import argparse
import itertools
import json
import math
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iut_compute as ic  # noqa: E402

AX1 = ["V", "L", "L0"]
AX2 = ["容器", "反復"]
AX3 = ["単数", "格子"]
PATTERNS = [(a, b, c) for a in AX1 for b in AX2 for c in AX3]


def lattice_ab(p, e):
    """IV 命題1.2(i) の a + b（lana の logLatticeA + logLatticeB）。a = ⌈e/(p−2)⌉/e（p = 2 なら 2）、
    b = ⌊log_p(pe/(p−1))⌋ − 1/e。床は整数の比較で正確に取る"""
    a = Fr(2) if p == 2 else Fr(-(-e // (p - 2)), e)
    k = 0
    while p ** (k + 1) * (p - 1) <= p * e:
        k += 1
    return a + k - Fr(1, e)


class Local:
    """一つの素点の局所量（ord_p を単位とする有理数）"""

    def __init__(self, v):
        p, e = v.prime, v.e
        self.v, self.p, self.e, self.w, self.name = v, p, e, Fr(v.weight), v.name
        self.delta = 1 if p == 2 else 0
        self.ball = p != 2 and e <= p - 2
        self.rho = Fr(v.rho)                         # 外側の半径（−min ord_p on 𝓘）
        self.mu = 1 + self.delta - self.rho          # log(𝒪^×) の最小の付値
        n0 = e // (p - 1) + 1
        self.rho_in = 1 + self.delta - Fr(n0, e)     # 内側の半径の下限（log(1 + 𝔪^{n0}) = 𝔪^{n0}）
        self.ab = lattice_ab(p, e)
        if self.ball:
            assert self.rho_in == self.rho == 1 - Fr(1, e) and self.ab == 0 and self.mu == Fr(1, e)
        self.bad = bool(v.in_Vbad)

    def s(self, j):
        return j * j * Fr(self.v.rq) if self.bad else Fr(0)

    def kI(self, j):
        """κ(θ𝓘) の区間（θ = 1 なら 0）"""
        if not self.bad:
            return (0, 0)
        s = self.s(j)
        hi = math.floor(s)
        lo = min(hi, max(math.floor(s - self.ab), math.floor(s - (self.rho - self.rho_in))))
        return (lo, hi)

    def kO(self):
        """κ(𝒪) の区間"""
        hi = math.floor(self.rho)
        return (min(hi, max(0, math.floor(self.rho_in))), hi)

    def kTO(self, j):
        """κ(θ𝒪) の区間（θ = 1 なら κ(𝒪)）"""
        if not self.bad:
            return self.kO()
        s = self.s(j)
        hi = math.floor(s + self.rho)
        lo = min(hi, max(math.floor(s + self.rho_in), self.kI(j)[0]))
        return (lo, hi)


def compositions(n, m):
    """n を m 個の非負整数に分ける"""
    if m == 1:
        yield (n,)
        return
    for k in range(n + 1):
        for rest in compositions(n - k, m - 1):
            yield (k,) + rest


def multinom(n, c):
    out = math.factorial(n)
    for x in c:
        out //= math.factorial(x)
    return out


def component_value(locs, n, delta, j, pat, end, present, tot):
    """成分の包の log 体積（log p の係数）。present = P の位置に現れる素点の番号、tot = 素点ごとの個数。
    end = 0 は下端（κ を上端で取る）、1 は上端"""
    _, ax2, ax3 = pat
    b = 1 - end                                      # 下端の体積には κ の上端
    m = len(locs)
    C = sum(tot[i] * locs[i].rho for i in range(m))
    if ax2 == "容器" and ax3 == "単数":
        return C - min(locs[i].s(j) for i in present)
    if ax2 == "容器" and ax3 == "格子":
        return C - min(locs[i].kI(j)[b] for i in present)
    if ax2 == "反復" and ax3 == "単数":
        h = min(Fr(0), sum(tot[i] * locs[i].mu for i in range(m)))
        return -(min(locs[i].s(j) for i in present) + h)
    G = sum(tot[i] * locs[i].kO()[b] for i in range(m))
    K0 = min(locs[i].kTO(j)[b] - locs[i].kO()[b] for i in present) + G
    K1 = n * (1 + delta) + min(locs[i].kI(j)[b] for i in present)
    return C - min(K0, K1)


def expect_prime(locs, j, P, pat, end):
    """一つの素数での、成分についての期待値（重みは素点の局所次数の割合で、和は 1）"""
    m, n, npos = len(locs), j + 1, len(P)
    assert sum(L.w for L in locs) == 1
    delta = locs[0].delta
    total = Fr(0)
    for c in compositions(npos, m):
        pc = multinom(npos, c)
        for i in range(m):
            pc *= locs[i].w ** c[i]
        present = [i for i in range(m) if c[i] > 0]
        for d in compositions(n - npos, m):
            pd = multinom(n - npos, d)
            for i in range(m):
                pd *= locs[i].w ** d[i]
            tot = [c[i] + d[i] for i in range(m)]
            total += pc * pd * component_value(locs, n, delta, j, pat, end, present, tot)
    return total


def enumerate_prime(locs, j, P, pat, end):
    """同じ量を成分 T の数え上げで（検算用）"""
    m, n = len(locs), j + 1
    delta = locs[0].delta
    total = Fr(0)
    for T in itertools.product(range(m), repeat=n):
        w = Fr(1)
        for i in T:
            w *= locs[i].w
        present = sorted({T[t] for t in P})
        tot = [T.count(i) for i in range(m)]
        total += w * component_value(locs, n, delta, j, pat, end, present, tot)
    return total


def local_groups(dt):
    """容器に数える素数ごとの素点（iut_compute.py と同じく、e が分からない素点のある素数は数えない）"""
    by = {}
    for v in dt.places:
        by.setdefault(v.prime, []).append(v)
    return {p: [Local(v) for v in vs] for p, vs in by.items() if all(v.e is not None for v in vs)}


def rhs(dt, pat, groups=None, use_enum=False):
    """−|log Θ| の区間 [下端, 上端]（数えた素点だけの値）を LogSum で"""
    groups = groups or local_groups(dt)
    ls = dt.ell_star
    out = []
    for end in (0, 1):
        tot = ic.LogSum()
        for j in range(1, ls + 1):
            P = ic.placements(pat[0], j)
            for p, locs in groups.items():
                f = enumerate_prime if use_enum else expect_prime
                tot = tot + ic.LogSum.log(p, f(locs, j, P, pat, end))
            tot = tot + ic.LogSum({'π': j + 1})
        out.append(tot * Fr(1, ls))
    return out


def uses_shell(pat):
    """分解していない因数の上の素点の寄与の下限（iut_compute.py の cofactor_container_bound）が当てはまるか。
    そこは θ = 1 の玉の素点なので、log 殻の容器を数える読みでは Σρ、反復・単数では 0"""
    return not (pat[1] == "反復" and pat[2] == "単数")


def small_prime_contribution(p, ls, e, pat):
    """θ = 1 の素数 p の上の素点がみな分岐指数 e のとき、その素数が −|log Θ| に足す量の上限（ラベル平均）：
    ((l*+3)/2)·g(e)·log p。g は読み②③で決まる（容器：ρ、反復・単数：max(0, ρ − 1 − δ)、反復・格子：ρ − min(κ(𝒪), 1 + δ)）"""
    delta = 1 if p == 2 else 0
    rho = ic.log_shell_radius(p, e)
    if pat[1] == "容器":
        g = rho
    elif pat[2] == "単数":
        g = max(Fr(0), rho - 1 - delta)
    else:
        rho_in = 1 + delta - Fr(e // (p - 1) + 1, e)
        kO_lo = min(math.floor(rho), max(0, math.floor(rho_in)))
        g = rho - min(kO_lo, 1 + delta)
    return float(Fr(ls + 3, 2) * g) * math.log(p)


def required_e(primes, ls, deficit, pat):
    """数えていない素数（2・3・5・ℓ）の上の素点がみな同じ分岐指数 e だとして、不足を埋めるのに要る e の最小値"""
    if deficit <= 0:
        return 1
    f = lambda e: sum(small_prime_contribution(q, ls, e, pat) for q in primes)
    hi = 1
    while f(hi) < deficit:
        hi *= 2
        if hi > 10 ** 15:
            return None
    lo = max(1, hi // 2)
    while lo < hi:
        mid = (lo + hi) // 2
        if f(mid) >= deficit:
            hi = mid
        else:
            lo = mid + 1
    return lo


def evaluate(dt):
    """12 通りの判定。数えた素点の区間 [lo, hi]、分解していない因数の上の素点の寄与の下限 extra（読みによる）、
    数えていない素点（2・3・5・ℓ の上と、分解していない因数の上）の寄与 U ≥ extra（上界なし）。
      成り立つ    ：−|log q̲̲| ≤ lo + extra
      決まらない  ：そうでなく、−|log q̲̲| ≤ hi + extra（玉でない素点の区間か、数えていない素点しだい）
      不足 d      ：d = −|log q̲̲| − (hi + extra) > 0。数えていない素点が、分かっている下限に加えて d 以上を足さないと破れる"""
    th = ic.Theater(dt, (1, 0))
    absq = th.degree(th.q_pilot())
    wayA = -absq.value()
    extra_all = dt.cofactor_container_bound()
    groups = local_groups(dt)
    rows = []
    for pat in PATTERNS:
        lo, hi = rhs(dt, pat, groups)
        extra = extra_all if uses_shell(pat) else ic.LogSum()
        lo_v, hi_v, ex_v = lo.value(), hi.value(), extra.value()
        assert lo_v <= hi_v + 1e-9, (dt.name, pat, lo_v, hi_v)
        deficit = 0.0
        if wayA <= lo_v + ex_v:
            verdict = "成り立つ"
        elif wayA <= hi_v + ex_v:
            verdict = "決まらない"
        else:
            verdict, deficit = "不足", wayA - hi_v - ex_v
        req, lograd = None, None
        if verdict == "不足":
            req = required_e(sorted({2, 3, 5, dt.ell}), dt.ell_star, deficit, pat)
            if dt.unfactored and uses_shell(pat):
                # 分解していない因数の素因数 w（重み ≥ 1/2、ρ ≥ 1 − 1/e_min）が足す量は (ℓ+5)/4·(1/2)·(1 − 1/e_min)·log w 以上
                C = dt.unfactored[0]
                Omega = int(math.log(C) // math.log(dt.factor_limit))
                emin = min(15 * dt.ell // math.gcd(15 * dt.ell, 2 * k) for k in range(1, Omega + 1))
                coef = float(Fr(dt.ell + 5, 4) * Fr(1, 2) * (1 - Fr(1, emin)))
                lograd = (deficit + ex_v) / coef / math.log(10)      # 根基の桁数（下限の分を足し戻す）
        rows.append(dict(pattern=list(pat), lo=lo_v, hi=hi_v, extra=ex_v, exact=lo.c == hi.c, verdict=verdict,
                         deficit=deficit, required_e=req, cofactor_rad_digits=lograd,
                         lo_exact=ic.ls_json(lo), hi_exact=ic.ls_json(hi)))
    return dict(name=dt.name, ell=dt.ell, absq=absq.value(), wayA=wayA, extra=extra_all.value(),
                unfactored_digits=[len(str(C)) for C in dt.unfactored], rows=rows,
                nonball=[f"{L.name}(p={L.p}, e={L.e})" for locs in groups.values() for L in locs if not L.ball],
                skipped=sorted({v.prime for v in dt.places if v.e is None}))


MARK = {"成り立つ": "○", "決まらない": "？", "不足": "△"}


def show(res):
    print(f"\n==================== {res['name']}（ℓ = {res['ell']}） ====================")
    if res.get("conditional"):
        print(f"  （{res['conditional']}）")
    print(f"  −|log q̲̲| = {res['wayA']:.4f}")
    if res["nonball"]:
        print(f"  玉でない素点（κ を区間で挟む）：{', '.join(res['nonball'])}")
    sk = [str(p) for p in res["skipped"] if p != 2]
    print(f"  数えていない素点：2{'・' + '・'.join(sk) if sk else ''} の上"
          + (f"、分解していない因数（{', '.join(str(d) + ' 桁' for d in res['unfactored_digits'])}）の上"
             f"（容器を数える読みでは寄与の下限 {res['extra']:.4f} を足す）" if res["unfactored_digits"] else ""))
    print(f"  {'①':<3}{'②':<4}{'③':<4}  {'−|log Θ|（数えた素点）':>16}  判定")
    for r in res["rows"]:
        a, b, c = r["pattern"]
        rng = f"{r['lo']:.4f}" if r["exact"] else f"{r['lo']:.4f} 〜 {r['hi']:.4f}"
        tail = ""
        if r["verdict"] == "不足":
            e = r["required_e"]
            req = f"2・3・5・{res['ell']} の上の分岐指数がみな e なら e ≥ {e:,}" if e else "2・3・5・ℓ の上だけでは埋まらない"
            tail = f" {r['deficit']:.2f}（数えていない素点がこれ以上を足さないと破れる。{req}"
            if r["cofactor_rad_digits"] is not None:
                tail += f"。分解していない因数の根基が 10^{r['cofactor_rad_digits']:.0f} 以上でも埋まる"
            tail += "）"
        print(f"  {a:<3}{b:<4}{c:<4}  {rng:>24}  {MARK[r['verdict']]} {r['verdict']}{tail}")


def summary(results):
    print("\n==================== まとめ（○ 成り立つ・？ 決まらない・△ 不足＝数えていない素点しだい） ====================")
    head = "  " + " " * 12 + "".join(f"{r['name']:>7}" for r in results)
    print(head)
    for k, pat in enumerate(PATTERNS):
        row = f"  {pat[0]:<3}{pat[1]:<4}{pat[2]:<4} "
        row += "".join(f"{MARK[r['rows'][k]['verdict']]:>6} " for r in results)
        print(row)


def check(names):
    """検査：① 旧版との完全一致（容器・単数）、② Δ(D)（今日の閉じた式）との一致、③ 数え上げとの一致、
    ④ 玉の素点での大小の順序、⑤ 模型の体で κ の区間が正確な値を含むこと"""
    ok = True
    for name in names:
        dt = ic.InitialThetaData(name, factor_seconds=1)
        groups = local_groups(dt)
        th00, th10 = ic.Theater(dt, (0, 0)), ic.Theater(dt, (1, 0))
        cable, et = ic.theta_link(th00, th10), ic.Etale(dt)
        for rd in AX1:
            old = ic.IUTAlgorithm(rd).run(cable, et, th10).possible
            lo, hi = rhs(dt, (rd, "容器", "単数"), groups)
            same = lo.c == old.c and hi.c == old.c
            ok &= same
            print(f"  [{name}] 旧版と一致（{rd}・容器・単数）：{same}")
        # Δ(D)：V・容器 の 格子 − 単数
        loS, _ = rhs(dt, ("V", "容器", "単数"), groups)
        loG, hiG = rhs(dt, ("V", "容器", "格子"), groups)
        print(f"  [{name}] Δ(D) ∈ [{(loG - loS).value():.4f}, {(hiG - loS).value():.4f}]")
        if dt.ell_star <= 4:
            for pat in PATTERNS:
                for end in (0, 1):
                    a = rhs(dt, pat, groups)[end]
                    b = rhs(dt, pat, groups, use_enum=True)[end]
                    ok &= a.c == b.c
            print(f"  [{name}] 期待値の式と数え上げが 12 通り×上下端で一致：{ok}")
        # 玉の素点だけの素数で、成分ごとの順序 反復・単数 ≤ 反復・格子 ≤ 容器・単数 ≤ 容器・格子
        for p, locs in groups.items():
            if not all(L.ball for L in locs):
                continue
            for j in range(1, dt.ell_star + 1):
                for rd in AX1:
                    P = ic.placements(rd, j)
                    v = [expect_prime(locs, j, P, (rd, b, c), 0) for (b, c) in
                         [("反復", "単数"), ("反復", "格子"), ("容器", "単数"), ("容器", "格子")]]
                    if not (v[0] <= v[1] <= v[2] <= v[3]):
                        ok = False
                        print(f"  [{name}] 順序が崩れた p={p} j={j} {rd}：{v}")
    # ⑤ 模型の体 ℚ_p(p^{1/e}) で、κ の正確な値が区間に入るか（shell_lattice.py の厳密な格子計算）
    import shell_lattice as sl

    class FakeV:
        pass

    for p, e in [(11, 3), (3, 4), (5, 6), (7, 10)]:
        L, I = sl.shell(p, e)
        fv = FakeV()
        fv.prime, fv.e, fv.weight, fv.name, fv.in_Vbad = p, e, 1, f"Q_{p}({p}^1/{e})", True
        fv.rho = ic.log_shell_radius(p, e)
        vmin = min(L.vw(b) for b in I)
        assert Fr(-vmin, e) == fv.rho, (p, e, vmin, fv.rho)
        for m in range(1, 2 * e + 2):
            for unit in (None, 1):
                th = L.wpow(m)
                if unit:
                    u = L.wpow(0)
                    u[1 % e] += 1
                    th = L.mul(u, th)
                fv.rq = Fr(m, e)                       # j = 1 として s = m/e
                loc = Local(fv)
                kI_exact = sl.kappa(L, I, th)
                # κ(θ𝒪)：θ·𝒪 の基底 θ·ϖ^r（r < e）を 𝓘 の座標で
                kTO_exact = min(sl.vp(x, p) for r in range(e) for x in sl.coords(I, L.mul(th, L.wpow(r)), e) if x != 0)
                kO_exact = min(sl.vp(x, p) for r in range(e) for x in sl.coords(I, L.wpow(r), e) if x != 0)
                a1, b1 = loc.kI(1)
                a2, b2 = loc.kTO(1)
                a3, b3 = loc.kO()
                good = a1 <= kI_exact <= b1 and a2 <= kTO_exact <= b2 and a3 <= kO_exact <= b3
                if loc.ball:
                    good &= a1 == b1 == kI_exact and a2 == b2 == kTO_exact and a3 == b3 == kO_exact
                if not good:
                    ok = False
                    print(f"  模型 {fv.name} θ={'(1+ϖ)' if unit else ''}ϖ^{m}：κ(θ𝓘)={kI_exact}∈[{a1},{b1}]、"
                          f"κ(θ𝒪)={kTO_exact}∈[{a2},{b2}]、κ(𝒪)={kO_exact}∈[{a3},{b3}]")
        print(f"  模型の体 ℚ_{p}({p}^(1/{e}))（{'玉' if p != 2 and e <= p - 2 else '玉でない'}）：κ の区間の検査を終えた")
    print("検査：" + ("すべて通った" if ok else "失敗あり"))
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", default="D2", choices=list(ic.DATA))
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--json")
    args = ap.parse_args()
    names = list(ic.DATA) if args.all else [args.data]
    if args.check:
        sys.exit(0 if check([n for n in names if n != "D2357"] or names) else 1)
    results = []
    for nm in names:
        dt = ic.InitialThetaData(nm, factor_seconds=1)
        res = evaluate(dt)
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
