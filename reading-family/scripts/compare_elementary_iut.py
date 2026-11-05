#!/usr/bin/env python3
"""初等的な計算（elementary_height.py）と IUT の手順（iut_height.py）を同じ 7 つのデータで並べる。

  1. 照合：両端（log 𝔮・log 𝔣・log 𝔡・定理1.10 の右辺）と、数えた素点の一覧が一致するか
  2. 初等的な計算だけが数えられる素点（2・3・5・ℓ の上、ℓ が ord q を割る素点）
  3. IUT の手順だけにある中間の段：(k−1)·|log q̲̲| ≤ 余地 C と、C の内訳
  4. 定数 6 がどこから来るか
  5. プログラムとしての大きさ：静的な行数・実際に走った行数・呼ばれた関数・入力・計算時間
使い方：python3 compare_elementary_iut.py
"""
import io
import math
import os
import sys
import time
import tokenize
from collections import Counter
from contextlib import redirect_stdout

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import elementary_height as el  # noqa: E402
import iut_compute as ic  # noqa: E402
import iut_height as ih  # noqa: E402
import iut_patterns as ip  # noqa: E402

TOL = 1e-9


def code_lines(path):
    """空行・注釈・docstring を除いた行数"""
    src = open(path, encoding="utf-8").read()
    lines = set()
    prev = tokenize.INDENT
    for tok in tokenize.generate_tokens(io.StringIO(src).readline):
        if tok.type == tokenize.STRING and prev in (tokenize.INDENT, tokenize.NEWLINE, tokenize.DEDENT):
            prev = tok.type
            continue                                         # docstring
        if tok.type not in (tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
                            tokenize.ENDMARKER):
            lines.update(range(tok.start[0], tok.end[0] + 1))
        if tok.type not in (tokenize.COMMENT, tokenize.NL):
            prev = tok.type
    return len(lines)


def traced(fn, *args):
    """fn(*args) を走らせ、このフォルダのファイルで実際に走った行と呼ばれた関数を記録する"""
    lines, calls = set(), Counter()

    def tracer(frame, event, arg):
        f = frame.f_code.co_filename
        if not f.startswith(HERE):
            return None
        if event == "call":
            co, qual = frame.f_code, frame.f_code.co_name
            if co.co_argcount:
                cls = type(frame.f_locals.get(co.co_varnames[0]))
                if co.co_name in getattr(cls, "__dict__", {}):
                    qual = cls.__name__ + "." + qual
            calls[(os.path.basename(f), qual)] += 1
        elif event == "line":
            lines.add((os.path.basename(f), frame.f_lineno))
        return tracer

    sys.settrace(tracer)
    try:
        with redirect_stdout(io.StringIO()):
            out = fn(*args)
    finally:
        sys.settrace(None)
    return out, lines, calls


def places_el(r):
    return sorted((x["q"], x["f"], x["ordq"]) for x in r["rows"]
                  if x["q"] not in (2, 3, 5, r["ell"]) and x["ordq"] % r["ell"] != 0)


def places_iut(name):
    dt = ic.InitialThetaData(name, factor_seconds=1)
    return sorted((v.prime, v.f, v.ord_q_w) for v in dt.bad)


def main():
    names = list(el.CURVES)
    print("=" * 100)
    print("1. 照合（初等的な計算の「𝕍^bad 型」と IUT の手順）")
    print("=" * 100)
    print(f"  {'データ':<7}{'素点の一覧':<10}{'log 𝔮 の差':>12}{'log 𝔣 の差':>12}{'log 𝔡 の差':>12}{'右辺の差':>12}   (1/6)log 𝔮 ≤ 右辺")
    E, U = {}, {}
    for n in names:
        E[n], U[n] = el.compute(n), ih.compute(n)
        s, u = E[n]["𝕍^bad 型"], U[n]
        same = places_el(E[n]) == places_iut(n)
        dq, df = abs(s["log_q"] - u["logq"]), abs(s["log_f"] - u["log_fF"])
        dd, dr = abs(E[n]["log_d"] - u["log_dF"]), abs(s["rhs"] - u["thm_rhs"])
        assert same and max(dq, df, dd) < TOL and dr < TOL * u["thm_rhs"], n
        print(f"  {n:<7}{'一致' if same else '不一致':<10}{dq:12.1e}{df:12.1e}{dd:12.1e}{dr:12.1e}   "
              f"{s['lhs']:.4f} ≤ {s['rhs']:.6g}")
    print("  → 7 データとも、数えた素点（素数・剰余次数・ord q）と両端の 4 つの数が一致（差は TOL = 1e-9 未満）")

    print("\n" + "=" * 100)
    print("2. 初等的な計算だけが数えられる素点（IUT の手順は 𝕍^bad の外を左辺に入れない。2・ℓ の上と ℓ | ord q は定義3.1 が除き、")
    print("   3・5 の上は iut_compute.py が除いている：F = F_mod(√−1, E[30]) の局所体が分からないため。理論は 3・5 を除かない）")
    print("=" * 100)
    for n in names:
        r = E[n]
        extra = [x for x in r["rows"] if x["q"] in (2, 3, 5, r["ell"]) or x["ordq"] % r["ell"] == 0]
        share = 1 - r["𝕍^bad 型"]["log_q"] / r["全部"]["log_q"]
        txt = "、".join(f"{x['place']}（ord q = {x['ordq']}）" for x in extra) or "なし"
        print(f"  {n:<7} {txt}  → log 𝔮 の {100 * share:.2f}%")

    print("\n" + "=" * 100)
    print("3. IUT の手順だけにある中間の段：(k−1)·|log q̲̲| ≤ 余地 C（C = U(D) + k·|log q̲̲|）")
    print("=" * 100)
    print(f"  {'データ':<7}{'(k−1)|log q̲̲|':>14}{'C':>10}{'比':>8}   {'定理の形の比':>12}   C の内訳（K の差積・Σlog p・I*・2,3,5,ℓ の上界・アルキメデス）")
    for n in names:
        if E[n]["unfactored"]:
            print(f"  {n:<7}（分解していない因数があり、両辺とも不完全なので省く）")
            continue
        u, s = U[n], E[n]["𝕍^bad 型"]
        gap, C = u["k_absq"] + u["lhs"], u["U"] + u["k_absq"]
        room = sum(x["room"] for x in u["rows"])
        logp = sum(x["s"] for x in u["rows"])
        star = sum(x["star_exact"] for x in u["rows"])
        assert abs(room + logp + star + u["U_unknown"] + u["arch"] - C) < 1e-6
        print(f"  {n:<7}{gap:14.2f}{C:10.2f}{gap / C:8.3f}   {s['lhs'] / s['rhs']:12.1e}   "
              f"{room:.1f}・{logp:.1f}・{star:.1f}・{u['U_unknown']:.1f}・{u['arch']:.1f}"
              f"（2,3,5,ℓ の上界が {100 * u['U_unknown'] / C:.0f}%）")

    print("\n" + "=" * 100)
    print("3b. IUT の連鎖の全体：−|log q̲̲| ≤ R（真ん中、12 通りの読み）≤ U(D) ≤ 段階 (viii) ≤ 定理の一様な上界")
    print("=" * 100)
    print("  右の 5 つはどれも −|log Θ| の側の数（R は数えた素点だけ。2・3・5・ℓ の上の分 ≥ 0 は入っていない）。")
    print("  初等的な計算が持つのは、左端と、右端を (1/6)·log 𝔮 ≤ … の形に直したものだけ。")
    print(f"  {'データ':<7}{'−|log q̲̲|':>10}{'R 元の読み':>12}{'R 12 通りの幅':>22}{'U(D)':>10}{'(viii)':>10}{'定理の上界':>12}   R < −|log q̲̲| の読み")
    blowup = []
    for n in names:
        if E[n]["unfactored"]:
            print(f"  {n:<7}（分解していない因数があり、両辺とも不完全なので省く）")
            continue
        u = U[n]
        with redirect_stdout(io.StringIO()):
            res = ip.evaluate(ic.InitialThetaData(n, factor_seconds=1))
        Rs = {tuple(r["pattern"]): (r["lo"] + r["extra"], r["hi"] + r["extra"]) for r in res["rows"]}
        R0 = Rs[("V", "容器", "単数")]
        lo, hi = min(a for a, _ in Rs.values()), max(b for _, b in Rs.values())
        ell, d = u["ell"], 2
        thm = (ell + 1) / 4 * ((1 + 12 * d / ell) * (u["log_dF"] + u["log_fF"]) + 10 * (u["e_star_l"] + 2.0)
                                - (1 - 12 / ell ** 2) * u["logq"] / 6) - u["logq"] / (2 * ell)
        assert hi <= u["U"] <= u["viii"] <= thm, n
        blowup.append(thm / u["viii"])
        below = [ "・".join(pt) for pt, (_, b) in Rs.items() if b < u["lhs"]]
        r0 = f"{R0[0]:.2f}" if R0[0] == R0[1] else f"[{R0[0]:.2f}, {R0[1]:.2f}]"
        print(f"  {n:<7}{u['lhs']:10.2f}{r0:>12}{'[' + format(lo, '.2f') + ', ' + format(hi, '.2f') + ']':>22}"
              f"{u['U']:10.2f}{u['viii']:10.1f}{thm:12.4g}   {'、'.join(below) or 'なし'}")
    print("  ・R の上端 ≤ U(D) ≤ (viii) ≤ 定理の上界 は 6 データとも成り立つ（assert で確認）。")
    print("  ・U(D)：このデータの局所体（K の分岐）を使う。(viii)：K を F の差積と導手で抑える（段階 (ii)）。")
    print(f"    定理の上界：さらに特別な素数の個数を η_prm（命題1.6）で一様に抑える。ここで (viii) の "
          f"{min(blowup):,.0f}〜{max(blowup):,.0f} 倍に膨らむ。")

    print("\n" + "=" * 100)
    print("4. 定数 6")
    print("=" * 100)
    print("  初等的な計算：6 は定理の文面から写した定数（コードの中の 1/6）。")
    print("  IUT の手順：ラベル j = 1…ℓ* についての二つの平均の比として出てくる。")
    print("    テータの項  Σ j²/ℓ* = ℓ(ℓ+1)/12 = k  →  k·|log q̲̲| = (ℓ+1)/24·log 𝔮")
    print("    差積の項    Σ (j+1)/ℓ* = (ℓ+5)/4      （テンソル積の因子の個数 j+1 の平均）")
    for ell in (7, 157, 10 ** 6):
        k = ell * (ell + 1) / 12
        coef = (2 * ell / (k - 1)) * (ell + 5) / 4
        print(f"    ℓ = {ell:>7}：log 𝔮 ≤ {coef:.4f}·log 𝔡^K + …（(ℓ+5)/4 ÷ ((ℓ+1)/24 − 1/(2ℓ))、ℓ → ∞ で 6）")

    print("\n" + "=" * 100)
    print("5. プログラムとしての大きさ")
    print("=" * 100)
    files_el = ["elementary_height.py"]
    files_iut = ["iut_height.py", "iut_compute.py"]
    st_el = sum(code_lines(os.path.join(HERE, f)) for f in files_el)
    st_iut = {f: code_lines(os.path.join(HERE, f)) for f in files_iut}
    lines_el, calls_el, lines_iut, calls_iut = set(), Counter(), set(), Counter()
    for n in names:
        _, l1, c1 = traced(el.compute, n)
        _, l2, c2 = traced(ih.compute, n)
        lines_el |= l1
        calls_el += c1
        lines_iut |= l2
        calls_iut += c2
    t_el = t_iut = 0.0
    for n in names:
        t0 = time.perf_counter()
        el.compute(n)
        t_el += time.perf_counter() - t0
        t0 = time.perf_counter()
        with redirect_stdout(io.StringIO()):
            ih.compute(n)
        t_iut += time.perf_counter() - t0
    by_file = Counter(f for f, _ in lines_iut)
    print(f"  {'':<34}{'初等的な計算':>14}{'IUT の手順':>14}")
    print(f"  {'静的な行数（空行・注釈を除く）':<30}{st_el:>14}{sum(st_iut.values()):>14}"
          f"   （IUT：{'・'.join(f'{f} {c}' for f, c in st_iut.items())}）")
    print(f"  {'7 データで実際に走った行':<30}{len(lines_el):>14}{len(lines_iut):>14}"
          f"   （IUT：{'・'.join(f'{f} {c}' for f, c in sorted(by_file.items()))}）")
    print(f"  {'呼ばれた関数（種類）':<30}{len(calls_el):>14}{len(calls_iut):>14}")
    print(f"  {'計算時間（7 データ、秒）':<30}{t_el:>14.2f}{t_iut:>14.2f}"
          "   （どちらも大半は素因数分解。IUT は分解の窓を 1 秒で切る）")
    print("  IUT の手順で呼ばれた関数：")
    for (f, q), c in sorted(calls_iut.items()):
        print(f"    {f}:{q}（{c} 回）")
    print("  初等的な計算で呼ばれた関数：")
    for (f, q), c in sorted(calls_el.items()):
        print(f"    {f}:{q}（{c} 回）")
    print("\n  読む入力：")
    print("    初等的な計算  曲線 (D, x, y, m, k) だけ。ℓ は定理の定数 1 + 20d/ℓ と 20·e*·ℓ にしか現れない。")
    print("    IUT の手順    曲線と ℓ に加えて、ラベル j = 1…ℓ*、悪い素点の組 T（重み）、K = F(E[ℓ]) の局所的な分岐指数 e、")
    print("                  特別な素数の集合（D6）、2・3・5・ℓ の上の (R4) の評価。")


if __name__ == "__main__":
    main()
