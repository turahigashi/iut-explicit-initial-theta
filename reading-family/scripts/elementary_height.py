#!/usr/bin/env python3
"""高さの不等式を初等的に計算する（IUT を使わない。iut_compute.py のコードも読み込まない）。

IUT を知らない人が、IV 定理1.10 の文面だけを見て書いたプログラムという想定。使うのは二次体の算術と、
楕円曲線の j-不変量の付値だけ。

曲線 E : y² = x(x−1)(x−a) を二次体 F = ℚ(√D) 上で考える。a = π^m·π̄^k、π = x + y√D。
  1. j = 256(a²−a+1)³/(a²(a−1)²) が負の付値をもつ素点は、a または 1 − a の付値が 0 でない素点か、2 の上の素点。
     N(a) = N(π)^{m+k} と N(1 − a) の分子・分母を素因数分解して候補の素数を集める。
  2. 各素点 v で ord_v(j) を求め、ord_v(j) < 0 なら（潜在的に）乗法的還元で、q-パラメータの位数は ord_v(q) = −ord_v(j)。
  3. 有効因子の正規化された次数 deg(Σ c_v·v) = (1/[F:ℚ])·Σ c_v·f_v·log p で
       log 𝔮 = deg(Σ ord_v(q)·v)、log 𝔣 = deg(Σ v)（𝔮 と同じ台で係数 1、定理1.10 の定義）、log 𝔡 = log|disc F|/[F:ℚ]。
  4. 定理1.10 の文面の不等式に数を入れる（定数は文面から写すだけ。証明は使わない）：
       (1/6)·log 𝔮 ≤ (1 + 20·d/ℓ)·(log 𝔡 + log 𝔣) + 20·(e*·ℓ + η)、e* = 2^12·3^3·5·e、e = F の最大分岐指数、η = 2
     F_tpd = F(E[2]) = F（Legendre 形なので 2 等分点は F 上有理）。

数える素点は二通り：
  全部     ＝ ord_v(j) < 0 の素点すべて（2 の上も含む）
  𝕍^bad 型 ＝ IUT 版（iut_compute.py）の 𝕍^bad と同じ選び方（剰余標数が 2・3・5・ℓ でなく、ℓ が ord_v(q) を割らないもの。
             2・ℓ と ℓ | ord q は I 定義3.1 による。3・5 は iut_compute.py の選択）。
             IUT を知らない人には「この条件の素点だけ数えよ」と外から渡す絞り込みで、IUT 版との照合に使う。
使い方：python3 elementary_height.py [--data D2 ...]
"""
import argparse
import math
import time
from fractions import Fraction as Fr

import sympy

# 曲線のデータ（公開した具体例の一覧と同じ 7 つ）：(D, x, y, m, k, ℓ)
CURVES = {
    "D211": (5, 16, 3, 29, 0, 7), "D109": (-1, 10, 3, 29, 0, 7),
    "D2": (5, 14164, 5825, 1, 6, 7), "D3": (5, 14164, 5825, 6, -30, 7),
    "D18": (5, 14164, 5825, 18, 0, 7), "D15": (5, -5932, -919, 15, 0, 7),
    "D2357": (-1, 41, 26, 472, 0, 157),
}
# 大きな素因数（一覧の検算で分解済みのもの。素因数分解の手間を省くためのデータ）
KNOWN = {
    "D211": [201398405550512586511, 147082999581684740821681663264012329589],
    "D109": [534775081, 6065177, 1174770007439769673, 16450055877403724897],
    "D18": [7457371, 114594031, 8359969, 11868455558719, 247189845979, 15816593425179028969,
            122433023686655037533287683513603412782199],
    "D15": [42007741, 958514677640959, 556976186531, 7351778124297277952197531, 90966988530583079263900051],
    "D3": [7546302221502292729989416349739, 1984003939995100146692750879, 166911169, 26746145815244461,
           486685363594452319041420748071613404758945479, 154072586477232178581475729,
           38269129828752271745435515342932155533891],
}


class Q:
    """ℚ(√D) の元 A + B√D（A, B は有理数）"""

    def __init__(self, D, A, B=0):
        self.D, self.A, self.B = D, Fr(A), Fr(B)

    def __mul__(s, o):
        o = o if isinstance(o, Q) else Q(s.D, o)
        return Q(s.D, s.A * o.A + s.D * s.B * o.B, s.A * o.B + s.B * o.A)

    __rmul__ = __mul__

    def __add__(s, o):
        o = o if isinstance(o, Q) else Q(s.D, o)
        return Q(s.D, s.A + o.A, s.B + o.B)

    __radd__ = __add__

    def __neg__(s): return Q(s.D, -s.A, -s.B)
    def __sub__(s, o): return s + (-(o if isinstance(o, Q) else Q(s.D, o)))
    def __rsub__(s, n): return Q(s.D, n) - s
    def conj(s): return Q(s.D, s.A, -s.B)
    def norm(s): return s.A * s.A - s.D * s.B * s.B

    def __pow__(s, n):
        if n < 0:
            nn = s.norm()
            return Q(s.D, s.A / nn, -s.B / nn) ** (-n)
        r, b = Q(s.D, 1), s
        while n:
            if n & 1:
                r = r * b
            b, n = b * b, n >> 1
        return r


def vq(n, q):
    """有理数 n の q 進付値"""
    n = Fr(n)
    return sympy.multiplicity(q, n.numerator) - sympy.multiplicity(q, n.denominator)


def sqrt_mod(D, q, K):
    """√D を q^K を法として（q は奇素数、ヘンゼルの持ち上げ）"""
    r, M = sympy.sqrt_mod(D % q, q), q
    while M < q ** K:
        M = min(M * M, q ** K)
        r = (r - (r * r - D) * pow(2 * r, -1, M)) % M
    return r


def places_over(D, q):
    """素数 q の上の F の素点：[(名前, f, 埋め込みの符号 または None)]"""
    disc = D if D % 4 == 1 else 4 * D
    if disc % q == 0:
        return [(f"{q}", 1, None)]                          # 分岐
    if q == 2:
        assert D % 8 == 5, "2 が分解する体は扱わない"
        return [("2", 2, None)]                             # 惰性
    if sympy.legendre_symbol(D % q, q) == 1:
        return [(f"{q}+", 1, +1), (f"{q}-", 1, -1)]        # 分解
    return [(f"{q}", 2, None)]                              # 惰性


def val(x, q, f, emb, K):
    """素点での付値（素元の位数）"""
    if emb is None:                                         # 素点が一つ：v(x) = ord_q(N(x))/f
        n = vq(x.norm(), q)
        assert n % f == 0
        return n // f
    r = sqrt_mod(x.D, q, K)
    if emb < 0:
        r = (-r) % q ** K
    den = math.lcm(x.A.denominator, x.B.denominator)
    n = (int(x.A * den) + int(x.B * den) * r) % q ** K
    assert n != 0, "窓を広げる"
    return sympy.multiplicity(q, n) - sympy.multiplicity(q, den)


def candidate_primes(a, one_minus_a, known):
    """a・1 − a の付値が 0 でない素点の下の素数（と 2）。分解していない因数も返す"""
    primes, rest = {2}, []
    for N in (a.norm(), one_minus_a.norm()):
        for n in (abs(N.numerator), N.denominator):
            for p in known:
                while n % p == 0:
                    primes.add(p)
                    n //= p
            if n > 1:
                for p, _ in sympy.factorint(n, limit=10 ** 6, use_pm1=False, use_rho=False, use_ecm=False).items():
                    (primes.add(p) if sympy.isprime(p) else rest.append(p))
    return sorted(primes), rest


def compute(name):
    t0 = time.perf_counter()
    D, x, y, m, k, ell = CURVES[name]
    pi = Q(D, x, y)
    a = pi ** m * pi.conj() ** k
    b = 1 - a
    c = a * a - a + 1
    primes, rest = candidate_primes(a, b, KNOWN.get(name, []))
    rows = []
    deg_a = deg_b = 0.0                                     # 検算：Σ_v f_v·v(x)·log q = log|N(x)|（積公式）
    for q in primes:
        K = 12 + 2 * max(abs(vq(a.norm(), q)), abs(vq(b.norm(), q)), abs(vq(c.norm(), q)))
        for nm, f, emb in places_over(D, q):
            # ord_v(j) = ord_v(256) + 3·ord_v(a²−a+1) − 2·ord_v(a) − 2·ord_v(a−1)
            e_q = 2 if f == 1 and emb is None else 1        # 分岐なら ord_v(q) = 2
            va, vb, vc = val(a, q, f, emb, K), val(b, q, f, emb, K), val(c, q, f, emb, K)
            deg_a += f * va * math.log(q)
            deg_b += f * vb * math.log(q)
            ordj = 8 * e_q * (q == 2) + 3 * vc - 2 * va - 2 * vb
            if ordj < 0:
                rows.append(dict(place=nm, q=q, f=f, ordq=-ordj))
    if not rest:
        for deg, x in ((deg_a, a), (deg_b, b)):
            N = x.norm()
            assert abs(deg - (math.log(abs(N.numerator)) - math.log(N.denominator))) < 1e-6 * max(1.0, abs(deg)), name
    d, disc = 2, (D if D % 4 == 1 else 4 * D)
    log_d = math.log(abs(disc)) / d
    e_max = 2                                               # 二次体はある素数で分岐する
    e_star = 2 ** 12 * 3 ** 3 * 5 * e_max
    eta = 2.0
    out = dict(name=name, ell=ell, unfactored=[len(str(c_)) for c_ in rest], rows=rows, log_d=log_d)
    keep = {"全部": lambda r: True,
            "𝕍^bad 型": lambda r: r["q"] not in (2, 3, 5, ell) and r["ordq"] % ell != 0}
    for label, ok in keep.items():
        sel = [r for r in rows if ok(r)]
        log_q = sum(r["f"] * r["ordq"] * math.log(r["q"]) for r in sel) / d
        log_f = sum(r["f"] * math.log(r["q"]) for r in sel) / d
        rhs = (1 + 20 * d / ell) * (log_d + log_f) + 20 * (e_star * ell + eta)
        out[label] = dict(log_q=log_q, log_f=log_f, lhs=log_q / 6, rhs=rhs,
                          szpiro=log_q / (log_d + log_f), places=[r["place"] for r in sel])
    out["seconds"] = time.perf_counter() - t0
    return out


def show(r):
    note = ("（分解していない因数 " + "・".join(f"{n} 桁" for n in r["unfactored"]) + " があり、その上の素点は数えていない）"
            if r["unfactored"] else "")
    print(f"\n=== {r['name']}（ℓ = {r['ell']}） ==={note}")
    print("  ord_v(q) > 0 の素点：" + "、".join(f"{x['place']}（ord q = {x['ordq']}）" for x in r["rows"]))
    for label in ("全部", "𝕍^bad 型"):
        s = r[label]
        print(f"  {label}（素点 {len(s['places'])} 個）：log 𝔮 = {s['log_q']:.4f}、log 𝔣 = {s['log_f']:.4f}、"
              f"log 𝔡 = {r['log_d']:.4f}、log 𝔮/(log 𝔡 + log 𝔣) = {s['szpiro']:.3f}")
        if label == "𝕍^bad 型":
            ok = s["lhs"] <= s["rhs"]
            print(f"      定理1.10 の不等式：(1/6)·log 𝔮 = {s['lhs']:.4f} {'≤' if ok else '>'} {s['rhs']:.6g}  → "
                  + ("成り立つ" if ok else ("決まらない（分解していない因数）" if r["unfactored"] else "成り立たない")))
    print(f"  計算時間 {r['seconds']:.3f} 秒")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", nargs="*", default=list(CURVES))
    args = ap.parse_args()
    for name in args.data:
        show(compute(name))


if __name__ == "__main__":
    main()
