#!/usr/bin/env python3
"""IUT を計算として走らせる ―― 初期Θデータを入れ、IUT の操作を施し、結果を統合する。

このプログラムの読み方
  IUT（宇宙際タイヒミュラー理論、IUT I–IV）の骨組みは「一つの初期Θデータに一連の操作を施し、その結果を最後に一つの
  不等式へ統合する」ことである。原典の大部分は、各操作が環構造を使わずに（群だけから）実行でき、互いに両立することの
  証明に充てられている。このプログラムはその証明を書かない。代わりに

    ・各劇場（ホッジ劇場）に、型で分けた体の写しを持たせる。劇場をまたいで渡るのは「ケーブル」（単数と次数）だけ。
      型の境界を越える演算は TypeError になる。これが「環構造が保たれない」ことのプログラム上の姿。
    ・無限の対象（p 進数、副有限群、全素数の積）は、有限の窓（p 進の桁数・Kummer の段・素因数分解の範囲）で計算し、
      窓を伸ばしたときに何が変わらなくなるかを出力する。人はその列を見て外挿する。
    ・二つの読みが分かれる箇所（Θ-パイロットのラベルをどう動かすか）は、入力 --reading の一か所だけ。
    ・不定性 (Ind2) の群は二つの模型で計算し、両方を出す：単数倍（可能な像の格子を動かさない）と、各因子の log-殻を
      保つ ℤ_p 線形な自己同型すべて（lana-agents/iut の tensorAut）。二つの差が、lana-agents/iut の Gap.lean で
      値が未解決とされた (Ind2) の項で、その値は [Gap]（Zenodo 10.5281/zenodo.23954194）の閉じた式で決まる。

  出力の最後の「統合」が IUT III 系3.12 の証明の段階 (xi) に当たる。そこで原典は二つの計算（Fig. 3.8 の「同語反復的に
  同値な二つの方法」）を結ぶ推論 (xi-f) を置く。このプログラムは二つの計算を両方とも実際に行い、数として並べる。
  推論 (xi-f) が正しいかどうかは計算では決まらない（値の極限ではなく、比べ方の規則だから）。プログラムはそこを
  一行の比較として見せるだけで、どちらが正しいとも主張しない。

対応表（原典の位置は IUT I–IV の番号。訳は著者による）
  §2 初期Θデータ         IUT I 定義3.1           本物の計算（曲線・q-パラメータ・悪い素点）＋窓（素因数分解の範囲）
  §3 ラベル               IUT I §4・§6、III 系3.12  有限なので全部計算（𝔽_l、|𝔽_l|、𝔽_l^⋇、procession、二つの対称性）
  §4 劇場                 IUT I §3–§6             型で分けた体の写し。q-パイロット・Θ-パイロット・log-殻・大域次数
  §5 リンク               I 系3.7、III 定義3.8・定義1.1  Θ-リンク＝ケーブル（単数部分と値群部分）、log-リンク＝p 進対数
  §6 多放射的アルゴリズム   III 定理3.11、注意3.11.1   入力＝ケーブル＋エタール側データ、出力＝可能な像の合併の包と log 体積
                          不定性 (Ind1)(Ind2)(Ind3)  (Ind1) が値を動かす（読みの分岐）。(Ind2) は二つの模型（単数・格子）
  §7 統合                 III 系3.12 証明 (xi)・(xii)  方法 A（q-パイロットを直接）と方法 B（アルゴリズム経由）を計算して比べる
                          IV 定理1.10              二つを合わせると高さの不等式になる。そのデータでの値を出す
  §8 注意3.11.1 の玩具     III 注意3.11.1 (vi)–(viii) 素朴な Θ-リンク、異なるラベル、強制的同一視（自明な多放射表現）

  APT・IPL・SHE（III 注意3.11.1 (iii)–(v)）は検査する命題としては書かない。コードの形と実行の記録として現れる。
    APT（アルゴリズム的平行移動）：同じ関数 run() を二つの劇場の環で実行する（値を関数で運ぶのではない）
    SHE（同時正則表現可能性）  ：run() が触った環を実行中に記録する。終域の列の環とケーブルだけで走ったことが記録に残る
    IPL（入力 prime-strip リンク）：出力に、入力ケーブルの値群部分（同一のオブジェクト）への参照が付いている

使い方
  python3 iut_compute.py                      # D2（大域部分まで完全に分かっているデータ）を読み (V) で
  python3 iut_compute.py --data D211 --reading L
  python3 iut_compute.py --all                # 7 つのデータ
  python3 iut_compute.py --data D2 --scale-q 4   # 仮に q の高さだけ 4 倍だったら（全称命題の一例を手で入れる）
  python3 iut_compute.py --windows            # 窓を伸ばしたときの列
"""
import argparse
import itertools
import math
import sys
from fractions import Fraction as Fr
from math import gcd

import sympy

# =====================================================================================================
# §1 窓の道具
# =====================================================================================================


class LogSum:
    """Σ c_p · log p（c_p は有理数）。log 体積を、log p の有理係数の和として正確に持つ。数値にするのは最後だけ。
    キー 'π' は log π（アルキメデス素点の容器）。"""

    def __init__(self, c=None):
        self.c = {k: Fr(v) for k, v in (c or {}).items() if Fr(v) != 0}

    @staticmethod
    def log(p, coef=1):
        return LogSum({p: coef})

    def __add__(s, o):
        d = dict(s.c)
        for k, v in o.c.items():
            d[k] = d.get(k, 0) + v
        return LogSum(d)

    def __neg__(s): return LogSum({k: -v for k, v in s.c.items()})
    def __sub__(s, o): return s + (-o)
    def __mul__(s, r): return LogSum({k: v * Fr(r) for k, v in s.c.items()})
    __rmul__ = __mul__

    def __repr__(s): return str(s)

    def value(s):
        return sum(float(v) * (math.log(math.pi) if k == 'π' else 1.0 if k == 'num' else math.log(k)) for k, v in s.c.items())

    def __str__(s):
        if not s.c:
            return "0"
        parts = []
        for k in sorted(s.c, key=lambda k: (k in ('π', 'num'), k if k not in ('π', 'num') else 0)):
            v = s.c[k]
            parts.append(f"{float(v):.4f}" if k == 'num' else f"{v}·log {k}")
        return " + ".join(parts).replace("+ -", "− ")


class Padic:
    """p 進数の窓：付値 v と、p^K を法とした単数 u（K が窓の大きさ）"""

    def __init__(self, p, K, v, u):
        self.p, self.K, self.v, self.u = p, K, v, u % p ** K

    @staticmethod
    def of(p, K, X):
        if X == 0:
            raise ValueError("0 は単数部分を持たない")
        v = 0
        while X % p == 0:
            X //= p
            v += 1
        return Padic(p, K, v, X)

    def __mul__(s, o):
        K = min(s.K, o.K)
        return Padic(s.p, K, s.v + o.v, s.u * o.u)

    def inv(s): return Padic(s.p, s.K, -s.v, pow(s.u, -1, s.p ** s.K))
    def __pow__(s, k): return Padic(s.p, s.K, s.v * k, pow(s.u if k >= 0 else pow(s.u, -1, s.p ** s.K), abs(k), s.p ** s.K))

    def __add__(s, o):
        m = min(s.v, o.v)
        K = min(s.K + s.v, o.K + o.v) - m          # 足した結果の精度（絶対精度 − 付値）
        M = s.p ** K
        x = (s.u * s.p ** (s.v - m) + o.u * s.p ** (o.v - m)) % M
        if x == 0:
            raise ValueError("窓の中で打ち消し合った（桁数を増やす）")
        k = 0
        while x % s.p == 0:
            x //= s.p
            k += 1
        return Padic(s.p, K - k, m + k, x)

    def __neg__(s): return Padic(s.p, s.K, s.v, -s.u)
    def __sub__(s, o): return s + (-o)

    def digits(s, n=6):
        """単数部分の p 進の桁（下から n 桁）"""
        u, out = s.u, []
        for _ in range(min(n, s.K)):
            out.append(u % s.p)
            u //= s.p
        return out


def q_series_in_t(N):
    """j(q) = 1/q + 744 + 196884 q + … の逆：q = t + 744 t² + 750420 t³ + …（t = 1/j）の係数を N 項まで。
    E4 = 1 + 240 Σ σ3(n) qⁿ、Δ = q Π (1 − qⁿ)^24、t = 1/j = q·(Δ/q)/E4³ を級数で逆にする。"""
    def mul(a, b):
        c = [0] * N
        for i, x in enumerate(a):
            if x:
                for j in range(N - i):
                    c[i + j] += x * b[j]
        return c
    E4 = [1] + [240 * sum(d ** 3 for d in range(1, n + 1) if n % d == 0) for n in range(1, N)]
    D = [1] + [0] * (N - 1)                       # Δ/q = Π (1 − qⁿ)^24
    for n in range(1, N):
        f = [0] * N
        f[0] = 1
        if n < N:
            f[n] = -1
        for _ in range(24):
            D = mul(D, f)
    E43 = mul(mul(E4, E4), E4)
    inv = [0] * N                                  # 1/E4³
    inv[0] = 1
    for n in range(1, N):
        inv[n] = -sum(E43[k] * inv[n - k] for k in range(1, n + 1))
    g = mul(D, inv)                                # t = q·g(q)、g(0) = 1
    # 逆級数 q = t·h(t) を反復で：q ← t / g(q)
    q = [0, 1] + [0] * (N - 2)
    for _ in range(N):
        gq = [0] * N                               # g(q(t))
        qpow = [1] + [0] * (N - 1)
        for k in range(N):
            if k:
                qpow = mul(qpow, q)
            for i in range(N):
                gq[i] += g[k] * qpow[i]
        ginv = [0] * N
        ginv[0] = 1
        for n in range(1, N):
            ginv[n] = -sum(gq[k] * ginv[n - k] for k in range(1, n + 1))
        q = [0] + ginv[:N - 1]                     # q = t·(1/g(q))
    return q


Q_COEF = q_series_in_t(12)
assert Q_COEF[1:5] == [1, 744, 750420, 872769632], Q_COEF[:5]


# =====================================================================================================
# §2 初期Θデータ（IUT I 定義3.1）
# =====================================================================================================
# 定義3.1（訳）：「(F̄/F, X_F, l, C_K, 𝕍, 𝕍_mod^bad, ϵ) を初期Θ-データと呼ぶ」。
#   (b) 𝕍_mod^bad は「奇数剰余標数をもつ F_mod の非アルキメデス付値の空でない集合であり、…その上にある各元において
#       X_F は悪い還元、すなわち乗法的還元をもつ」。
#   (c) l ≥ 5 は素数で、「𝕍_mod^bad の各元の剰余標数、および … q-パラメータの位数 … と素である」。
# このプログラムのデータは、公開した具体例の一覧（版 1.0.0）の 7 つ。モジュライ体 F_mod = ℚ(√D)、
# 曲線 y² = x(x−1)(x−a)、a = π^m·π̄^k（π は分解する素数 p の上の素元）、ℓ。
# K = F(E[l]) の分岐指数は e(F_mod,w/ℚ_q)·15ℓ/gcd(15ℓ, ord q) とする。p の上の素点（F_mod,w = ℚ_p）では一覧の付録 A の
# 証明で使う式で、一覧の表 1 を再現する。p 以外の悪い素点にも同じ式を当てはめる（仮定）。

DATA = {
    "D211": (5, 16, 3, 29, 0, 7), "D109": (-1, 10, 3, 29, 0, 7),
    "D2": (5, 14164, 5825, 1, 6, 7), "D3": (5, 14164, 5825, 6, -30, 7),
    "D18": (5, 14164, 5825, 18, 0, 7), "D15": (5, -5932, -919, 15, 0, 7),
    "D2357": (-1, 41, 26, 472, 0, 157),
}
CONDITIONAL = {"D2357": "準備中の別報に依る（一覧で † を付けたもの）"}


class QF:
    """F_mod = ℚ(√D) の元 A + B√D（A, B は有理数）"""

    def __init__(self, D, A, B=0):
        self.D, self.A, self.B = D, Fr(A), Fr(B)

    def __mul__(s, o): return QF(s.D, s.A * o.A + s.D * s.B * o.B, s.A * o.B + s.B * o.A)
    def __sub__(s, o): return QF(s.D, s.A - o.A, s.B - o.B)
    def conj(s): return QF(s.D, s.A, -s.B)
    def norm(s): return s.A * s.A - s.D * s.B * s.B
    def __pow__(s, n):
        r, b = QF(s.D, 1), s if n >= 0 else QF(s.D, s.A / s.norm(), -s.B / s.norm())
        for _ in range(abs(n)):
            r = r * b
        return r


class Place:
    """F_mod の素点 w（と、その上に 𝕍 が選ぶ K の素点）の局所データ"""

    def __init__(self, **kw):
        self.__dict__.update(kw)

    def __repr__(self): return self.name


def sqrt_mod_prime_power(D, p, K):
    """√D を p^K を法として（D は負でもよい。D mod p を持ち上げてはいけない：2 桁目から別の数の平方根になる）"""
    r = sympy.sqrt_mod(D % p, p)
    if r is None:
        return None
    M = p
    for _ in range(K.bit_length() + 2):
        M = min(M * M, p ** K)
        r = (r - (r * r - D) * pow(2 * r, -1, M)) % M
    return r % p ** K


def val_at(xqf, p, r, K):
    """F_mod の元 xqf の、√D ↦ r（p 進）の埋め込みでの付値（分解する素数 p）"""
    A, B = xqf.A, xqf.B
    den = math.lcm(A.denominator, B.denominator)
    K += sympy.multiplicity(p, den)
    num = int(A * den) + int(B * den) * r
    num %= p ** K
    if num == 0:
        raise ValueError(f"付値が窓 p^{K} をはみ出した（窓を広げる）")
    v = 0
    while num % p == 0:
        num //= p
        v += 1
    return v - sympy.multiplicity(p, den)


# 既知の素因数（窓の外から持ち込む）
#   D3：公開した一覧の検算 check_pratt_factorizations.py が Pratt 証明つきで分解したもの
#   D211・D109・D18・D15：このプログラムの窓（sympy の楕円曲線法、2026-11-02、各 6〜67 秒）で見つけ、BPSW で素数と判定したもの
KNOWN_PRIMES = {
    "D211": [201398405550512586511, 147082999581684740821681663264012329589],
    "D109": [534775081, 6065177, 1174770007439769673, 16450055877403724897],
    "D18": [7457371, 114594031, 8359969, 11868455558719, 247189845979, 15816593425179028969,
            122433023686655037533287683513603412782199],
    "D15": [42007741, 958514677640959, 556976186531, 7351778124297277952197531, 90966988530583079263900051],
    "D3": [7546302221502292729989416349739, 1984003939995100146692750879, 166911169, 26746145815244461,
           486685363594452319041420748071613404758945479, 154072586477232178581475729,
           38269129828752271745435515342932155533891],
}


def factor_window(n, limit, seconds, known=()):
    """n の素因数を窓の中で：limit までの試し割り、残りが素数ならそれも、合成数なら seconds 秒だけ ρ 法と楕円曲線法。
    返り値：(見つかった素数のリスト, 分解できずに残った合成数のリスト)。窓を伸ばす（limit・seconds を増やす）と
    残りが減り、見つかる素数が増える。"""
    import signal
    found, rest = [], []
    for q in known:                                       # 既知の素因数を先に割る
        if n % q == 0:
            found.append(q)
            while n % q == 0:
                n //= q
    f = sympy.factorint(n, limit=limit, use_pm1=False, use_rho=False, use_ecm=False) if n > 1 else {}
    for q, _ in f.items():
        if q < limit or sympy.isprime(q):
            found.append(q)
            continue
        pp = sympy.perfect_power(q)
        if pp and sympy.isprime(pp[0]):
            found.append(pp[0])
            continue
        if seconds <= 0:
            rest.append(q)
            continue

        def handler(signum, frame):
            raise TimeoutError
        old = signal.signal(signal.SIGALRM, handler)
        signal.alarm(max(1, int(seconds)))
        try:
            g = sympy.factorint(q)
            signal.alarm(0)
            found.extend(g)
        except TimeoutError:
            rest.append(q)
        finally:
            signal.alarm(0)
            signal.signal(signal.SIGALRM, old)
    return found, rest


class InitialThetaData:
    """初期Θデータの具体例。悪い素点・q・分岐指数・log-殻の半径を計算で導く"""

    def __init__(self, name, factor_limit=10 ** 6, padic_digits=8, scale_q=1, factor_seconds=5, use_known=True):
        D, x, y, m, k, ell = DATA[name]
        self.name, self.D, self.ell, self.m, self.k = name, D, ell, m, k
        self.ell_star = (ell - 1) // 2
        self.pi = QF(D, x, y)
        self.p = int(self.pi.norm())
        self.a = (self.pi ** m) * (self.pi.conj() ** k)
        self.one_minus_a = QF(D, 1) - self.a
        self.scale_q = Fr(scale_q)
        self.factor_limit = factor_limit
        self.factor_seconds = factor_seconds
        self.use_known = use_known
        self.padic_digits = padic_digits
        self.notes = []
        self._places()

    # ---- 曲線の悪い素点：a と 1 − a を割る F_mod の素点（2 は除く。定義3.1(b) は奇数剰余標数）
    def _places(self):
        D, p, ell = self.D, self.p, self.ell
        Na, N1 = self.a.norm(), self.one_minus_a.norm()
        # N(a) = p^{m+|k|}（π の冪）なので p は分かっている。N(1 − a) を窓の中で分解する（大域の窓）
        c = abs(N1.numerator) * abs(N1.denominator)
        while c % p == 0:
            c //= p
        known = KNOWN_PRIMES.get(self.name, ()) if self.use_known else ()
        primes, self.unfactored = factor_window(c, self.factor_limit, self.factor_seconds, known)
        primes = sorted(set(primes) | {p})
        self.places = []
        for q in primes:
            if q == 2:
                continue
            # 付値を求める窓：ノルムに現れる q の重複度より大きく取る（はみ出すと「付値なし」に化ける）
            K = 10 + sympy.multiplicity(q, Na.numerator) + sympy.multiplicity(q, Na.denominator) \
                + sympy.multiplicity(q, N1.numerator) + sympy.multiplicity(q, N1.denominator)
            if D % q == 0:
                kind, embeds = "分岐", [None]
            elif sympy.legendre_symbol(D % q, q) == 1:
                K += 2 * sympy.multiplicity(q, Na.denominator) + 2 * sympy.multiplicity(q, N1.denominator)
                r = sqrt_mod_prime_power(D, q, K)
                kind, embeds = "分解", [r, (-r) % q ** K]
            else:
                kind, embeds = "惰性", [None]
            for idx, r in enumerate(embeds):
                if r is not None:
                    va, v1 = val_at(self.a, q, r, K), val_at(self.one_minus_a, q, r, K)
                    weight, f_w, e_w = Fr(1, 2), 1, 1
                else:                                      # 惰性・分岐：一つの素点。付値はノルムから
                    va = sympy.multiplicity(q, Na.numerator) - sympy.multiplicity(q, Na.denominator)
                    v1 = sympy.multiplicity(q, N1.numerator) - sympy.multiplicity(q, N1.denominator)
                    f_w, e_w = (2, 1) if kind == "惰性" else (1, 2)
                    if kind == "惰性":
                        va, v1 = va // 2, v1 // 2
                    weight = Fr(1)
                # 多重的還元の判定：j = 256(a²−a+1)³/(a²(a−1)²) の付値が負
                if va and va < 0:
                    ordj = 2 * va                       # a の極：分子 6va、分母 4va
                else:
                    ordj = -2 * max(va or 0, 0) - 2 * max(v1 or 0, 0)
                ordq = max(-ordj, 0)                    # ord_w(q)（w の正規化付値）。0 なら良い還元
                name = f"{q}" + ("" if len(embeds) == 1 else ("₁" if idx == 0 else "₂"))
                pl = Place(name=name, prime=q, kind=kind, weight=weight, f=f_w, e_base=e_w, ord_q_w=ordq,
                           ord_a=va, ord_1ma=v1)
                small = q in (3, 5, ell)
                pl.small = small
                pl.good = ordq == 0
                if small:
                    pl.e = None                          # 2・3・5・ℓ の上は F の構成に依る（分からない：容器は 0 以上として捨てる）
                elif pl.good:
                    pl.e = e_w                           # 良い還元で 2·3·5·ℓ の外：K/F_mod は不分岐
                else:
                    pl.e = e_w * 15 * ell // gcd(15 * ell, ordq)   # K_v/ℚ_q の分岐指数（p の上では一覧の付録 A の式。他は仮定）
                self.places.append(pl)
        # q-パラメータの p 進計算（分解する素数 p の上の二つの素点）
        for pl in self.places:
            pl.q = None
            if pl.prime == p and not pl.good:
                pl.q = self._tate_q(pl)
        # 𝕍_mod^bad（定義3.1(b)(c) の条件を満たすもの全部。分解できなかった部分は入れない＝空でない部分集合の選択）
        for pl in self.places:
            ok = (not pl.good) and pl.prime % 2 == 1 and pl.prime != ell and pl.ord_q_w % ell != 0 and not pl.small
            pl.in_Vbad = ok
            pl.rq = Fr(pl.ord_q_w, pl.e_base * 2 * ell) * self.scale_q if ok else Fr(0)   # ord_p(q̲̲)（q̲̲ = q^{1/2l}）
            pl.rho = log_shell_radius(pl.prime, pl.e) if pl.e else None                  # log-殻の半径（§4 で窓の計算と照合）
        self.bad = [pl for pl in self.places if pl.in_Vbad]
        if not self.bad:
            raise ValueError("𝕍_mod^bad が空")
        self.notes.append("分岐指数は e(F_mod,w/ℚ_q)·15ℓ/gcd(15ℓ, ord q)。p の上の素点では一覧の付録 A の証明で使う式で、一覧の表 1 を再現する（検算済み）。p 以外の悪い素点にも同じ式を当てはめた（仮定）")
        if self.unfactored:
            self.notes.append(f"N(a(1−a)) に分解していない因数が残る（{', '.join(str(len(str(c))) + ' 桁' for c in self.unfactored)}）。"
                              "その上の素点は 𝕍_mod^bad に入れず、容器も 0 以上として捨てる（下からの見積もり）")
        if name_cond := CONDITIONAL.get(self.name):
            self.notes.append(name_cond)

    def cofactor_container_bound(self):
        """分解できなかった因数 C の上の素点が容器に足す量の下限。C の素因数はどれも試し割りの範囲 B 以上なので、
        重複を込めた個数は Ω ≤ log C / log B。よって根基 rad(C) ≥ C^{1/Ω}。各素因数 w の上で 1 − a を割る素点が
        少なくとも一つあり（重み ≥ 1/2）、そこで ord q = 2k（k ≤ Ω）、e = 15ℓ/gcd(15ℓ, 2k) ≥ e_min、ρ = 1 − 1/e。
        IUT の容器は procession の平均で (ℓ+5)/4 倍される。"""
        tot = LogSum()
        for C in self.unfactored:
            logC = math.log(C)
            Omega = int(logC // math.log(self.factor_limit))
            emin = min(15 * self.ell // gcd(15 * self.ell, 2 * k) for k in range(1, Omega + 1))
            lower_log_rad = logC / Omega
            coef = Fr(self.ell + 5, 4) * Fr(1, 2) * (1 - Fr(1, emin))
            lo = Fr(math.floor(lower_log_rad * 10 ** 9) - 1, 10 ** 9)   # 切り捨てて有理数に（浮動小数の誤差を含めて下限のまま）
            tot = tot + LogSum({'num': coef * lo})
        return tot

    def _tate_q(self, pl):
        """悪い素点 w | p の Tate パラメータ q を p 進で：t = 1/j、q = t + 744t² + …"""
        p, K = self.p, self.padic_digits
        W = K + 40 + 4 * (abs(self.m) + abs(self.k))            # √D の窓：a の付値ぶんの桁を足す
        r = sqrt_mod_prime_power(self.D, p, W)
        if pl.name.endswith("₂"):
            r = (-r) % p ** W
        # π が w で消える方の埋め込みを ₁ にしてある（_places の順）。a, 1−a の p 進の値
        def emb(x):
            den = math.lcm(x.A.denominator, x.B.denominator)
            n = (int(x.A * den) + int(x.B * den) * r) % p ** W
            return Padic.of(p, K + 30, n) * Padic.of(p, K + 30, den).inv()
        a = emb(self.a)
        one = Padic(p, K + 30, 0, 1)
        num = (a * a - a) + one
        den = a * a * (a - one) * (a - one)
        j = Padic(p, K + 30, 0, 256) * num ** 3 * den.inv()
        assert -j.v == pl.ord_q_w, (j.v, pl.ord_q_w)
        t = j.inv()
        q, tk = t, t
        for n in range(2, len(Q_COEF)):
            tk = tk * t
            if tk.v - t.v > K:
                break
            q = q + Padic(p, K + 30, 0, Q_COEF[n]) * tk
        return Padic(p, K, q.v, q.u)

    # ---- 定義3.1 の条件のうち、計算で確かめられるもの
    def checks(self):
        out = []
        out.append(("l は 5 以上の素数", sympy.isprime(self.ell) and self.ell >= 5))
        out.append(("𝕍_mod^bad は空でなく、剰余標数は奇数", bool(self.bad) and all(pl.prime % 2 for pl in self.bad)))
        out.append(("l は 𝕍_mod^bad の剰余標数と素", all(pl.prime != self.ell for pl in self.bad)))
        out.append(("l は q の位数と素", all(pl.ord_q_w % self.ell for pl in self.bad)))
        out.append(("𝕍_mod^bad の上で乗法的還元（ord j < 0）", all(pl.ord_q_w > 0 for pl in self.bad)))
        out.append(("q̲̲ = q^{1/2l} が K_v に入る（e·ord q/2l が整数）",
                    all((pl.e * pl.ord_q_w) % (pl.e_base * 2 * self.ell) == 0 for pl in self.bad)))
        return out

    def table1_check(self):
        """公開した一覧（版 1.0.0）の表 1：p の上の二つの素点の (e, ord_p(q̲̲))"""
        T1 = {"D211": [(1, Fr(0)), (105, Fr(29, 7))], "D109": [(1, Fr(0)), (105, Fr(29, 7))],
              "D2": [(105, Fr(1, 7)), (35, Fr(6, 7))], "D3": [(35, Fr(6, 7)), (7, Fr(30, 7))],
              "D18": [(1, Fr(0)), (35, Fr(18, 7))], "D15": [(1, Fr(0)), (7, Fr(15, 7))],
              "D2357": [(1, Fr(0)), (15 * 157, Fr(472, 157))]}
        mine = sorted((v.e, v.rq / self.scale_q) for v in self.places if v.prime == self.p)
        return mine == sorted(T1[self.name]), mine

    def s(self):
        """s = (1/l*) Σ_{j=1}^{l*} j² = l(l+1)/12（Θ-パイロットとq-パイロットの次数の比）"""
        ls = self.ell_star
        val = Fr(sum(j * j for j in range(1, ls + 1)), ls)
        assert val == Fr(self.ell * (self.ell + 1), 12)
        return val


def log_shell_radius(p, e):
    """log-殻 𝓘_v = (1/2p)·log(𝓞_v^×) の半径 ρ = −min{ord_p z : z ∈ 𝓘_v}（ord_p(p) = 1）。
    𝓞^× = μ × (1 + ϖ𝓞) で log(μ) = 0。log(1 + x) = Σ ±x^k/k の項の付値は ϖ 単位で k·ord_ϖ(x) − e·ord_p(k)。
    最小は ord_ϖ(x) = 1、k = p^s のときで、m* = min_{s ≥ 0} (p^s − s·e)（穏やか e ≤ p−2 なら s = 0 で m* = 1）。
    ρ = 1 + ord_p(2) − m*/e。窓の中の実際の級数計算（LogShell.verify）と照合する。"""
    best, s = 1, 1
    while p ** s - s * e < best or p ** s <= s * e + e:
        best = min(best, p ** s - s * e)
        s += 1
    return 1 + (1 if p == 2 else 0) - Fr(best, e)


def log_shell_inner(p, e):
    """log-殻の内側の半径の下限 ρ′：n > e/(p−1) なら log(1 + 𝔪^n) = 𝔪^n なので、n0 = ⌊e/(p−1)⌋ + 1 として
    (1/2p)·𝔪^{n0} ⊆ 𝓘_v、つまり ord_p ≥ −ρ′ の元はみな 𝓘_v に入る。ρ′ = 1 + ord_p(2) − n0/e。小さい素点では ρ′ = ρ"""
    n0 = e // (p - 1) + 1
    return 1 + (1 if p == 2 else 0) - Fr(n0, e)


def log_shell_ab(p, e):
    """IV 命題1.2(i) の定数の和 a + b（p^a·𝒪_v ⊆ log(𝒪_v^×) ⊆ p^{−b}·𝒪_v）。a = ⌈e/(p−2)⌉/e（p = 2 なら 2）、
    b = ⌊log_p(pe/(p−1))⌋ − 1/e。床は整数の比較で正確に取る。小さい素点（p 奇・e ≤ p−2）では 0"""
    a = Fr(2) if p == 2 else Fr(-(-e // (p - 2)), e)
    k = 0
    while p ** (k + 1) * (p - 1) <= p * e:
        k += 1
    return a + k - Fr(1, e)


def kappa_range(v, s):
    """κ_v(θ) = max{k ∈ ℤ : θ·𝓘_v ⊆ p^k·𝓘_v} の区間 (下端, 上端)（ord_p θ = s）。(Ind2) を格子の自己同型すべてにした
    模型で、θ·𝓘_v の GL(𝓘_v) 軌道が張る格子は p^κ·𝓘_v（[Gap] 補題4.1）。上端は ⌊s⌋（体積の比較、[Gap] 定理3.3）。
    下端は ⌊s − (a+b)⌋（IV 命題1.2(i)、[Gap] 定理3.3）と ⌊s − (ρ − ρ′)⌋（𝓘_v ⊆ {ord_p ≥ −ρ}、{ord_p ≥ −ρ′} ⊆ 𝓘_v）の
    大きい方。θ = 1 なら κ = 0。小さい素点（p 奇・e ≤ p−2）では 𝓘_v が 𝒪_v 加群なので κ = ⌊s⌋（両端が一致する）"""
    if s == 0:
        return 0, 0
    hi = math.floor(s)
    p, e = v.prime, v.e
    lo = max(math.floor(s - log_shell_ab(p, e)), math.floor(s - (v.rho - log_shell_inner(p, e))))
    if p != 2 and e <= p - 2:
        assert lo == hi, (v, s)
    return min(lo, hi), hi


# =====================================================================================================
# §3 ラベル（IUT I §4・§6）
# =====================================================================================================


class Labels:
    """𝔽_l、|𝔽_l| = 𝔽_l/{±1} = {0, 1, …, l*}、𝔽_l^⋇ = 𝔽_l^×/{±1} = {1, …, l*}。
    𝔽_l^{⋊±} = 𝔽_l ⋊ {±1} は |𝔽_l| に（加法的に）働き、0 を動かす。𝔽_l^⋇ は 𝔽_l^⋇ に（乗法的に）働き、0 を持たない。
    IUT はこの二つを別々の劇場（Θ^{±ell}-劇場と ΘNF-劇場）に置いて貼り合わせる（I §4–§6）。"""

    def __init__(self, ell):
        self.ell, self.ls = ell, (ell - 1) // 2

    def abs_label(self, t):
        t %= self.ell
        return min(t, self.ell - t)

    def plus_minus_group(self):          # 𝔽_l^{⋊±}：t ↦ ε·t + c
        return [(eps, c) for eps in (1, -1) for c in range(self.ell)]

    def star_group(self):                # 𝔽_l^⋇：|t| ↦ |λ·t|
        return list(range(1, self.ls + 1))

    def procession(self, j):
        """procession の j 番目の容器のラベル 𝕊^±_{j+1} = {0, 1, …, j}（III 系3.12 の証明 ℐ^ℚ(𝕊^±_{j+1}; …)）"""
        return list(range(0, j + 1))

    def report(self):
        l, ls = self.ell, self.ls
        G = self.plus_minus_group()
        orbit0 = {self.abs_label(eps * 0 + c) for eps, c in G}
        S = self.star_group()
        orb1 = {self.abs_label(lam * 1) for lam in S}
        print(f"  𝔽_{l}：{l} 元、|𝔽_{l}| = {{0, …, {ls}}}（{ls + 1} 元）、𝔽_{l}^⋇ = {{1, …, {ls}}}（{ls} 元）")
        def short(xs):
            xs = sorted(xs)
            return str(xs) if len(xs) <= 8 else f"[{xs[0]}, {xs[1]}, …, {xs[-1]}]（{len(xs)} 個）"
        print(f"  𝔽_{l}^{{⋊±}}（位数 {len(G)}）の作用で 0 の軌道 = {short(orbit0)} = |𝔽_l| 全体：0 を他のラベルと混ぜる（加法的）")
        print(f"  𝔽_{l}^⋇（位数 {len(S)}）の作用で 1 の軌道 = {short(orb1)}：0 は現れない（乗法的）")
        print(f"  記号 △ は「0」と「⟨𝔽_l^⋇⟩」を同一視したもの（III 系3.12・II 系4.10(i)）。q-パイロットはこのラベルを持つ")
        js = list(range(1, ls + 1)) if ls <= 5 else [1, 2, 3, ls]
        shown = ["{" + ",".join(map(str, self.procession(j))) + "}" if j <= 5 else "{0,…," + str(j) + "}" for j in js]
        print(f"  procession（j = 1, …, {ls} の容器のラベル）：" + " ⊂ ".join(shown[:3] + (["…"] if ls > 5 else []) + shown[3:]))


# =====================================================================================================
# §4 劇場（ホッジ劇場）：型で分けた体の写し
# =====================================================================================================


class Elem:
    """劇場 theater の体 K_v の元。ϖ_v を単位とする付値 val と、単数部分（p 進の窓、分からなければ None）。
    別の劇場の元とは演算できない（環構造が劇場ごとに別だから）。"""

    def __init__(self, theater, place, val, unit=None):
        self.theater, self.place, self.val, self.unit = theater, place, val, unit

    def __mul__(s, o):
        if s.theater is not o.theater:
            raise TypeError(f"劇場 {s.theater.label} と劇場 {o.theater.label} の元は掛けられない（環構造が別）")
        u = s.unit * o.unit if (s.unit and o.unit) else None
        return Elem(s.theater, s.place, s.val + o.val, u)

    def __pow__(s, n):
        return Elem(s.theater, s.place, s.val * n, s.unit ** n if s.unit else None)

    def ord_p(s):
        """ord_p（ord_p(p) = 1）"""
        return Fr(s.val, s.place.e)


class Lattice:
    """劇場 theater の K_v の中の格子 ϖ^a·𝓞_v（a は有理数でよい：実数化した値群）。正規化した log 体積は −(a/e)·log p"""

    def __init__(self, theater, place, a):
        self.theater, self.place, self.a = theater, place, Fr(a)

    def log_vol(self):
        return LogSum.log(self.place.prime, -self.a / self.place.e)


class Theater:
    """ホッジ劇場 (n, m)。自分の体の写し（各素点 v の K_v）と、その中で作られる対象を持つ"""

    def __init__(self, datum, label):
        self.datum, self.label = datum, label
        self.access = []                                  # この劇場の環が使われた記録（SHE の記録に使う）

    def touch(self, what):
        self.access.append(what)

    # q-パラメータ q_v、q̲̲_v = q_v^{1/2l}、テータ値 q̲̲_v^{j²}（I 定義3.1(b)、II 系3.5・III 定義3.8(i)）
    def q(self, v):
        self.touch(f"q_{v.name}")
        val = v.e * Fr(v.ord_q_w, v.e_base) * self.datum.scale_q
        assert val.denominator == 1
        return Elem(self, v, int(val), v.q)

    def qbar(self, v):
        self.touch(f"q̲̲_{v.name}")
        val = v.e * v.rq
        assert val.denominator == 1, "q^{1/2l} が K_v に入らない"
        return Elem(self, v, int(val), None)

    def q_pilot(self):
        """q-パイロット：{q̲̲_v}_{v ∈ 𝕍^bad}（ラベル △）"""
        return {v: self.qbar(v) for v in self.datum.bad}

    def theta_pilot(self):
        """Θ-パイロット：{q̲̲_v^{j²}}_{j = 1…l*, v ∈ 𝕍^bad}（テータ値。II §2–§4 の評価で得られる）"""
        return {(j, v): self.qbar(v) ** (j * j) for j in range(1, self.datum.ell_star + 1) for v in self.datum.bad}

    def degree(self, pilot):
        """大域的実数化 Frobenioid での次数（III 命題3.9(iii)：大域的算術次数は log 体積として解釈できる）。
        ラベルつきのもの（Θ-パイロット）は procession 正規化：ラベルについて平均"""
        tot = LogSum()
        labels = {k[0] for k in pilot if isinstance(k, tuple)}
        for key, x in pilot.items():
            v = key[1] if isinstance(key, tuple) else key
            tot = tot + LogSum.log(v.prime, v.weight * x.ord_p())
        return tot * (Fr(1, len(labels)) if labels else 1)

    def lattice(self, v, a):
        self.touch(f"𝓞_{v.name}")
        return Lattice(self, v, a)


class LogShell:
    """log-殻 𝓘_v = (1/2p)·log(𝓞_v^×)（III 定義1.1(i)）。単数だけから作られるので、Θ-リンクを渡る（§5）"""

    @staticmethod
    def verify(p, e, terms=None):
        """窓の中で、実際に log(1 + c·ϖ) を級数で計算し（ϖ^e = p の全分岐の模型）、ϖ 単位の付値を求める。
        単項式 c^k ϖ^k / k を ϖ^e = p で簡約して足すだけなので、e が大きくても正確に計算できる。"""
        if terms is None:                                 # 窓：付値が最小値＋e 以下の項をすべて含む長さ
            terms, s = e + 2, 1
            while p ** s <= 3 * e * s + 2 * e + 2:
                terms = max(terms, p ** s * (e // p ** s + 2) if p ** s <= 4 * e else p ** s + 1)
                s += 1
        # 係数は p 進の窓で持つ：全項に p^A を掛けて分母の p を払い、p^(A+M) を法とした整数で足す
        A = max(sympy.multiplicity(p, k) for k in range(1, terms + 1))
        M = A + 12
        mod = p ** M
        c = 3 if p == 2 else 2                            # c は単数
        coef = [0] * e                                    # ϖ^i（0 ≤ i < e）の係数 × p^A（mod p^M）
        ck = 1
        for k in range(1, terms + 1):
            ck = ck * c % mod
            vk = sympy.multiplicity(p, k)
            unit_k = k // p ** vk
            term = ck * pow(unit_k, -1, mod) * p ** (A - vk + k // e)
            coef[k % e] = (coef[k % e] + (term if k % 2 else -term)) % mod
        vals = [e * (sympy.multiplicity(p, x) - A) + i for i, x in enumerate(coef) if x % mod]
        return min(vals)


# =====================================================================================================
# §5 リンク
# =====================================================================================================


class ValuePart:
    """値群部分：大域的実数化 Frobenioid の、ラベルのない正の実数一つ（λ）。Θ-リンクの両端で同じオブジェクト。
    実現（どの劇場で何に当たるか）は劇場ごとに違い、その実現の大きさはそれぞれの劇場の物差しで測る。"""

    def __init__(self):
        self.realizations = {}


class Cable:
    """Θ-リンク（III 定義3.8(ii)）が渡すもの＝𝓕^{⊩▶×μ}-prime-strip。
      単数部分 𝓕^{⊢×μ}：各 v で 𝓞_v^×/μ。抽象的な群としては (p, e, f) だけで決まる（環構造を持たない）。
                       Aut(𝓕^{⊢×μ}) の不定性（(Ind1)(Ind2)）に服する
      値群部分 𝓕^{⊩▶}：大域的実数化 Frobenioid の対象（ValuePart）。不定性に服さない（剛的）
    系3.12 の証明 (i)：「この Θ-link の値群部分は、⁰,⁰HT の Θ-pilot 対象を、¹,⁰HT の q-pilot 対象へ写す」"""

    def __init__(self, units, value_part):
        self.units, self.value_part = units, value_part


def theta_link(dom, cod):
    """Θ-リンク dom = ⁰,⁰HT → cod = ¹,⁰HT。値を関数で写すのではなく、ケーブル（共有のオブジェクト）を作り、
    それを dom の Θ-パイロットと cod の q-パイロットの両方に結びつける（貼合せ）。"""
    units = {v: ("𝓞^×/μ", v.prime, v.e, v.f) for v in dom.datum.places if v.e}
    lam = ValuePart()
    lam.realizations[dom.label] = ("Θ-パイロット", dom.degree(dom.theta_pilot()))
    lam.realizations[cod.label] = ("q-パイロット", cod.degree(cod.q_pilot()))
    return Cable(units, lam)


def padic_log_unit(u, p, K):
    """𝓞^× ∋ u（u は p^K を法とする整数、p ∤ u）の p 進対数 log(u) = log(u^{p−1})/(p−1) を p^K を法として。
    返り値：(付値, p^K を法とした値)。w = u^{p−1} ≡ 1 (mod p)、log w = Σ (−1)^{k+1}(w−1)^k/k"""
    M = p ** (K + 2)
    w = pow(u, p - 1, M)
    x = (w - 1) % M
    s, xk = Fr(0), 1
    for k in range(1, 3 * K + 3):
        xk = xk * x % M
        s += Fr((-1) ** (k + 1) * xk, k)
    s /= (p - 1)
    num, den = s.numerator, s.denominator
    vden = sympy.multiplicity(p, den)
    den //= p ** vden
    val = (num * pow(den, -1, p ** (K + 2))) % p ** (K + 2)
    if val == 0:
        return None, 0
    v = sympy.multiplicity(p, val) - vden
    return v, val


def log_link_demo(datum, K=6):
    """log-リンク（III 定義1.1）：劇場 (n, m) の単数を p 進対数で加法群へ送り、それを劇場 (n, m+1) の体の元とみなす。
    悪い素点 v | p の q の単数部分 u について log(u) を窓の中で計算する。値は 𝓘_v（log-殻）に入る"""
    out = []
    for v in datum.bad:
        if v.q is None:
            continue
        val, x = padic_log_unit(v.q.u, datum.p, K)
        out.append((v, val, x))
    return out


def bsgs(w, zeta, n, p):
    """ζ^I = w（mod p）となる I（0 ≤ I < n）を小歩大歩で"""
    m = int(math.isqrt(n)) + 1
    table = {}
    x = 1
    for i in range(m):
        table.setdefault(x, i)
        x = x * zeta % p
    step = pow(pow(zeta, m, p), -1, p)
    y = w % p
    for k in range(m + 1):
        if y in table:
            return (k * m + table[y]) % n
        y = y * step % p
    raise ValueError("離散対数が見つからない")


def kummer_recover(datum, v, levels, rigid=True):
    """Kummer 理論（エタール側だけで q の付値を取り出す）。段 n（n | p−1）で、q_v^{j²}（テータ値）の Kummer 類 κ ∈ Hom(A, μ_n)
    の慣性方向の成分 I は、穏やかなヒルベルト記号 (·, g)_n で計算でき、I ≡ −ord(q^{j²}) (mod n)。類（群の準同型）を得たあとは
    環を使わず、I から付値を mod n で取り出し、段を増やして中国剰余で合わせる。窓 = 使う段の集まり。"""
    p = datum.p
    g = sympy.primitive_root(p)
    rows = []
    for j in range(1, datum.ell_star + 1):
        alpha = j * j * v.ord_q_w                           # 環の側の真の付値（比べるためだけに使う）
        r, M = 0, 1
        seq = []
        for n in levels:
            zeta = pow(g, (p - 1) // n, p)
            z = pow(pow(g, alpha, p), -1, p)                # (q^{j²}, g)_n の中身：g^{−α}（単数部分は効かない）
            w = pow(z, (p - 1) // n, p)
            I = bsgs(w, zeta, n, p)
            res = (-I) % n                                  # エタール側で読む付値 mod n
            gg = gcd(M, n)
            l = M // gg * n
            t = ((res - r) // gg * pow(M // gg, -1, n // gg)) % (n // gg) if n // gg > 1 else 0
            r, M = (r + M * t) % l, l
            seq.append((n, M, r))
        rows.append((j, alpha, seq))
    return rows


# =====================================================================================================
# §6 多放射的アルゴリズム（III 定理3.11、注意3.11.1）
# =====================================================================================================
# 注意3.11.1(v)（訳）：「入力データが、同型まで考えた一つの 𝓕^{⊩▶×μ}-prime-strip だけからなり、出力データが、…
#   入力データ prime-strip と連結／関係づけられたデータからなり、しかもその構成アルゴリズムが、Θ-link の定義域で Θ-pilot
#   対象を生じさせる算術的正則構造と、入力データ prime-strip を生じさせる算術的正則構造との双方について、同時に有効・
#   実行可能・良定義な語彙で表現できる、というアルゴリズムである。」
#
# エタール側のデータ（共有）：Θ-リンクの両側で同じ（副有限群は環構造を持たないので渡る）。ここから
#   ・各素点の (p, e, f)（単解析的な容器＝log-殻はこれだけで作れる）
#   ・テータ値の Kummer 類（[EtTh] の結論。注意3.11.1(iv) の「隠れた内部構造 HIS」）。このプログラムでは、
#     テータ値 q̲̲^{j²} の付値を、エタール側が与える量として渡す（分解する素数 p では §7 で Kummer 類から窓で取り出して見せる）


class Etale:
    """エタール側の共有データ（環を持たない）"""

    def __init__(self, datum):
        self.places = [v for v in datum.places]
        self.theta_valuation = {(j, v): j * j * v.rq for j in range(1, datum.ell_star + 1) for v in datum.bad}  # HIS
        self.ell_star = datum.ell_star


class Output:
    def __init__(self, possible, link, ring_label, detail=None):
        self.possible = possible            # 可能な log 体積の上限（LogSum）、または None（上限なし）
        self.link = link                    # IPL：入力ケーブルの値群部分への参照
        self.ring_label = ring_label
        self.detail = detail or {}


READINGS = {
    "V": "テータ値はラベル j にとどまる（段階 (v) の書き方、lana-agents/iut の「IV の読み」）",
    "L": "0 を固定するラベルの置換が、包を取る前に働く（一覧の (L)、短報の (R)）",
    "L0": "(L) に加えて 0 を動かす置換も許す＝カプセルのすべての位置（lana-agents/iut の「字義どおりの読み」）",
}

IND2 = {
    "units": "単数倍。可能な像の格子を動かさない（版 1.0.0 の模型。恒等写像だけの群と同じ包）",
    "lattice": "各因子の log-殻 𝓘 を保つ ℤ_p 線形な自己同型すべて（lana-agents/iut の tensorAut。IV 命題1.2 の ⊗𝓘 を保つ任意の自己同型でも同じ値）",
}


def placements(reading, j):
    """(Ind1)：エタール像の置換対称性。Θ-パイロットのラベル j の値が、容器のどの因子に乗りうるか。読みの分岐はここだけ"""
    if reading == "V":
        return [j]
    if reading == "L":
        return list(range(1, j + 1))
    if reading == "L0":
        return list(range(0, j + 1))
    raise ValueError(reading)


class IUTAlgorithm:
    """定理3.11 の多放射的構成アルゴリズムを、可能な像の log 体積の計算として実行する。
    入力：ケーブル、エタール側データ、それに一つの劇場の環（ring）。ring は容器を格子として実現するのにだけ使う。
    ind2 は不定性 (Ind2) の群の模型（IND2）：units（単数倍）か lattice（各因子の log-殻を保つ格子の自己同型すべて）。"""

    name = "IUT（定理3.11 の計算）"

    def __init__(self, reading="V", window_ind3=3, enumerate_limit=256, ind2="units"):
        assert ind2 in IND2, ind2
        self.reading = reading
        self.window_ind3 = window_ind3
        self.enumerate_limit = enumerate_limit
        self.ind2 = ind2

    def run(self, cable, etale, ring):
        ls = etale.ell_star
        by_prime = {}
        for v in etale.places:
            by_prime.setdefault(v.prime, []).append(v)
        total = LogSum()
        # theta_shift は −|log Θ| の下からの値に使う縮み（格子の模型では κ の上端で）、theta_shift_low は κ の下端での縮み。
        # 単数の模型では二つは等しい
        detail = {"container": LogSum(), "theta_shift": LogSum(), "theta_shift_low": LogSum(), "per_label": []}
        for j in range(1, ls + 1):
            labels = list(range(0, j + 1))                       # 𝕊^±_{j+1}
            cont_j, shift_j, low_j = LogSum(), LogSum(), LogSum()
            for p, vs in by_prime.items():
                if any(v.e is None for v in vs):
                    continue                                     # 2・3・5・ℓ の上：容器は 0 以上（捨てる）
                # テンソル packet ⊗_{t ∈ 𝕊} (⊕_{v|p} 𝓘_v) は、因子ごとに素点を選んだ組 T ごとの成分に分かれる。重み Π w_{v_t}
                cont, shift, low = self._packet(vs, labels, j, etale, ring)
                cont_j, shift_j, low_j = cont_j + cont, shift_j + shift, low_j + low
            arch = LogSum({'π': j + 1})                          # アルキメデス素点：IV 定理1.10 段階 (vii) の容器 π^{j+1}·B_I
            cont_j = cont_j + arch
            detail["per_label"].append((j, cont_j, shift_j))
            total = total + cont_j - shift_j
            detail["container"] = detail["container"] + cont_j
            detail["theta_shift"] = detail["theta_shift"] + shift_j
            detail["theta_shift_low"] = detail["theta_shift_low"] + low_j
        total = total * Fr(1, ls)                                 # procession 正規化（j について平均）
        for key in ("container", "theta_shift", "theta_shift_low"):
            detail[key] = detail[key] * Fr(1, ls)
        return Output(total, cable.value_part, ring.label, detail)

    def _kappa(self, etale, v, j):
        """因子 v に Θ-パイロットのラベル j の値 θ = q̲̲_v^{j²} が乗ったときの κ_v(θ) の区間（θ = 1 なら 0）"""
        return kappa_range(v, etale.theta_valuation.get((j, v), Fr(0)))

    def _packet(self, vs, labels, j, etale, ring):
        """一つの素数 p での、ラベル j の容器の包の体積と、Θ-パイロットによる縮み（可能な像の合併の包）。
        縮みは二つ返す（theta_shift と theta_shift_low に当たる。単数の模型では等しい）"""
        n = len(labels)
        P = placements(self.reading, j)
        if len(vs) ** n <= self.enumerate_limit:
            cont, shift, low = LogSum(), LogSum(), LogSum()
            for T in itertools.product(vs, repeat=n):            # 組 T = (v_0, …, v_j)
                w = Fr(1)
                for v in T:
                    w *= v.weight
                # 容器：⊗ 𝓘_{v_t} の包。成分の log 体積は Σ_t ρ(v_t)·log p（III 命題3.9(i)、IV 命題1.4(iii) の加法性）
                regions = [ring.lattice(v, -v.rho * v.e) for v in T]
                c = sum((L.log_vol() for L in regions), LogSum())
                if self.ind2 == "units":
                    # 可能な像：(Ind1) で値が因子 t に乗る × (Ind2) 単数倍（格子は変わらない）× (Ind3) 部分格子（包は変わらない）
                    images = []
                    for t in P:
                        s = etale.theta_valuation.get((j, T[t]), Fr(0))
                        for k in range(self.window_ind3 + 1):     # (Ind3) の窓：一段ずつ小さい格子も可能な像
                            images.append(s + Fr(k, T[t].e))
                    hi = lo = min(images)                         # 合併の包＝いちばん大きい格子（成分の中で格子は全順序）
                else:
                    # 可能な像：(Ind1) で値が因子 t に乗る × (Ind2) 因子ごとの GL(𝓘) × (Ind3) 部分格子。位置 t の像が張る格子は
                    # p^{κ_t}·(⊗𝓘)（[Gap] 補題4.3）、合併が張る格子は p^{min κ_t}·(⊗𝓘)。包は張る格子だけで決まり（補題4.2）、
                    # 部分格子は κ を下げないので包を変えない
                    ks = [self._kappa(etale, T[t], j) for t in P]
                    hi, lo = Fr(min(k[1] for k in ks)), Fr(min(k[0] for k in ks))
                cont = cont + c * w
                shift = shift + LogSum.log(vs[0].prime, hi) * w
                low = low + LogSum.log(vs[0].prime, lo) * w
            # 閉じた式と照合（窓を伸ばしても変わらない量）
            c2, s2, l2 = self._closed(vs, n, j, P, etale)
            assert c2.c == cont.c and s2.c == shift.c and l2.c == low.c, (c2, cont, s2, shift, l2, low)
            return cont, shift, low
        for v in vs:                                             # 組が多いときも、容器は環の中の格子として実現する
            ring.lattice(v, -v.rho * v.e)
        return self._closed(vs, n, j, P, etale)

    def _closed(self, vs, n, j, P, etale):
        """組の数が多いとき（ℓ が大きい）の閉じた式。重みは確率なので、容器は (j+1)·ρ̄、縮みは E[min_{t∈P} f(v_t)]。
        f は単数の模型では ord(θ_v)、格子の模型では κ_v(θ_v) の上端と下端"""
        p = vs[0].prime
        rho_bar = sum((v.weight * v.rho for v in vs), Fr(0))
        cont = LogSum.log(p, n * rho_bar)
        if self.ind2 == "units":
            f_hi = f_lo = {v: etale.theta_valuation.get((j, v), Fr(0)) for v in vs}
        else:
            ks = {v: self._kappa(etale, v, j) for v in vs}
            f_hi = {v: Fr(k[1]) for v, k in ks.items()}
            f_lo = {v: Fr(k[0]) for v, k in ks.items()}
        return cont, LogSum.log(p, self._emin(vs, f_hi, len(P))), LogSum.log(p, self._emin(vs, f_lo, len(P)))

    @staticmethod
    def _emin(vs, f, npos):
        """E[min_{npos 個の独立な選択} f(v)]（重み w_v で選ぶ）。値を並べて r_(1) ≤ r_(2) ≤ … とすると
        Σ_k (r_(k) − r_(k−1))·(重み ≥ r_(k) の和)^npos、r_(0) = 0。重みの和は 1 なので最初の項は r_(1)（負でもよい）"""
        vals = sorted((f[v], v.weight) for v in vs)
        Emin, prev = Fr(0), Fr(0)
        for idx, (r, _) in enumerate(vals):
            tail = sum(w for (rr, w) in vals[idx:])
            Emin += (r - prev) * tail ** npos
            prev = r
        return Emin


# =====================================================================================================
# §7 統合（III 系3.12 の証明 段階 (xi)）
# =====================================================================================================


def run_with_record(alg, cable, etale, ring, others):
    """アルゴリズムを ring の上で走らせ、どの劇場の環に触ったかを記録する（SHE の記録）"""
    for th in [ring] + others:
        th.access.clear()
    out = alg.run(cable, etale, ring)
    touched = {th.label: len(th.access) for th in [ring] + others}
    return out, touched


def integrate(datum, reading="V", verbose=True):
    pr = print if verbose else (lambda *a, **k: None)
    th00, th10 = Theater(datum, (0, 0)), Theater(datum, (1, 0))
    cable = theta_link(th00, th10)
    etale = Etale(datum)
    alg = IUTAlgorithm(reading)

    pr("\n[段階 (i)] Θ-リンク ⁰,⁰HT → ¹,⁰HT：ケーブルを作り、両端に結ぶ")
    for lab, (what, deg) in cable.value_part.realizations.items():
        pr(f"  値群部分 λ の実現：劇場 {lab} では {what}、その劇場の物差しでの次数 = {deg.value():.4f}  （{deg}）")
    dom_deg = cable.value_part.realizations[(0, 0)][1].value()
    cod_deg = cable.value_part.realizations[(1, 0)][1].value()
    pr(f"  同じ λ の大きさが、劇場 (0,0) と (1,0) の物差しで比 {dom_deg / cod_deg:.4f} 倍（= s = l(l+1)/12 = {datum.s()}）")
    try:
        th00.q(datum.bad[0]) * th10.q(datum.bad[0])
    except TypeError as ex:
        pr(f"  劇場をまたいだ演算：{ex}")

    pr("\n[段階 (ii)・(v)・(vi)] 単数は log-リンクで加法へ：log-殻（容器）は単数だけから作られる")
    for v, val, x in log_link_demo(datum):
        pr(f"  劇場 (0,0) の q_{v.name} の単数部分 u → log(u) は付値 {val}（p 進の下の桁 {[x // datum.p ** i % datum.p for i in range(1, 4)]}…）："
           f"劇場 (0,1) の加法群の元。log-殻 𝓘 = (1/2p)·log(𝓞^×) に入る")
    pr("  q 自身は単数でないので log-リンクを通らない。値群部分（q の冪）は Θ-リンクの λ で、単数部分は log-殻で、別々に運ばれる")

    pr("\n[段階 (ii)・(vi)] エタール側（群だけ）から Θ-パイロットの大きさを読む：Kummer 理論（窓 = 段 n の集まり）")
    vp = max((v for v in datum.bad if v.q is not None), key=lambda v: v.ord_q_w, default=None)
    if vp is not None:
        levels = [n for n in sorted(sympy.divisors(datum.p - 1)) if n > 1][:10]
        rows = kummer_recover(datum, vp, levels)
        fixed = 0
        for idx, (j, alpha, seq) in enumerate(rows):
            ok = seq[-1][2] == alpha and seq[-1][1] > alpha
            fixed += ok
            if idx < 3 or idx == len(rows) - 1:
                shown = "、".join(f"段{n}→{r} mod {M}" for n, M, r in seq[:5])
                pr(f"  ラベル {j}：テータ値 q_{vp.name}^{{{j * j}}} の Kummer 類から付値：{shown}… → {seq[-1][2]}"
                   f"（環の側の値 {alpha}：{'窓の中で確定' if ok else 'この窓ではまだ mod ' + str(seq[-1][1])}）")
            elif idx == 3:
                pr("  …")
        rest = "" if fixed == len(rows) else "。残りは段を剰余拡大へ伸ばすと決まる（法が値を超えるまで）"
        pr(f"  窓（段 {levels[0]}…{levels[-1]}、法 {rows[0][2][-1][1]}）の中で確定したラベル：{fixed}/{len(rows)}{rest}")
        pr("  （類を得たあとは群の言葉だけ。段を増やすと値が動かなくなる。これがアルゴリズムの「隠れた内部構造 HIS」の一部）")

    pr("\n[段階 (xi-b)] 多放射的アルゴリズムを走らせる（入力はケーブルとエタール側データだけ）")
    out1, touched1 = run_with_record(alg, cable, etale, th10, [th00])
    out0, touched0 = run_with_record(alg, cable, etale, th00, [th10])
    pr(f"  APT：同じ run() を劇場 (1,0) の環で → −|log Θ| = {out1.possible.value():.4f}、劇場 (0,0) の環で → {out0.possible.value():.4f}")
    assert out1.possible.c == out0.possible.c
    pr(f"       （値を写したのではなく同じコードを二つの環で実行した。容器が単数だけから作られるので結果が一致する）")
    pr(f"  SHE：(1,0) の環で走らせたとき触った環 = {touched1}（(0,0) には触っていない）")
    pr(f"  IPL：出力の link は入力ケーブルの値群部分そのもの：{out1.link is cable.value_part}")
    # 注意3.11.1(ii)：終域の q-パイロットを q^λ-パイロットに置き換えても理論は影響を受けない（入力についての関手性）
    lam = 2
    cable2 = Cable(cable.units, ValuePart())
    cable2.value_part.realizations = dict(cable.value_part.realizations)
    cable2.value_part.realizations[(1, 0)] = ("q^λ-パイロット（λ = 2）", th10.degree(th10.q_pilot()) * lam)
    out2, _ = run_with_record(alg, cable2, etale, th10, [th00])
    pr(f"  注意3.11.1(ii)：入力の q-パイロットを q^{lam}-パイロットに替えて同じ run() → −|log Θ| = {out2.possible.value():.4f}"
       f"（{'変わらない' if out2.possible.c == out1.possible.c else '変わった'}。出力は入力の値を読まない＝(xi-e) の「固定値に服してもなお実行可能」）")
    d = out1.detail
    pr(f"  内訳：容器（log-殻のテンソル packet の包、j について平均）= {d['container'].value():.4f}")
    pr(f"        Θ-パイロットによる縮み（可能な像の合併の包、読み {reading}）= {d['theta_shift'].value():.4f}")

    # (Ind2) の群を、各因子の log-殻を保つ ℤ_p 線形な自己同型すべて（lana-agents/iut の tensorAut）に替えた模型
    alg_l = IUTAlgorithm(reading, ind2="lattice")
    outl1, touchedl = run_with_record(alg_l, cable, etale, th10, [th00])
    outl0, _ = run_with_record(alg_l, cable, etale, th00, [th10])
    assert outl1.possible.c == outl0.possible.c
    dl = outl1.detail
    gap_lo = d["theta_shift"] - dl["theta_shift"]                # 差の下端（κ の上端で）
    gap_hi = d["theta_shift"] - dl["theta_shift_low"]            # 差の上端（κ の下端で）
    rng = lambda a, b: f"{a.value():.4f}" if a.c == b.c else f"{a.value():.4f} 〜 {b.value():.4f}"
    pr("\n[段階 (xi-b)、(Ind2) の群を替える] 各因子の log-殻 𝓘 を保つ ℤ_p 線形な自己同型すべて（lana-agents/iut の tensorAut）")
    pr("  位置 t の可能な像が張る格子は p^κ·(⊗𝓘)（κ = κ_v(θ) = max{k : θ𝓘_v ⊆ p^k𝓘_v}、[Gap] 補題4.1・4.3）。"
       "合併の包は p^{min κ}·包(⊗𝓘)")
    pr(f"  APT：同じ run() を劇場 (1,0) の環で → −|log Θ| ≥ {outl1.possible.value():.4f}、劇場 (0,0) の環で → {outl0.possible.value():.4f}"
       f"（SHE：触った環 {touchedl}）")
    pr(f"  縮み = {rng(dl['theta_shift_low'], dl['theta_shift'])}（小さい素点（p 奇・e ≤ p−2）では κ = ⌊ord θ⌋ で正確。"
       "そうでない素点では κ を ⌊ord θ − (a+b)⌋・⌊ord θ − (ρ − ρ′)⌋ と ⌊ord θ⌋ で挟む）")
    pr(f"  単数の模型との差 Δ_{reading} = {rng(gap_lo, gap_hi)}（縮みの差。lana-agents/iut の Gap.lean の (Ind2) の項の平均）")
    pr("  （原典の (Ind2) の群での包は、恒等写像だけの群（単数の模型と同じ包）と tensorAut（lana-agents/iut によれば原典の Ism の像を"
       "含む「意図的な拡大」）の間にある）")

    pr("\n[段階 (xi-d)〜(xi-f)] 二つの方法（Fig. 3.8「同語反復的に同値な二つの方法」）")
    wayA = -th10.degree(th10.q_pilot())
    wayB = out1.possible
    extra = datum.cofactor_container_bound()
    pr(f"  方法 A：(1,0) の q-パイロットを (1,0) の環で直接測る → −|log q| = {wayA.value():.4f}")
    pr(f"  方法 B：(0,0) の Θ-パイロットをアルゴリズム経由で (1,0) の環で測る → 可能な log 体積 ℝ_≤−|log Θ|、"
       f"−|log Θ| ≥ {wayB.value():.4f}")
    if extra.c:
        pr(f"          （分解していない因数の上の素点の寄与の下限 {extra.value():.4f} を足すと ≥ {(wayB + extra).value():.4f}）")
    pr(f"          容器のうち 2・3・5・ℓ の上の素点は F の構成に依るので 0 以上として捨てた。だから方法 B は下からの値")
    pr("  原典の推論 (xi-f)：入力 prime-strip は出力と IPL で結ばれ（値群部分は同じ λ）、出力は (1,0) の語彙だけで書ける（SHE）。")
    pr("                    ゆえに「出力の可能性の構成は、入力のパイロットの log 体積 −|log q| の構成でもある」⟹ −|log q| ∈ ℝ_≤−|log Θ|")
    lhs = wayA.value()
    rhs1, rhs2 = wayB.value(), (wayB + extra).value()
    if lhs <= rhs1:
        verdict = "成り立つ（分解済みの部分の容器だけで）"
    elif lhs <= rhs2:
        verdict = "成り立つ（分解していない因数の下限を足して）"
    else:
        verdict = f"この窓では決まらない（不足 {lhs - rhs2:.4f}）"
    pr(f"  計算した二つの数の比較：−|log q| = {lhs:.4f} と −|log Θ| ≥ {rhs2:.4f}：{verdict}")
    wayBl = outl1.possible
    rhs1l, rhs2l = wayBl.value(), (wayBl + extra).value()
    if lhs <= rhs1l:
        verdict_l = "成り立つ（分解済みの部分の容器だけで）"
    elif lhs <= rhs2l:
        verdict_l = "成り立つ（分解していない因数の下限を足して）"
    else:
        verdict_l = f"この窓では決まらない（不足 {lhs - rhs2l:.4f}）"
    pr(f"  (Ind2) を格子の模型にしたとき：−|log Θ| ≥ {rhs2l:.4f}：{verdict_l}（縮みが小さくなるので、成り立つのは単数の模型で成り立つときを含む）")
    if lhs > rhs2 and datum.unfactored:
        need = lhs - rhs1                                  # 分解していない因数の素点が埋めるべき量
        coef = Fr(datum.ell + 5, 4) * Fr(1, 2) * Fr(14, 15)
        need_lograd = need / float(coef)
        logC = sum(math.log(C) for C in datum.unfactored)
        pr(f"  外挿の手がかり：分解していない因数 C（10^{logC / math.log(10):.0f}）の根基が 10^{need_lograd / math.log(10):.0f} 以上なら埋まる"
           f"（素因数がすべて 10^6 以上で、C は素数の冪でない。重複が少なければ根基 ≈ C）")
    s = datum.s()
    absq = th10.degree(th10.q_pilot())
    V = d["container"]
    shift_over_q = d["theta_shift"].value() / absq.value()
    pr(f"  この比較は  (縮み − |log q|) ≤ 容器  と同じ。縮み = {shift_over_q:.4f}·|log q|（読み (V) なら s·|log q|、s = {s}）")
    if reading == "V":
        lhsV, rhsV = ((s - 1) * absq).value(), (V + extra).value()
        pr(f"  読み (V) では比較は (s−1)·|log q| ≤ 容器 と同じ：{lhsV:.4f} {'≤' if lhsV <= rhsV else '>'} {rhsV:.4f}（容器は下からの値）。"
           "lana-agents/iut の SSIneq の形。IV 定理1.10 の証明は容器を log-different などでさらに上から見積もり、高さの不等式を得る")
        pr(f"  格子の模型では比較は (s−1)·|log q| ≤ 容器 + Δ_V と同じ（lana-agents/iut の変種 (Var) の形）。Δ_V = {rng(gap_lo, gap_hi)} は"
           " [Gap] の Δ(D)。二つの壁の差は Δ_V だけで、その上界は q の位数の大きさを含まない（[Gap] 系3.5）")
    return dict(wayA=lhs, wayB=rhs2, verdict=verdict, V=(V + extra).value(), absq=absq.value(), s=float(s),
                shift=d["theta_shift"].value(),
                exact=dict(absq=ls_json(absq), container=ls_json(V), shift=ls_json(d["theta_shift"]), extra=ls_json(extra),
                           wayB_lower=ls_json(wayB)),
                apt=[out1.possible.value(), out0.possible.value(), out1.possible.c == out0.possible.c],
                she={str(k): n for k, n in touched1.items()}, ipl=out1.link is cable.value_part,
                q2_same=out2.possible.c == out1.possible.c,
                lattice=dict(wayB=rhs2l, verdict=verdict_l,
                             shift=[dl["theta_shift_low"].value(), dl["theta_shift"].value()],
                             gap=[gap_lo.value(), gap_hi.value()], gap_exact=gap_lo.c == gap_hi.c,
                             exact=dict(shift_low=ls_json(dl["theta_shift_low"]), shift_high=ls_json(dl["theta_shift"]),
                                        wayB_lower=ls_json(wayBl)),
                             apt=[outl1.possible.value(), outl0.possible.value(), outl1.possible.c == outl0.possible.c]))


# =====================================================================================================
# §8 注意3.11.1 (vi)–(viii) の玩具を同じ枠で走らせる
# =====================================================================================================


class NaiveLink:
    """(vi)：一つの環 R の中で q ↦ q^λ。「q の λ 乗をとる」は両方の環構造で実行可能（SHE は同語反復的に成立）。
    しかし固定容器 R の中では q と q^λ のいかなる同一視も誘導しない（IPL の類似物がない）"""
    name = "素朴な Θ-リンク q ↦ q^λ"

    def __init__(self, lam=2):
        self.lam = lam

    def run(self, cable, etale, ring):
        v = ring.datum.bad[0]
        x = ring.qbar(v) ** self.lam
        return Output(LogSum.log(v.prime, -v.weight * x.ord_p()), None, ring.label, {})


class DistinctLabels:
    """(vii) 前半：二つの環に異なるラベル †、‡ を付ける。* ↦ ‡q^λ と * ↦ †q を同時に考えられる（IPL は成立）。
    しかし †R の構造から ‡R の量を計算する語彙がない（SHE が分からない）"""
    name = "異なるラベル（†R と ‡R）"

    def __init__(self, lam=2):
        self.lam = lam

    def run(self, cable, etale, ring):
        other = Theater(ring.datum, ("‡",))
        v = ring.datum.bad[0]
        x = other.qbar(v) ** self.lam * ring.qbar(v)          # ‡q^λ を †R の語彙で書こうとする → TypeError
        return Output(None, cable.value_part, ring.label, {})


class ForcedIdentification:
    """(vii) 後半：† と ‡ を強制的に同一視する。q は q^{λⁿ}（n ∈ ℤ）との混同までしか定まらない＝自明な多放射表現。
    (viii)：値群部分に不定性を許すので log 体積の評価には役に立たない。窓 |n| ≤ W で計算し、W を伸ばす"""
    name = "強制的同一視（自明な多放射表現 {q^{λⁿ}}）"

    def __init__(self, lam=2, W=6):
        self.lam, self.W = lam, W

    def run(self, cable, etale, ring):
        v = ring.datum.bad[0]
        base = Fr(v.weight) * v.rq
        vols = [-base * Fr(self.lam) ** n for n in range(-self.W, self.W + 1)]
        return Output(LogSum.log(v.prime, max(vols)), cable.value_part, ring.label, {"W": self.W})


def toys(datum):
    print("\n==== 注意3.11.1 (vi)–(viii) の玩具を同じ枠で ====")
    th10 = Theater(datum, (1, 0))
    th00 = Theater(datum, (0, 0))
    cable = theta_link(th00, th10)
    etale = Etale(datum)
    for alg in [NaiveLink(), DistinctLabels(), ForcedIdentification(W=2), ForcedIdentification(W=6),
                ForcedIdentification(W=12), IUTAlgorithm("V")]:
        try:
            out, touched = run_with_record(alg, cable, etale, th10, [th00])
            ipl = "あり" if out.link is cable.value_part else "なし"
            vol = "上限なし" if out.possible is None else f"{out.possible.value():.6f}"
            extra = f"（窓 W = {out.detail['W']}）" if "W" in out.detail else ""
            print(f"  {alg.name}{extra}：実行できた、IPL のリンク {ipl}、可能な log 体積の上限 {vol}")
        except TypeError as ex:
            print(f"  {alg.name}：実行できない（{ex}）")
    print("  強制的同一視では W を伸ばすと上限が 0 に近づく：値群が不定なので体積が何も言わない（(viii) の「役に立たない」）")


# =====================================================================================================
# 出力
# =====================================================================================================


def show_datum(dt):
    print(f"\n==================== 初期Θデータ {dt.name}：F_mod = ℚ(√{dt.D})、p = {dt.p}、l = {dt.ell} ====================")
    for n in dt.notes:
        print("  注：" + n)
    print("[§2 初期Θデータ（I 定義3.1）] a, 1 − a を割る素点（2 は除く）。𝕍^bad は、分解できた乗法的還元の素点のうち 2・3・5・ℓ の外のもの全部"
          "（一覧の 𝕍^bad は 3・5 の上も含む。ここでは K の分岐が F の構成に依る 3・5 の上を外した部分集合を取る）")
    for v in dt.places:
        mark = "𝕍^bad" if v.in_Vbad else ("良い還元" if v.good else "容器のみ")
        e = v.e if v.e else "?"
        rho = f"{v.rho}" if v.rho is not None else "?（0 以上として捨てる）"
        qinfo = ""
        if v.q is not None:
            qinfo = f"、q の p 進の桁 {v.q.digits(5)}…（付値 {v.q.v}）"
        print(f"  {v.name:>8}（{v.kind}）ord(q) = {v.ord_q_w}、e = {e}、log-殻の半径 ρ = {rho}、ord_p(q̲̲) = {v.rq} [{mark}]{qinfo}")
    ok1, mine = dt.table1_check()
    shown = "、".join(f"(e = {e}, {r})" for e, r in mine)
    print(f"  公開した一覧の表 1 と照合（p の上の (e, ord_p q̲̲)）：{shown}：{'一致' if ok1 else '不一致'}")
    for text, ok in dt.checks():
        print(f"  定義3.1 の条件：{text}：{'✓' if ok else '✗'}")
    print("[§4 log-殻] 半径を窓の中の級数計算で確かめる（log(1 + 2ϖ) の ϖ 進の付値。ϖ^e = p の模型）")
    seen = set()
    for v in dt.places:
        if v.e and (v.prime, v.e) not in seen:
            seen.add((v.prime, v.e))
            m = LogShell.verify(v.prime, v.e)
            rho_series = 1 + (1 if v.prime == 2 else 0) - Fr(m, v.e)
            tame = "穏やか e ≤ p−2" if v.e <= v.prime - 2 else "e > p−2"
            print(f"  p = {v.prime}、e = {v.e}（{tame}）：級数の付値 {m} → ρ = {rho_series}（式と {'一致' if rho_series == v.rho else '不一致'}）")
    print("[§3 ラベル]")
    Labels(dt.ell).report()


def ls_json(x):
    """LogSum を JSON に：{素数（文字列） or 'π' or 'num': 'a/b'}"""
    return {str(k): str(v) for k, v in x.c.items()}


def export_json(path):
    """ページの二つ目のタブに埋め込むデータ。重い計算（p 進の q、級数、Kummer、素因数分解）の結果と、
    読みごとの Python の計算結果（ページの JavaScript が計算し直して一致を確かめる）"""
    import json
    import datetime
    WIN = [("w0", "試し割り 10⁴ まで（楕円曲線法なし）", dict(factor_limit=10 ** 4, factor_seconds=0, use_known=False)),
           ("w1", "試し割り 10⁶ ＋ 楕円曲線法 1 秒", dict(factor_limit=10 ** 6, factor_seconds=1, use_known=False)),
           ("w2", "＋ 既知の分解（窓の外から）", dict(factor_limit=10 ** 6, factor_seconds=1, use_known=True))]
    out = {"generated": datetime.date.today().isoformat(), "windows": [[k, lab] for k, lab, _ in WIN], "data": {}}
    for name in DATA:
        D, x, y, m, k, ell = DATA[name]
        rec = {"D": D, "pi": [x, y], "m": m, "k": k, "ell": ell, "conditional": CONDITIONAL.get(name), "variants": {}}
        for wk, _, kw in WIN:
            dt = InitialThetaData(name, padic_digits=16, **kw)
            places = []
            for v in dt.places:
                places.append(dict(name=v.name, prime=str(v.prime), kind=v.kind, weight=str(v.weight), f=v.f, e=v.e,
                                   rho=None if v.rho is None else str(v.rho), rq=str(v.rq), ord_q=v.ord_q_w, ord_a=v.ord_a,
                                   ord_1ma=v.ord_1ma, bad=v.in_Vbad, good=v.good, small=v.small,
                                   q_digits=v.q.digits(16) if v.q is not None else None, q_val=v.q.v if v.q is not None else None))
            ok1, mine = dt.table1_check()
            var = dict(places=places, unfactored=[len(str(C)) for C in dt.unfactored], notes=dt.notes,
                       cofactor=ls_json(dt.cofactor_container_bound()), checks=[[t, bool(o)] for t, o in dt.checks()],
                       table1=[ok1, [[e, str(r)] for e, r in mine]], results={})
            for rd in READINGS:
                var["results"][rd] = integrate(dt, rd, verbose=False)
            rec["variants"][wk] = var
            if wk == "w2":
                rec["p"] = str(dt.p)
                rec["s"] = str(dt.s())
                seen, shells = set(), []
                for v in dt.places:
                    if v.e and (v.prime, v.e) not in seen:
                        seen.add((v.prime, v.e))
                        mm = LogShell.verify(v.prime, v.e)
                        rs = 1 + (1 if v.prime == 2 else 0) - Fr(mm, v.e)
                        shells.append(dict(prime=str(v.prime), e=v.e, series_val=mm, rho=str(rs), match=rs == v.rho))
                rec["shells"] = shells
                rec["loglink"] = [dict(place=v.name, val=val, digits=[x // dt.p ** i % dt.p for i in range(1, 4)])
                                  for v, val, x in log_link_demo(dt)]
                vp = max((v for v in dt.bad if v.q is not None), key=lambda v: v.ord_q_w, default=None)
                if vp is not None:
                    divs = [n for n in sorted(sympy.divisors(dt.p - 1)) if n > 1][:16]
                    rows = kummer_recover(dt, vp, divs)
                    rec["kummer"] = dict(place=vp.name, ord_q=vp.ord_q_w, levels=divs,
                                         rows=[dict(j=j, alpha=a, seq=[[n, M, r] for n, M, r in seq]) for j, a, seq in rows])
        out["data"][name] = rec
        print("exported", name, file=sys.stderr)
    with open(path, "w") as f:
        json.dump(out, f, ensure_ascii=False, separators=(",", ":"))


def windows(name, reading):
    """窓を伸ばしたときの列。人はこれを見て外挿する"""
    print(f"\n==================== 窓を伸ばす：{name}、読み {reading} ====================")
    print("[1] p 進の桁数 K を伸ばす：q の下の桁は変わらず、上の桁が足されていく")
    for K in (2, 4, 8, 16):
        dt = InitialThetaData(name, padic_digits=K, factor_seconds=1)
        for v in dt.places:
            if v.q is not None:
                print(f"  K = {K:2d}：q_{v.name} の単数部分の桁 {v.q.digits(K)}")
    print("[2] 大域の窓（N(1 − a) の分解の範囲）を伸ばす：𝕍^bad と容器が増え、比較の結果が決まっていく")
    for label, kw in (("試し割り 10^4、楕円曲線法なし", dict(factor_limit=10 ** 4, factor_seconds=0, use_known=False)),
                      ("試し割り 10^6、楕円曲線法 1 秒", dict(factor_limit=10 ** 6, factor_seconds=1, use_known=False)),
                      ("＋ 既知の分解（窓の外から）", dict(factor_limit=10 ** 6, factor_seconds=1, use_known=True))):
        dt = InitialThetaData(name, **kw)
        r = integrate(dt, reading, verbose=False)
        un = "、".join(f"{len(str(C))} 桁" for C in dt.unfactored) or "なし"
        print(f"  {label}：𝕍^bad の素数 {sorted({v.prime for v in dt.bad})[:6]}{'…' if len({v.prime for v in dt.bad}) > 6 else ''}、"
              f"残り {un}、|log q| = {r['absq']:.3f}、容器 ≥ {r['V']:.3f} → {r['verdict']}")
    dt = InitialThetaData(name, factor_seconds=1)
    print("[3] Kummer の段を増やす：テータ値の付値が確定するラベルの数")
    vp = max((v for v in dt.bad if v.q is not None), key=lambda v: v.ord_q_w, default=None)
    if vp is not None:
        divs = [n for n in sorted(sympy.divisors(dt.p - 1)) if n > 1]
        for cnt in (1, 2, 4, 8, len(divs)):
            rows = kummer_recover(dt, vp, divs[:cnt])
            fixed = sum(1 for j, a, seq in rows if seq[-1][2] == a and seq[-1][1] > a)
            print(f"  段 {cnt} 個（法 {rows[0][2][-1][1]}）：確定 {fixed}/{len(rows)}")
    print("[4] (Ind3) の窓（部分格子をいくつ可能な像に入れるか）を伸ばす：包の体積は変わらない")
    th00, th10 = Theater(dt, (0, 0)), Theater(dt, (1, 0))
    cable, et = theta_link(th00, th10), Etale(dt)
    for W in (0, 1, 3, 6):
        out = IUTAlgorithm(reading, window_ind3=W).run(cable, et, th10)
        print(f"  W = {W}：−|log Θ| ≥ {out.possible.value():.6f}")
    print("[5] 仮に q の位数だけを c 倍したら（全称命題の一例を手で入れる。容器は同じ）")
    base = integrate(InitialThetaData(name, factor_seconds=1), reading, verbose=False)
    for c in (1, 2, 3, 4, 6, 8):
        r = integrate(InitialThetaData(name, factor_seconds=1, scale_q=c), reading, verbose=False)
        print(f"  c = {c}：−|log q| = {r['wayA']:.3f}、−|log Θ| ≥ {r['wayB']:.3f} → {r['verdict']}")
    if base["shift"] > base["absq"]:
        cstar = base["V"] / (base["shift"] - base["absq"])
        print(f"  この容器の見積もりで比較が成り立つのは c ≤ {cstar:.3f} まで（容器 ÷ (縮み − |log q|)。容器は下からの値なので本当の境はこれ以上）")
        print("  （q だけを動かすのは実在のデータではなく仮の入力）")
    print("[6] log(1 + 2ϖ) の級数の項数 N を伸ばす：部分和の付値が m* で止まる（ϖ^e = p の模型）")
    cand = [v for v in dt.bad if v.e and v.e > v.prime - 2]
    v6 = max(cand, key=lambda v: v.e - v.prime, default=None) or next((v for v in dt.bad if v.e), None)
    if v6 is not None:
        p6, e6 = v6.prime, v6.e
        for N in sorted({n for n in (p6 - 1, p6, p6 ** 2) if 1 <= n <= 20000}):
            print(f"  {v6.name}（p = {p6}、e = {e6}）、項数 N = {N}：部分和の付値 {LogShell.verify(p6, e6, terms=N)}")
        ms = min(p6 ** s - s * e6 for s in range(0, 8))
        print(f"  項数を自動で決めた窓：付値 {LogShell.verify(p6, e6)}（式の m* = {ms}）")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", default="D2", choices=list(DATA))
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--reading", default="V", choices=list(READINGS))
    ap.add_argument("--scale-q", default="1", help="仮に q の位数だけを何倍かにする（全称命題の一例を手で入れる）")
    ap.add_argument("--toys", action="store_true")
    ap.add_argument("--windows", action="store_true")
    ap.add_argument("--factor-seconds", type=float, default=5)
    ap.add_argument("--export-json", help="ページに埋め込むデータを書き出す")
    args = ap.parse_args()
    if args.export_json:
        export_json(args.export_json)
        return
    names = list(DATA) if args.all else [args.data]
    print(f"読み：{args.reading} ＝ {READINGS[args.reading]}")
    for nm in names:
        if args.windows:
            windows(nm, args.reading)
            continue
        dt = InitialThetaData(nm, scale_q=Fr(args.scale_q), factor_seconds=args.factor_seconds)
        show_datum(dt)
        integrate(dt, args.reading)
        if args.toys:
            toys(dt)


if __name__ == "__main__":
    main()
