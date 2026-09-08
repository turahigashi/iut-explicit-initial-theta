#!/usr/bin/env python3
"""Exact coefficient comparisons for the fifth report (standard library only).

The checks concern rational identities, inequalities and the printed tables.
They do not certify source interpretations, initial-data admissibility, or a
possible-image hull.  Run from any directory; no input file is modified.
"""

from fractions import Fraction as F
from pathlib import Path
import sys


class CheckFailure(Exception):
    pass


def require(condition, message):
    if not condition:
        raise CheckFailure(message)


def is_prime(n):
    return n >= 2 and all(n % k for k in range(2, integer_sqrt(n) + 1))


def integer_sqrt(n):
    lo, hi = 0, n + 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid * mid <= n:
            lo = mid
        else:
            hi = mid
    return lo


def coefficients(ell):
    require(type(ell) is int, "ell must be an integer")
    require(ell >= 5 and ell % 2 == 1, "algebraic range: odd ell >= 5")
    m = (ell - 1) // 2
    r = F(1, 2 * ell)
    c = sum((F(j, m) for j in range(1, m + 1)), F(0))
    b = sum((F(j * j, 2 * ell * m) for j in range(1, m + 1)), F(0))
    chi = r / b
    tau = F(12, ell * ell)
    A = b / r
    u = b * tau
    epsilon = u - r
    f_chi = 1 / (1 - chi)
    f_tau = 1 / (1 - tau)
    require(c == F(ell + 1, 4), "first-moment coefficient")
    require(b == F(ell + 1, 24), "second-moment coefficient")
    require(b == c / 6, "origin of the factor 1/6")
    require(chi == F(12, ell * (ell + 1)), "exact threshold chi")
    require(A == F(ell * (ell + 1), 12), "reciprocal coefficient")
    require(0 < chi < tau < 1, "positive reciprocal denominators")
    require(tau / chi == F(ell + 1, ell), "relative coefficient change")
    require(tau - chi == F(12, ell * ell * (ell + 1)), "absolute coefficient change")
    require(u == F(ell + 1, 2 * ell * ell), "IV cancellation allowance")
    require(epsilon == F(1, 2 * ell * ell), "raw kernel slack")
    require(epsilon / r == F(1, ell), "normalized kernel slack")
    require(f_tau - f_chi == F(12 * ell, (ell * ell - 12) * (ell * (ell + 1) - 12)),
            "reciprocal-factor absolute difference")
    require(f_tau / f_chi - 1 == F(12, (ell + 1) * (ell * ell - 12)),
            "reciprocal-factor relative difference")
    require(f_chi < f_tau, "direction of same-input bound comparison")
    return dict(ell=ell, m=m, r=r, c=c, b=b, chi=chi, tau=tau, A=A,
                u=u, epsilon=epsilon, f_chi=f_chi, f_tau=f_tau)


def kernel(row, t, H, D):
    return row["c"] * (D - (1 - t) * H / 6) - row["r"] * H


def terminal_bounds(row, d):
    return (row["f_tau"], F(2),
            row["f_tau"] * (1 + F(12 * d, row["ell"])),
            1 + F(20 * d, row["ell"]))


def tex(q):
    q = F(q)
    if q.denominator == 1:
        return str(q.numerator)
    return r"\frac{" + str(q.numerator) + "}{" + str(q.denominator) + "}"


def tex_row(values):
    return " & ".join("$" + tex(v) + "$" for v in values) + r" \\"


def expected_tables(rows):
    coefficients_rows, factors_rows, data_rows = [], [], []
    for row in rows:
        coefficients_rows.append(tex_row([row[k] for k in
            ("ell", "chi", "tau", "A", "r", "u", "epsilon")]))
        factors_rows.append(tex_row([row["ell"], row["f_chi"], row["f_tau"],
            row["f_tau"] - row["f_chi"], row["f_tau"] / row["f_chi"] - 1]))
    # The two rows have different quadratic fields.  The first uses
    # 16+3*sqrt(5), N=29, p=211; the second uses 41+26*i, N=472, p=2357.
    models = ((7, 211, 29, 5, 16, 3), (157, 2357, 472, -1, 41, 26))
    require(len(rows) == len(models), "one row for each specified curve and level")
    for row, (ell, p, N, d, x, y) in zip(rows, models):
        require(row["ell"] == ell, "curve/level correspondence")
        require(is_prime(p) and p > 2, "designated odd prime")
        require(x * x - d * y * y == p, "quadratic norm of the designated element")
        require(y % p != 0, "invertible coefficient at the designated prime")
        root = (-x * pow(y, -1, p)) % p
        require(root * root % p == d % p and 2 * root % p != 0,
                "two distinct roots in the correct quadratic field")
        data_rows.append(tex_row([row["ell"], p, N, N * row["r"],
            N * row["b"], N * row["u"], N * row["epsilon"]]))
    return {"coefficients": coefficients_rows, "factors": factors_rows, "data": data_rows}


def check_printed_tables(path, tables):
    require(path.is_file(), "the report TeX file is missing")
    text = path.read_text(encoding="utf-8")
    for name, expected in tables.items():
        begin = "% BEGIN EXACT TABLE " + name
        end = "% END EXACT TABLE " + name
        require(text.count(begin) == 1 and text.count(end) == 1,
                "unique table delimiters: " + name)
        region = text.split(begin, 1)[1].split(end, 1)[0].strip()
        require(region == "\n".join(expected), "printed table differs: " + name)


def run():
    if not __debug__:
        raise CheckFailure("run without -O or -OO")
    require(len(sys.argv) == 1, "no command-line arguments are accepted")
    for n in range(65):
        expected_root = max(k for k in range(n + 1) if k * k <= n)
        expected_prime = n > 1 and sum(n % k == 0 for k in range(1, n + 1)) == 2
        require(integer_sqrt(n) == expected_root, "integer square-root check")
        require(is_prime(n) == expected_prime, "primality check")
    # Direct finite sums are compared with the closed formula at every odd
    # level in this finite range, including algebraic level 5.  This is not
    # a claim that all these levels satisfy the source's initial-data axioms.
    for ell in range(5, 202, 2):
        row = coefficients(ell)
        for H in (F(1), F(29), F(472), F(17, 3)):
            for D in (F(0), F(1), F(5, 7)):
                exact = row["c"] * D - row["b"] * H
                require(kernel(row, row["chi"], H, D) == exact,
                        "exact cancellation identity")
                require(kernel(row, row["tau"], H, D) - exact == H / (2 * ell * ell),
                        "looser kernel has the stated positive slack")
                require((kernel(row, row["tau"], H, D) - exact) / (row["r"] * H)
                        == F(1, ell), "C-normalized slack")
                for R in (F(0), F(2, 5)):
                    left = -row["r"] * H <= row["c"] * (D - H / 6) + R
                    right = H / 6 <= row["f_chi"] * (D + R / row["c"])
                    require(left == right, "same-input rearrangement with explicit error")
                    require(row["f_chi"] * (D + R / row["c"])
                            <= row["f_tau"] * (D + R / row["c"]),
                            "nonnegative-input upper-bound direction")

    require(F(12, 3 * 4) == 1, "ell=3 is the singular chi boundary")
    boundary_tau = F(12, 3 * 3)
    require(boundary_tau == F(4, 3) and boundary_tau > 1,
            "ell=3 is outside the tau-positive range")
    for ell in (7, 157):
        require(is_prime(ell) and ell >= 7, "displayed prime range")
        row = coefficients(ell)
        for d in (1, 2, 7):
            lhs1, rhs1, lhs2, rhs2 = terminal_bounds(row, d)
            require(lhs1 <= rhs1, "IV terminal estimate, first inequality")
            require(lhs2 <= rhs2,
                    "IV terminal estimate, second inequality")
    row5 = coefficients(5)
    at5 = terminal_bounds(row5, 1)
    require(at5 == (F(25, 13), F(2), F(85, 13), F(5)),
            "ell=5 terminal expressions, including the printed 85/13 > 5")
    require(terminal_bounds(coefficients(7), 1) == (F(49, 37), F(2), F(133, 37), F(27, 7)),
            "ell=7 terminal expressions")
    require(at5[2] > at5[3],
            "ell=5 must not be used for IV's terminal estimate")

    rows = [coefficients(7), coefficients(157)]
    # Independent fixed anchors prevent a consistently altered numerator or
    # reporting convention from silently changing the two published examples.
    require((rows[0]["chi"], rows[0]["A"], rows[0]["epsilon"])
            == (F(3, 14), F(14, 3), F(1, 98)), "ell=7 anchors")
    require((rows[1]["chi"], rows[1]["A"], rows[1]["epsilon"])
            == (F(6, 12403), F(12403, 6), F(1, 49298)), "ell=157 anchors")
    require(rows[1]["f_tau"] - rows[1]["f_chi"] == F(942, 305424889),
            "ell=157 reciprocal difference anchor")
    tables = expected_tables(rows)
    paper = Path(__file__).resolve().parents[1] / "paper" / "constant_comparison.tex"
    check_printed_tables(paper, tables)
    output = ["Exact rational coefficient comparison; source applicability is not certified."]
    for name, lines in tables.items():
        output.append("TABLE: " + name)
        output.extend(lines)
    output.append("Checked: 99 odd algebraic levels, 2 displayed prime levels, 6 printed rows.")
    output.append("Checked: kernel slack, reciprocal differences, signs, range and table synchronization.")
    output.extend(["RESULT: PASS", "EXIT:0"])
    rendered = "\n".join(output) + "\n"
    frozen = Path(__file__).with_name("constant_comparison_output.txt")
    require(frozen.is_file(), "the frozen output file is missing")
    require(frozen.read_text(encoding="utf-8") == rendered,
            "frozen output differs from the computed output")
    print(rendered, end="")


if __name__ == "__main__":
    try:
        run()
    except (CheckFailure, OSError, ValueError, ZeroDivisionError) as exc:
        print("RESULT: FAIL")
        print("Reason: " + str(exc))
        print("EXIT:1")
        sys.exit(1)
