# An explicit initial Θ-datum with mixed reduction over a split prime

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22537342.svg)](https://doi.org/10.5281/zenodo.22537342)

Draft paper, version 0.1.3-draft.
Archived at DOI [10.5281/zenodo.22537342](https://doi.org/10.5281/zenodo.22537342) (all versions); this version is 10.5281/zenodo.22544085.

```
paper/note.tex      the first report (12 pages) -- the paper of record
paper/paper.tex     the companion full draft (22 pages), cited as [Full]
scripts/checks.py   displayed arithmetic and exact comparison certificates
scripts/check_round3.py   corrected margins and rigorous selected-degree ratios
scripts/check_normalization.py   local/global weights and coefficient identities
scripts/check_crt_family.py   finite CRT and valuation checks for N=1,106,211
scripts/check_norm_seventh_power_free.cpp   exhaustive norm certificate
lean/              the finite model of Appendix B (Lean 4, Init only)
logs/              recorded arithmetic, sieve and Lean output
```

## Reproducing

```
python3 scripts/checks.py
python3 scripts/check_round3.py
python3 scripts/check_normalization.py
python3 scripts/check_crt_family.py
g++ -O2 -std=c++17 scripts/check_norm_seventh_power_free.cpp -o /tmp/initial_theta_norm_check
/tmp/initial_theta_norm_check
lean lean/RegardedUpToIsOrbit.lean
cd paper && pdflatex -halt-on-error note.tex && pdflatex -halt-on-error note.tex
```

Python uses its standard library; the C++ program requires Boost.Multiprecision
headers. Keep assertions enabled in both programs. The sieve tests every prime
up to 225,469,788, using about 30 MB for its bitmap. It proves the required norm
is seventh-power-free without asserting that its residual cofactor is prime.
The Lean file uses Lean 4.33.1 and prints the axiom dependencies of all nine
theorems. These computations do not certify the geometric constructions or (SA).

## The two results

- **Theorem 1.1** — `F₀=ℚ(√5)`, `π=16+3√5` (Norm 211, split), `a=π²⁹`,
  `E₀: y²=x(x−1)(x−a)`, `ℓ=7`, `F=F₀(i,E₀[15])`, `K=F(E₀[7])`, with the
  compatible cover, section and cusp constructed in §4 and all multiplicative
  places outside 2,7 selected as bad, yields an initial Θ-datum satisfying
  Definition 3.1 (a)–(f), with a **mixed profile** above 211:
  two places, one multiplicative and one good; `e_g=1`, `e_b=105`,
  `ord(q̲_b)=29/7`; tame since `105 ≤ 209 = p−2`.
  *Independent of (SA); uses exact arithmetic and cited geometric results.*
- **Theorem 1.2** — assuming the hypothesis (SA) of §7, the upper bound
  `−226/105` obtained from Proposition 1.4(iii) is incompatible with the value
  `−106/105` of the region it is applied to; margin `8/7`.
  *Conditional on one stated reading of the source.*

## What is and is not claimed

(SA) is a **reading**, not a computation. §11 lists four objections to its derivation;
**(F2)** is named as the likeliest, and the paper undertakes to withdraw
Theorem 1.2 if (F2) is shown to hold.

Not claimed: that `abc` is false; that the lower bound of IUT III Corollary 3.12
is false; that the global inequality of IUT IV Theorem 1.10 is false; that
Scholze–Stix are vindicated or that the 2018 Report is wrong; that the estimate
cannot be repaired.

The N=211 averaged comparison in §9 uses a different existence family. Appendix D
supplies its full Hensel/CRT and counting proof. It is not the explicit N=29
curve with its exponent changed.

## The revised reports

The second report proves the nonsplit-selection obstruction for the stated
congruence family and distinguishes it from the explicit curve, whose retained
selected Tate-degree ratio is between 0.012318439876860 and 0.012318439876861.
It corrects the stage-2 margin to 88/7 and restricts the logarithm-lattice
identity to e_i <= p-2.

Its normalization calculation matches the Tate input degrees used by
Scholze–Stix and IUT IV. The factors 1/(2 ell) and 1/2 are respectively the
root exponent and a moduli-place weight. The coefficient difference 13/48
compares a conditional lower bound with a specified upper expression; it is
not an equality for actual hull volumes. The two source arguments still need
a comparison preserving the full structures to identify their output objects.

All three manuscripts retain the source-reading hypothesis, withdrawal
criterion and correction history. No overall verdict on either side is claimed.
Compile each TeX file twice, repeating if LaTeX requests another pass.
Current verification logs have the prefix `round3-`; earlier logs remain as
records of the preceding draft.

## Second report (2026-09-07)

**An initial Θ-datum over an imaginary quadratic field, and numerical values of the
local quantities of inter-universal Teichmüller theory IV.**
DOI [10.5281/zenodo.22601335](https://doi.org/10.5281/zenodo.22601335)
(all versions: 10.5281/zenodo.22601333).

The datum is `E_0: y^2 = x(x-1)(x-a)` with `a = (10+3i)^29` and `ℓ = 7` over
`Q(i)`, for which 109 splits into one multiplicative and one good place.  All of
[IUT I, Def. 3.1] (a)–(f) is verified, and the local quantities of [IUT IV, Thm 1.10]
and [Prop. 1.4(iii)] are evaluated at that input.

```
second-report/paper/note5.pdf         the paper (20 pages)
second-report/scripts/                reproduction; python3 scripts/tables.py etc.
second-report/lean/                   14 files, Init-only
second-report/audit-logs/             the Lean audit of 2026-09-07
```

263 stated theorems, 768 declarations, 565 axiom-free, no `sorryAx`, no
`Classical.choice`.  Seven of the fourteen Lean files are pinned by SHA-256 to the
bytes released with the first report.  **What the kernel does not carry is stated in
the paper**: the sieve is not run there, the identification of the numeric predicates
with the actual Galois representation and with the places and cusps of the named curve
is an interface field rather than a theorem, the geometric arguments are not verified
by these programs, and Proposition 2 is formalised only in part.

Scope: this report constructs data and evaluates local quantities on them.  It does not
compute the hull of the union of the possible images of the actual Θ-pilot or compare
the two sides of [IUT III, Cor. 3.12]; no claim is made about Corollary 3.12, about the
objections of Scholze–Stix, or about the abc conjecture.
