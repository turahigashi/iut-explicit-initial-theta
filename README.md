# An explicit initial Θ-datum with mixed reduction over a split prime

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22537342.svg)](https://doi.org/10.5281/zenodo.22537342)

Draft paper, **version 0.1.7**.
Archived at DOI [10.5281/zenodo.22537342](https://doi.org/10.5281/zenodo.22537342) (all versions).

Published versions of this revision: first report **0.1.7**, second report **1.0.5**,
fourth report **1.0.4** (2026-09-12). The bundle shipped with all three is
`iut-explicit-initial-theta-v0.7.0.zip`. Cite the concept DOIs above, which always
resolve to the latest version.

> **v0.1.7 — Theorem 1 stands; the source application of Theorems 5 and 6 is withdrawn.**
> A direct re-reading of IUT IV showed that v0.1.6 did not establish an
> identification of the kind (F2) describes, discharging that version's
> undertaking to withdraw. This is **not** a proof that (SA) is false. The exact
> rational calculation is retained, with the adapter premise that was not
> justified identified; see `paper/note.tex`, §7.1 "The withdrawal".

```
paper/note.tex      the first report (15 pages) -- the paper of record
paper/paper.tex     the companion full draft (23 pages), cited as [First-full]
                    -- its SS.7-9 predate and are superseded by note.tex SS.7
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

- **Theorem 1** (`t:datum`) — `F₀=ℚ(√5)`, `π=16+3√5` (Norm 211, split), `a=π²⁹`,
  `E₀: y²=x(x−1)(x−a)`, `ℓ=7`, `F=F₀(i,E₀[15])`, `K=F(E₀[7])`, with the
  compatible cover, section and cusp constructed in §4 and all multiplicative
  places outside 2,7 selected as bad, yields an initial Θ-datum satisfying
  Definition 3.1 (a)–(f), with a **mixed profile** above 211:
  two places, one multiplicative and one good; `e_g=1`, `e_b=105`,
  `ord(q̲_b)=29/7`; tame since `105 ≤ 209 = p−2`.
  *Independent of (SA); uses exact arithmetic and cited geometric results.*
- **Theorems 5 and 6** (`t:cmp`, `t:fix0`) — the exact rational comparison: `−λ+d_I+1 = −226/105`
  against `−106/105`, margin `8/7`. The arithmetic is correct and its constants
  agree with IUT IV, Props. 1.1, 1.2, 1.4.
  ***Its source application is withdrawn in v0.1.7***: IUT IV, Prop. 1.2 bounds
  `φ(p^λ·(R_I)~)`, not `log_p(R_I^×)`; the same φ carries `log_p(R_I^×)` onto
  itself; Step (v) absorbs (Ind1),(Ind2) into "the arbitrary nature of the
  automorphism φ"; and the `i†`-asymmetry is symmetrized there, which "does not
  affect the computation of the upper bound".

## What is and is not claimed

(SA) was a **reading**, not a computation. §7 lists five failure modes (F1)-(F5)
and named **(F2)** as the likeliest. **v0.1.6 did not establish an identification
of the kind (F2) describes, and the source application is withdrawn.** This is
not a proof that (SA) is false. (SA) and the five failure modes are retained in
the paper as the record of the reading that did not hold.

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
version 1.0.5, DOI [10.5281/zenodo.22601333](https://doi.org/10.5281/zenodo.22601333) (all versions).

The datum is `E_0: y^2 = x(x-1)(x-a)` with `a = (10+3i)^29` and `ℓ = 7` over
`Q(i)`, for which 109 splits into one multiplicative and one good place.  All of
[IUT I, Def. 3.1] (a)–(f) is verified, and the local quantities of [IUT IV, Thm 1.10]
and [Prop. 1.4(iii)] are evaluated at that input.

```
second-report/paper/note5.pdf         the paper (21 pages)
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
objections of Scholze–Stix, or about the abc inequality.

## The third report — the cost of each distinction (September 2026)

`third-report/paper/note6.pdf` (9 pages), DOI
[10.5281/zenodo.22646136](https://doi.org/10.5281/zenodo.22646136).

The local estimates of [IUT IV, §1] are assembled from several steps that the source
keeps apart: a *p*-primary torsion term, a normalization dividing by the local degree,
a tensor order sitting inside its own normalization, a floor function, a ramification
support, and a weighting of places.  This report computes, in actual local fields and
for named curves, **what each of those separations is worth** — how far the estimate
moves if one of them is elided and nothing else changes.  The answers are exact
rationals or exact multiples of log *p*.

```
third-report/paper/note6.tex          the third report (9 pages)
third-report/scripts/costs.py         twelve tables, standard library only, exit 0
third-report/scripts/costs_output.txt the stored output, reproduced byte for byte
third-report/scripts/note6_output_contract.py   frozen presentation contract
third-report/scripts/note6_output_fixture.json  its fixture -- never regenerated by a test
third-report/scripts/note6_regression_gate.py   31 named single-token defects
third-report/scripts/mutation_test.py           the harness the gate exercises
```

Reproducing:

```
cd third-report
python3 scripts/costs.py | diff - scripts/costs_output.txt
python3 scripts/note6_regression_gate.py scripts/costs.py
```

The first prints twelve tables and exits zero; the second reports
`{"PASS": 31, "FAIL": 0, "UNSUPPORTED": 0}`.  Each table's printed output is compared
against a frozen fixture, so a row that changes or disappears fails rather than passing
quietly; the gate holds thirty-one single-token changes that earlier versions of the
script did not notice, each contributed by external review.

**Nothing in this report is offered as a correction to the source.**  Formulas printed
in the source are marked [S] and exact computations from them [P]; the two places where
the distinction being measured is the author's own rather than the source's — the
weighting contrast of §8 and the two-adic cap of §12 — are marked as such in the text.
No claim is made about [IUT III, Cor. 3.12], about the objections of Scholze–Stix, or
about the abc inequality.

## The reports, and which file is which

The file names carry an older working numbering; the reports are numbered as follows.

| report | paper | Zenodo (all versions) |
|---|---|---|
| first | `paper/note.tex` | [10.5281/zenodo.22537342](https://doi.org/10.5281/zenodo.22537342) |
| second | `second-report/paper/note5.tex` | [10.5281/zenodo.22601333](https://doi.org/10.5281/zenodo.22601333) |
| third | `third-report/paper/note6.tex` | [10.5281/zenodo.22646136](https://doi.org/10.5281/zenodo.22646136) |
| fourth | `fourth-report/paper/note3.tex` | [10.5281/zenodo.22648944](https://doi.org/10.5281/zenodo.22648944) |
| fifth | `fifth-report/paper/constant_comparison.tex` | [10.5281/zenodo.22659796](https://doi.org/10.5281/zenodo.22659796) |

`paper/paper.tex` is the expanded version of the **first** report, cited as `[First-full]`;
the first report is the version of record.

## The fourth report — split bad primes and the tuple structure (September 2026)

`fourth-report/paper/note3.pdf` (12 pages), DOI
[10.5281/zenodo.22648944](https://doi.org/10.5281/zenodo.22648944) (all versions).

It collects statements that are **either quoted from a source or proved outright**: that a
tensor packet admits place tuples of mixed reduction type and that selecting only nonsplit
bad primes does not remove them; the stage margin `j²s − (j+2)`; where the source places the
evaluation, quoted verbatim; two constraints on the indeterminacies, at a fixed
nonarchimedean tuple and a fixed stage; and an identity between the two forms in which
[IUT IV, Thm. 1.10] prints its procession-normalized coefficient.

Writing `S(R)` for "the source asserts `R`", the report notes that `S(R)` does not imply `R`,
and states the scope of each proposition rather than offering a blanket guarantee.  **No
verdict on the theory or on abc is asserted.**

```
cd fourth-report
python3 scripts/check_round3.py
python3 scripts/check_normalization.py
python3 scripts/check_crt_family.py
```

Each prints its tables and exits zero.  A quotation checker is included as
`scripts/note3_quotes.py`; it needs your own copies of the cited printings, and what it
reports is a **candidate located by a word-sequence match, not a verdict of verbatim
identity** — every candidate still needs an eye on the source.

## The fifth report — two constants (September 2026)

`fifth-report/paper/constant_comparison.pdf` (7 pages), DOI
[10.5281/zenodo.22659796](https://doi.org/10.5281/zenodo.22659796) (all versions).

The constants `χ = 12/(ℓ(ℓ+1))` and `τ = 12/ℓ²` occur at **different steps** of the
numerical estimates surrounding [IUT IV].  The first is the exact ratio of the stage-one
coefficient `1/(2ℓ)` to the mean of `j²/(2ℓ)` over `j = 1, …, (ℓ−1)/2`, and appears in the
approximate calculation of Scholze–Stix.  The second is used in the upper-bound
rearrangement in the proof of [IUT IV, Thm. 1.10], quoted from Step (viii).  Both are
located in the sources and their difference is computed with exact rational arithmetic.

**What is compared are two scalar expressions under a common set of inputs, stated as a
hypothesis.**  This is not a comparison of the two sources' full estimates, whose positive
terms, divisor supports and approximation conventions differ and are kept separate.  The
same rearrangement and the same slack term are already in print in Joshi,
arXiv:2403.10430v2, p. 70; no priority is claimed for either.

```
cd fifth-report
python3 scripts/constant_comparison.py
python3 scripts/note3_quotes.py --sources YOUR_PDFS --manifest scripts/quotes_manifest.json \
        --paper paper/constant_comparison.tex
```

The first prints the tables and exits zero.  The second needs your own copies of the cited
printings, and reports a **candidate located by a word-sequence match, not a verdict of
verbatim identity**.  **These calculations do not determine a possible-image hull, and they
adjudicate neither the theory nor the objection.**
