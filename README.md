# An explicit initial Θ-datum with mixed reduction over a split prime

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22537342.svg)](https://doi.org/10.5281/zenodo.22537342)

Draft paper, **version 0.1.8**.
Archived at DOI [10.5281/zenodo.22537342](https://doi.org/10.5281/zenodo.22537342) (all versions).

Published versions of this revision (2026-11-08): first report **0.1.8**, second report **1.0.6**,
third report **1.0.3**, fourth report **1.0.5**, fifth report **1.0.1**. The bundle shipped with all five is
`iut-explicit-initial-theta-v0.24.0.zip`. Cite the concept DOIs, which always resolve to the latest version;
the table in "The reports, and which file is which" lists every note with its current version.

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

## About these notes

These notes record what the author could establish about inter-universal Teichmüller theory, working from the
original papers with Lean 4 and with the assistance of generative AI tools under the author's direction. They are
preprints and have not been checked by experts in the field. Statements said to be proved in Lean are
machine-checked; whether the formal statements and axioms match the source is checked by reading the source, and
each note says how. None of the notes claims that Corollary 3.12 of IUT III is false, and none takes a position on
whether the abc conjecture holds. Corrections are welcome: please open an issue, or write to the address in
`CITATION.cff`.

## How the notes fit together

These notes record what the author could establish about Corollary 3.12 of IUT III and the estimates of IUT IV,
Theorem 1.10, on explicit data, in models, and in Lean.

- **The five reports (September 2026)** construct explicit initial Θ-data whose field of moduli is not Q (over
  Q(√5) in the first report, over Q(i) in the second), evaluate the local quantities of IUT IV on them, measure what
  each separation in those estimates is worth (third), collect statements on split bad primes and the tuple
  structure, including that (Ind2) acts at a nonarchimedean tuple by unit scalars (fourth), and compare the constants
  12/(ℓ(ℓ+1)) and 12/ℓ² (fifth).
- **Step (v) and the explicit data.** The Step (v) note and the catalogue compare Step (v) of the proof of
  Theorem 1.10 under two readings of the label permutations of (Ind1) on seven data; fourteen-levels proves that one
  curve over Q(i) gives an initial Θ-datum at fourteen levels; the walkthrough runs the computable parts of the theory
  on these data; ind2-gap gives the (Ind2)-terms of lana-agents/iut in closed form; reading-family shows that in each of
  36 readings Corollary 3.12 and the upper bound of IV give the same height inequality (k − 1)|log q| ≤ C.
- **Step (xi).** Segment or loop? and its elementary companion, Indexed identifications, state the comparison of
  Step (xi) as a lax 2-cell, which is equivalent to that inequality. Two computations and Bridge and size are essays
  that read it as a comparison of programs and as a bridge versus its size. Where Theorem 3.11 sits takes the content
  of the results cited in the proof as axioms about log-volumes and gives models, one on actual local objects, in which
  the conclusion fails, so that what is missing lies between a weak and a strong reading of (SHE).

Each note credits the earlier work it builds on or agrees with, including the Lean repositories lana-agents/iut and
Takkun-kohinata/IUT_LEAN and the preprints of Higuchi, Pajo, Saito, sfingali, Geiger and others. The ratio
12/(ℓ(ℓ+1)) between the two pilots is written s in Where Theorem 3.11 sits, m in Segment or loop?, 1/k in Indexed
identifications, reading-family, Two computations and Bridge and size, and 1/s in lana-agents/iut, the walkthrough,
ind2-gap and the catalogue; in the first four reports, s is the q-order at a bad place. None of the notes claims that
Corollary 3.12 or the abc conjecture is true or false.

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
version 1.0.6, DOI [10.5281/zenodo.24039381](https://doi.org/10.5281/zenodo.24039381); all versions: [10.5281/zenodo.22601333](https://doi.org/10.5281/zenodo.22601333).

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

`third-report/paper/note6.pdf` (9 pages), version 1.0.3, DOI
[10.5281/zenodo.24039382](https://doi.org/10.5281/zenodo.24039382); all versions: [10.5281/zenodo.22646136](https://doi.org/10.5281/zenodo.22646136).

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

| note | paper | Zenodo, all versions | current version |
|---|---|---|---|
| first | `paper/note.tex` | [10.5281/zenodo.22537342](https://doi.org/10.5281/zenodo.22537342) | 0.1.8, [10.5281/zenodo.24039378](https://doi.org/10.5281/zenodo.24039378) |
| second | `second-report/paper/note5.tex` | [10.5281/zenodo.22601333](https://doi.org/10.5281/zenodo.22601333) | 1.0.6, [10.5281/zenodo.24039381](https://doi.org/10.5281/zenodo.24039381) |
| third | `third-report/paper/note6.tex` | [10.5281/zenodo.22646136](https://doi.org/10.5281/zenodo.22646136) | 1.0.3, [10.5281/zenodo.24039382](https://doi.org/10.5281/zenodo.24039382) |
| fourth | `fourth-report/paper/note3.tex` | [10.5281/zenodo.22648944](https://doi.org/10.5281/zenodo.22648944) | 1.0.5, [10.5281/zenodo.24039383](https://doi.org/10.5281/zenodo.24039383) |
| fifth | `fifth-report/paper/constant_comparison.tex` | [10.5281/zenodo.22659796](https://doi.org/10.5281/zenodo.22659796) | 1.0.1, [10.5281/zenodo.24039384](https://doi.org/10.5281/zenodo.24039384) |
| Step (v) short note | `stepv-local-noncontainment/paper/stepv_local_noncontainment.tex` | [10.5281/zenodo.23166432](https://doi.org/10.5281/zenodo.23166432) | 3.1.0, [10.5281/zenodo.24039373](https://doi.org/10.5281/zenodo.24039373) |
| catalogue of the data | `initial-theta-catalogue/paper/initial_theta_catalogue.tex` | [10.5281/zenodo.23870447](https://doi.org/10.5281/zenodo.23870447) | 1.2.0, [10.5281/zenodo.24039374](https://doi.org/10.5281/zenodo.24039374) |
| fourteen initial Θ-data (D_2357) | `fourteen-levels/paper/fourteen_levels.tex` | [10.5281/zenodo.23990716](https://doi.org/10.5281/zenodo.23990716) | 1.0.0, [10.5281/zenodo.23990717](https://doi.org/10.5281/zenodo.23990717) |
| programmer's walkthrough | `iut-walkthrough/paper/iut_walkthrough.tex` | [10.5281/zenodo.23880259](https://doi.org/10.5281/zenodo.23880259) | 1.2.0, [10.5281/zenodo.24039375](https://doi.org/10.5281/zenodo.24039375) |
| segment or loop (HoTT overview) | `segment-or-loop/paper/segment_or_loop.tex` | [10.5281/zenodo.23931343](https://doi.org/10.5281/zenodo.23931343) | 1.4.0, [10.5281/zenodo.24039360](https://doi.org/10.5281/zenodo.24039360) |
| indexed identifications (educational) | `indexed-identifications/paper/indexed_identifications.tex` | [10.5281/zenodo.23931345](https://doi.org/10.5281/zenodo.23931345) | 2.3.0, [10.5281/zenodo.24039367](https://doi.org/10.5281/zenodo.24039367) |
| the gap between the two walls | `ind2-gap/paper/ind2_gap.tex` | [10.5281/zenodo.23954193](https://doi.org/10.5281/zenodo.23954193) | 1.1.0, [10.5281/zenodo.24039377](https://doi.org/10.5281/zenodo.24039377) |
| no reading avoids the height inequality | `reading-family/paper/reading_family.tex` | [10.5281/zenodo.23965951](https://doi.org/10.5281/zenodo.23965951) | 1.1.0, [10.5281/zenodo.24039368](https://doi.org/10.5281/zenodo.24039368) |
| two computations | `two-computations/paper/two_computations.tex` | [10.5281/zenodo.23968298](https://doi.org/10.5281/zenodo.23968298) | 1.1.0, [10.5281/zenodo.24039369](https://doi.org/10.5281/zenodo.24039369) |
| bridge and size | `bridge-and-size/paper/bridge_and_size.tex` | [10.5281/zenodo.23984200](https://doi.org/10.5281/zenodo.23984200) | 1.1.0, [10.5281/zenodo.24039372](https://doi.org/10.5281/zenodo.24039372) |
| where Theorem 3.11 sits | `where-311-sits/paper/where-311-sits.tex` | [10.5281/zenodo.24028832](https://doi.org/10.5281/zenodo.24028832) | 1.1.0, [10.5281/zenodo.24039357](https://doi.org/10.5281/zenodo.24039357) |

`paper/paper.tex` is the expanded version of the **first** report, cited as `[First-full]`;
the first report is the version of record.

## The fourth report — split bad primes and the tuple structure (September 2026)

`fourth-report/paper/note3.pdf` (13 pages), version 1.0.5, DOI
[10.5281/zenodo.24039383](https://doi.org/10.5281/zenodo.24039383); all versions: [10.5281/zenodo.22648944](https://doi.org/10.5281/zenodo.22648944).

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

`fifth-report/paper/constant_comparison.pdf` (8 pages), version 1.0.1, DOI
[10.5281/zenodo.24039384](https://doi.org/10.5281/zenodo.24039384); all versions: [10.5281/zenodo.22659796](https://doi.org/10.5281/zenodo.22659796).

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

## Step (v) short note (October 2026)

**A local non-containment in Step (v) of IUT IV, Theorem 1.10.**
`stepv-local-noncontainment/paper/stepv_local_noncontainment.pdf` (9 pages), version 3.1.0, DOI
[10.5281/zenodo.24039373](https://doi.org/10.5281/zenodo.24039373).
All versions: [10.5281/zenodo.23166432](https://doi.org/10.5281/zenodo.23166432).

This note presents an explicit local non-containment calculation for a datum with two places of
multiplicative reduction above the prime 30965771. A pure tensor obtained from a theta value by a label
permutation remains outside the comparison module under every factorwise log-shell-preserving
automorphism. Its application to the possible-image union in Step (v) of IUT IV, Theorem 1.10 is
conditional on the membership and orbit-closure readings (M) and (R) in Section 4, including the
compatibility with the cited constructions of the local-coordinate descriptions used in Lemmas 3
and 4. Under those assumptions, the corresponding hull component has larger log-volume than the
displayed bound. A complete identification with the source construction is not established in this note.
Section 6 relates the reading (R) to the literal reading of Corollary 3.12 formalized in the public Lean
repository [lana-agents/iut](https://github.com/lana-agents/iut), and, using the distinctions recorded there, places the example in a
two-by-two classification by reading and by whether the orders of the q-parameters at the places above p
agree.

**No assertion is made about Corollary 3.12 itself, the final global inequality of Theorem 1.10,
or the abc conjecture.** This is a preprint; it has not been refereed.

The first report in this repository compared a different datum, at the prime 211, with the local
estimates of IUT IV; the source application of that comparison was withdrawn in its version 0.1.7. This
note is a separate paper, not a revision of the first report: its datum has two places above the prime,
both of multiplicative reduction, and it neither cites nor relies on the first report.

The files in `stepv-local-noncontainment/` are licensed under CC BY 4.0; the rest of the repository
remains under Apache-2.0.

```
cd stepv-local-noncontainment/paper
pdflatex -interaction=nonstopmode -halt-on-error stepv_local_noncontainment.tex   # run twice
```

## Catalogue of the data (November 2026)

**Explicit initial Θ-data and the two readings of Step (v) of IUT IV, Theorem 1.10: a catalogue.**
`initial-theta-catalogue/paper/initial_theta_catalogue.pdf` (7 pages), version 1.2.0, DOI
[10.5281/zenodo.24039374](https://doi.org/10.5281/zenodo.24039374) (all versions: [10.5281/zenodo.23870447](https://doi.org/10.5281/zenodo.23870447)). Version 1.1.0 removed the condition on
the datum D_2357^(ℓ), whose verification is in `fourteen-levels/` (below); version 1.2.0 credits earlier work
(Takkun-kohinata/IUT_LEAN) and corrects two locators and a count.

The note collects the explicit initial Θ-data constructed over Q(√5) and Q(i) — the three of the first
report, the second report and the Step (v) short note, and four new ones, one of them for fourteen values
of ℓ — with their local invariants above one split prime and the comparisons of Step (v) of IUT IV,
Theorem 1.10, under the two readings of Corollary 3.12 formalized in
[lana-agents/iut](https://github.com/lana-agents/iut). Under the reading of IUT IV every comparison is a
containment; under the literal reading and stated membership hypotheses each datum gives a
non-containment for a single component. **No conclusion is drawn about Corollary 3.12, the final
inequality of Theorem 1.10, or the abc conjecture.** The programs that compute the tables and check the
arithmetic of the new data are in the same folder; see `initial-theta-catalogue/README.md`.

The files in `initial-theta-catalogue/` are licensed under CC BY 4.0; the rest of the repository remains
under Apache-2.0.

## A programmer's walkthrough (November 2026)

**A programmer's walkthrough of inter-universal Teichmüller theory: running the multiradial algorithm on
explicit initial Θ-data.** `iut-walkthrough/paper/iut_walkthrough.pdf` (18 pages), version 1.2.0, DOI
[10.5281/zenodo.24039375](https://doi.org/10.5281/zenodo.24039375) (all versions:
[10.5281/zenodo.23880259](https://doi.org/10.5281/zenodo.23880259)).

A program, with an interactive web page, that runs on explicit numbers those operations of IUT that can be
written as procedures, on the seven initial Θ-data of the catalogue above. It computes the Tate parameters
and local data p-adically, keeps the two Hodge theaters of a Θ-link as type-separated copies of the local
fields, computes log-shells, Kummer read-outs, containers, possible images and the log-volume of the
holomorphic hull of their union for three readings of the label indeterminacy, and places side by side the
two quantities that Step (xi) of the proof of Corollary 3.12 compares. Version 1.1.0 adds a second model of the
indeterminacy (Ind2), the group of all ℤ_p-linear automorphisms of the log-shells of the factors used in
lana-agents/iut, whose hull is given by the closed form of the note in `ind2-gap/`; in the reading of IUT IV the
two models give the Scholze–Stix inequality and the variant of Corollary 3.12, and the program computes their
difference for each datum. Infinite objects are computed in
finite windows. **The purpose is expository; no conclusion is drawn about Corollary 3.12, Theorem 1.10 of
IUT IV, or the abc conjecture.** Turning the objects and processes of IUT into data types has been done
earlier and on a broader scale in [motizukipdf](https://github.com/oneman/motizukipdf); the container
formulas and the readings are taken from [lana-agents/iut](https://github.com/lana-agents/iut). See
`iut-walkthrough/README.md` for the files and how to rerun the program (Python 3.10 or later, sympy).

The files in `iut-walkthrough/` are licensed under CC BY 4.0.

## Segment or loop? and indexed identifications (November 2026)

Two companion notes, published together and citing each other.

**Segment or loop? A homotopy-type-theoretic overview of the dispute over Corollary 3.12 of inter-universal
Teichmüller theory.** `segment-or-loop/paper/segment_or_loop.pdf` (28 pages), version 1.4.0, DOI
[10.5281/zenodo.24039360](https://doi.org/10.5281/zenodo.24039360) (all versions:
[10.5281/zenodo.23931343](https://doi.org/10.5281/zenodo.23931343)). The vocabularies of the dispute (identification
and labels, monodromy, segment, loop and universal cover, IPL, SHE and APT, logical AND and OR, descent, commutativity
up to indeterminacies, the size of the blurring) are stated as propositions of homotopy type theory about families of
ordered real lines over graphs. Corollary 3.12 becomes equivalent to a lax 2-cell between two paths, an inequality of
the shape of a height bound. The quantitative core is checked in Lean 4 (`segment-or-loop/lean/`). Version 1.1.0 added
pointers to Part II of the companion note; version 1.2.0 cited Laniewski, version 1.3.0 the `Iut/WallEquiv/` files of
lana-agents/iut, and version 1.4.0 the further earlier work described below.

**Reading the IUT dispute through indexed identifications: an educational model in undergraduate mathematics.**
`indexed-identifications/paper/indexed_identifications.pdf` (28 pages), version 2.3.0, DOI
[10.5281/zenodo.24039367](https://doi.org/10.5281/zenodo.24039367) (all versions:
[10.5281/zenodo.23931345](https://doi.org/10.5281/zenodo.23931345)). The same model written with sets, maps,
positive real numbers, graphs and inequalities, with a symbol for indexed identifications, exercises and answers.
Part II, new in version 2.0.0, extends the notation to the components of tensor packets: in a model with one prime and
the label permutations of (Ind1), the two readings of the union in Corollary 3.12 differ by an expected order
statistic, and in either reading Corollary 3.12 together with the upper bound of IV implies the height bound. The
quantitative core of Part II is checked in Lean 4 (`indexed-identifications/lean/`). Version 2.1.0 cited Laniewski, version 2.2.0
the `Iut/WallEquiv/` files, and version 2.3.0 the further earlier work described below.

None of the results of either note is new mathematically; the contribution is the formulation and the
correspondences. A general semantics for comparison problems in arithmetic geometry, in which the passage between
labelled presentations is a transport carrying a cost, appears earlier, without reference to IUT, in R. Laniewski,
*Intensional semantics for comparison problems in arithmetic geometry*, arXiv:2608.13609; no priority is claimed for
that idea. Statements of the same shape as the central equivalence of both notes (Step (xi) is equivalent to one
inequality, which the properties at the level of Theorem 3.11 do not decide) were proved earlier, in models, in the
Lean repository lana-agents/iut (`Iut/WallEquiv/`, added 13 October 2026); they are not claimed as new. Both notes also credit earlier readings and formalizations of the same dispute: J. Whaley Jr
(a reading in homotopy type theory, Zenodo, 15 October 2026), sfingali (a Lean formalization of the Scholze–Stix
objection, Zenodo, 2 August 2026), Takkun-kohinata/IUT_LEAN (July 2026), Gogopex/iut-lean (labelled copies of the real
line, May 2026), and the files `Iut/Wall/Pilots.lean` and `Iut/Wall/Constraints.lean` of lana-agents/iut (October 2026).
**No claim is made about the truth of Corollary 3.12, Theorem 1.10 of IUT IV, or the abc
conjecture.** The files in `segment-or-loop/` and `indexed-identifications/` are licensed under CC BY 4.0.

## The gap between the two walls (November 2026)

**The gap between the two walls is positive: a closed form for the (Ind2)-terms of lana-agents/iut.**
`ind2-gap/paper/ind2_gap.pdf` (11 pages), version 1.1.0, DOI
[10.5281/zenodo.24039377](https://doi.org/10.5281/zenodo.24039377).

[lana-agents/iut](https://github.com/lana-agents/iut) proves that the difference Δ(D) between its variant of
Corollary 3.12 and the Scholze–Stix inequality is a weighted average of (Ind2)-terms at the bad residue
characteristics, and leaves their value open. The note determines the (Ind2)-terms in closed form, on lana's
definitions as they stand. It follows that Δ(D) > 0 for every initial Θ-datum, that Δ(D) is bounded above by a
quantity that does not involve the size of the q-orders, and that its average over the labels is given by the class
number of Q(√−ℓ). The values for the data of the catalogue are computed with the program of the walkthrough above.
lana-agents/iut had earlier proved positivity for the form of the gap without the hull; the note concerns Δ(D) with the
hull, and explains the relation. The proofs are on paper and have not been checked in Lean. **No claim is made about the truth of (Var), (SS),
Corollary 3.12, or the abc conjecture.** See `ind2-gap/README.md` for the files and how to rerun the scripts.

The files in `ind2-gap/` are licensed under CC BY 4.0.

## No reading avoids the height inequality (November 2026)

**No reading avoids the height inequality: 36 readings of Corollary 3.12 and the conservation of the height load.**
`reading-family/paper/reading_family.pdf` (17 pages), version 1.1.0, DOI
[10.5281/zenodo.24039368](https://doi.org/10.5281/zenodo.24039368).

The value of −|log Θ| in Corollary 3.12 depends on how the statement is read, along five axes ((Ind1), (Ind3), (Ind2),
the hull, the archimedean container), which give 36 readings. In each of them, Corollary 3.12 and the upper bound of
IUT IV together give the same height inequality (k − 1)|log q| ≤ C, because the two ends are computed by one procedure
that takes no reading. A reading only splits the wall (k − 1)|log q| between the two statements, at a point decided by
(Ind1) alone; no reading makes both loads nonpositive, and in the family q → q^N the statement that holds for every N
carries no positive load. The statements are proved in Lean 4 for a component model (`reading-family/lean/`), and the
36 readings are computed for the seven data of the catalogue with the program of the walkthrough above. That the wall
is needed was shown earlier in Lean by Takkun-kohinata/IUT_LEAN and lana-agents/iut, whom the note credits. **No claim is
made about the truth of Corollary 3.12, Theorem 1.10 of IUT IV, or the abc conjecture.** See `reading-family/README.md`
for the files and how to rerun them.

The files in `reading-family/` are licensed under CC BY 4.0.

## Two computations of the height inequality (November 2026)

**Two computations of the height inequality and the multiradial algorithm: reading IUT from the viewpoint of computer
science.** `two-computations/paper/two_computations.pdf` (30 pages), version 1.1.0, DOI
[10.5281/zenodo.24039369](https://doi.org/10.5281/zenodo.24039369).

An essay with almost no new mathematical results, which proposes to read IUT from the side of computer science. In
every reading listed in `reading-family/`, IUT passes through the height inequality, which is written in classical
quantities and can be computed for a given curve without IUT; what IUT has to add is the "for every initial Θ-datum" of
Corollary 3.12, which is supposed to come from the multiradial algorithm of Theorem 3.11. Two C programs place the
classical computation and the computation of IUT (in the reading of IUT IV) side by side on the same input, and a C++
mockup of the multiradial algorithm implements what can be implemented at present and leaves the rest as named oracles
whose values are reverse-computed and marked as such. D. Richards' motizukipdf (data types, a web tool and a Lean form of
the same comparison) and Takkun-kohinata/IUT_LEAN are credited as earlier work. **No claim is made about the truth of IUT, of Corollary 3.12, or
of the abc conjecture**; the output of the mockup proves nothing. See `two-computations/README.md` for the files and how
to rerun them.

The files in `two-computations/` are licensed under CC BY 4.0.

## Bridge and size (November 2026)

**Bridge and size: the Kodaira–Spencer morphism, arithmetic derivatives and Step (xi) of IUT as lax 2-cells.**
`bridge-and-size/paper/bridge_and_size.pdf` (22 pages), version 1.1.0, DOI
[10.5281/zenodo.24039372](https://doi.org/10.5281/zenodo.24039372).

An essay with almost no new mathematical results. It places the Kodaira–Spencer argument of function fields, the
bridges built from an additive relation a + b = c (the p-adic logarithms of Baker's method, Pasten's arithmetic
derivatives) and Step (xi) of the proof of Corollary 3.12 side by side as the lax 2-cells of `segment-or-loop/`, and
separates a *bridge* (that a 2-cell exists) from its *size* (the blurring) — a restatement of two requirements stated
by Mochizuki himself. The term bridge for this inclusion, and the observation that the written argument bounds the
blurring but does not derive the bridge, appear earlier in Higuchi, Pajo and Geiger, whom the note credits. A bridge from an additive relation does not cross the Θ-link; on the seven data of
`two-computations/data/`, absorbing the resulting discrepancy needs ℓ times the wall (k − 1)Q. **No claim is made
about whether IUT is correct.** See `bridge-and-size/README.md` for the files and how to rerun them.

The files in `bridge-and-size/` are licensed under CC BY 4.0.

## Fourteen initial Θ-data on one curve over Q(i) (November 2026)

**Fourteen initial Θ-data on one curve over Q(i).**
`fourteen-levels/paper/fourteen_levels.pdf` (9 pages), version 1.0.0, DOI
[10.5281/zenodo.23990717](https://doi.org/10.5281/zenodo.23990717).

The note proves that the curve y² = x(x − 1)(x − a), a = (41 + 26i)^472, of §13 of the second report extends, for
each of the fourteen primes ℓ = 89, …, 157 found there, to an initial Θ-datum in the sense of IUT I, Definition 3.1,
satisfying the hypotheses of IUT IV, Theorem 1.10; the levels satisfy condition (C1) of IUT IV, Corollary 2.2. The
order condition is proved without factoring 1 − a, by bounding its valuations through cyclotomic factors, and the
program `fourteen-levels/scripts/d2357_check.py` recomputes the numbers of the note. **Nothing is claimed about
Corollary 3.12 or about abc.** With this note the catalogue above is released as version 1.1.0, without the
condition on D_2357^(ℓ). See `fourteen-levels/README.md`.

The files in `fourteen-levels/` are licensed under CC BY 4.0.

## Where Theorem 3.11 sits (November 2026)

**Where Theorem 3.11 sits: the log-volume content of the results cited in the proof of IUT III, Corollary 3.12, does
not imply its conclusion.** `where-311-sits/paper/where-311-sits.pdf` (24 pages), version 1.1.0, DOI
[10.5281/zenodo.24039357](https://doi.org/10.5281/zenodo.24039357) (all versions:
[10.5281/zenodo.24028832](https://doi.org/10.5281/zenodo.24028832)).

The note lists the results that Corollary 3.12 and its proof cite, states the content of the 22 that the proof uses
as definitions or premises as axioms about log-volumes, at the strength of the source, and gives models of the axioms
— one of them built from actual local objects at a finite extension of Q_p — in which the conclusion fails. A weak
reading of (SHE) follows from the axioms; within the models, the conclusion holds exactly where a strong reading
holds. A Venn diagram displays this position. Results of the same shape were proved earlier, for abstractions of the passage by Higuchi and
Pajo, and in Lean by Takkun-kohinata/IUT_LEAN (July 2026) and [lana-agents/iut](https://github.com/lana-agents/iut)
(October 2026); the note was obtained independently of these Lean works, which were made public first, and cites them. Every statement marked [P] is proved in Lean 4 with Mathlib (`where-311-sits/lean/`).
**Nothing is claimed about whether Corollary 3.12 is true, nor about abc.** See `where-311-sits/README.md`.

The paper and README in `where-311-sits/` are licensed under CC BY 4.0, and the Lean sources in
`where-311-sits/lean/` under the Apache License 2.0.
