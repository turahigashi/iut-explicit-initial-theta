# Explicit initial Θ-data and the two readings of Step (v) of IUT IV, Theorem 1.10: a catalogue

Version 1.2.0, 8 November 2026 (7 pages).
DOI [10.5281/zenodo.24039374](https://doi.org/10.5281/zenodo.24039374); version 1.1.0:
[10.5281/zenodo.23990719](https://doi.org/10.5281/zenodo.23990719); version 1.0.0:
[10.5281/zenodo.23870448](https://doi.org/10.5281/zenodo.23870448).

We collect the explicit initial Θ-data, in the sense of Definition 3.1 of the first paper of Mochizuki's
series on inter-universal Teichmüller theory, that the author has constructed over Q(√5) and Q(i): three
published earlier, three given here, and one, for fourteen values of ℓ, that is verified in a separate note
([fourteen-levels](../fourteen-levels/)). Each has a split rational
prime above which the two places of the field of moduli are either one of good and one of multiplicative
reduction, or both of multiplicative reduction with different orders of the q-parameter. For each datum
we tabulate the local invariants and compare, in Step (v) of the proof of Theorem 1.10 in the fourth
paper, the displayed comparison module with the hull component of the union of possible images. Under
the reading in which the theta value stays at the label j, as in Step (v) and in what the public Lean
formalization [lana-agents/iut](https://github.com/lana-agents/iut) calls the reading of IUT IV, every
comparison is a containment. Under the reading in which label permutations fixing the label 0 act before the
hull is taken, which is contained in what the same formalization calls the literal reading (that reading also
admits permutations moving 0), and under stated membership hypotheses, every
datum gives a non-containment for a single component; at primes with a good and a bad place the excess
grows like j², and for three data the weighted average over the components also exceeds the bound
displayed at the prime.

**No conclusion is drawn about Corollary 3.12, the final inequality of Theorem 1.10, or the abc
conjecture.** Neither reading is claimed to be the one the source intends. This is a preprint.

What is new is the data themselves and the numbers: initial Θ-data whose field of moduli is not Q, data
realizing both kinds of prime, and exact values of the comparisons of Step (v) on them. The distinctions
between the readings, and the mechanism by which they differ, are not new; Section 6 of the note gives
the earlier work and the dates.

| datum | field | p | the two places above p |
|---|---|---|---|
| D_211 | Q(√5) | 211 | good, bad (first report) |
| D_109 | Q(i) | 109 | good, bad (second report) |
| D_2 | Q(√5) | 30965771 | bad, bad (Step (v) short note) |
| D_3 | Q(√5) | 30965771 | bad, bad (new) |
| D_18 | Q(√5) | 30965771 | good, bad (new) |
| D_15 | Q(√5) | 30965819 | good, bad (new) |
| D_2357^(ℓ) | Q(i) | 2357 | good, bad; 14 levels ℓ ([fourteen-levels](../fourteen-levels/)) |

## Changes in version 1.2.0

Cites earlier work. [Takkun-kohinata/IUT_LEAN](https://github.com/Takkun-kohinata/IUT_LEAN) (15 July 2026) proved
in Lean, in its model, that the hull bound of Step (xi) with a ledger L of local terms is equivalent to
(s − 1)|log q| ≤ L; version 1.1.0 credited this inequality to lana-agents/iut and did not cite the earlier result
(Section 5). lana-agents/iut constructs initial Θ-data in Lean from an elliptic curve and stated inputs
(`Iut/Concrete/Existence.lean`, 2 September 2026), with no numerical example (Section 6). Adds pointers to the
author's fourth report (its Section 6: in a procession of copies of one prime-strip, fixing D_0 does not by itself
fix the label 0 inside the larger capsules; its Proposition 5: the (GB_L) comparison for every j) and to Theorem 5
of the first report, the (GB_L) comparison at j = 1. Corrects the locators of the readings (M) and (R) of the
Step (v) note (its Section 4, not Section 3); makes the count of the data consistent (three published earlier,
three new here, and D_2357^(ℓ), verified in fourteen-levels); says that the reading with label permutations fixing
0 is contained in the literal reading of lana-agents/iut rather than equal to it; and gives the date of the first
version of Zeng's paper (29 October 2026). The tables and numbers are unchanged.

## Changes in version 1.1.0

Version 1.1.0 removes the condition on D_2357^(ℓ): version 1.0.0 marked its values as conditional on a
companion report, which is now [fourteen-levels](../fourteen-levels/) (doi:10.5281/zenodo.23990717). That report
verifies Definition 3.1 of the first paper and the hypotheses of Theorem 1.10 of the fourth paper at all fourteen
levels. Nothing else in the note is changed.

## Files

```
paper/initial_theta_catalogue.pdf     the note (7 pages)
paper/initial_theta_catalogue.tex     its LaTeX source, bibliography included
scripts/catalogue.py                  Proposition 1 and Table 2 (closed forms, checked against an
                                      enumeration of all tuples for l = 7, j <= 3)
scripts/averaged.py                   Theorem 4, Table 3 and Remark 5
checks/certify_datum.py               D_18: arithmetic of the datum
checks/independent_check.py           D_18: independent re-check (sympy)
checks/certify_mixed15.py             D_15: arithmetic of the datum (uses certify_datum.py)
checks/independent_check_mixed15.py   D_15: independent re-check from the specification (sympy, numpy)
checks/certify_wide.py                D_3: arithmetic of the datum (uses certify_datum.py and
                                      seventh_power_sieve.c)
checks/independent_check_wide.py      D_3: independent re-check (sympy and seventh_power_wheel.c)
checks/seventh_power_sieve.c          segmented sieve listing the prime divisors up to a bound
checks/seventh_power_wheel.c          trial division by a wheel, written independently of the sieve
checks/check_pratt_factorizations.py  D_3: complete factorization of the four norms with primality
                                      certificates; also N(1 - a) = 2^2 11^2 R for D_2
checks/pratt_certificates.json        the Lucas (Pratt) certificates, checked by the program above
logs/                                 the output of every program above
LICENSE                               Creative Commons Attribution 4.0 International (CC BY 4.0)
SHA256SUMS                            SHA-256 checksums of the files above
```

## Reproducing

From this folder:

```
python3 scripts/catalogue.py                       # standard library; a few seconds
python3 scripts/averaged.py                        # standard library; a few seconds
python3 checks/certify_datum.py                    # standard library
python3 checks/independent_check.py                # sympy
python3 checks/certify_mixed15.py                  # standard library
python3 checks/independent_check_mixed15.py        # sympy, numpy; a few minutes
python3 checks/certify_wide.py --threads 8         # needs gcc with pthreads; a few minutes
python3 checks/independent_check_wide.py --threads 8   # sympy, gcc; several minutes
python3 checks/check_pratt_factorizations.py       # standard library
cd paper && pdflatex initial_theta_catalogue.tex   # run twice
```

Keep assertions enabled (do not use `python -O`). Every program exits with status 0 if and only if all
its checks pass; the recorded output, with exit status and running time, is in `logs/`. The averaged
values printed by the check programs are those of the variants in Remark 5 of the note (without rounding;
for D_18 and D_15 with permutations moving the label 0 as well). These computations check the arithmetic
of the data and the rational comparisons; they do not certify the geometric constructions or the
readings of Corollary 3.12 under which the comparisons apply.

## Use of generative AI

Generative AI tools (large language models: Claude by Anthropic, and ChatGPT and Codex by OpenAI) were
used extensively in this work, under the author's direction, in finding the data and the proofs, in the
computations and in the writing. The author takes full responsibility for the contents of this note.

Copyright 2026 Toshihisa Urahigashi. The files in this folder are licensed under the Creative Commons
Attribution 4.0 International License (CC BY 4.0); see `LICENSE`. The rest of this repository remains
under the Apache License, Version 2.0.
