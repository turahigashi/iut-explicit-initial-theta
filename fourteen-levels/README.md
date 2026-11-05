# Fourteen initial Θ-data on one curve over Q(i)

Version 1.0.0, 6 November 2026 (9 pages). DOI [10.5281/zenodo.23990717](https://doi.org/10.5281/zenodo.23990717).

Let E: y² = x(x − 1)(x − a) with a = (41 + 26i)^472, a curve over Q(i). The note proves that for each prime ℓ in

Λ = {89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157}

the curve extends to an initial Θ-datum in the sense of Definition 3.1 of the first paper of Mochizuki's series on
inter-universal Teichmüller theory, and that this datum satisfies the hypotheses of Theorem 1.10 of the fourth paper.
The field of moduli is Q(i); above the split prime 2357 there is one place of multiplicative and one of good
reduction, with ramification indices 15ℓ and 1.

The curve and the fourteen levels come from §13 of the [second report](../second-report/), which showed that the
levels pass five numerical conditions and said explicitly that they had not been verified to be initial Θ-data.
This note gives the verification. The proof uses the individual ℓ only through five integer facts and one Frobenius
witness per level. The norm of 1 − a has 1592 digits and its factorization is not used: the valuation of 1 − a at each
split place is bounded through the cyclotomic factor Φ_d(π), where d is the order of π modulo the place, and the
138,731 primes that the bound does not exclude are tested directly; the inert places and the places above 2357 are
treated directly. The fourteen levels are the primes in [√(log q^∀), 472/3), and they satisfy condition (C1) of
Corollary 2.2 of the fourth paper.

In version 1.0.0 of the [catalogue](../initial-theta-catalogue/) the datum is listed as D_2357^(ℓ) with its values
marked as conditional on this verification; version 1.1.0 of the catalogue, released together with this note, removes
the condition.

**Nothing is claimed about Corollary 3.12 of the third paper or about the abc conjecture.**

## Files

```
paper/fourteen_levels.pdf     the note
paper/fourteen_levels.tex     its LaTeX source, bibliography included
scripts/d2357_check.py        the computations of the note (Proposition 3.2, Tables 1 and 2, the test of the
                              138,731 primes, the local invariants above 2357, the values of Section 5),
                              compared with the numbers printed in the note
outputs/d2357_check.txt       python3 -I scripts/d2357_check.py
LICENSE                       Creative Commons Attribution 4.0 International (CC BY 4.0)
SHA256SUMS                    checksums of the files above
```

## Reproducing

```
python3 -I scripts/d2357_check.py > outputs/d2357_check.txt
cd paper && pdflatex fourteen_levels.tex && pdflatex fourteen_levels.tex && pdflatex fourteen_levels.tex
```

The program uses the Python 3 standard library only and runs in about ten seconds; it exits with a nonzero status
if a computed value differs from the one printed in the note. The second, independent computation of the order bound
is `scripts/powerfree_certificate.py` of the [second report](../second-report/). The arguments that are not
computations (Lemma 3.1 and the reduction in the proof of Proposition 3.2(d), the image argument apart from the point
counts and the residues, the stable and split reduction, the core, the choice of places and cusp, and the hypotheses
of Theorem 1.10) are not checked by the program.

The files in this folder are licensed under CC BY 4.0.
