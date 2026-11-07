# Three tiers of indeterminacy: the exact hull at small places and the container of Step (v) of IUT IV

Version 1.0.0, 8 November 2026 (11 pages). DOI [10.5281/zenodo.24043000](https://doi.org/10.5281/zenodo.24043000).

In Step (v) of the proof of IUT IV, Theorem 1.10, the holomorphic hull of the union of the possible images of the
Θ-pilot object is bounded by a container that contains the region p^λ·(R_I)^∼; the indeterminacies (Ind1) and (Ind2)
are accounted for by the arbitrary automorphisms φ of IUT IV, Proposition 1.2, and (Ind3) by taking upper bounds.

At places that are small in the sense of Proposition 1.2(iii) (p odd, every ramification index at most p − 2), the
note compares this container with the hulls reached by four classes of maps: unit scalars and field automorphisms;
the maps induced factor by factor by the actual (Ind1) and (Ind2); all factorwise automorphisms of the log-shells;
and all automorphisms φ of Proposition 1.2. For the last two classes the hull is exactly p^(⌈λ⌉ − 𝔡_I)·(R_I)^∼,
whereas the container of Step (v) has hull p^(⌊λ⌋ − 𝔡_I)·(R_I)^∼: when λ is not an integer, which is always the case
at bad places, the container is larger by exactly a factor p (log p in log-volume). The difference comes from the
proof of Proposition 1.2(ii), which uses Proposition 1.1 with the different of every factor; Proposition 1.1 applied
to the factor that carries p^λ removes it. Unit scalars and field automorphisms do not enlarge the hull; the actual
(Ind1), (Ind2) reach the exact value when λ is an integer if automorphisms of the local Galois groups carry a unit to
the boundary of the log-shell, which at small places reduces to one condition on the transvections of Hoshi–Nishio
and Kondo. The difference is a term of conductor type and does not change the shape of the inequality of IUT IV.

Relation to earlier work, in short: Proposition 1.1 of IUT IV is stated with a free choice of the factor that does not
pay its different; Dupuy–Hilado (arXiv:2004.13108, Remark 2.8.2 and step (6.4)) choose the factor with the largest
different; [lana-agents/iut](https://github.com/lana-agents/iut) (`Iut/WallEquiv/VcI.md`, 13 October 2026) states that
for λ = 0 the hull is exactly the container of IUT IV; Mochizuki states that automorphisms of the log-shells give only
bounded discrepancies (EssLgc, Example 3.5.1). The note is the local, numerical counterpart of
[`../where-311-sits/`](../where-311-sits/) (its Theorem 22 uses only an upper bound for the same quantity) and
measures from the region of Step (v) itself, whereas [`../ind2-gap/`](../ind2-gap/) measures from the region built on
the log-shells.

**No claim is made about the truth of Corollary 3.12 of IUT III or of the abc conjecture.** The proofs of Sections 3
and 4 are on paper; versions of the statements of Section 4 were also checked in Lean 4 in a development of the author
that is not part of this folder, and the proofs do not rely on it. This folder contains no Lean code.

## Files

```
paper/three_tiers.pdf                  the note
paper/three_tiers.tex                  its LaTeX source, bibliography included
scripts/check_example.py               Q_5(sqrt5), two factors: the largest k with Theta inside 5^k (x)I is
                                       ceil(m/2), m = 0..12 (Remark 3.6)
scripts/check_perfactor.py             two factors: random factorwise automorphisms of the log-shells (400 per m);
                                       the hull of the images against the exact value and the container
scripts/check_nfactor.py               the same for two and three factors (150 per m), with the largest k
scripts/example_d109.py                the table of Section 5, reading the place data of D109 from
                                       ../iut-walkthrough/program/iut_compute.py
outputs/check_example_output.txt       python3 scripts/check_example.py
outputs/check_perfactor_output.txt     python3 scripts/check_perfactor.py
outputs/check_nfactor_output.txt       python3 scripts/check_nfactor.py
outputs/example_d109_output.txt        python3 scripts/example_d109.py
LICENSE                                Creative Commons Attribution 4.0 International (CC BY 4.0)
SHA256SUMS                             checksums of the files above
```

## Reproducing

From this folder (Python 3, standard library only; `example_d109.py` also needs sympy, as the walkthrough program
does):

```
python3 scripts/check_example.py   | diff - outputs/check_example_output.txt
python3 scripts/check_perfactor.py | diff - outputs/check_perfactor_output.txt
python3 scripts/check_nfactor.py   | diff - outputs/check_nfactor_output.txt
python3 scripts/example_d109.py    | diff - outputs/example_d109_output.txt
sha256sum -c SHA256SUMS
```

The random samples use fixed seeds, so the outputs are reproduced byte for byte.

## Licence

The files in this folder are licensed under CC BY 4.0 (see `LICENSE`).
