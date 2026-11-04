# The gap between the two walls is positive: a closed form for the (Ind2)-terms of lana-agents/iut

Version 1.0.0, 5 November 2026 (10 pages). DOI [10.5281/zenodo.23954194](https://doi.org/10.5281/zenodo.23954194).

The public Lean formalization [lana-agents/iut](https://github.com/lana-agents/iut) writes the comparison step in the
proof of Corollary 3.12 of IUT III in two forms, a variant of Corollary 3.12, (Var), and the Scholze–Stix inequality,
(SS). It proves that the difference Δ(D) of their right-hand sides is a weighted average of (Ind2)-terms at the bad
residue characteristics, and records as open whether these terms are zero or positive.

This note determines the (Ind2)-terms in closed form: the term equals (ord_p θ − κ_v(θ))·log p, where θ = q̲_v^{j²} is
the theta value and κ_v(θ) is the largest integer k with θ·𝓘_v ⊆ p^k·𝓘_v, 𝓘_v being the log-shell. Consequently the
term is at least frac(ord_p θ)·log p, with equality when p is odd and e_v ≤ p − 2. At a bad place ord_p θ is never an
integer, so Δ(D) > 0 for every initial Θ-datum, and in this formalization (SS) is strictly stronger than (Var). On the
other hand Δ(D) is bounded above by a quantity that does not involve the size of the q-orders, and its average over
the labels is given by the class number of Q(√−ℓ). The values are computed for the six explicit initial Θ-data of the
catalogue in [`../initial-theta-catalogue/`](../initial-theta-catalogue/).

**No claim is made about the truth of (Var), (SS), Corollary 3.12, or the abc conjecture.** The proofs are on paper;
they have not been checked in Lean on top of the definitions of lana-agents/iut.

## Files

```
paper/ind2_gap.pdf               the note
paper/ind2_gap.tex               its LaTeX source, bibliography included
scripts/check_delta.py           the table of Section 5 (lower bounds by fractional parts, upper bounds by the
                                 constants a, b of IUT IV, Proposition 1.2) and the check of Proposition 3.6
scripts/delta2.py                the same lower bounds, with upper bounds from the radii of the log-shells,
                                 place by place
scripts/shell_lattice.py         the log-shell (2p)^(-1) log(1 + m) of Q_p(p^(1/e)) and kappa, in exact rational
                                 arithmetic
scripts/gl_check.py              the span of the GL-orbit of theta * I compared with p^kappa * I (Lemma 4.1,
                                 Example 5.2) for (p, e) = (11, 3), (3, 4), (5, 6)
outputs/check_delta_output.txt   python3 scripts/check_delta.py
outputs/delta2_output.txt        python3 scripts/delta2.py
outputs/gl_check_output.txt      python3 scripts/gl_check.py
LICENSE                          Creative Commons Attribution 4.0 International (CC BY 4.0)
SHA256SUMS                       checksums of the files above
```

## Reproducing

From this folder:

```
python3 scripts/check_delta.py > outputs/check_delta_output.txt
python3 scripts/delta2.py      > outputs/delta2_output.txt
python3 scripts/gl_check.py    > outputs/gl_check_output.txt
cd paper && pdflatex ind2_gap.tex    # run three times
```

`check_delta.py` and `delta2.py` import the program `iut_compute.py` of
[`../iut-walkthrough/program/`](../iut-walkthrough/program/) (Python 3.10 or later, sympy); to use another copy, pass
the folder that contains `iut_compute.py` as the first argument. `shell_lattice.py` and `gl_check.py` use only the
standard library. At the bad places other than those above the special prime of each datum, the ramification index of
`K_v/Q_p` is an assumption of the program (Section 5 of the note); it affects only which places are small and the
upper bounds.
