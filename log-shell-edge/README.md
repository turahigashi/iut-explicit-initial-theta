# How far automorphisms of a p-adic absolute Galois group move the ring of integers: to the edge of the log-shell, with an application to Step (v) of IUT IV

Version 1.0.0, 8 November 2026 (19 pages). DOI [10.5281/zenodo.24050445](https://doi.org/10.5281/zenodo.24050445).

Let p be an odd prime and K/Q_p a finite extension with ramification index e ≤ p − 2. A continuous automorphism α of
the absolute Galois group G_K induces, through the mono-anabelian reconstruction, a Q_p-linear automorphism α_+ of K,
which preserves Λ = log U¹_K = 𝔪_K and the log-shell 𝔪_K^(1−e) but in general not the ring of integers 𝒪_K. The note
shows that for every integer m the Z_p-module spanned by all images of 𝔪_K^m is 𝔪_K^lo(m), where lo(m) is the largest
integer ≤ m congruent to 1 modulo e: the trivial upper bound from the invariance of Λ is attained, and the images of
𝒪_K span the whole log-shell.

For even degree, and for odd degree with residue degree at least 2, this follows from Kondo's description of the
kernel of the trace and Kondo's transvections, the preservation of traces shown by Hoshi–Nishio, and automorphisms of
free groups that mix the pairs of the Jannsen–Wingberg presentation. In odd degree with total ramification everything
is decided by one line in Λ/pΛ; to move it, the note constructs an automorphism of G_K modulo the third term of the
descending p-central series of the wild inertia group that shifts the generator x_1 towards x_2, and lifts it by
Wingberg's lifting theorem (Neukirch–Schmidt–Wingberg, (7.5.15)). As a by-product, for every finite extension k/Q_p of
odd degree d ≥ 3 there is an automorphism with α_+(y_1) ≠ y_1, the element whose existence Kondo left open in Remark
1.10 of arXiv:2512.09231; there are also automorphisms that move (Q_p)_+ ⊂ k.

Application: in Step (v) of the proof of IUT IV, Theorem 1.10, at small places the actual (Ind1), (Ind2) always reach
the exact hull p^(⌈λ⌉ − 𝔡_I)·(R_I)^∼ of [`../three-tiers/`](../three-tiers/); the hypotheses λ ∈ Z and (U) of that note
are not needed. Among the bad places of the explicit initial Θ-datum D109, the one above 534775081 is of the
odd-degree, totally ramified kind.

Relation to earlier work, in short: the induced maps α_+ and the fact that the ring of integers is not group-theoretic
are due to Hoshi; the preservation of traces to Hoshi–Nishio; the description of the kernel of the trace, the
transvections, Sp_2g(Z_p) in the image, and the question of Remark 1.10 to Kondo (arXiv:2512.09231, arXiv:2605.25428,
which proves the Hodge–Tate consequence in odd degree by a Haar-measure argument without explicit automorphisms); the
presentation to Jannsen–Wingberg; the lifting theorem to Wingberg, as stated in NSW, who use it for G_Q_p, and which
Nishio (arXiv:2609.19696) uses for finite subgroups acting on the pairs (x_2, x_3), … . The note uses these and adds
the exact lattice computation, the shift of x_1 at the third level, and the application to Step (v).

**No claim is made about the truth of Corollary 3.12 of IUT III or of the abc conjecture.** The proofs are on paper;
nothing is formally verified, and the author's own reading of the proofs is still in progress. This folder contains no
Lean code.

## Files

```
paper/log_shell_edge.pdf             the note
paper/log_shell_edge.tex             its LaTeX source, bibliography included
scripts/check_free_group.py          Section 4: the free-group identities (Z, H, J, the swap of pairs and their
                                     inverses, the boundary words, M(a) = a) and the abelianization matrices
scripts/check_lemma52.py             Lemma 5.2: the determinant of the d images is -u^d (d = 2, ..., 12)
scripts/check_group_ring.py          steps (2)-(4) and (6) of the proof of Theorem 6.5 in finite models (25 pairs of
                                     a metacyclic group of order 4 to 27 and a nontrivial character)
scripts/example_d109.py              Example 7.3, reading the place data of D109 from
                                     ../iut-walkthrough/program/iut_compute.py
outputs/check_free_group_output.txt  python3 scripts/check_free_group.py
outputs/check_lemma52_output.txt     python3 scripts/check_lemma52.py
outputs/check_group_ring_output.txt  python3 scripts/check_group_ring.py
outputs/example_d109_output.txt      python3 scripts/example_d109.py
LICENSE                              Creative Commons Attribution 4.0 International (CC BY 4.0)
SHA256SUMS                           checksums of the files above
```

## Reproducing

From this folder (Python 3, standard library only; `example_d109.py` also needs sympy, as the walkthrough program
does):

```
python3 scripts/check_free_group.py | diff - outputs/check_free_group_output.txt
python3 scripts/check_lemma52.py    | diff - outputs/check_lemma52_output.txt
python3 scripts/check_group_ring.py | diff - outputs/check_group_ring_output.txt
python3 scripts/example_d109.py     | diff - outputs/example_d109_output.txt
sha256sum -c SHA256SUMS
```

The random samples use fixed seeds, so the outputs are reproduced byte for byte. The paper is built with pdflatex
(three runs) from `paper/log_shell_edge.tex`.

## Licence

The files in this folder are licensed under CC BY 4.0 (see `LICENSE`).
