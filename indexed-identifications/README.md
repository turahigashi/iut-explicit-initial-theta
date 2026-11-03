# Reading the IUT dispute through indexed identifications: an educational model in undergraduate mathematics

Version 1.0.0, 4 November 2026 (16 pages). DOI [10.5281/zenodo.23931346](https://doi.org/10.5281/zenodo.23931346).

An educational model that states the shape of the dispute over Corollary 3.12 of IUT III using only undergraduate
mathematics: sets and maps, multiplication of positive real numbers, graphs and inequalities. Instead of the equality
sign it uses a symbol x ≈_f y that records which identification is used, with four rules declared at the outset.
Mochizuki's own elementary numerical model and the three options described by Scholze–Stix then sit on one
inequality, (k−1)Q ≤ E. The note separates what is agreed from what is disputed, and does not decide the latter. It
ends with exercises and their answers. Each statement carries a label (S, P, R, N, H).

**No claim is made about the truth of Corollary 3.12, Theorem 1.10 of IUT IV, or the abc conjecture.**

The companion paper, which states the same model in homotopy type theory and checks its quantitative core in Lean, is
in [`../segment-or-loop/`](../segment-or-loop/) (DOI
[10.5281/zenodo.23931344](https://doi.org/10.5281/zenodo.23931344)).

## Files

```
paper/indexed_identifications.pdf    the note
paper/indexed_identifications.tex    its LaTeX source, bibliography included
LICENSE                              Creative Commons Attribution 4.0 International (CC BY 4.0)
SHA256SUMS                           checksums of the files above
```

The note builds with `pdflatex indexed_identifications.tex` (run three times).
