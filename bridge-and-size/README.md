# Bridge and size: the Kodaira–Spencer morphism, arithmetic derivatives and Step (xi) of IUT as lax 2-cells

Version 1.1.0, 8 November 2026 (22 pages). DOI [10.5281/zenodo.24039372](https://doi.org/10.5281/zenodo.24039372).
Version 1.0.0: [10.5281/zenodo.23984201](https://doi.org/10.5281/zenodo.23984201).

**Changes in 1.1.0.** Cites the earlier use of the word "bridge" for the same inclusion of Step (xi): Higuchi
("numerical bridge statement", ResearchGate, 31 March 2026), Pajo ("bridge certificate", ResearchGate, 26 April 2026)
and Geiger (*The Bridge Certificate*, Zenodo, 13–14 August 2026; *The Bridge-Contract Criterion*, Zenodo, 16 August
2026). Cites the earlier assignment for IUT (the load of the theta values is quantified in IUT IV, while the inclusion
is not derived) in Geiger's Bridge-Contract Criterion (§6.2, rows F-R4a, F-R4b, F-R6b) and in Takkun-kohinata/IUT_LEAN
(15 July 2026, observation (F4)), and replaces the sentence that this assignment had not been found. Cites Laniewski and
Müller (arXiv:2610.26490, 19 October 2026: the derivation gives no bound on the quality by itself), the word "wall" of
the interim report of Project LANA, and two related Lean files of lana-agents/iut (`Iut/Abc/FunctionFieldSzpiro.lean`,
`Iut/Abc/P24Table.lean`, 14 October 2026). Corrects the abstract and §7.2: ℓ times the wall is below the constant C of
IUT IV on the six completely factored data (0.36 to 0.92 of C) and exceeds it after replacing q by q^N for N ≥ 3.
Uses "size" in the sense of Definition 2.1 only (IUT has a bound on the blurring, not a size); corrects "only two ways"
(three are listed), restores "(in the model)" in §1.1, states Pasten's Corollary 4.6 as its two implications, and adds
"with q prime" to the exceptional triples of Pasten's conjecture. Updates the citation of *Segment or loop?* to version
1.3.0 and adds a cross-reference to *Where Theorem 3.11 sits* (Theorem 10, Corollary 11, Theorem 22). The script, its
output and the tables are unchanged.

This note is an essay that proposes a viewpoint; it contains almost no new mathematical results. In function fields,
the height inequality follows from the Kodaira–Spencer morphism. The note places this classical argument, the
"bridges" built in number fields from an additive relation a + b = c (the p-adic logarithms of Baker's method and the
arithmetic derivatives of Pasten), and Step (xi) of the proof of Corollary 3.12 of IUT III side by side in the form of
the lax 2-cells of [*Segment or loop?*](../segment-or-loop/).

The difficulty splits into a *bridge* (that a 2-cell exists) and a *size* (the blurring that must be allowed). This
restates, in the language of lax 2-cells, two requirements stated by Mochizuki himself (in his slides on the classical
roots of IUT): a common container large enough to house both sides, and small enough to yield a nontrivial estimate.
In function fields both are automatic; a bridge from an additive relation exists unconditionally, but bounding its
size is equivalent to the abc conjecture (Pasten); in IUT the blurring is small by IUT IV, while the bridge (the
inclusion of Step (xi)) is not derived in the written argument. A bridge from an additive relation does not cross the
Θ-link: carrying it across gives, on the seven explicit initial Θ-data of
[`../two-computations/data/`](../two-computations/data/), a discrepancy at the level of units whose absorption by
blurring needs exactly ℓ times the wall (k − 1)Q of Corollary 3.12. The curves on which isogenies give a bridge are
excluded from the initial Θ-data by Definition 3.1 (c) of IUT I. The reading of the note is that the ring structure
(in particular, the addition) that IUT gives up in order to circumvent the absence of a global multiplicative subspace
is precisely the material of a Kodaira–Spencer-type bridge.

**No claim is made about whether IUT is correct.** The propositions of the note are classical or elementary; the
dichotomy is an analogy, not a theorem.

## Files

```
paper/bridge_and_size.pdf     the note
paper/bridge_and_size.tex     its LaTeX source, bibliography included
paper/generated.tex           the DOI, Tables 4.1 and 7.1 and the numbers of the text (written by make_generated.py)
paper/make_generated.py       writes generated.tex from scripts/bridge_lib.py
scripts/bridge_lib.py         Table 4.1 (four abc triples: the p-adic logarithm of the ratio, from the series) and
                              Table 7.1 (seven initial Theta-data: the depth of the additive bridge, the gaps, and the
                              label-averaged sum, which is checked to be exactly ell times the wall (k - 1)Q)
data/D*.txt                   the local data of the seven initial Theta-data (the same files as
                              ../two-computations/data/)
outputs/bridge.txt            python3 scripts/bridge_lib.py
LICENSE                       Creative Commons Attribution 4.0 International (CC BY 4.0)
SHA256SUMS                    checksums of the files above
```

## Reproducing

```
python3 scripts/bridge_lib.py > outputs/bridge.txt
cd paper && python3 make_generated.py && pdflatex bridge_and_size.tex && pdflatex bridge_and_size.tex && pdflatex bridge_and_size.tex
```

From a clean folder, LaTeX needs three runs before the table of contents settles.

The scripts use the Python 3 standard library only. The values of the wall (k − 1)Q and of Q agree with the output of
the programs of [`../two-computations/`](../two-computations/). The quotations in the note are taken from the English
originals; mathematical symbols and decorations were checked on the page images.

The files in this folder are licensed under CC BY 4.0.
