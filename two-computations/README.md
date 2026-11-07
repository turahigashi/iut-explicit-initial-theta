# Two computations of the height inequality and the multiradial algorithm: reading IUT from the viewpoint of computer science

Version 1.1.0, 8 November 2026 (30 pages). DOI [10.5281/zenodo.24039369](https://doi.org/10.5281/zenodo.24039369).
Version 1.0.0: [10.5281/zenodo.23968299](https://doi.org/10.5281/zenodo.23968299).

**Changes in 1.1.0.** Cites earlier work that version 1.0.0 did not cite: the toolkit motizukipdf of D. Richards
(GitHub, October 2026), which already turns the objects and processes of IUT into C data types, a WebAssembly
application and a Lean port, with the constants of Theorem 1.10 of IUT IV, a numerical form of Step (xi) (`Fuzzify`),
`dsc_APT`, and the constant c_ℓ of observation (iv) (`corThreeTwelve_unfolded`); and Takkun-kohinata/IUT_LEAN (GitHub,
15 July 2026), which proves in Lean, for one reading, points (1) and (4) of the argument. Narrows "what this note adds"
accordingly. Attributes the folding of observation (ii), with the coefficients (ℓ+5)/4 and (ℓ+1)/24, to the proof of
Theorem 1.10 of IUT IV itself (Step (v); Remark 1.10.1), with Dupuy–Hilado as a later rederivation. Adds the author's
first to fifth reports to Table 1, and cross-references to the fourth and fifth reports (observation (iv)), to *Where
Theorem 3.11 sits* (§6.3), to *Fourteen initial Θ-data on one curve over Q(i)* (that D2357 is an initial Θ-datum; its
values remain conditional because the places above the unfactored cofactor are not counted), to Higuchi and Pajo, and to
Geiger's Bridge-Contract Criterion (IV takes the conclusion of Corollary 3.12 as an input). Corrects the description of
the 36 readings (lana-agents/iut supplied some of the axes; it did not list readings), the wording of the abstract on
what lana-agents/iut states (it has not shown that Step (xi) fails for a genuine datum), the words for the ratio in
observation (iv), the description of Zhou's code (the C++ is that of Part II), and adds the missing entry for IUT I and
the definitions of M, ρ̄_p and ℓ*. The programs, their outputs and all numbers are unchanged.

This note contains almost no new mathematical results. It is an essay that proposes a viewpoint: to read
inter-universal Teichmüller theory (IUT) from the side of computer science, by placing the classical computation of the
height inequality and the computation of IUT side by side as two programs that read the same input. In each of the 36
readings of [`../reading-family/`](../reading-family/), Corollary 3.12 of IUT III and Theorem 1.10 of IUT IV together
give the same height inequality (k − 1)|log q| ≤ C, which is written in classical quantities only and can be computed
for a given curve without IUT. What IUT has to add is the "for every initial Θ-datum" of Corollary 3.12, and what is
supposed to supply it is the multiradial algorithm of Theorem 3.11. The note takes the position that this algorithm is
the essence of IUT, and that one has not understood IUT essentially unless it has been elucidated and implemented.

The folder contains two C programs (the classical computation, and the computation of IUT in the reading of IUT IV) and
a C++ mockup of the multiradial algorithm. In the mockup, the parts that can be implemented at present are implemented
(the local invariants from the abstract group G_{K_v}^ab, the log-shells, Kummer classes at a finite level, cyclotomic
rigidity from the commutator in a theta group, the labels and tuples of the tensor packets, the hull of the possible
images), and the rest is left as named oracles: `[gab]`, `[global]`, `[kummer]`, `[theta-group]`, `[ind3]` and
`[step-xi]`. **The values of the oracles are reverse-computed** from the ring structure of a theater or, for
`[step-xi]`, from the conclusion itself; the code, the output and a ledger at the end of the output say so. The
implemented part is separated by its headers so that it cannot read the ring structure of a theater (`make check`
follows the headers transitively), and its output does not depend on the coordinates that a theater hides.

**No claim is made about the truth of IUT, of Corollary 3.12, or of the abc conjecture.** The output of the mockup
proves nothing. The 36 readings are the combinations of the axes found so far, not a classification of all readings,
and the C programs and the mockup implement only the reading of IUT IV.

## Files

```
paper/two_computations.pdf      the note
paper/two_computations.tex      its LaTeX source, bibliography included
paper/generated.tex             the tables and numbers of the note (written by make_generated.py)
paper/excerpt_data_D211.txt     the excerpts of the data and the code shown in the note (written by make_generated.py)
paper/excerpt_iut_core.c
paper/excerpt_box.hpp
paper/excerpt_rigidity.cpp
paper/excerpt_stepxi.cpp
paper/make_generated.py         writes generated.tex and the excerpts from c/, cpp/ and outputs/
c/localdata.h                   reads a datum file
c/classical.c                   the classical computation, from the statement of Theorem 1.10 of IUT IV alone
c/iut.c                         the computation of IUT in the reading of IUT IV
c/Makefile                      make (gcc -O2 -Wall -Wextra -std=c11)
cpp/                            the mockup of the multiradial algorithm (16 files, 1,170 lines): make; make check
data/D*.txt                     the local data of the seven initial Theta-data, the common input of all programs
scripts/export_local_data.py    writes data/ from ../reading-family/scripts and checks it against the walkthrough
scripts/check_c.py              compares the C programs with the Python programs of ../reading-family/ (119 items)
scripts/check_cpp.py            compares the mockup with the C programs (204 items), runs make check and the scans
scripts/run_all.sh              builds the programs, rewrites outputs/ and runs all the checks
outputs/classical_D*.txt        c/classical data/D.txt
outputs/iut_D*.txt              c/iut data/D.txt
outputs/mockup_D*.txt           cd cpp && ./mockup ../data/D.txt
outputs/selftest_D*.txt         cd cpp && ./mockup --selftest ../data/D.txt   (non-interference)
outputs/scan40_D*.txt           cd cpp && ./mockup --scan ../data/D.txt 40    (the family q -> q^N, six data)
outputs/scan_D211.txt           cd cpp && ./mockup --scan ../data/D211.txt 20
outputs/export_local_data.txt   python3 scripts/export_local_data.py ../reading-family/scripts <folder>
outputs/check_c.txt             python3 scripts/check_c.py ../reading-family/scripts c data
outputs/check_cpp.txt           python3 scripts/check_cpp.py
LICENSE                         Creative Commons Attribution 4.0 International (CC BY 4.0)
SHA256SUMS                      checksums of the files above
```

## Reproducing

From this folder, with gcc, g++, Python 3.10 or later and sympy:

```
scripts/run_all.sh
cd paper && python3 make_generated.py && pdflatex two_computations.tex    (run pdflatex three times)
```

`run_all.sh` takes about eight minutes on the author's machine, most of it the selftests and scans of the mockup. It
needs the folder `../reading-family/scripts` of this repository (version 0.17.0), whose programs
`export_local_data.py` and `check_c.py` import; it checks that `export_local_data.py` reproduces `data/` exactly.
The outputs are deterministic, and a rerun reproduces `outputs/` byte for byte. The compiled programs are not included.
The C programs compile with `gcc -O2 -Wall -Wextra -std=c11` and the mockup with
`g++ -std=c++17 -O2 -Wall -Wextra -pedantic`, both without warnings. For D2357 (ℓ = 157) the places above an
unfactored cofactor of 1564 digits are not counted, and its values are conditional.
