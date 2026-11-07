# A programmer's walkthrough of inter-universal Teichmüller theory

Version 1.2.0, 8 November 2026 (18 pages). DOI [10.5281/zenodo.24039375](https://doi.org/10.5281/zenodo.24039375).
Version 1.1.0: [10.5281/zenodo.23955994](https://doi.org/10.5281/zenodo.23955994); version 1.0.0:
[10.5281/zenodo.23880260](https://doi.org/10.5281/zenodo.23880260).

A program, with an interactive web page, that runs on explicit numbers those operations of
inter-universal Teichmüller theory (IUT) that can be written as procedures. Its input is one of the
seven explicit initial Θ-data of the author's catalogue
([doi:10.5281/zenodo.23870448](https://doi.org/10.5281/zenodo.23870448)). It computes the Tate parameters
and local data p-adically, arranges labels and processions, keeps the two Hodge theaters of a Θ-link as
type-separated copies of the local fields so that only a "cable" passes between them, computes log-shells,
Kummer read-outs, containers, possible images and the log-volume of the holomorphic hull of their union,
for three readings of the label indeterminacy and two models of the indeterminacy (Ind2): multiplication by
units, and all ℤ_p-linear automorphisms of the log-shells of the factors as in lana-agents/iut, for which the
hull is given by the closed form of the author's note
([doi:10.5281/zenodo.23954194](https://doi.org/10.5281/zenodo.23954194)), exact where p is odd and e ≤ p − 2
and bracketed elsewhere. It places side by side the two quantities that Step (xi) of the proof of
Corollary 3.12 of IUT III compares.
Infinite objects are computed in finite windows. IPL, SHE and APT (IUT III, Remark 3.11.1) appear as the
shape of the code and as records of its execution; the inference (xi-f) is displayed, not evaluated.

Version 1.1.0 adds the second model of (Ind2). In the reading of IUT IV the two models give the two forms of
the comparison that lana-agents/iut calls the Scholze–Stix inequality and the variant of Corollary 3.12, and
the program computes their difference Δ(D) for each datum and reading (Table 4 of the note).

**No conclusion is drawn about Corollary 3.12, Theorem 1.10 of IUT IV, or the abc conjecture.** The
purpose is expository. Turning the objects and processes of IUT into data types, with IPL and APT proved for a
Lean model, has been done earlier and on a broader scale in [motizukipdf](https://github.com/oneman/motizukipdf);
the container formulas and the distinction between the readings are taken from
[lana-agents/iut](https://github.com/lana-agents/iut).
Section 8 of the note gives the related work.

## Changes in version 1.2.0

Cites earlier work: [Takkun-kohinata/IUT_LEAN](https://github.com/Takkun-kohinata/IUT_LEAN) (15 July 2026), which
proved in Lean, in its model, the reduction of Step (xi) to (s − 1)|log q| ≤ L with a ledger L of local terms in
place of the container volume V (Introduction and Section 3.7); and the Lean models of Hodge theaters, the Θ-link
and the log-link in lana-agents/iut (12 October 2026), in which Theorem 3.11, as formalized there, holds
(`thm311_full_model`, 13 October 2026; "What is not new"). Adds pointers to the author's fourth report: by its
Proposition 9, which uses Minamide–Tsujimura (RIMS-1973, Theorem F), the group Ism through which IUT III,
Theorem 3.11(i), describes (Ind2) is ℤ_p^× at a finite extension of Q_p and acts by unit scalars, as in the first
model (Sections 3.6 and 7); by its Section 6, fixing D_0 does not by itself fix the label 0 inside the larger
capsules (Section 2.3). Replaces the outdated sentence in the caption of Table 3: that D_2357^(157) is an initial
Θ-datum satisfying the hypotheses of IUT IV, Theorem 1.10, is proved in
[fourteen-levels](../fourteen-levels/) (Theorem 2.1); its values remain lower bounds. The program, its outputs, the
page and the tables are unchanged.

## Files

```
paper/iut_walkthrough.pdf      the note
paper/iut_walkthrough.tex      its LaTeX source, bibliography included
paper/fig/fig1.png, fig2.png   the two figures (screenshots of the page)
program/iut_compute.py         the program (Python 3.10 or later, sympy); its output is in Japanese
outputs/out_all_V.txt          python3 iut_compute.py --all --reading V
outputs/out_all_L.txt          python3 iut_compute.py --all --reading L
outputs/out_all_L0.txt         python3 iut_compute.py --all --reading L0
outputs/out_D2_toys.txt        python3 iut_compute.py --data D2 --toys
outputs/out_windows_D2.txt     python3 iut_compute.py --windows --data D2
outputs/out_windows_D211.txt   python3 iut_compute.py --windows --data D211
outputs/out_windows_D2357.txt  python3 iut_compute.py --windows --data D2357
outputs/run_data.json          python3 iut_compute.py --export-json run_data.json (embedded in the page)
page/iut-walkthrough.html      the interactive page (one file, Japanese; open it in a browser)
LICENSE                        Creative Commons Attribution 4.0 International (CC BY 4.0)
SHA256SUMS                     checksums of the files above
```

The page recomputes the containers, shrinkages and outcomes in exact rational arithmetic each time it is
opened, in both models of (Ind2), and displays whether they agree with the program's output.

## The animation tab

The composition of the animation tab follows the animation *The Multiradial Representation of
Inter-universal Teichmüller Theory* by Etienne Farcot, made from the specifications of Shinichi Mochizuki
and suggestions of Ivan Fesenko, licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) and available from
<https://www.kurims.kyoto-u.ac.jp/~motizuki/research-english.html>. The pictures and motions are new; the
numbers, colours and sizes and the positions on the number lines come from the computation. This
adaptation is not endorsed by the authors of the original.

## 日本語の概要

IUT のうち手続きとして書ける操作を、具体的な初期Θデータ（著者の一覧の 7 つ）の上で実際に走らせるプログラムと、
その入出力・アニメーション・工場の図を持つ一枚の HTML ページ。版 1.1.0 で、不定性 (Ind2) の二つ目の模型
（各因子の log-殻の ℤ_p 格子自己同型すべて）と、比較の二つの形の差を加えた。系3.12・定理1.10・abc 予想については何も結論しない。
プログラムの出力とページは日本語。
