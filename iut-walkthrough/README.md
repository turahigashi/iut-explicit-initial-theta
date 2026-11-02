# A programmer's walkthrough of inter-universal Teichmüller theory

Version 1.0.0, 2 November 2026 (15 pages). DOI [10.5281/zenodo.23880260](https://doi.org/10.5281/zenodo.23880260).

A program, with an interactive web page, that runs on explicit numbers those operations of
inter-universal Teichmüller theory (IUT) that can be written as procedures. Its input is one of the
seven explicit initial Θ-data of the author's catalogue
([doi:10.5281/zenodo.23870448](https://doi.org/10.5281/zenodo.23870448)). It computes the Tate parameters
and local data p-adically, arranges labels and processions, keeps the two Hodge theaters of a Θ-link as
type-separated copies of the local fields so that only a "cable" passes between them, computes log-shells,
Kummer read-outs, containers, possible images and the log-volume of the holomorphic hull of their union
(exactly, in a model in which (Ind2) acts by units, for three readings of the label indeterminacy), and
places side by side the two quantities that Step (xi) of the proof of Corollary 3.12 of IUT III compares.
Infinite objects are computed in finite windows. IPL, SHE and APT (IUT III, Remark 3.11.1) appear as the
shape of the code and as records of its execution; the inference (xi-f) is displayed, not evaluated.

**No conclusion is drawn about Corollary 3.12, Theorem 1.10 of IUT IV, or the abc conjecture.** The
purpose is expository. Turning the objects and processes of IUT into data types, with IPL and APT proved for a
Lean model, has been done earlier and on a broader scale in [motizukipdf](https://github.com/oneman/motizukipdf);
the container formulas and the distinction between the readings are taken from
[lana-agents/iut](https://github.com/lana-agents/iut).
Section 8 of the note gives the related work.

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
opened, and displays whether they agree with the program's output.

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
その入出力・アニメーション・工場の図を持つ一枚の HTML ページ。系3.12・定理1.10・abc 予想については何も結論しない。
プログラムの出力とページは日本語。
