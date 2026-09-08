# Two constants in the numerical estimates of IUT IV

Version 1.0.0-draft.2, 8 September 2026. Prepared for author verification; publication has not been approved.

This fifth report compares `12/(ell*(ell+1))` and `12/ell**2`, keeping the other inputs fixed. It gives exact rational tables at levels 7 and 157. The latter is retained as a candidate level in the cited second report. The comparison does not establish applicability of either source's full inequalities, a possible-image hull, or a conclusion about IUT or the Scholze–Stix objection.

The manuscript and PDF are in `paper/constant_comparison.tex` and `paper/constant_comparison.pdf`. Large language models assisted drafting, source comparison, and computations. The checks described here are internal checks.

## Reproduce the arithmetic

Run from the extracted directory with Python 3.8 or later:

```sh
python3 scripts/constant_comparison.py
```

The standard-library program uses exact fractions, evaluates finite sums at 99 odd levels from 5 through 201, and checks the six printed table rows. A successful run ends with `RESULT: PASS` and `EXIT:0`. The program also requires `scripts/constant_comparison_output.txt` and rejects any difference from the computed output, including a changed line or a missing file. This establishes consistency of the supplied artifacts, not their authenticity. Optimization flags `-O` and `-OO` are rejected. Level 5 is an algebraic boundary check and is outside the IUT IV theorem's permitted prime range.

These finite checks supplement the written proofs. They do not certify the interpretation of source statements, initial-data admissibility, or omitted error terms.

## Locate the short quotations

Obtain the English source PDFs separately, under the names and SHA-256 values specified in `scripts/quotes_manifest.json`. The quotation sources are Mochizuki's IUT I (May 2020 author version), IUT IV (April 2020 author version), his September 2018 comments on Scholze–Stix, and Scholze–Stix, *Why abc is still a conjecture* (16 July 2018). The bibliography gives publication information; the manifest identifies the actual author versions used.

With `pdftotext` installed, run:

```sh
python3 scripts/note3_quotes.py --sources /path/to/source-pdfs --manifest scripts/quotes_manifest.json --paper paper/constant_comparison.tex
```

The expected result is five `CANDIDATE` entries and no `NOCHECK`. Inspect Scholze–Stix p. 4, IUT IV p. 30, IUT I p. 62, and comment (C14), p. 4, together with their surrounding text. All five passages were inspected during the internal checks; author verification remains pending.

The locator drops mathematics and punctuation, permits intervening words, and examines only the quotations listed in the manifest. A coordinated change to a formula in both the manuscript and manifest, removal of a qualifying clause, or deletion of a quotation from both can escape detection. `NOCHECK` is a warning and does not make the process exit with failure. A candidate match is not a certificate of verbatim identity, complete claim coverage, or mathematical implication.

## Build the PDF

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error constant_comparison.tex
pdflatex -interaction=nonstopmode -halt-on-error constant_comparison.tex
```

The supplied PDF has seven pages. Rebuilding may change PDF metadata and byte checksums even when the visible text is unchanged. Source PDFs are not included in this bundle.

## Contents

This bundle contains nine files: `LICENSE`, `README.md`, `CHANGELOG.md`, the manuscript and PDF under `paper/`, and the arithmetic program, frozen output, quotation locator, and quotation manifest under `scripts/`. The change history distinguishes revisions to the checks from revisions to the prose.

Copyright 2026 Toshihisa Urahigashi. Licensed under the Apache License, Version 2.0; see `LICENSE`.
