# Draft changes

## 0.6.1 — 2026-09-09

- Title blocks now print the **concept** DOI, which resolves to the latest version.
  The fourth report printed the DOI of its version 1.0.0 on a document that is now
  1.0.3, the third report printed its own 1.0.0, and the second named a "this version"
  DOI that its later versions no longer are.  The fifth report's bibliography was
  already correct: it cites the concept DOI marked "(all versions)" and names the
  consulted version in words.

## 0.6.0 — 2026-09-09

- **Adds the fifth report**: *Two constants in the numerical estimates of inter-universal
  Teichmüller theory IV — 12/(ℓ(ℓ+1)) and 12/ℓ²*.  It locates both constants in the
  sources and compares them with exact rational arithmetic.  The comparison is between
  two scalar expressions under a common set of inputs, stated as a hypothesis; it is not
  a comparison of the two sources' full estimates, and no map identifying their supports,
  positive terms or approximation conventions is given.
- The fifth report cites Joshi, *Construction of Arithmetic Teichmüller Spaces IV*,
  arXiv:2403.10430v2, p. 70, which puts the same rearrangement and the same slack term in
  print; no priority is claimed for either.
- **Corrects the fourth report, §7.**  It called the reciprocal-coefficient display of
  Scholze–Stix "their (1.5)"; that display is unnumbered and follows (1.5).  It also
  printed the relation as ≤, where the source states it in essential approximation and
  the following sentence retains an error.  A sentence claiming that a reading with
  different normalizations "is not available" is withdrawn: the coefficient agreeing does
  not identify the full estimates, their positive or error terms, or their regions.
- **Corrects the third report**: the injectivity proposition now states the hypotheses
  e_g = 1, c_b > 0 and s > 0 that its proof uses, and the log-shell statement assumes
  what the cited definition requires.
- **Neutral naming for abc.**  Five disclaimers said "the abc conjecture is false"; they
  now say "any conclusion about the abc inequality", which is also the wider disclaimer.
  The Scholze–Stix title is a bibliographic fact and is unchanged.
- Scripts shipped with the third and fourth reports describe their checks as an internal
  check.  No computation changes; the frozen outputs are unchanged.

## 0.5.0 — 2026-09-08

- **Citations added.**  The first report (both versions) and the second report now
  cite Zhou, *The inter-universal Teichmüller theory and new Diophantine results over
  the rational numbers. I*, arXiv:2503.14510v1, for constructions of mu_6-initial
  Theta-data over Q, and Dupuy--Hilado §2.10 for the curve 11a1, and say how those
  rational-moduli constructions differ from the mixed-place profile considered here.
  Dupuy--Hilado is now cited by its exact version and date.
- **An overstatement in two abstracts is withdrawn.**  Both said the arithmetic "is
  reproduced by a short script".  Establishing the data also uses a separate
  exhaustive power-freeness certificate, in the second report an exhaustive sieve in
  C++; the abstracts now point to the reproduction section instead.
- **The title blocks are made coherent.**  The second report printed two different
  version numbers, and all three documents printed the build date rather than a
  release date.
- The scripts shipped with the second report describe their own checks as an internal
  check rather than an external review; no computation changes and the frozen output
  is unchanged.
- No numerical value, theorem, proof or verbatim quotation changes.

## 0.4.2 — 2026-09-08

- Corrects a statement about process, not about mathematics.  The fourth report and
  the two scripts shipped with it described the checks that produced several of their
  corrections as `external review`.  No external review took place: the checks are the
  author's own, carried out with the help of language models, and are now described as
  an internal check.  The same wording is being corrected in the second and third
  reports and in the remaining scripts.
- No mathematical statement, number, quotation, locator or manifest entry changes.
  The quotation checker still reports 40 quotations, 25 located in the cited source,
  0 not located there.

## 0.4.1 — 2026-09-08

- **The fourth report now cites Scholze–Stix.**  Its Proposition 10 names the ratio
  `chi = 12/(l(l+1))` between the stage-one and the averaged procession-normalized
  coefficient of [IUT IV, Thm. 1.10].  That is exactly the factor on which [SS]'s final
  inequality (1.5) turns, and [SS] reaches it by averaging with the same coefficient the
  source prints.  The report derived `chi` from the source's own two numbers and cited
  no one; a reader who knows [SS] would see the coincidence at once, so the citation
  belonged there.  §7 now records it, together with the fact that the source's own
  corresponding constant is a **different** one — [IUT IV] uses `12/l^2`, which is larger,
  with slack `1/(2 l^2)`; the source bounds where [SS] computes exactly.
- **This records that the averaging coefficient is common to both sides and the final
  constant is not.  It decides nothing about [IUT III, Cor. 3.12] or about the objection
  of [SS].**
- No other statement of the fourth report changes; the mathematics is unchanged.

## 0.4.0 — 2026-09-08

- Adds the **fourth report**, `fourth-report/`: what the source states about split bad
  primes and the tuple structure, and what follows.  DOI 10.5281/zenodo.22648945.
- **A blanket guarantee is withdrawn.**  An earlier draft of the fourth report claimed that
  no statement in it was conditional on a reading of the source.  It now says that every
  assertion is quoted or proved, that S(R) does not imply R, and states the scope of each
  proposition — a fixed nonarchimedean tuple, a fixed stage.
- Proposition 9 of the fourth report is proved for the holomorphic hull of
  [IUT III, Rem. 3.9.5(i)] **in both of its branches**; an earlier draft identified that hull
  with the module generated by the region, which does not hold in general.
- Corrects three statements in already-published text that claimed more scrutiny than took
  place: the second and third reports said findings came from "external review", when the
  checking was the author's own, carried out with language models as the Disclosure sections
  state.  The word "external" is removed; the findings and the mathematics are unchanged.
- The companion draft `paper/paper.tex` now says what it is: the expanded version of the
  first report, which is the version of record, with its unconditional sections
  distinguished from those that assume (SA).  Its citation label is `[First-full]`
  throughout, replacing `[Full]` and `[FullPaper]`.
- README gains a table mapping each report to its file and DOI.

## 0.3.0 — 2026-09-07

- Adds the **third report**: what each separation drawn in [IUT IV, §1] is worth, in
  exact rationals or exact multiples of log p, at the data of the first two reports and
  at named curves from the literature.  DOI 10.5281/zenodo.22646137.
- `third-report/scripts/costs.py` computes twelve tables from the standard library and
  asserts each conclusion.  Its printed output is held by a frozen presentation
  contract, so a row that changes or vanishes fails rather than passing quietly.
- `third-report/scripts/note6_regression_gate.py` holds **31 named single-token
  defects**, every one of them found by external review and none of them noticed by the
  script as first written; the shipped script rejects all 31.  An absent mutation target
  counts as a failure, never as a silent pass.
- Two attributions corrected in the third report after review: the contrast between
  weighting by local degrees and by ramification indices (§8) and the cap at
  8 = v_2(256) in the two-adic contribution (§12) are this paper's, not the source's.
  The abstract's claim that every distinction measured is one the source itself draws
  now names §8 as its exception.
- **The first and second reports' files are unchanged.**

## 0.2.1 — 2026-09-07

- Corrects one mathematical error in the second report, §9: the ramification indices
  printed for Dupuy–Hilado's curves 11a1 and 37a1 carried over the torsion level 105
  of *this* paper's datum, which those curves do not have.  Since [IUT I, Def. 3.1(b)]
  makes the 2·3-torsion rational over F, at the reference level ℓ = 7 the field K
  contains E[42]; both primes are prime to 42 with Tate orders 5 and 1, so e_b ≥ 42.
  **The exclusions those rows state are unchanged** (42 > 9 and 42 > 35), and the
  datum, its tables, Proposition 2, the fourteen candidate levels and the Lean
  development are untouched.
- Aligns the remaining descriptions of the 89th-power-free certificate with the fact
  that it ships and runs.
- Zenodo 10.5281/zenodo.22634210.

## 0.2.0 — 2026-09-07

- Adds the **second report**: an initial Θ-datum over the imaginary quadratic field
  Q(i) — the curve y² = x(x−1)(x−a) with a = (10+3i)²⁹ and ℓ = 7, at which 109 splits
  into one multiplicative and one good place — and numerical values of the local
  quantities of [IUT IV, Thm 1.10] and [Prop. 1.4(iii)] at that input.
  DOI 10.5281/zenodo.22601335.
- Fourteen Lean files (Init only): 263 stated theorems, 768 declarations, 565
  axiom-free, no `sorryAx`, no `Classical.choice`; audit log included.  Seven of them
  are pinned by SHA-256 to the bytes released with the first report.
- Adds an executable 89th-power-free certificate for the fourteen candidate levels,
  with its own negative control (`--self-test`).
- The first report's files are unchanged.


## 0.1.2-draft — 2026-09-06

- Rechecked every stage-dependent theta depth. The full paper already retained
  j²; made the stage-1 specialization explicit and corrected the first report's
  residual 1/7 claim to 88/7. The equivalent general threshold divides by j².
- Reworked the first report's initial-data verification to retain every selected
  bad place, the compatible marked cover and the exact local torsion field.
- Rewrote the second report with separate statements about nonconstant place
  tuples, mixed reduction, and the distinguished slot's permitted orbit.
- Proved the deterministic nonsplit-selection obstruction and reproduced the
  selected Tate-degree ratio with rigorous rational logarithm intervals.
- Restricted the logarithm-lattice identity to e_i <= p-2 and supplied the tame
  Q_3(zeta_3) counterexample to the broader assertion.
- Matched global Tate degrees to local orders and tuple weights, separating
  the coefficients 1/3, 1/14 and the conditional seed coefficient 1/16.
  Retained 13/48 solely as the coefficient difference of specified bounds.
- Compared the SS exponent diagnosis with the tuple-transport inclusion;
  identified the unproved actual-output comparisons and corrected the scope
  of SS footnote 12. Map types alone do not prove a failed estimate.
- Standardized [S]/[P]/[H] status labels and preserved withdrawal clauses and
  all recorded preparation errors. Added two exact arithmetic certificates.

The full paper is now 22 pages. All three TeX documents were rebuilt and their
PDF pages inspected. The new arithmetic certificates pass; unchanged Lean
proofs and the norm sieve retain their previously verified scope. This remains
a draft with an explicit source-reading hypothesis.

## 0.1.1-draft — 2026-09-06

- Supplied the compatible global quotient, cusp and section in the initial datum,
  the core descent, local covers and the log-theta-lattice construction. Selected
  all multiplicative places outside residue characteristics 2 and 7 and checked
  every required Tate order, including the additional hypotheses of IUT IV.
- Added the exact torsion-field equality and both ramification bounds proving
  `e_b=105`. Cited the semistability criterion in IUT IV Proposition 1.8(v).
- Restored the floor functions in Proposition 1.4(iii), distinguished tameness
  from `e_i <= p-2`, and supplied the sources for the different and logarithm
  constants. The conditional local margin remains `8/7`.
- Corrected the degree factorization to `46080=2^10*3^2*5`, the first exceptional
  j-invariant to `2^14*31^3/5^3`, and the reduction argument using `c_4`.
- Expanded the native-ideal, integral-lattice and whole-procession transport
  steps supporting (SA), preserving it as the single source-reading hypothesis.
- Derived the normalized tuple weights and the final local expression directly
  from the specified source passages. Replaced rounded inequalities with exact
  rational bounds.
- Added the complete Hensel/CRT and elementary sieve proof for the separate
  N=211 existence family in Appendix D, together with finite CRT checks and an
  exhaustive norm certificate for the explicit N=29 datum.
- Checked all bibliography entries and citation occurrences against the specified
  source versions. Added nine verified DOIs and clarified author-version versus
  publication metadata. Unquoted source descriptions are identified as paraphrases.
- Limited the public Lean comments to the finite model actually proved, and
  printed the axiom dependencies of all nine theorems. The proof terms are unchanged.
- Retained the scope restrictions, F1–F4, the F2 withdrawal commitment and all
  three recorded preparation errors. Distinguished numerical checks, cited
  geometric results, the source reading and independent human review.

The accompanying PDF is a 21-page draft. Arithmetic, the norm sieve, the CRT
checks, all nine Lean theorems and two consecutive LaTeX runs passed. The final
PDF was visually inspected on every page. This audit does not turn (SA) into an
unconditional theorem or establish a global contradiction.

## 0.1.3-draft (2026-09-07)

Version DOI 10.5281/zenodo.22544085.  Concept DOI 10.5281/zenodo.22537342 resolves
to the latest version.

- ★Added the two references we had missed at the first deposit, and a Remark on the
  relation.  ★The first two drafts of that Remark were wrong; three independent audits
  found six errors, each confirmed verbatim against the sources.

  Round 1 (four errors):
  - "the same object as (SA4) and (F2)" -- LANA's goal (9-1) is whether the rigidified
    q-pilot is represented in the output regions (§9.2-§9.3); (SA4) is about which
    regions the union contains.  The corresponding place in LANA is §10.4.
  - ★"does not consider a rational prime with several places, so the configuration does
    not arise there" -- **false**: LANA §5.2(a) sets
    K_{S_{j+1},v} = (⊗_t ⊕_{w|v_Q} K_{t,w}) ⊗ K_{j,v}.  Our word search missed it
    because they write "⊕_{w|v_Q}" and never "tuple" or "split".
  - ★★identifying the transport of (SA3) with the algorithmic parallel transport (APT)
    of IUT III Rem 3.11.1(iv).  Removed.
  - a convergence paragraph that read as corroboration of (SA).  Removed.

  Round 2 (two further errors, introduced by the first correction):
  - ★★★"the two cannot both stand as written" -- **a logic error**.  Theorem 4 is
    conditional; SA => D is compatible with not-D, which yields not-SA.  There is no
    contradiction, only a falsifier.  Also, the regions, transports, hull and readout
    of LANA were never identified with the fixed component used here, so the two
    accounts are not yet about the same objects.
  - ★reading Rem 3.11.1(iv) as prohibiting the component map tau.  The remark is about
    the transport *mechanism* being an algorithm valid on both sides of the Theta-link;
    tau maps between summands of one fixed ambient object on one side.  We neither
    borrow the name nor read the remark as a prohibition.

- ★★(F5) is now stated as a two-part conditional cross-check, not a contradiction:
  the identification must be supplied *and* the locality statement must hold; then
  (SA) fails and the source application -- not the rational calculation -- is withdrawn.
- ★An exact point of contact: LANA's LGP element (§5.2(f)) carries the 2l-th root
  double-underline q_v^{j^2} in the distinguished slot alone and 1 in every other slot,
  the same shape as the reading of Step (v) used here.
- "3.11.5" is recorded as an explanatory label; [Form] states it does not appear in the
  four IUT papers.
- Title block now carries the concept DOI 10.5281/zenodo.22537342 (all versions).
  Version 1 (10.5281/zenodo.22537343) is unchanged and remains the record of what was
  circulated on 2026-09-06.  ★No auditor asked for its withdrawal.
