# Changes

## 1.0.1 — 2026-11-08

- Cite earlier work and narrow the sentence on what this report adds (§3): the normalized difference 1/ℓ appears earlier in Takkun-kohinata/IUT_LEAN (15 July 2026, `IdentificationAudit.lean`); sfingali (Zenodo 10.5281/zenodo.21727741, 31 July 2026) computes `s(1−12/ℓ²)`; the χ form is used in Dupuy–Hilado, arXiv:2004.13108v2, §§7.12, 8.6, and Zhou, arXiv:2503.14510v1, Prop. 1.10. What is added is the comparison of the reciprocal factors `F_χ`, `F_τ` and the tables.
- Note in §2 that sfingali (Zenodo 10.5281/zenodo.21757640, 2 August 2026) also observes that the j²-average appears in the computation of Scholze–Stix, and in §4 that sfingali also records the range ℓ ≥ 7 of the two terminal estimates.
- Print the version and the DOIs on the title page; update the README, which still described version 1.0.0 as awaiting approval although it was published (10.5281/zenodo.22659797).

The table values and the program's output are unchanged.

## 1.0.0-draft.2 — 8 September 2026

This revision awaits author verification and approval for publication.

- Add the complete estimate clause from IUT IV, Theorem 1.10, Step (viii), and extend the quotations used to locate the other source passages.
- Clarify that the sufficient coefficient used in IUT IV is compared with the sharp threshold of the specified scalar rearrangement. No priority is claimed for this comparison.
- State the degree restriction in the terminal estimates and retain the distinction between source assertions, deductions, and common-input hypotheses.
- Extend discussion of the difference between scalar expressions and the underlying regions, with the source context stated explicitly.
- Make the arithmetic program reject a missing or changed frozen output file. Require an integer level and anchor the level-three boundary value exactly. These are changes to the checks, not just changes in terminology.

The table values are unchanged. The program's successful output is unchanged. Finite arithmetic checks do not certify all initial-data conditions, source interpretation, or an actual possible-image hull.

## 1.0.0-draft — 8 September 2026

Initial draft prepared for author verification.
