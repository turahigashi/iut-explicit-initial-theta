# Draft changes

## 0.1.7 — 2026-09-12

**The source application of Theorems `t:cmp` and `t:fix0` is withdrawn.**
Version 0.1.6 stated hypothesis (SA), listed the failure modes (F1)-(F5), and
undertook to withdraw the application if one were established. A direct
re-reading of IUT IV showed that v0.1.6 **did not establish an identification of
the kind (F2) describes**. That undertaking is discharged here. **This is not a
proof that (SA) is false**, nor that no other argument could establish its
inclusion.

Four locators, in the new subsection §7.1 "The withdrawal":

- (W1) IUT IV, Prop. 1.2(iii) bounds `φ(p^λ·S)` with `S = (R_I)~`, and its
  right-hand side is a multiple of `S`. The lattice `L = log_p(R_I^×)` occurs as
  the *intermediate* term of Prop. 1.2(ii), namely
  `φ(p^λ S) ⊆ p^{⌊λ−d_I−a_I⌋} L ⊆ p^{⌊λ−d_I−a_I⌋−b_I} S` — note `−b_I` lies
  **outside** the floor — which Prop. 1.4(iii) also states. The region compared
  in Theorem 5 is `L_t`, i.e. `L` itself, not an input `p^λ S`.
- (W2) Prop. 1.2 defines `φ` as inducing an automorphism of `L`, so the admitted
  automorphisms carry `L` onto itself.
- (W3) Step (v) states that (Ind1),(Ind2) "are taken into account by the
  arbitrary nature of the automorphism φ". We record this as **the source's own
  treatment**; we do **not** identify the typed component transport
  `E_{σ⁻¹t} → E_t` with an automorphism `φ: E_t → E_t`, and do not claim to have
  shown independently that the treatment covers it.
- (W4) The same proof calls λ "asymmetric with respect to the choice of i† in
  S±_{j+1}", symmetrizes, and says this "does not affect the computation of the
  upper bound" — a statement about the **weighted average**, not about an
  individual tuple. Step (v)'s containment is stated for
  `p^{⌊λ⌋−|I|}·2^{−|I|}·L_t` times a nonpositive power of `p`; since
  `d_I + a_I = |I|` here, that exponent equals `⌊λ−d_I−a_I⌋` (2 at `j=1`, 13 at
  `j=2`), so at `k=0` the module named **is** the `p²L_t` of §6.

New in §7.1: **Proposition 7** — with `m = ⌊λ−d_I−a_I⌋` and **`m ≥ 1`** (both
tuples satisfy it: `m = 2`, `13`), `φ(p^λ S) ⊆ p^m L` and `p^m L ⊊ L` hold
simultaneously, so `L ⊄ p^m L` is not a counterexample to the first. Hence **the
lattice noncontainments and numerical comparisons recorded in §6 do not, by
themselves, refute the fixed-input estimates of IUT IV.** It cites only
Prop. 1.2(ii)/1.4(iii) and Prop. 1.2's definition of φ — it does **not** depend
on (W3) or (W4). Remark 9 states its scope: **not** a no-go result for explicit
counterexamples to IUT, not a proof that (SA) is false, not a statement about
IUT III Cor. 3.12 or about abc.

Retained unchanged: Theorem 1 and §§3-4, which never used (SA); and the rational
calculations, whose constants `d_I = 104/105`, `a_I = 106/105`,
`b_I = −106/105`, `λ = 29/7`, `⌊λ−d_I−a_I⌋ = 2` were rechecked against IUT IV,
Props. 1.1, 1.2, 1.4 and found correct. What failed is the identification of
which source quantity they compare with. (F1)-(F5) and §8's question are kept as
the record of the reading that did not hold, with §8's second question no longer
pressed.

§5 now opens by saying that its permutation identities concern the chosen tensor
model and do not assert stability of the actual possible-image family, membership
of the proposed seed, or compatibility with the source's hull evaluation, and
that `T_σ` is not identified with (Ind1) as a whole. Step (v) is cited as
invoking Prop. 1.4(iii); the "weighted average" quotation is from Step (iv).

**Second report 1.0.5 and fourth report 1.0.4** carry a forward reference only.
Both display the values `8/7` and `88/7`; each now states that the first report
has withdrawn that source application in its v0.1.7, points at [First, §7] for
the locators and the scope-limiting proposition, and records that **no statement
of that report used the application**. No numerical value changes and nothing in
either report is withdrawn. The third report (`note6`) and the fifth
(`constant_comparison`) need no note.

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
  relation.  ★The first two drafts of that Remark were wrong; three internal checks
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
