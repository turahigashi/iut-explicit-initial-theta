import LogShellEdge

/-!
# Axiom check for the main results

Run `lake env lean Verify.lean` after `lake build`. Every line should report only (a subset of)
`propext`, `Classical.choice` and `Quot.sound`. The cited inputs are hypotheses of the theorems, not
axioms; see `README.md` for the list of inputs.
-/

-- Lemma 2.2(a)(b): `μ_p ⊄ K`, `U¹` torsion-free, `log : U¹ → 𝔪` bijective and norm-preserving
#print axioms LogShellEdge.SmallLog.mu_p_not_subset
#print axioms LogShellEdge.SmallLog.eq_one_of_pow_eq_one
#print axioms LogShellEdge.SmallLog.eq_one_of_pow_prime_pow_eq_one
#print axioms LogShellEdge.SmallLog.norm_log1p_eq
#print axioms LogShellEdge.SmallLog.log1p_bijOn
#print axioms LogShellEdge.SmallLog.log_hom_on_ball
#print axioms LogShellEdge.SmallLog.padic_mu_p_trivial

-- Proposition 2.5: the upper bound and the periodicity
#print axioms LogShellEdge.upper
#print axioms LogShellEdge.S_le_lo
#print axioms LogShellEdge.S_shift
#print axioms LogShellEdge.reaches_shift
#print axioms LogShellEdge.S_eq_of_period
#print axioms LogShellEdge.reaches_of_period

-- Lemma 3.2 (module computation) and Lemma 3.4
#print axioms LogShellEdge.ShearRelation.isUnit_of_relation
#print axioms LogShellEdge.lemma32_core
#print axioms LogShellEdge.lemma34

-- Lemma 4.1 (group-theoretic part), Lemmas 4.2 and 4.3
#print axioms LogShellEdge.lemma41_descends
#print axioms LogShellEdge.fixes_relation
#print axioms LogShellEdge.FG.mulAE_cmt
#print axioms LogShellEdge.FG.mulBE_cmt
#print axioms LogShellEdge.FG.pairSwap_delta
#print axioms LogShellEdge.FG.vecN_pairSwap
#print axioms LogShellEdge.ShearFreeGroup.Z_delta
#print axioms LogShellEdge.ShearFreeGroup.H_delta
#print axioms LogShellEdge.ShearFreeGroup.J_delta
#print axioms LogShellEdge.ShearFreeGroup.M_a
#print axioms LogShellEdge.ShearFreeGroup.M_delta
#print axioms LogShellEdge.ShearFreeGroup.M_ab
#print axioms LogShellEdge.FG.evenU_boundary
#print axioms LogShellEdge.FG.evenU_vec

-- Proposition 4.4 and the map `M` of Lemma 8.8, from the realization of Lemma 4.1
#print axioms LogShellEdge.oddMoves_of_realizes
#print axioms LogShellEdge.evenMoves_of_realizes
#print axioms LogShellEdge.cycloM_of_realizes

-- Section 5: Lemmas 5.2, 5.3, 5.4 and Theorem 5.1
#print axioms LogShellEdge.ShearLattice.span_orbit_eq
#print axioms LogShellEdge.EvenSmall.lemma52
#print axioms LogShellEdge.OddSmall.lemma53
#print axioms LogShellEdge.OddSmall.lemma54
#print axioms LogShellEdge.EvenSmall.thm51_even
#print axioms LogShellEdge.OddSmall.thm51_odd
#print axioms LogShellEdge.thm51c_of_inputs

-- Section 6: Theorem 6.1, Proposition 6.2, the group-ring identities in the proof of Theorem 6.5,
-- Corollary 6.6, Theorem 6.7, Corollary 6.8, Remark 6.9
#print axioms LogShellEdge.OddTR.thm61_i
#print axioms LogShellEdge.OddTR.thm61_ii
#print axioms LogShellEdge.OddTR.prop62
#print axioms LogShellEdge.GroupRing.adjRule_of_unit
#print axioms LogShellEdge.GroupRing.adjRule_of_mem_adjoin
#print axioms LogShellEdge.GroupRing.c_spec
#print axioms LogShellEdge.GroupRing.c_mem_ker
#print axioms LogShellEdge.GroupRing.eps_mu
#print axioms LogShellEdge.GroupRing.eps_nu
#print axioms LogShellEdge.GroupRing.E_mem
#print axioms LogShellEdge.GroupRing.exists_zeta
#print axioms LogShellEdge.GroupRing.coinv_action
#print axioms LogShellEdge.GroupRing.coinv_action_basis
#print axioms LogShellEdge.GroupRing.relCoinv_action_basis
#print axioms LogShellEdge.OddTR.cor66
#print axioms LogShellEdge.OddTR.main
#print axioms LogShellEdge.main_even
#print axioms LogShellEdge.main_odd_f2
#print axioms LogShellEdge.main_odd_tr
#print axioms LogShellEdge.main_even_of_inputs
#print axioms LogShellEdge.main_odd_f2_of_inputs
#print axioms LogShellEdge.main_odd_tr_of_inputs
#print axioms LogShellEdge.OddLattice.cor68
#print axioms LogShellEdge.OddLattice.rem69

-- Section 7: the orders in Theorem 7.1, the hull of a unit, Corollary 7.2
#print axioms LogShellEdge.ord_identity
#print axioms LogShellEdge.lo_div
#print axioms LogShellEdge.unit_smul_subset_hull
#print axioms LogShellEdge.cor72_even
#print axioms LogShellEdge.cor72_odd_f2
#print axioms LogShellEdge.cor72_odd_tr

-- Section 8: Lemmas 8.1, 8.2 (cores), Proposition 8.3, Lemma 8.6 (module computation), Lemmas 8.7,
-- 8.8, Theorems 8.9, 8.11, Proposition 8.13
#print axioms LogShellEdge.lemma81
#print axioms LogShellEdge.lemma82_core
#print axioms LogShellEdge.prop83
#print axioms LogShellEdge.lemma86_span
#print axioms LogShellEdge.Symp.orbit_eq_nonzero
#print axioms LogShellEdge.CycloData.moveM
#print axioms LogShellEdge.CycloData.lemma87
#print axioms LogShellEdge.CycloData.lemma88
#print axioms LogShellEdge.CycloData.thm89
#print axioms LogShellEdge.thm811
#print axioms LogShellEdge.OddKondo.prop813a_full
#print axioms LogShellEdge.OddKondo.prop813a_tr
#print axioms LogShellEdge.OddKondo.prop813c_a_not_add
#print axioms LogShellEdge.CycloData.prop813b
#print axioms LogShellEdge.CycloData.prop813c_b_not_add
#print axioms LogShellEdge.card_union_a
#print axioms LogShellEdge.card_union_b

-- the explicit maps put into `Γ` preserve the trace (the hypotheses are not contradictory for them)
#print axioms LogShellEdge.OddSmall.moveU_tau
#print axioms LogShellEdge.OddSmall.moveV_tau
#print axioms LogShellEdge.OddSmall.swap_tau
#print axioms LogShellEdge.EvenSmall.moveT_tau
#print axioms LogShellEdge.EvenSmall.moveU_tau
#print axioms LogShellEdge.CycloData.moveM_tau
#print axioms LogShellEdge.CycloData.kondoT_tau
#print axioms LogShellEdge.CycloData.kondoNeg_tau
#print axioms LogShellEdge.OddKondo.kondoT_tau
#print axioms LogShellEdge.OddKondo.lift_tau
