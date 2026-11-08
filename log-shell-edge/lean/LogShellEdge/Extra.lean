import LogShellEdge.OddMain

/-!
# Proposition 6.2 (the main implication) and the module computation of Lemma 8.6

* `prop62`: if the line `ℓ₀ = F_p p̄` is not the line of `ȳ₁`, i.e. some coordinate of `p` outside `y_1`
  is a unit, then a move inside a pair (Proposition 4.4(b)) does not preserve `ℓ₀`; so (ii) of Theorem 6.1
  holds.
* `lemma86_span`: if `y₀ = t • y₁` then `ℤ_p y₀ + ℤ_p y₁ = ℤ_p z` with `z = y₁` (if `‖t‖ ≤ 1`) or
  `z = y₀` (otherwise).
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge

variable {p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]

namespace OddTR

variable {g : ℕ} (K : OddTR p V g)

/-- Proposition 6.2 (main implication): if a coordinate of `p` on some pair is a unit (equivalently
`ℓ₀ ≠ F_p ȳ₁`), some `γ ∈ Γ` does not preserve `ℓ₀`. -/
theorem prop62 (k : Fin g)
    (hk : ‖K.y.repr K.pv (uIdx k)‖ = 1 ∨ ‖K.y.repr K.pv (vIdx k)‖ = 1) :
    ∃ γ ∈ K.Γ, ∀ b : ℤ_[p], γ K.pv - b • K.pv ∉ K.F.L (1 + K.F.e) := by
  have hpvL1 := K.pv_L1
  set c := K.y.repr K.pv with hc
  have hc0 : ‖c 0‖ = 1 := by rw [hc, ← K.norm_tau_eq]; exact K.hpvτ
  have test : ∀ (x : V) (i : Fin (2 * g + 1)), x ∈ K.F.L (1 + K.F.e) → ‖K.y.repr x i‖ ≤ ‖(p : ℚ_[p])‖ :=
    fun x i hx => (K.toSmallField.mem_pL1_iff x).1 hx i
  rcases hk with hu | hv
  · obtain ⟨γ, hγ, hU⟩ := K.moveU k
    refine ⟨γ, hγ, fun b hb => ?_⟩
    rw [zpS_smul] at hb
    have happ := apply_of_move K.y (γ : V →ₗ[ℚ_[p]] V) (uIdx k) (vIdx k) (fun i => hU i) K.pv
    change γ K.pv = _ at happ
    have h0 := test _ 0 hb
    have hv := test _ (vIdx k) hb
    have h0ne : (0 : Fin (2 * g + 1)) ≠ vIdx k := by
      intro h; have := congrArg Fin.val h; simp [vIdx] at this
    rw [happ, repr_sub, repr_add_smul, repr_smul, if_neg h0ne, add_zero, ← hc] at h0
    rw [happ, repr_sub, repr_add_smul, repr_smul, if_pos rfl, ← hc] at hv
    have hb1 : ‖(1 : ℚ_[p]) - b‖ ≤ ‖(p : ℚ_[p])‖ := by
      have : c 0 - (b : ℚ_[p]) * c 0 = (1 - b) * c 0 := by ring
      rw [this, norm_mul, hc0, mul_one] at h0; exact h0
    have hcv : ‖c (vIdx k)‖ ≤ 1 := K.toSmallField.coeff_le_one hpvL1 _
    have : c (vIdx k) + c (uIdx k) - (b : ℚ_[p]) * c (vIdx k) = c (uIdx k) + (1 - b) * c (vIdx k) := by ring
    rw [this] at hv
    have hsmall : ‖(1 - (b : ℚ_[p])) * c (vIdx k)‖ ≤ ‖(p : ℚ_[p])‖ := by
      rw [norm_mul]
      calc ‖(1 : ℚ_[p]) - b‖ * ‖c (vIdx k)‖ ≤ ‖(p : ℚ_[p])‖ * 1 :=
            mul_le_mul hb1 hcv (norm_nonneg _) (norm_nonneg _)
        _ = _ := mul_one _
    rw [norm_add_eq_one_of hu hsmall] at hv
    exact absurd hv (not_le.mpr norm_p_lt_one')
  · obtain ⟨γ, hγ, hV⟩ := K.moveV k
    refine ⟨γ, hγ, fun b hb => ?_⟩
    rw [zpS_smul] at hb
    have happ := apply_of_move K.y (γ : V →ₗ[ℚ_[p]] V) (vIdx k) (uIdx k) (fun i => hV i) K.pv
    change γ K.pv = _ at happ
    have h0 := test _ 0 hb
    have hu := test _ (uIdx k) hb
    have h0ne : (0 : Fin (2 * g + 1)) ≠ uIdx k := by
      intro h; have := congrArg Fin.val h; simp [uIdx] at this
    rw [happ, repr_sub, repr_add_smul, repr_smul, if_neg h0ne, add_zero, ← hc] at h0
    rw [happ, repr_sub, repr_add_smul, repr_smul, if_pos rfl, ← hc] at hu
    have hb1 : ‖(1 : ℚ_[p]) - b‖ ≤ ‖(p : ℚ_[p])‖ := by
      have : c 0 - (b : ℚ_[p]) * c 0 = (1 - b) * c 0 := by ring
      rw [this, norm_mul, hc0, mul_one] at h0; exact h0
    have hcu : ‖c (uIdx k)‖ ≤ 1 := K.toSmallField.coeff_le_one hpvL1 _
    have : c (uIdx k) + c (vIdx k) - (b : ℚ_[p]) * c (uIdx k) = c (vIdx k) + (1 - b) * c (uIdx k) := by ring
    rw [this] at hu
    have hsmall : ‖(1 - (b : ℚ_[p])) * c (uIdx k)‖ ≤ ‖(p : ℚ_[p])‖ := by
      rw [norm_mul]
      calc ‖(1 : ℚ_[p]) - b‖ * ‖c (uIdx k)‖ ≤ ‖(p : ℚ_[p])‖ * 1 :=
            mul_le_mul hb1 hcu (norm_nonneg _) (norm_nonneg _)
        _ = _ := mul_one _
    rw [norm_add_eq_one_of hv hsmall] at hu
    exact absurd hu (not_le.mpr norm_p_lt_one')

end OddTR

/-- Lemma 8.6, module computation: if `y₀ = t • y₁` then the `ℤ_p`-span of `y₀, y₁` is cyclic, generated
by `y₁` if `‖t‖ ≤ 1` and by `y₀` otherwise. -/
theorem lemma86_span (y₀ y₁ : V) (t : ℚ_[p]) (ht : y₀ = t • y₁) :
    Submodule.span ℤ_[p] {y₀, y₁} =
      Submodule.span ℤ_[p] {if ‖t‖ ≤ 1 then y₁ else y₀} := by
  split_ifs with h
  · apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro z (rfl | rfl)
      · rw [ht, ← zp_smul t h]; exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · exact Submodule.subset_span rfl
    · exact Submodule.span_mono (by simp)
  · push_neg at h
    have ht0 : t ≠ 0 := by intro h0; rw [h0, norm_zero] at h; linarith
    have hti : ‖t⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ h.le
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro z (rfl | rfl)
      · exact Submodule.subset_span rfl
      · have : z = t⁻¹ • y₀ := by rw [ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
        rw [this, ← zp_smul _ hti]; exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · exact Submodule.span_mono (by simp)

end LogShellEdge
