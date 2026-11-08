import LogShellEdge.Realize

/-!
# The map `M` used in Lemma 8.8, from Lemma 4.1

The proof of Lemma 8.8 applies the mixing word `M` of Section 4.3 (Lemma 4.3) to the first two pairs
`(x_1, x_2), (x_3, x_4)`; by Lemma 4.1 it induces an element of `Γ_K` that acts on `log` by
`y_2 ↦ y_2 + y_1 + y_4`, `y_3 ↦ y_3 - y_1 - y_4` (the abelianization `M^ab = T_{a+d}`, `M_ab`), fixing the
other `y_i`.

`mixMove` is `M` extended by the identity to the free group on `z_1, …, z_d` (0-based: letters `0, …, 3`),
`mixMove_vec` is its abelianization, and `cycloM_of_realizes` derives the field `moveM` of `CycloData`
(Section 8.2) from `RealizesEven`. In the basis `z, y_2, …, y_d` of Lemma 8.6 (0-based `b 0 = z`,
`b j = y_{j+1}`), `y_1 = α z`: `y 0 = α • b 0` and `y j = b j` for `j ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge

open LogShellEdge.ShearFreeGroup in
/-- the mixing word `M` of Section 4.3 on the letters `z 0, …, z 3` of the free group on `2g` letters,
the other letters fixed -/
def mixMove (g : ℕ) (hg : 2 ≤ g) : FreeGroup (Fin (2 * g)) ≃* FreeGroup (Fin (2 * g)) :=
  FG.extendE 0 (by omega) Mequiv

open LogShellEdge.ShearFreeGroup in
theorem mixMove_fix0 (g : ℕ) (hg : 2 ≤ g) :
    mixMove g hg (FreeGroup.of ⟨0, by omega⟩) = FreeGroup.of ⟨0, by omega⟩ := by
  rw [mixMove, FG.extendE_apply]
  exact FG.extend_of_eq_off 0 _ _ 0 _ rfl M_a

open LogShellEdge.ShearFreeGroup in
theorem mixMove_boundary (g : ℕ) (hg : 2 ≤ g) :
    mixMove g hg (FG.evenBoundary g) = FG.evenBoundary g := by
  have hM : ∀ x, (Mequiv : F4 ≃* F4) x = M x := fun _ => rfl
  have hMd : (Mequiv : F4 ≃* F4) delta = delta := by
    rw [hM]
    exact M_delta
  rw [mixMove, FG.evenBoundary]
  exact FG.extendE_bdry_pair (2 * g) 0 g 0 0 (by omega) _ (by omega) Mequiv hMd

open LogShellEdge.ShearFreeGroup in
/-- the abelianization of `mixMove` (`M_ab`): `e_1 ↦ e_1 + e_0 + e_3`, `e_2 ↦ e_2 - e_0 - e_3`, the other
basis vectors fixed -/
theorem mixMove_vec (g : ℕ) (hg : 2 ≤ g) (i : Fin (2 * g)) :
    FG.vecN (mixMove g hg (FreeGroup.of i)) =
      if i.val = 1 then Pi.single i 1 + Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨3, by omega⟩ 1
      else if i.val = 2 then Pi.single i 1 - Pi.single ⟨0, by omega⟩ 1 - Pi.single ⟨3, by omega⟩ 1
      else Pi.single i 1 := by
  have h4 : 0 + 4 ≤ 2 * g := by omega
  rw [mixMove, FG.extendE_apply]
  by_cases hi : 0 ≤ i.val ∧ i.val < 0 + 4
  · obtain ⟨a, rfl⟩ := FG.exists_off 0 h4 i hi
    rw [FG.vecN_extend_off, MulEquiv.coe_toMonoidHom]
    obtain ⟨hab, hbb, hcb, hdb⟩ := M_ab
    obtain ⟨va, vb, vc, vd⟩ := vec_gen
    have hM : ∀ x, (Mequiv : F4 ≃* F4) x = M x := fun _ => rfl
    fin_cases a
    · rw [if_neg (by simp), if_neg (by simp)]
      change FG.linExt _ (FG.vecN (Mequiv ga)) = _
      rw [hM, FG.vecN_eq_vec, hab, va, FG.linExt_single]
      rfl
    · rw [if_pos (by simp)]
      change FG.linExt _ (FG.vecN (Mequiv gb)) = _
      rw [hM, FG.vecN_eq_vec, hbb, va, vb, vd, FG.linExt_add, FG.linExt_add, FG.linExt_single,
        FG.linExt_single, FG.linExt_single]
      ext t
      simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff, FG.off_val]
      split_ifs <;> omega
    · rw [if_neg (by simp), if_pos (by simp)]
      change FG.linExt _ (FG.vecN (Mequiv gc)) = _
      rw [hM, FG.vecN_eq_vec, hcb, va, vc, vd, FG.linExt_sub, FG.linExt_sub, FG.linExt_single,
        FG.linExt_single, FG.linExt_single]
      ext t
      simp only [Pi.sub_apply, Pi.single_apply, Fin.ext_iff, FG.off_val]
      split_ifs <;> omega
    · rw [if_neg (by simp), if_neg (by simp)]
      change FG.linExt _ (FG.vecN (Mequiv gd)) = _
      rw [hM, FG.vecN_eq_vec, hdb, vd, FG.linExt_single]
      rfl
  · rw [FG.vecN_extend_out _ _ _ _ hi, if_neg (by omega), if_neg (by omega)]

variable {p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]

omit [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V] in
theorem combo_sub {n : ℕ} (y : Module.Basis (Fin n) ℚ_[p] V) (c c' : Fin n → ℤ) :
    combo y (c - c') = combo y c - combo y c' := by
  simp only [combo, Pi.sub_apply, Int.cast_sub, sub_smul, Finset.sum_sub_distrib]

/-- The field `moveM` of `CycloData`, from Lemma 4.1 (`RealizesEven`) applied to the mixing word `M`
(Lemma 4.3), written in the basis `b` of Lemma 8.6. -/
theorem cycloM_of_realizes {g : ℕ} (hg2 : 2 ≤ g) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V))
    (y : Module.Basis (Fin (2 * g)) ℚ_[p] V) (hR : RealizesEven Γ y (by omega))
    (b : Module.Basis (Fin (2 * g)) ℚ_[p] V) (α : ℤ_[p])
    (hy0 : y ⟨0, by omega⟩ = (α : ℚ_[p]) • b ⟨0, by omega⟩)
    (hyj : ∀ j : Fin (2 * g), j.val ≠ 0 → y j = b j) :
    ∃ γ ∈ Γ, ∀ i : Fin (2 * g),
      γ (b i) = if i.val = 1 then b i + (α : ℚ_[p]) • b ⟨0, by omega⟩ + b ⟨3, by omega⟩
        else if i.val = 2 then b i - (α : ℚ_[p]) • b ⟨0, by omega⟩ - b ⟨3, by omega⟩ else b i := by
  obtain ⟨γ, hγ, hM⟩ := hR (mixMove g hg2) (mixMove_fix0 g hg2) (mixMove_boundary g hg2)
  have hg0 : 0 < 2 * g := by omega
  have h3 : (⟨3, by omega⟩ : Fin (2 * g)).val ≠ 0 := by simp
  refine ⟨γ, hγ, fun i => ?_⟩
  by_cases h0 : i.val = 0
  · obtain rfl : i = ⟨0, hg0⟩ := Fin.ext h0
    rw [if_neg (by simp), if_neg (by simp)]
    have hα : (α : ℚ_[p]) ≠ 0 := by
      intro h
      exact y.ne_zero ⟨0, by omega⟩ (by rw [hy0, h, zero_smul])
    have hb0 : b ⟨0, by omega⟩ = ((α : ℚ_[p]))⁻¹ • y ⟨0, by omega⟩ := by
      rw [hy0, smul_smul, inv_mul_cancel₀ hα, one_smul]
    have hγ0 : γ (y ⟨0, by omega⟩) = y ⟨0, by omega⟩ := by
      rw [hM, mixMove_vec, if_neg (by simp), if_neg (by simp), combo_single]
    rw [hb0, map_smul, hγ0]
  · have hyi : y i = b i := hyj i h0
    rw [← hyi, hM i, mixMove_vec]
    by_cases h1 : i.val = 1
    · rw [if_pos h1, if_pos h1, combo_add, combo_add, combo_single, combo_single, combo_single, hy0,
        hyi, hyj _ h3]
    · by_cases h2 : i.val = 2
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, combo_sub, combo_sub, combo_single,
          combo_single, combo_single, hy0, hyi, hyj _ h3]
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, combo_single, hyi]

end LogShellEdge
