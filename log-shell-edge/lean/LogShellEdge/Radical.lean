import LogShellEdge.Coord

/-!
# Section 8.1 and 8.3: the invariant lattice from the unramified extension of degree p

* `lemma81`: the group-theoretic core of Lemma 8.1. If `ι : A_K → A_L` (the inclusion `K^× → L^×`, which
  local class field theory identifies with the transfer [Hoshi, Lemma 1.7(3)]) commutes with automorphisms
  `β_K`, `β_L` (naturality of the transfer, and `β(G_L) = G_L` [Hoshi, Definition 3.5(iii),
  Proposition 3.6]) and `β_K` preserves the principal units [Hoshi, Proposition 3.11(i)], then `β_K`
  maps `C_K = U¹_K ∩ ι⁻¹((A_L)^p)` into itself.
* `lemma82_core`: the counting step of Lemma 8.2: if `(U¹)^p ≤ C`, `U^(p e₁) ≤ C`, the index
  `[C : (U¹)^p]` divides `p` (Kummer theory: `C/(U¹)^p ↪ Hom(Gal(L/K), μ_p)`) and `U^(p e₁) ⊄ (U¹)^p`,
  then `C = U^(p e₁) (U¹)^p`. The `p`-adic inputs (Hensel's lemma, the Artin-Schreier reduction) are
  classical [FV, Chapter IV (1.4), §1 Exercise 7] and are checked numerically in
  `check_boundary_lattices.py`.
* `prop83`: Proposition 8.3: if `Γ` preserves `log C_K = pΛ + 𝔪^(p e₁)` then it preserves
  `Λ + 𝔪^(e₁)`.
* `thm811`: Theorem 8.11: for `K/ℚ₂` unramified, if `Γ` preserves `log C_K = 𝔪²`, then `Γ` preserves
  every `𝔪^m`, so `S_K(m) = 𝔪^m` and `a_K(m) = 0`.
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge

/-- Lemma 8.1, group-theoretic core. -/
theorem lemma81 {A B : Type*} [CommGroup A] [CommGroup B] (ι : A →* B) (U : Subgroup A) (n : ℕ)
    (βK : A →* A) (βL : B →* B) (hcomm : ∀ a, ι (βK a) = βL (ι a)) (hU : ∀ u ∈ U, βK u ∈ U) :
    ∀ u ∈ U, (∃ y : B, y ^ n = ι u) → βK u ∈ U ∧ ∃ y : B, y ^ n = ι (βK u) := by
  rintro u hu ⟨y, hy⟩
  exact ⟨hU u hu, βL y, by rw [← map_pow, hy, hcomm]⟩

/-- Lemma 8.2, counting step. -/
theorem lemma82_core {A : Type*} [CommGroup A] (C P Q : Subgroup A) (hP : P ≤ C) (hQ : Q ≤ C)
    (p : ℕ) [Fact p.Prime] (hidx : P.relIndex C ∣ p) (hnot : ¬ Q ≤ P) : C = Q ⊔ P := by
  have hQP : Q ⊔ P ≤ C := sup_le hQ hP
  have hPQP : P ≤ Q ⊔ P := le_sup_right
  have hmul := Subgroup.relIndex_mul_relIndex P (Q ⊔ P) C hPQP hQP
  have hne1 : P.relIndex (Q ⊔ P) ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact hnot (le_sup_left.trans h)
  have hdvd : P.relIndex (Q ⊔ P) ∣ p := by rw [← hmul] at hidx; exact dvd_of_mul_right_dvd hidx
  have hp := (Fact.out : p.Prime)
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | hpq
  · exact absurd h1 hne1
  · have hx : (Q ⊔ P).relIndex C = 1 := by
      rw [← hmul, hpq] at hidx
      obtain ⟨k, hk⟩ := hidx
      have : p * 1 = p * ((Q ⊔ P).relIndex C * k) := by rw [mul_one, ← mul_assoc]; exact hk
      exact Nat.eq_one_of_mul_eq_one_right (Nat.eq_of_mul_eq_mul_left hp.pos this).symm
    rw [Subgroup.relIndex_eq_one] at hx
    exact le_antisymm hx hQP

variable {p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]

/-- the submodule `{x | p⁻¹ • x ∈ N}`, i.e. `p N` -/
def pMul (N : Submodule ℤ_[p] V) : Submodule ℤ_[p] V := N.comap (smulL ((p : ℚ_[p])⁻¹))

/-- Proposition 8.3: if `e = (p - 1) e₁` and `Γ` preserves `log C_K = pΛ + 𝔪^(p e₁)` (Lemmas 8.1, 8.2),
then `Γ` preserves `Λ + 𝔪^(e₁)` (and `pΛ + 𝔪^(p e₁)` itself). -/
theorem prop83 (F : Filtration p V) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (Λ : Submodule ℤ_[p] V) (e₁ : ℕ)
    (he : F.e = (p - 1) * e₁)
    (hC : ∀ γ ∈ Γ, ∀ x ∈ pMul Λ ⊔ F.L (p * e₁ : ℕ), γ x ∈ pMul Λ ⊔ F.L (p * e₁ : ℕ)) :
    ∀ γ ∈ Γ, ∀ x ∈ Λ ⊔ F.L e₁, γ x ∈ Λ ⊔ F.L e₁ := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hpe : ((p * e₁ : ℕ) : ℤ) = e₁ + 1 * F.e := by
    rw [he]; push_cast
    have : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
    rw [this]; ring
  -- `x ∈ Λ ⊔ 𝔪^e₁ ↔ p • x ∈ pΛ ⊔ 𝔪^(p e₁)`
  have key : ∀ x, x ∈ Λ ⊔ F.L e₁ ↔ ((p : ℚ_[p]) • x) ∈ pMul Λ ⊔ F.L (p * e₁ : ℕ) := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      refine Submodule.mem_sup.2 ⟨(p : ℚ_[p]) • a, ?_, (p : ℚ_[p]) • b, ?_, (smul_add _ _ _).symm⟩
      · show smulL _ ((p : ℚ_[p]) • a) ∈ Λ
        rw [smulL_apply, smul_smul, inv_mul_cancel₀ padic_p_ne_zero, one_smul]; exact ha
      · rw [hpe, F.mem_shift_zpow]
        rw [smul_smul, zpow_neg_one, inv_mul_cancel₀ padic_p_ne_zero, one_smul]; exact hb
    · intro hx
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx
      have hx' : x = (p : ℚ_[p])⁻¹ • a + (p : ℚ_[p])⁻¹ • b := by
        rw [← smul_add, hab, smul_smul, inv_mul_cancel₀ padic_p_ne_zero, one_smul]
      rw [hx']
      refine Submodule.add_mem_sup ha ?_
      rw [hpe, F.mem_shift_zpow, zpow_neg_one] at hb
      exact hb
  intro γ hγ x hx
  rw [key] at hx ⊢
  rw [← map_smul]
  exact hC γ hγ _ hx

/-- Theorem 8.11: for `K/ℚ₂` unramified (`e = 1`), if every `γ ∈ Γ` preserves `log C_K = 𝔪²`
(Lemmas 8.1, 8.2: `C_K = U^(2)`, `log U^(2) = 4𝒪_K`), then every `γ` preserves every `𝔪^m`;
hence `S_K(m) = 𝔪^m` and the valuation does not drop (`a_K(m) = 0`). -/
theorem thm811 (F : Filtration p V) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (he : F.e = 1)
    (h2 : ∀ γ ∈ Γ, ∀ x ∈ F.L 2, γ x ∈ F.L 2) (m : ℤ) :
    (∀ γ ∈ Γ, ∀ x ∈ F.L m, γ x ∈ F.L m) ∧ S Γ (F.L m) = F.L m ∧ Reaches F Γ (F.L m) m := by
  have hpres : ∀ γ ∈ Γ, ∀ x ∈ F.L m, γ x ∈ F.L m := by
    intro γ hγ x hx
    have e : m = 2 + (m - 2) * F.e := by rw [he]; push_cast; ring
    rw [e, F.mem_shift_zpow] at hx ⊢
    have := h2 γ hγ _ hx
    rwa [map_smul] at this
  have hS : S Γ (F.L m) = F.L m := by
    refine le_antisymm (Submodule.span_le.mpr ?_) (fun x hx => Submodule.subset_span ⟨1, Γ.one_mem, x, hx, rfl⟩)
    rintro _ ⟨γ, hγ, x, hx, rfl⟩
    exact hpres γ hγ x hx
  exact ⟨hpres, hS, reaches_of_S_eq F Γ _ _ hpres hS⟩

end LogShellEdge
