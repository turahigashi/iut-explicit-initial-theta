import LogShellEdge.Odd

/-!
# Odd degree: Lemma 5.4, Theorem 5.1(b)(c), Theorem 6.1, Corollary 6.6 and Theorem 6.7

See `LogShellEdge.Odd` for the conventions.
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge

variable {p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]

/-- One value of `m` from one residue: if `Λ ⊆ S_K(r)` with `1 ≤ r ≤ e` then
`S_K(r + q e) = 𝔪^(1 + q e)`. -/
theorem S_eq_of_one (F : Filtration p V) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (hΓ : PreservesL1 F Γ)
    (r q : ℤ) (hr1 : 1 ≤ r) (hre : r ≤ F.e) (h : F.L 1 ≤ S Γ (F.L r)) :
    S Γ (F.L (r + q * F.e)) = F.L (lo F.e (r + q * F.e)) := by
  have hlo : lo F.e (r + q * F.e) = 1 + q * F.e := by
    rw [show r + q * (F.e : ℤ) = q * F.e + r by ring, lo_add_mul F.e F.e_pos r q hr1 hre]; ring
  refine le_antisymm (S_le_lo F Γ hΓ _) ?_
  rw [hlo, S_shift]
  intro y hy
  obtain ⟨z, hz, rfl⟩ := (F.mem_shift_iff_exists q 1 y).1 hy
  exact ⟨z, h hz, rfl⟩

/-- a `ℚ_p`-linear map commutes with `ℤ_p`-scalars -/
theorem equiv_zsmul (γ : V ≃ₗ[ℚ_[p]] V) (a : ℤ_[p]) (x : V) : γ (a • x) = a • γ x := by
  rw [zpS_smul, map_smul, ← zpS_smul]

namespace OddSmall

variable {g : ℕ} (K : OddSmall p V g)

theorem L_le_L1 {r : ℤ} (hr : 1 ≤ r) : K.F.L r ≤ K.F.L 1 := K.F.anti_le hr

/-- the counting step of Lemma 5.4: if `#(𝔪^r / pΛ) ≥ p²` there is `z ∈ 𝔪^r ∖ pΛ` with
`Tr(z) ∈ p² ℤ_p`. -/
theorem exists_kernel_elt (r : ℕ) (hr1 : 1 ≤ r) (hre : r ≤ K.F.e)
    (hf : 2 ≤ K.f * (K.F.e + 1 - r)) :
    ∃ z ∈ K.F.L r, z ∉ K.F.L (1 + K.F.e) ∧ ‖K.τ z‖ < 1 := by
  by_contra H
  simp only [not_exists, not_and, not_lt] at H
  -- `H : ∀ z ∈ 𝔪^r, z ∉ pΛ → 1 ≤ ‖τ z‖`
  have hpe : ((K.F.e + 1 : ℕ) : ℤ) = 1 + K.F.e := by push_cast; ring
  set N : Submodule ℤ_[p] ↥(K.F.L r) := (K.F.L ((K.F.e + 1 : ℕ) : ℤ)).comap (K.F.L r).subtype with hN
  have hLr1 : ∀ z ∈ K.F.L r, z ∈ K.F.L 1 := fun z hz => K.L_le_L1 (by exact_mod_cast hr1) hz
  have surj := Submodule.Quotient.mk_surjective N
  let s := Function.surjInv surj
  have hs : ∀ q, Submodule.Quotient.mk (s q) = q := Function.surjInv_eq surj
  let φ : (↥(K.F.L r) ⧸ N) → ZMod p := fun q =>
    PadicInt.toZMod (zp (K.τ (s q : V)) (K.norm_tau_le (hLr1 _ (s q).2)))
  have inj : Function.Injective φ := by
    intro q q' hq
    have hsub : PadicInt.toZMod (zp (K.τ (s q : V)) (K.norm_tau_le (hLr1 _ (s q).2)) -
        zp (K.τ (s q' : V)) (K.norm_tau_le (hLr1 _ (s q').2))) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hq
    have hmem := (RingHom.mem_ker).mpr hsub
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hmem
    have hnorm : ‖K.τ ((s q : V) - (s q' : V))‖ < 1 := by
      rw [map_sub]; exact hmem
    have hdiff : (s q : V) - (s q' : V) ∈ K.F.L r := sub_mem (s q).2 (s q').2
    have hin : (s q : V) - (s q' : V) ∈ K.F.L (1 + K.F.e) := by
      by_contra hnot
      exact absurd (H _ hdiff hnot) (not_le.mpr hnorm)
    rw [← hs q, ← hs q', Submodule.Quotient.eq]
    show ((s q - s q' : ↥(K.F.L r)) : V) ∈ K.F.L ((K.F.e + 1 : ℕ) : ℤ)
    rw [hpe]
    simpa using hin
  have hle := Nat.card_le_card_of_injective φ inj
  rw [K.hcard r hr1 (by omega), Nat.card_zmod] at hle
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have : p ^ 2 ≤ p ^ (K.f * (K.F.e + 1 - r)) := Nat.pow_le_pow_right (by omega) hf
  have : p ^ 2 ≤ p := this.trans hle
  nlinarith

/-- Lemma 5.4: if `f (e + 1 - r) ≥ 2` (with `1 ≤ r ≤ e`) then `Λ ⊆ S_K(r)`. -/
theorem lemma54 (r : ℕ) (hr1 : 1 ≤ r) (hre : r ≤ K.F.e) (hf : 2 ≤ K.f * (K.F.e + 1 - r)) :
    K.F.L 1 ≤ S K.Γ (K.F.L r) := by
  obtain ⟨z, hz, hz', hτz⟩ := K.exists_kernel_elt r hr1 hre hf
  have hr1' : (1 : ℤ) ≤ r := by exact_mod_cast hr1
  have hpcLr : K.pc ∈ K.F.L r := K.F.anti_le (by exact_mod_cast hre) K.hpc
  have hpcL1 : K.pc ∈ K.F.L 1 := K.L_le_L1 hr1' hpcLr
  have hτpc0 : K.τ K.pc ≠ 0 := by
    intro h; have := K.hpcτ; rw [h, norm_zero] at this; exact zero_ne_one this
  set t : ℚ_[p] := K.τ z / K.τ K.pc with ht
  have htn : ‖t‖ ≤ ‖(p : ℚ_[p])‖ := by
    rw [ht, norm_div, K.hpcτ, div_one]
    exact norm_le_p_of_lt_one (K.norm_tau_le (K.L_le_L1 hr1' hz)) hτz
  have ht1 : ‖t‖ ≤ 1 := htn.trans norm_p_lt_one'.le
  set w := z - t • K.pc with hw
  have hwLr : w ∈ K.F.L r := by
    refine sub_mem hz ?_
    rw [← zp_smul _ ht1]; exact (K.F.L r).smul_mem _ hpcLr
  have hwL1 : w ∈ K.F.L 1 := K.L_le_L1 hr1' hwLr
  have hτw : K.τ w = 0 := by
    rw [hw, map_sub, map_smul, smul_eq_mul, ht, div_mul_cancel₀ _ hτpc0, sub_self]
  have hw' : w ∉ K.F.L (1 + K.F.e) := by
    intro hin
    apply hz'
    have : z = w + t • K.pc := by rw [hw]; abel
    rw [this]
    exact add_mem hin (K.smul_mem_pL1 hpcL1 htn)
  have hW := K.lemma53 w hwL1 hτw hw'
  refine K.L1_le_of_ker (S K.Γ (K.F.L r)) (fun x hx hx0 => spanImg_le_S K.Γ hwLr (hW x hx hx0))
    K.pc hpcL1 (Submodule.subset_span ⟨1, K.Γ.one_mem, K.pc, hpcLr, rfl⟩) K.hpcτ

theorem f_pos : 0 < K.f := by
  have h := K.hdeg
  simp only [Fintype.card_fin] at h
  rcases Nat.eq_zero_or_pos K.f with h0 | h0
  · rw [h0, mul_zero] at h; omega
  · exact h0

/-- `Λ ⊆ S_K(1)` (the identity map). -/
theorem L1_le_S_one : K.F.L 1 ≤ S K.Γ (K.F.L 1) := fun x hx =>
  Submodule.subset_span ⟨1, K.Γ.one_mem, x, hx, rfl⟩

/-- Theorem 5.1(b)(c): in odd degree, if `f ≥ 2`, or `f = 1` and `e ∤ m`, then
`S_K(m) = 𝔪^(lo m)` and `a_K(m) = (m - 1) mod e` is attained. -/
theorem thm51_odd (m : ℤ) (hcase : 2 ≤ K.f ∨ ¬ ((K.F.e : ℤ) ∣ m)) :
    S K.Γ (K.F.L m) = K.F.L (lo K.F.e m) ∧ Reaches K.F K.Γ (K.F.L m) (lo K.F.e m) := by
  obtain ⟨q, r, hr1, hre, rfl, -⟩ := decomp K.F.e K.F.e_pos m
  have hrS : K.F.L 1 ≤ S K.Γ (K.F.L r) := by
    lift r to ℕ using (by omega)
    by_cases h1 : r = 1
    · subst h1; exact K.L1_le_S_one
    · refine K.lemma54 r (by omega) (by exact_mod_cast hre) ?_
      rcases hcase with hf | hdvd
      · calc 2 ≤ K.f := hf
          _ = K.f * 1 := (mul_one _).symm
          _ ≤ K.f * (K.F.e + 1 - r) := Nat.mul_le_mul_left _ (by omega)
      · have hre' : r ≠ K.F.e := by
          intro h; apply hdvd; subst h; exact ⟨q + 1, by ring⟩
        have hr' : r < K.F.e := by exact_mod_cast lt_of_le_of_ne (by exact_mod_cast hre) hre'
        calc 2 ≤ K.F.e + 1 - r := by omega
          _ = 1 * (K.F.e + 1 - r) := (one_mul _).symm
          _ ≤ K.f * (K.F.e + 1 - r) := Nat.mul_le_mul_right _ K.f_pos
  have hS := S_eq_of_one K.F K.Γ K.hΓ1 r q hr1 hre hrS
  exact ⟨hS, reaches_of_S_eq K.F K.Γ _ _ (upper K.F K.Γ K.hΓ1 _) hS⟩

end OddSmall

/-- The totally ramified odd case `d = e`, `f = 1` (Section 6), with the inputs used there. -/
structure OddTR (p : ℕ) [Fact p.Prime] (V : Type*) [AddCommGroup V] [Module ℚ_[p] V]
    [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V] (g : ℕ) extends OddSmall p V g where
  hf1 : f = 1
  /-- the element `p ∈ ℚ_p ⊂ K` -/
  pv : V
  /-- `p ∈ 𝔪^e` -/
  hpv : pv ∈ F.L F.e
  /-- `Tr(p) = p d` with `p ∤ d` -/
  hpvτ : ‖τ pv‖ = 1
  /-- `𝔪^e / p𝔪 = F_p · p̄` (since `f = 1`) -/
  hLe : ∀ z ∈ F.L F.e, ∃ a : ℤ_[p], z - a • pv ∈ F.L (1 + F.e)
  /-- the integer `s` of the Jannsen-Wingberg presentation: `p^s = #μ_{p^∞}(K_tr)` -/
  s : ℕ
  /-- `s(K) = 1` because `p ∤ e` (Section 6.2) -/
  hs : s = 1
  /-- Theorem 6.5 (proved for `s = 1`): an automorphism with `φ₊(y₁) ≡ y₁ + y₂` and `φ₊(yᵢ) ≡ yᵢ`
  modulo `pΛ`. The algebraic core of its construction is `LogShellEdge.GroupRing`; the lifting
  (Theorem 6.3, which needs `s = 1`) is a cited input. -/
  lift : s = 1 → ∀ hg : 1 ≤ g, ∃ φ ∈ Γ, ∀ i : Fin (2 * g + 1),
    φ (y i) - (if i = 0 then y 0 + y ⟨1, by omega⟩ else y i) ∈ F.L (1 + F.e)

namespace OddTR

variable {g : ℕ} (K : OddTR p V g)

theorem pv_L1 : K.pv ∈ K.F.L 1 := K.F.anti_le (by have := K.F.e_pos; omega) K.hpv

/-- Theorem 6.1(ii): if some `γ` does not preserve the line `ℓ₀ = F_p p̄`, then `Λ ⊆ S_K(e)`. -/
theorem thm61_ii (γ : V ≃ₗ[ℚ_[p]] V) (hγ : γ ∈ K.Γ)
    (hmove : ∀ b : ℤ_[p], γ K.pv - b • K.pv ∉ K.F.L (1 + K.F.e)) :
    K.F.L 1 ≤ S K.Γ (K.F.L K.F.e) := by
  have hpvL1 := K.pv_L1
  set w := γ K.pv - K.pv with hw
  have hγpv : γ K.pv ∈ K.F.L 1 := K.hΓ1 γ hγ _ hpvL1
  have hwL1 : w ∈ K.F.L 1 := sub_mem hγpv hpvL1
  have hτw : K.τ w = 0 := by rw [hw, map_sub, K.hΓ2 γ hγ, sub_self]
  have hw' : w ∉ K.F.L (1 + K.F.e) := by
    have := hmove 1; rwa [one_smul] at this
  have hW := K.lemma53 w hwL1 hτw hw'
  have hwS : w ∈ S K.Γ (K.F.L K.F.e) :=
    sub_mem (Submodule.subset_span ⟨γ, hγ, K.pv, K.hpv, rfl⟩)
      (Submodule.subset_span ⟨1, K.Γ.one_mem, K.pv, K.hpv, rfl⟩)
  have hspan : spanImg K.Γ w ≤ S K.Γ (K.F.L K.F.e) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨δ, hδ, rfl⟩
    exact S_stable K.Γ _ hδ hwS
  exact K.L1_le_of_ker _ (fun x hx hx0 => hspan (hW x hx hx0)) K.pv hpvL1
    (Submodule.subset_span ⟨1, K.Γ.one_mem, K.pv, K.hpv, rfl⟩) K.hpvτ

/-- Theorem 6.1(i): if every `γ` preserves `ℓ₀`, then every `γ` preserves `𝔪^e = p𝒪` (hence `𝒪`). -/
theorem thm61_i (hpres : ∀ γ ∈ K.Γ, ∃ b : ℤ_[p], γ K.pv - b • K.pv ∈ K.F.L (1 + K.F.e)) :
    ∀ γ ∈ K.Γ, ∀ z ∈ K.F.L K.F.e, γ z ∈ K.F.L K.F.e := by
  intro γ hγ z hz
  obtain ⟨a, ha⟩ := K.hLe z hz
  obtain ⟨b, hb⟩ := hpres γ hγ
  have hpe : K.F.L (1 + K.F.e) ≤ K.F.L K.F.e := K.F.anti_le (by omega)
  -- `γ` maps `pΛ` into `pΛ`
  have hγp : ∀ x ∈ K.F.L (1 + K.F.e), γ x ∈ K.F.L (1 + K.F.e) := by
    intro x hx
    rw [K.F.shift] at hx ⊢
    have := K.hΓ1 γ hγ _ hx
    rwa [map_smul] at this
  have hz' : z = a • K.pv + (z - a • K.pv) := by abel
  rw [hz', map_add, equiv_zsmul]
  refine add_mem ?_ (hpe (hγp _ ha))
  have hb' : γ K.pv = b • K.pv + (γ K.pv - b • K.pv) := by abel
  rw [hb', smul_add, smul_smul]
  exact add_mem ((K.F.L K.F.e).smul_mem _ K.hpv) ((K.F.L K.F.e).smul_mem _ (hpe hb))

/-- Corollary 6.6: some `γ ∈ Γ` does not preserve `ℓ₀` (for `d = e ≥ 3`, using Theorem 6.5). -/
theorem cor66 (hg : 1 ≤ g) :
    ∃ γ ∈ K.Γ, ∀ b : ℤ_[p], γ K.pv - b • K.pv ∉ K.F.L (1 + K.F.e) := by
  have hpvL1 := K.pv_L1
  set c := K.y.repr K.pv with hc
  have hc0 : ‖c 0‖ = 1 := by rw [hc, ← K.norm_tau_eq]; exact K.hpvτ
  -- the coordinate test for membership in `pΛ`
  have test : ∀ (x : V) (i : Fin (2 * g + 1)), x ∈ K.F.L (1 + K.F.e) → ‖K.y.repr x i‖ ≤ ‖(p : ℚ_[p])‖ :=
    fun x i hx => (K.toSmallField.mem_pL1_iff x).1 hx i
  -- from `γ pv - b pv ∈ pΛ` and the 0-th coordinate of `γ pv` being `c 0`, `‖1 - b‖ ≤ ‖p‖`
  by_cases hpair : ∃ k : Fin g, ‖c (uIdx k)‖ = 1 ∨ ‖c (vIdx k)‖ = 1
  · obtain ⟨k, hk⟩ := hpair
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
      -- `‖(1 - b) c 0‖ ≤ ‖p‖` forces `‖1 - b‖ ≤ ‖p‖`
      have hb1 : ‖(1 : ℚ_[p]) - b‖ ≤ ‖(p : ℚ_[p])‖ := by
        have : c 0 - (b : ℚ_[p]) * c 0 = (1 - b) * c 0 := by ring
        rw [this, norm_mul, hc0, mul_one] at h0; exact h0
      -- then the `v`-coordinate is `(1 - b) c_v + c_u`, of norm `1`
      have hcv : ‖c (vIdx k)‖ ≤ 1 := K.toSmallField.coeff_le_one hpvL1 _
      have : c (vIdx k) + c (uIdx k) - (b : ℚ_[p]) * c (vIdx k) =
          c (uIdx k) + (1 - b) * c (vIdx k) := by ring
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
      have : c (uIdx k) + c (vIdx k) - (b : ℚ_[p]) * c (uIdx k) =
          c (vIdx k) + (1 - b) * c (uIdx k) := by ring
      rw [this] at hu
      have hsmall : ‖(1 - (b : ℚ_[p])) * c (uIdx k)‖ ≤ ‖(p : ℚ_[p])‖ := by
        rw [norm_mul]
        calc ‖(1 : ℚ_[p]) - b‖ * ‖c (uIdx k)‖ ≤ ‖(p : ℚ_[p])‖ * 1 :=
              mul_le_mul hb1 hcu (norm_nonneg _) (norm_nonneg _)
          _ = _ := mul_one _
      rw [norm_add_eq_one_of hv hsmall] at hu
      exact absurd hu (not_le.mpr norm_p_lt_one')
  · -- every coordinate of `p̄` outside `y_1` vanishes mod `p`: use the automorphism of Theorem 6.5
    push_neg at hpair
    obtain ⟨φ, hφ, hφy⟩ := K.lift K.hs hg
    refine ⟨φ, hφ, fun b hb => ?_⟩
    rw [zpS_smul] at hb
    have hsmallc : ∀ i : Fin (2 * g + 1), i ≠ 0 → ‖c i‖ ≤ ‖(p : ℚ_[p])‖ := by
      intro i hi
      obtain ⟨k, hk⟩ := idx_cases i hi
      have hle : ‖c i‖ ≤ 1 := K.toSmallField.coeff_le_one hpvL1 i
      have hne : ‖c i‖ ≠ 1 := by
        rcases hk with h | h <;> subst h
        · exact (hpair k).1
        · exact (hpair k).2
      exact norm_le_p_of_lt_one hle (lt_of_le_of_ne hle hne)
    -- `φ pv ≡ c₀ (y₀ + y₁) + Σ_{i ≠ 0} cᵢ yᵢ` modulo `pΛ`
    set i1 : Fin (2 * g + 1) := ⟨1, by omega⟩ with hi1
    have hi10 : i1 ≠ 0 := by intro h; have := congrArg Fin.val h; simp [hi1] at this
    set D : V := φ K.pv - (K.pv + c 0 • K.y i1) with hD
    have hDmem : D ∈ K.F.L (1 + K.F.e) := by
      have hsum : φ K.pv = ∑ i, c i • φ (K.y i) := by
        rw [hc]; exact apply_eq_sum K.y (φ : V →ₗ[ℚ_[p]] V) K.pv
      have hpvsum : K.pv + c 0 • K.y i1 =
          ∑ i, c i • (if i = 0 then K.y 0 + K.y i1 else K.y i) := by
        conv_lhs => rw [K.toSmallField.sum_repr K.pv]
        rw [← hc]
        have : ∀ i, c i • (if i = 0 then K.y 0 + K.y i1 else K.y i) =
            c i • K.y i + (if i = 0 then c 0 • K.y i1 else 0) := by
          intro i; split_ifs with h
          · subst h; rw [smul_add]
          · rw [add_zero]
        rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, Finset.sum_ite_eq',
          if_pos (Finset.mem_univ _)]
      rw [hD, hsum, hpvsum, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      rw [← smul_sub, ← zp_smul _ (K.toSmallField.coeff_le_one hpvL1 i)]
      exact (K.F.L (1 + K.F.e)).smul_mem _ (hφy i)
    -- coordinate `i1` of `φ pv - b pv`
    have h0 := test _ 0 hb
    have h1 := test _ i1 hb
    have hφpv : φ K.pv = K.pv + c 0 • K.y i1 + D := by rw [hD]; abel
    have hD0 := test D 0 hDmem
    have hD1 := test D i1 hDmem
    rw [hφpv, repr_sub, map_add, Finsupp.add_apply, repr_add_smul, repr_smul, ← hc,
      if_neg (Ne.symm hi10), add_zero] at h0
    rw [hφpv, repr_sub, map_add, Finsupp.add_apply, repr_add_smul, repr_smul, ← hc,
      if_pos rfl] at h1
    -- from coordinate 0: `‖(1 - b) c₀ + D₀‖ ≤ ‖p‖`, so `‖1 - b‖ ≤ ‖p‖`
    have hb1 : ‖(1 : ℚ_[p]) - b‖ ≤ ‖(p : ℚ_[p])‖ := by
      have e0 : c 0 + K.y.repr D 0 - (b : ℚ_[p]) * c 0 = (1 - b) * c 0 + K.y.repr D 0 := by ring
      rw [e0] at h0
      have : ‖(1 - (b : ℚ_[p])) * c 0‖ ≤ ‖(p : ℚ_[p])‖ := by
        have h3 : (1 - (b : ℚ_[p])) * c 0 = ((1 - b) * c 0 + K.y.repr D 0) - K.y.repr D 0 := by ring
        rw [h3]
        rw [sub_eq_add_neg]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_neg]; exact max_le h0 hD0)
      rwa [norm_mul, hc0, mul_one] at this
    -- coordinate `i1`: `c₁ + c₀ + D₁ - b c₁ = c₀ + ((1 - b) c₁ + D₁)`, of norm `1`
    have e1 : c i1 + c 0 + K.y.repr D i1 - (b : ℚ_[p]) * c i1 =
        c 0 + ((1 - b) * c i1 + K.y.repr D i1) := by ring
    rw [e1] at h1
    have hsmall : ‖(1 - (b : ℚ_[p])) * c i1 + K.y.repr D i1‖ ≤ ‖(p : ℚ_[p])‖ := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hD1)
      rw [norm_mul]
      calc ‖(1 : ℚ_[p]) - b‖ * ‖c i1‖ ≤ ‖(p : ℚ_[p])‖ * 1 :=
            mul_le_mul hb1 (K.toSmallField.coeff_le_one hpvL1 i1) (norm_nonneg _) (norm_nonneg _)
        _ = _ := mul_one _
    rw [norm_add_eq_one_of hc0 hsmall] at h1
    exact absurd h1 (not_le.mpr norm_p_lt_one')

/-- Theorem 6.7 in the totally ramified odd case: `Λ ⊆ S_K(r)` for every `1 ≤ r ≤ e`. -/
theorem L1_le_S_all (hg : 1 ≤ g) (r : ℤ) (hr1 : 1 ≤ r) (hre : r ≤ K.F.e) :
    K.F.L 1 ≤ S K.Γ (K.F.L r) := by
  lift r to ℕ using (by omega)
  by_cases hr : r = K.F.e
  · subst hr
    obtain ⟨γ, hγ, hmove⟩ := K.cor66 hg
    exact K.thm61_ii γ hγ hmove
  · by_cases h1 : r = 1
    · subst h1; exact K.toOddSmall.L1_le_S_one
    · refine K.toOddSmall.lemma54 r (by omega) (by exact_mod_cast hre) ?_
      have hr' : r < K.F.e := lt_of_le_of_ne (by exact_mod_cast hre) hr
      calc 2 ≤ K.F.e + 1 - r := by omega
        _ = 1 * (K.F.e + 1 - r) := (one_mul _).symm
        _ ≤ K.f * (K.F.e + 1 - r) := Nat.mul_le_mul_right _ K.toOddSmall.f_pos

/-- Theorem 6.7 (main theorem) in the totally ramified odd case `d = e ≥ 3`. -/
theorem main (hg : 1 ≤ g) (m : ℤ) :
    S K.Γ (K.F.L m) = K.F.L (lo K.F.e m) ∧ Reaches K.F K.Γ (K.F.L m) (lo K.F.e m) := by
  have h := K.L1_le_S_all hg
  exact ⟨S_eq_of_period K.F K.Γ K.hΓ1 h m, reaches_of_period K.F K.Γ K.hΓ1 h m⟩

end OddTR

end LogShellEdge
