import LogShellEdge.Coord
import LogShellEdge.Small
import LogShellEdge.Symplectic

/-!
# Reduction modulo `p`, counting in quotients, and unions of images

Shared tools for Sections 8.2 and 8.4 (`LogShellEdge.Cyclo`, `LogShellEdge.Unions`).

* `red c`: the reduction modulo `p` of `c ∈ ℤ_p ⊂ ℚ_p` (`0` outside `ℤ_p`); `rd y x`: the reduced
  coordinates of `x` in the basis `y`. Two elements of the `ℤ_p`-span of `y` are congruent modulo `p`
  times that span iff their reduced coordinates agree (`rd_eq_iff`).
* `lift_list`, `exists_move`, `exists_translate`: products of symplectic transvections over `F_p`
  realised by elements of `Γ` (given single transvections), and the translations obtained by
  conjugating one translation.
* `card_quot_le`, `exists_sub_mem_of_card`: counting in quotients `A / (P ∩ A)`.
* `mem_imgSet_of_sub_mem`, `imgSet_shift`, `L_shift_set`: unions of images.
* `mem_of_unit_smul_mem`, `smul_mem_of_norm_le`, `unit_or_unit`, `repr_apply_diag`: small lemmas on
  lattices and coordinates.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LogShellEdge

variable {p : ℕ} [Fact p.Prime]

/-! ## Norms in `ℚ_p` -/

theorem norm_add_le_one {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem norm_sub_le_one {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact norm_add_le_one ha (by rwa [norm_neg])

theorem norm_mul_le_one {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

theorem norm_natCast_le_one (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 := by
  rw [← PadicInt.coe_natCast]
  exact PadicInt.norm_le_one _

/-! ## Reduction of scalars -/

/-- the reduction modulo `p` of an element of `ℚ_p` (`0` if it is not in `ℤ_p`) -/
def red (c : ℚ_[p]) : ZMod p := if h : ‖c‖ ≤ 1 then PadicInt.toZMod (⟨c, h⟩ : ℤ_[p]) else 0

theorem red_coe (t : ℤ_[p]) : red (t : ℚ_[p]) = PadicInt.toZMod t := by
  unfold red
  rw [dif_pos t.2]
  rfl

theorem red_of {c : ℚ_[p]} (h : ‖c‖ ≤ 1) : red c = PadicInt.toZMod (zp c h) :=
  red_coe (zp c h)

theorem red_add {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : red (a + b) = red a + red b := by
  rw [red_of ha, red_of hb, ← map_add]
  exact red_coe (zp a ha + zp b hb)

theorem red_mul {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : red (a * b) = red a * red b := by
  rw [red_of ha, red_of hb, ← map_mul]
  exact red_coe (zp a ha * zp b hb)

theorem red_neg (a : ℚ_[p]) : red (-a) = -red a := by
  by_cases ha : ‖a‖ ≤ 1
  · rw [red_of ha, ← map_neg]
    exact red_coe (-zp a ha)
  · have ha' : ¬ ‖-a‖ ≤ 1 := by rwa [norm_neg]
    unfold red
    rw [dif_neg ha, dif_neg ha', neg_zero]

theorem red_sub {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : red (a - b) = red a - red b := by
  rw [sub_eq_add_neg, red_add ha (by rwa [norm_neg]), red_neg, ← sub_eq_add_neg]

theorem red_natCast (n : ℕ) : red (n : ℚ_[p]) = n := by
  rw [← PadicInt.coe_natCast, red_coe, map_natCast]

theorem red_zero : red (0 : ℚ_[p]) = 0 := by
  rw [← PadicInt.coe_zero, red_coe, map_zero]

theorem red_one : red (1 : ℚ_[p]) = 1 := by
  rw [← PadicInt.coe_one, red_coe, map_one]

theorem red_eq_zero_iff {a : ℚ_[p]} (ha : ‖a‖ ≤ 1) : red a = 0 ↔ ‖a‖ < 1 := by
  rw [red_of ha, ← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
    PadicInt.mem_nonunits]
  exact Iff.rfl

theorem red_eq_zero_iff' {a : ℚ_[p]} (ha : ‖a‖ ≤ 1) : red a = 0 ↔ ‖a‖ ≤ ‖(p : ℚ_[p])‖ := by
  rw [red_eq_zero_iff ha]
  exact ⟨norm_le_p_of_lt_one ha, fun h => lt_of_le_of_lt h norm_p_lt_one'⟩

theorem red_eq_iff {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    red a = red b ↔ ‖a - b‖ ≤ ‖(p : ℚ_[p])‖ := by
  rw [← red_eq_zero_iff' (norm_sub_le_one ha hb), red_sub ha hb, sub_eq_zero]

theorem norm_eq_one_of_red_ne_zero {a : ℚ_[p]} (ha : ‖a‖ ≤ 1) (h : red a ≠ 0) : ‖a‖ = 1 := by
  rw [ne_eq, red_eq_zero_iff ha, not_lt] at h
  exact le_antisymm ha h

theorem red_ne_zero_of_norm_eq_one {a : ℚ_[p]} (h : ‖a‖ = 1) : red a ≠ 0 := by
  rw [ne_eq, red_eq_zero_iff h.le, h]
  exact lt_irrefl 1

theorem red_sum {α : Type*} (s : Finset α) (f : α → ℚ_[p]) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    red (∑ i ∈ s, f i) = ∑ i ∈ s, red (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [red_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 : ‖f a‖ ≤ 1 := h a (Finset.mem_insert_self a s)
    have h2 : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [red_add h1 (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one h2), ih h2]

theorem red_natCast_val (k : ZMod p) : red (((k.val : ℕ) : ℚ_[p])) = k := by
  rw [red_natCast, ZMod.natCast_zmod_val]

theorem toZMod_natCast_val (k : ZMod p) : PadicInt.toZMod ((k.val : ℕ) : ℤ_[p]) = k := by
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem two_ne_zero_zmod (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hp' := (Fact.out : p.Prime)
  have := (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).1 h2
  exact hp this

/-! ## Reduction of coordinates -/

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `x` lies in the `ℤ_p`-span of the basis `y` -/
def Integ (y : Module.Basis ι ℚ_[p] V) (x : V) : Prop := ∀ i, ‖y.repr x i‖ ≤ 1

/-- the coordinates of `x` in the basis `y`, reduced modulo `p` -/
def rd (y : Module.Basis ι ℚ_[p] V) (x : V) : ι → ZMod p := fun i => red (y.repr x i)

section Coords

variable (y : Module.Basis ι ℚ_[p] V)

theorem rd_apply (x : V) (i : ι) : rd y x i = red (y.repr x i) := rfl

theorem integ_add {x x' : V} (hx : Integ y x) (hx' : Integ y x') : Integ y (x + x') := by
  intro i
  rw [map_add, Finsupp.add_apply]
  exact norm_add_le_one (hx i) (hx' i)

theorem integ_neg {x : V} (hx : Integ y x) : Integ y (-x) := by
  intro i
  rw [map_neg, Finsupp.neg_apply, norm_neg]
  exact hx i

theorem integ_sub {x x' : V} (hx : Integ y x) (hx' : Integ y x') : Integ y (x - x') := by
  rw [sub_eq_add_neg]
  exact integ_add y hx (integ_neg y hx')

theorem integ_smul {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) {x : V} (hx : Integ y x) : Integ y (c • x) := by
  intro i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact norm_mul_le_one hc (hx i)

theorem integ_zsmul (t : ℤ_[p]) {x : V} (hx : Integ y x) : Integ y (t • x) := by
  rw [zpS_smul]
  exact integ_smul y t.2 hx

theorem integ_basis (i : ι) : Integ y (y i) := by
  intro j
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

theorem integ_zero : Integ y 0 := by
  intro i
  simp

theorem rd_add {x x' : V} (hx : Integ y x) (hx' : Integ y x') :
    rd y (x + x') = rd y x + rd y x' := by
  funext i
  simp only [rd, Pi.add_apply, map_add, Finsupp.add_apply]
  exact red_add (hx i) (hx' i)

theorem rd_neg (x : V) : rd y (-x) = -rd y x := by
  funext i
  simp only [rd, Pi.neg_apply, map_neg, Finsupp.neg_apply]
  exact red_neg _

theorem rd_sub {x x' : V} (hx : Integ y x) (hx' : Integ y x') :
    rd y (x - x') = rd y x - rd y x' := by
  rw [sub_eq_add_neg, rd_add y hx (integ_neg y hx'), rd_neg, ← sub_eq_add_neg]

theorem rd_smul {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) {x : V} (hx : Integ y x) :
    rd y (c • x) = red c • rd y x := by
  funext i
  simp only [rd, Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact red_mul hc (hx i)

theorem rd_zsmul (t : ℤ_[p]) {x : V} (hx : Integ y x) :
    rd y (t • x) = PadicInt.toZMod t • rd y x := by
  rw [zpS_smul, rd_smul y t.2 hx, red_coe]

theorem rd_basis (i : ι) : rd y (y i) = Pi.single i 1 := by
  funext j
  simp only [rd, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h; simp [red_one]
  · rw [if_neg (Ne.symm h), if_neg h, red_zero]

theorem rd_zero : rd y 0 = 0 := by
  funext i
  simp [rd, red_zero]

theorem rd_eq_zero_iff {x : V} (hx : Integ y x) :
    rd y x = 0 ↔ ∀ i, ‖y.repr x i‖ ≤ ‖(p : ℚ_[p])‖ := by
  constructor
  · intro h i
    exact (red_eq_zero_iff' (hx i)).1 (congrFun h i)
  · intro h
    funext i
    exact (red_eq_zero_iff' (hx i)).2 (h i)

theorem rd_eq_iff {x x' : V} (hx : Integ y x) (hx' : Integ y x') :
    rd y x = rd y x' ↔ ∀ i, ‖y.repr (x - x') i‖ ≤ ‖(p : ℚ_[p])‖ := by
  rw [← sub_eq_zero, ← rd_sub y hx hx', rd_eq_zero_iff y (integ_sub y hx hx')]

/-- a lift of reduced coordinates -/
def liftV (v : ι → ZMod p) : V := ∑ i, (((v i).val : ℕ) : ℚ_[p]) • y i

theorem repr_liftV (v : ι → ZMod p) (i : ι) :
    y.repr (liftV y v) i = (((v i).val : ℕ) : ℚ_[p]) := by
  simp only [liftV, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem integ_liftV (v : ι → ZMod p) : Integ y (liftV y v) := by
  intro i
  rw [repr_liftV]
  exact norm_natCast_le_one _

theorem rd_liftV (v : ι → ZMod p) : rd y (liftV y v) = v := by
  funext i
  rw [rd_apply, repr_liftV, red_natCast_val]

theorem repr_liftV_eq_zero {v : ι → ZMod p} {i : ι} (h : v i = 0) : y.repr (liftV y v) i = 0 := by
  rw [repr_liftV, h, ZMod.val_zero, Nat.cast_zero]

end Coords

/-! ## Lifting symplectic transvections and translations to `Γ` -/

section Lift

variable (y : Module.Basis ι ℚ_[p] V) {Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)}
variable {n : ℕ} (B : (ι → ZMod p) → (Fin (2 * n) → ZMod p))

/-- If every symplectic transvection of `F_p^(2n)` is realised (on the reduced coordinates seen
through `B`) by an element of `Γ`, so is every product of transvections. -/
theorem lift_list (hΓ : ∀ γ ∈ Γ, ∀ x, Integ y x → Integ y (γ x))
    (H : ∀ (v : Fin (2 * n) → ZMod p) (a : ZMod p), ∃ γ ∈ Γ, ∀ x, Integ y x →
      B (rd y (γ x)) = Symp.transv v a (B (rd y x)))
    (l : List ((Fin (2 * n) → ZMod p) × ZMod p)) :
    ∃ γ ∈ Γ, ∀ x, Integ y x → B (rd y (γ x)) = Symp.applyList l (B (rd y x)) := by
  induction l with
  | nil => exact ⟨1, Γ.one_mem, fun x _ => rfl⟩
  | cons q l ih =>
    obtain ⟨γ₁, hγ₁, h₁⟩ := H q.1 q.2
    obtain ⟨γ₂, hγ₂, h₂⟩ := ih
    refine ⟨γ₂ * γ₁, Γ.mul_mem hγ₂ hγ₁, fun x hx => ?_⟩
    rw [LinearEquiv.mul_apply, h₂ _ (hΓ γ₁ hγ₁ x hx), h₁ x hx, Symp.applyList_cons]

/-- Transitivity on the nonzero reduced vectors. -/
theorem exists_move (hΓ : ∀ γ ∈ Γ, ∀ x, Integ y x → Integ y (γ x))
    (H : ∀ (v : Fin (2 * n) → ZMod p) (a : ZMod p), ∃ γ ∈ Γ, ∀ x, Integ y x →
      B (rd y (γ x)) = Symp.transv v a (B (rd y x)))
    {u u' : Fin (2 * n) → ZMod p} (hu : u ≠ 0) (hu' : u' ≠ 0) :
    ∃ γ ∈ Γ, ∀ x, Integ y x → B (rd y x) = u → B (rd y (γ x)) = u' := by
  obtain ⟨l, -, -, hl⟩ := Symp.exists_list_transv hu hu'
  obtain ⟨γ, hγ, hγl⟩ := lift_list y B hΓ H l
  exact ⟨γ, hγ, fun x hx hxu => by rw [hγl x hx, hxu, hl]⟩

/-- No line of `F_p^(2n)` is stable: a nonzero reduced vector is moved off its line. -/
theorem exists_off_line
    (H : ∀ (v : Fin (2 * n) → ZMod p) (a : ZMod p), ∃ γ ∈ Γ, ∀ x, Integ y x →
      B (rd y (γ x)) = Symp.transv v a (B (rd y x)))
    {u : Fin (2 * n) → ZMod p} (hu : u ≠ 0) :
    ∃ γ ∈ Γ, ∀ x, Integ y x → B (rd y x) = u → B (rd y (γ x)) ∉ (ZMod p ∙ u) := by
  obtain ⟨v, a, hva⟩ := Symp.exists_transv_not_mem_span hu
  obtain ⟨γ, hγ, hγx⟩ := H v a
  exact ⟨γ, hγ, fun x hx hxu => by rw [hγx x hx, hxu]; exact hva⟩

/-- Conjugating one translation `B x ↦ B x + ℓ x • e` (`e ≠ 0`) by products of transvections gives
the translation by `ℓ x • w` for every `w`. -/
theorem exists_translate (hΓ : ∀ γ ∈ Γ, ∀ x, Integ y x → Integ y (γ x))
    (H : ∀ (v : Fin (2 * n) → ZMod p) (a : ZMod p), ∃ γ ∈ Γ, ∀ x, Integ y x →
      B (rd y (γ x)) = Symp.transv v a (B (rd y x)))
    (ℓ : V → ZMod p) (hℓ : ∀ γ ∈ Γ, ∀ x, ℓ (γ x) = ℓ x) {e : Fin (2 * n) → ZMod p} (he : e ≠ 0)
    (hφ : ∃ φ ∈ Γ, ∀ x, Integ y x → B (rd y (φ x)) = B (rd y x) + ℓ x • e)
    (w : Fin (2 * n) → ZMod p) :
    ∃ γ ∈ Γ, ∀ x, Integ y x → B (rd y (γ x)) = B (rd y x) + ℓ x • w := by
  by_cases hw : w = 0
  · refine ⟨1, Γ.one_mem, fun x _ => ?_⟩
    rw [hw, smul_zero, add_zero]
    rfl
  obtain ⟨l, -, -, hl⟩ := Symp.exists_list_transv he hw
  obtain ⟨S, hS, hSl⟩ := lift_list y B hΓ H l
  obtain ⟨φ, hφΓ, hφe⟩ := hφ
  refine ⟨S * φ * S⁻¹, Γ.mul_mem (Γ.mul_mem hS hφΓ) (Γ.inv_mem hS), fun x hx => ?_⟩
  have hx' : Integ y (S⁻¹ x) := hΓ _ (Γ.inv_mem hS) x hx
  have hSx : S (S⁻¹ x) = x := by simp
  have e1 : B (rd y x) = Symp.applyList l (B (rd y (S⁻¹ x))) := by
    rw [← hSl _ hx', hSx]
  have e2 : ℓ (S⁻¹ x) = ℓ x := by
    have := hℓ S hS (S⁻¹ x)
    rw [hSx] at this
    exact this.symm
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hSl _ (hΓ φ hφΓ _ hx'), hφe _ hx',
    Symp.applyList_add, Symp.applyList_smul, ← e1, e2, hl]

end Lift

/-! ## Counting in quotients -/

section Count

/-- A map that is injective modulo `P` on `A` bounds `#(A / (P ∩ A))`. -/
theorem card_quot_le {A P : Submodule ℤ_[p] V} {T : Type*} [Finite T] (φ : V → T)
    (h : ∀ x ∈ A, ∀ x' ∈ A, φ x = φ x' → x - x' ∈ P) :
    Nat.card (↥A ⧸ P.comap A.subtype) ≤ Nat.card T := by
  set N := P.comap A.subtype
  have surj := Submodule.Quotient.mk_surjective N
  let s := Function.surjInv surj
  have hs : ∀ q, Submodule.Quotient.mk (s q) = q := Function.surjInv_eq surj
  refine Nat.card_le_card_of_injective (fun q => φ (s q : V)) (fun q q' hq => ?_)
  rw [← hs q, ← hs q', Submodule.Quotient.eq]
  have := h _ (s q).2 _ (s q').2 hq
  simpa [N] using this

/-- If `T` injects into `A / (P ∩ A)` (through `ψ`) and is at least as large, every element of
`A` is congruent modulo `P` to some `ψ t`. -/
theorem exists_sub_mem_of_card {A P : Submodule ℤ_[p] V} {T : Type*} (ψ : T → V)
    (hψA : ∀ t, ψ t ∈ A) (hinj : ∀ t t', ψ t - ψ t' ∈ P → t = t')
    [Finite (↥A ⧸ P.comap A.subtype)] (hcard : Nat.card (↥A ⧸ P.comap A.subtype) ≤ Nat.card T) :
    ∀ x ∈ A, ∃ t, x - ψ t ∈ P := by
  set N := P.comap A.subtype
  let f : T → ↥A ⧸ N := fun t => Submodule.Quotient.mk ⟨ψ t, hψA t⟩
  have finj : Function.Injective f := by
    intro t t' htt
    apply hinj
    have := (Submodule.Quotient.eq N).1 htt
    simpa [N] using this
  have fbij := finj.bijective_of_nat_card_le hcard
  intro x hx
  obtain ⟨t, ht⟩ := fbij.2 (Submodule.Quotient.mk ⟨x, hx⟩)
  refine ⟨t, ?_⟩
  have h1 := (Submodule.Quotient.eq N).1 ht
  have h2 : ψ t - x ∈ P := by simpa [N] using h1
  have := P.neg_mem h2
  rwa [neg_sub] at this

end Count

/-! ## Unions of images -/

/-- If `x ≡ γ z (mod P)` with `z ∈ B`, `P ⊆ B` and `P` stable, then `x` is an image of `B`. -/
theorem mem_imgSet_of_sub_mem {Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)} {B P : Submodule ℤ_[p] V}
    (hPB : P ≤ B) (hP : ∀ γ ∈ Γ, ∀ x ∈ P, γ x ∈ P) {x : V} {γ : V ≃ₗ[ℚ_[p]] V} (hγ : γ ∈ Γ)
    {z : V} (hz : z ∈ B) (h : x - γ z ∈ P) : x ∈ imgSet Γ B := by
  refine ⟨γ, hγ, z + γ⁻¹ (x - γ z), B.add_mem hz (hPB (hP _ (Γ.inv_mem hγ) _ h)), ?_⟩
  rw [map_add]
  simp

/-- `A_K(r + q e) = p^q A_K(r)`. -/
theorem imgSet_shift (F : Filtration p V) (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V)) (r q : ℤ) :
    imgSet Γ (F.L (r + q * F.e)) = (smulL ((p : ℚ_[p]) ^ q)) '' imgSet Γ (F.L r) := by
  ext y
  simp only [imgSet, Set.mem_setOf_eq, Set.mem_image, smulL_apply]
  constructor
  · rintro ⟨γ, hγ, x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (F.mem_shift_iff_exists q r x).1 hx
    exact ⟨γ z, ⟨γ, hγ, z, hz, rfl⟩, (map_smul γ _ z).symm⟩
  · rintro ⟨_, ⟨γ, hγ, z, hz, rfl⟩, rfl⟩
    exact ⟨γ, hγ, _, (F.mem_shift_iff_exists q r _).2 ⟨z, hz, rfl⟩, map_smul γ _ z⟩

/-- `𝔪^(r + q e) = p^q 𝔪^r` as sets. -/
theorem L_shift_set (F : Filtration p V) (r q : ℤ) :
    (F.L (r + q * F.e) : Set V) = (smulL ((p : ℚ_[p]) ^ q)) '' (F.L r : Set V) := by
  ext y
  simp only [SetLike.mem_coe, Set.mem_image, smulL_apply]
  rw [F.mem_shift_iff_exists]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

/-! ## Small lemmas on submodules and coordinates -/

/-- if `c • z ∈ N` with `‖c‖ = 1` then `z ∈ N` -/
theorem mem_of_unit_smul_mem (N : Submodule ℤ_[p] V) {c : ℚ_[p]} (hc : ‖c‖ = 1) {z : V}
    (hz : c • z ∈ N) : z ∈ N := by
  have hc0 : c ≠ 0 := by intro h0; rw [h0, norm_zero] at hc; exact zero_ne_one hc
  have hci : ‖c⁻¹‖ ≤ 1 := by rw [norm_inv, hc, inv_one]
  have := N.smul_mem (zp c⁻¹ hci) hz
  rwa [zp_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

/-- `c • z ∈ N` if `z ∈ N` and `‖c‖ ≤ 1` -/
theorem smul_mem_of_norm_le (N : Submodule ℤ_[p] V) {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) {z : V}
    (hz : z ∈ N) : c • z ∈ N := by
  rw [← zp_smul c hc]
  exact N.smul_mem _ hz

/-- for `p` odd, one of `c₁ - c₂`, `c₁ + c₂` is a unit if `c₁` is -/
theorem unit_or_unit (hp : p ≠ 2) {c1 c2 : ℚ_[p]} (hc1 : ‖c1‖ = 1) (hc2 : ‖c2‖ ≤ 1) :
    ‖c1 - c2‖ = 1 ∨ ‖c1 + c2‖ = 1 := by
  by_contra H
  push Not at H
  have hs : ‖c1 - c2‖ ≤ 1 := norm_sub_le_one hc1.le hc2
  have ha : ‖c1 + c2‖ ≤ 1 := norm_add_le_one hc1.le hc2
  have h1 : red (c1 - c2) = 0 := (red_eq_zero_iff hs).2 (lt_of_le_of_ne hs H.1)
  have h2 : red (c1 + c2) = 0 := (red_eq_zero_iff ha).2 (lt_of_le_of_ne ha H.2)
  have h3 : red (c1 - c2) + red (c1 + c2) = 2 * red c1 := by
    rw [red_sub hc1.le hc2, red_add hc1.le hc2]
    ring
  rw [h1, h2, add_zero] at h3
  exact mul_ne_zero (two_ne_zero_zmod hp) (red_ne_zero_of_norm_eq_one hc1) h3.symm

/-- the coordinates of a map that is diagonal in the basis -/
theorem repr_apply_diag (y : Module.Basis ι ℚ_[p] V) (γ : V →ₗ[ℚ_[p]] V) (s : ι → ℚ_[p])
    (hγ : ∀ i, γ (y i) = s i • y i) (x : V) (j : ι) : y.repr (γ x) j = s j * y.repr x j := by
  rw [apply_eq_sum y γ x]
  simp only [hγ, smul_smul, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end LogShellEdge
