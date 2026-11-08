import LogShellEdge.Realize
import LogShellEdge.MainTheorem

/-!
# The main results from the inputs, with Proposition 4.4 derived

The structures `OddSmall`, `EvenSmall` and `OddLattice` list the maps of Proposition 4.4 as fields.
Here those fields are derived from one input, the conclusion of Lemma 4.1 (`RealizesOdd`,
`RealizesEven`), by `oddMoves_of_realizes` and `evenMoves_of_realizes`. The theorems below state the
main results with only the remaining inputs as hypotheses:

* the data of a small field (`SmallField`): the filtration `𝔪^j`, the basis `y` of `Λ` (Lemmas 2.2(b),
  3.2), the trace, (Γ1) and (Γ2) of Proposition 2.3, the sizes of `𝔪^r/p𝔪`, and the element `pc` of
  Lemma 2.2(d);
* Kondo's description of `ker Tr` ([Kondo, Theorem 1.3]) and Lemma 3.4;
* the realization of Lemma 4.1 (`RealizesOdd` / `RealizesEven`);
* in the totally ramified odd case, the line `𝔪^e/p𝔪 = F_p p̄` and Theorem 6.5 (the field `lift`).
-/

set_option autoImplicit false

noncomputable section

namespace LogShellEdge

variable {p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]

/-- `OddSmall` from the data of a small field of odd degree, Kondo's kernel, Lemma 3.4 and the
realization of Lemma 4.1; the maps of Proposition 4.4(b) are derived. -/
def OddSmall.ofRealizes {g : ℕ} (B : SmallField p V (Fin (2 * g + 1)))
    (hker : ∀ i : Fin (2 * g + 1), i ≠ 0 → B.τ (B.y i) = 0) (hτ0 : ‖B.τ (B.y 0)‖ = 1)
    (hR : RealizesOdd B.Γ B.y) : OddSmall p V g where
  toSmallField := B
  hker := hker
  hτ0 := hτ0
  moveU := (oddMoves_of_realizes B.Γ B.y hR).1
  moveV := (oddMoves_of_realizes B.Γ B.y hR).2.1
  swap := (oddMoves_of_realizes B.Γ B.y hR).2.2

/-- `EvenSmall` from the data of a small field of even degree, Kondo's kernel, Lemma 3.4 and the
realization of Lemma 4.1; the maps of Proposition 4.4(a) are derived. -/
def EvenSmall.ofRealizes {g : ℕ} (hg : 1 ≤ g) (B : SmallField p V (Fin (2 * g)))
    (hker : ∀ i : Fin (2 * g), i.val ≠ 1 → B.τ (B.y i) = 0) (hτ1 : ‖B.τ (B.y ⟨1, by omega⟩)‖ = 1)
    (hR : RealizesEven B.Γ B.y hg) : EvenSmall p V g where
  toSmallField := B
  hg := hg
  hker := hker
  hτ1 := hτ1
  moveT := (evenMoves_of_realizes hg B.Γ B.y hR).1
  moveU := (evenMoves_of_realizes hg B.Γ B.y hR).2

/-- Theorem 6.7 (and Theorem 5.1(a)), even degree, from the inputs. -/
theorem main_even_of_inputs {g : ℕ} (hg : 1 ≤ g) (B : SmallField p V (Fin (2 * g)))
    (hker : ∀ i : Fin (2 * g), i.val ≠ 1 → B.τ (B.y i) = 0) (hτ1 : ‖B.τ (B.y ⟨1, by omega⟩)‖ = 1)
    (hR : RealizesEven B.Γ B.y hg) (m : ℤ) :
    S B.Γ (B.F.L m) = B.F.L (lo B.F.e m) ∧ Reaches B.F B.Γ (B.F.L m) (lo B.F.e m) :=
  main_even (EvenSmall.ofRealizes hg B hker hτ1 hR) m

/-- Theorem 6.7 (and Theorem 5.1(b)), odd degree with `f ≥ 2`, from the inputs. -/
theorem main_odd_f2_of_inputs {g : ℕ} (B : SmallField p V (Fin (2 * g + 1)))
    (hker : ∀ i : Fin (2 * g + 1), i ≠ 0 → B.τ (B.y i) = 0) (hτ0 : ‖B.τ (B.y 0)‖ = 1)
    (hR : RealizesOdd B.Γ B.y) (hf : 2 ≤ B.f) (m : ℤ) :
    S B.Γ (B.F.L m) = B.F.L (lo B.F.e m) ∧ Reaches B.F B.Γ (B.F.L m) (lo B.F.e m) :=
  main_odd_f2 (OddSmall.ofRealizes B hker hτ0 hR) hf m

/-- Theorem 5.1(c): odd degree, `f = 1`, `e ∤ m`, from the inputs (Theorem 6.5 is not used). -/
theorem thm51c_of_inputs {g : ℕ} (B : SmallField p V (Fin (2 * g + 1)))
    (hker : ∀ i : Fin (2 * g + 1), i ≠ 0 → B.τ (B.y i) = 0) (hτ0 : ‖B.τ (B.y 0)‖ = 1)
    (hR : RealizesOdd B.Γ B.y) (m : ℤ) (hm : ¬ ((B.F.e : ℤ) ∣ m)) :
    S B.Γ (B.F.L m) = B.F.L (lo B.F.e m) ∧ Reaches B.F B.Γ (B.F.L m) (lo B.F.e m) :=
  (OddSmall.ofRealizes B hker hτ0 hR).thm51_odd m (Or.inr hm)

/-- Theorem 6.7, odd degree, totally ramified (`d = e = 2g+1 ≥ 3`, `f = 1`), from the inputs; here
Theorem 6.5 enters through the field `lift`. -/
theorem main_odd_tr_of_inputs {g : ℕ} (hg : 1 ≤ g) (B : SmallField p V (Fin (2 * g + 1)))
    (hker : ∀ i : Fin (2 * g + 1), i ≠ 0 → B.τ (B.y i) = 0) (hτ0 : ‖B.τ (B.y 0)‖ = 1)
    (hR : RealizesOdd B.Γ B.y) (hf1 : B.f = 1) (pv : V) (hpv : pv ∈ B.F.L B.F.e)
    (hpvτ : ‖B.τ pv‖ = 1) (hLe : ∀ z ∈ B.F.L B.F.e, ∃ a : ℤ_[p], z - a • pv ∈ B.F.L (1 + B.F.e))
    (s : ℕ) (hs : s = 1)
    (lift : s = 1 → ∀ hg : 1 ≤ g, ∃ φ ∈ B.Γ, ∀ i : Fin (2 * g + 1),
      φ (B.y i) - (if i = 0 then B.y 0 + B.y ⟨1, by omega⟩ else B.y i) ∈ B.F.L (1 + B.F.e))
    (m : ℤ) :
    S B.Γ (B.F.L m) = B.F.L (lo B.F.e m) ∧ Reaches B.F B.Γ (B.F.L m) (lo B.F.e m) :=
  main_odd_tr (g := g)
    { toOddSmall := OddSmall.ofRealizes B hker hτ0 hR
      hf1 := hf1, pv := pv, hpv := hpv, hpvτ := hpvτ, hLe := hLe, s := s, hs := hs, lift := lift }
    hg m

/-- `OddLattice` from the realization of Lemma 4.1; the maps of Proposition 4.4(b) inside the pairs
are derived. -/
def OddLattice.ofRealizes {g : ℕ} (Γ : Subgroup (V ≃ₗ[ℚ_[p]] V))
    (y : Module.Basis (Fin (2 * g + 1)) ℚ_[p] V) (τ : V →ₗ[ℚ_[p]] ℚ_[p])
    (hΓ2 : ∀ γ ∈ Γ, ∀ x, τ (γ x) = τ x) (hker : ∀ i : Fin (2 * g + 1), i ≠ 0 → τ (y i) = 0)
    (hτ0 : τ (y 0) ≠ 0) (hR : RealizesOdd Γ y) (s : ℕ)
    (lift : s = 1 → ∀ hg : 1 ≤ g, ∃ φ ∈ Γ, ∀ i j : Fin (2 * g + 1),
      ‖y.repr (φ (y i) - (if i = 0 then y 0 + y ⟨1, by omega⟩ else y i)) j‖ ≤ ‖(p : ℚ_[p])‖) :
    OddLattice p V g where
  Γ := Γ
  y := y
  τ := τ
  hΓ2 := hΓ2
  hker := hker
  hτ0 := hτ0
  moveU := (oddMoves_of_realizes Γ y hR).1
  moveV := (oddMoves_of_realizes Γ y hR).2.1
  s := s
  lift := lift

end LogShellEdge
