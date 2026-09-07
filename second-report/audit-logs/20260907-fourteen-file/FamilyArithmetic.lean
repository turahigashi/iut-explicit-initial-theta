/-!
# Finite arithmetic behind Proposition 2 (the existence family)

Proposition 2 of the report is an existence statement over all `N`, and most of its
proof -- Hensel lifting, a sieve over primes, a density bound and an asymptotic -- is
NOT formalised anywhere in this development, as the Reproduction section says.

What IS formalised here is the finite, algebraic part, and specifically the step whose
absence was a real gap: the root count in the sieve needs `q ∤ M = 5 p^(N+1)`, so the
case `q = p` has to be excluded, and an earlier version of the proof did not exclude
it.  External review found that on 2026-09-07.  The lemma below is the exclusion.

Nothing here imports anything beyond `Init`.

`f(A) = (A^2 + 1) * ((A-1)^2 + 1)`, the norm form of the family.
-/

namespace FamilyArith

/-- **The gap, closed.**  If `p` divides both `r^2 + 1` and `(r-1)^2 + 1`, then `p ∣ 5`.

The sieve chooses `A ≡ r (mod p)` with `r^2 ≡ -1 (mod p)`, so `p` divides the first
factor of `f(A)` to order exactly `N`.  This says `p` cannot also divide the second
factor unless `p ∣ 5`, which the family excludes.  Hence `p ∤ G_N(x)`, hence `q ≠ p`
for any `q` with `q^7 ∣ G_N(x)`, which is what makes `q ∤ M` and lets the roots in `x`
be counted by the roots of `f`. -/
theorem dvd_five_of_both (p r : Int)
    (h1 : p ∣ (r * r + 1)) (h2 : p ∣ ((r - 1) * (r - 1) + 1)) : p ∣ 5 := by
  -- p divides the difference of the two factors, which is 2r - 1
  have e1 : (r * r + 1) - ((r - 1) * (r - 1) + 1) = 2 * r - 1 := by
    simp [Int.sub_mul, Int.mul_sub]; omega
  have hlin : p ∣ (2 * r - 1) := e1 ▸ Int.dvd_sub h1 h2
  -- 4*(r^2+1) - (2r-1)(2r+1) = 5, and p divides each term on the left
  -- omega is linear, so the two products are supplied to it as facts
  -- NOTE: `Int.mul_left_comm` is flagged "unused" by the linter and is NOT: dropping
  -- it makes this `simp` fail, and a failed tactic silently puts `sorryAx` into every
  -- theorem below.  Verified by `#print axioms` after each edit.
  have sq4 : (2 * r) * (2 * r) = 4 * (r * r) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have key : 4 * (r * r + 1) - (2 * r - 1) * (2 * r + 1) = 5 := by
    simp [Int.sub_mul, Int.mul_add]; omega
  obtain ⟨d, hd⟩ := h1
  obtain ⟨c, hc⟩ := hlin
  have hA : p ∣ 4 * (r * r + 1) := ⟨4 * d, by
    rw [hd]; simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]⟩
  have hB : p ∣ (2 * r - 1) * (2 * r + 1) := ⟨c * (2 * r + 1), by
    rw [hc]; simp [Int.mul_assoc]⟩
  exact key ▸ Int.dvd_sub hA hB

/-- The contrapositive, in the form the proof uses: a prime not dividing `5` and
dividing `r^2 + 1` does not divide `(r-1)^2 + 1`. -/
theorem not_dvd_other_factor (p r : Int)
    (hp : ¬ (p ∣ 5)) (h1 : p ∣ (r * r + 1)) : ¬ (p ∣ ((r - 1) * (r - 1) + 1)) :=
  fun h2 => hp (dvd_five_of_both p r h1 h2)

/-- The factorisation of the integer `400`.  **This is not a discriminant theorem.**
`400` is the value of `disc(f)` for `f(A) = (A^2+1)((A-1)^2+1)`, computed by ordinary
means outside Lean; neither `f` nor the discriminant appears in the statement below.
What the kernel checks is the numeric identity, which is what the sieve uses when it
says only `2` and `5` need separate treatment. -/
theorem four_hundred_factors : (400 : Int) = 2 ^ 4 * 5 ^ 2 := by decide

end FamilyArith
