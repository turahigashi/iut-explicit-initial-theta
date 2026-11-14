/-
# The shape of Definition 5.2 and the two squares do not decide non-degeneracy

This file collects three statements about the prime-strip skeleton of
`FVdashPrimeStripSkeleton.lean`.

1. The degenerate case, in which every component is the closed unit `ZMod 1`,
   satisfies `PrimeLabelSquare` (compatibility with the labels of primes) and
   `RhoNaturalitySquare` (naturality of `ρ`), but not `FVdashIsoNondegenerate`.
   So the shape of [IUTchI] Definition 5.2 together with the two commutative
   squares does not exclude the trivial case (a restatement of
   `source_shape_and_squares_do_not_exclude_closed_unit`).
2. The two squares are independent of each other: either can hold while the
   other fails (a restatement of `prime_and_rho_compatibility_are_independent`).
3. Hence non-degeneracy is an additional input that does not follow from the
   definition; it has to be supplied by the actual construction
   ([IUTchI] §§4–6, Hodge theatres).

No new axioms and no `sorry`.
-/
import M3.thetalink.FVdashPrimeStripSkeleton

namespace IUTFormal.Bridge.ShapeDoesNotDecide

open IUTFormal.ThetaLink

/-! ## 1. Shape and commutativity do not exclude degeneration -/

/-- Restatement of an existing theorem: the degenerate case satisfies the shape
and both squares but is not non-degenerate.  So the shape of Definition 5.2
alone does not decide the matter. -/
theorem shape_admits_degenerate :
    PrimeLabelSquare closedFVdashIso
    ∧ RhoNaturalitySquare closedFVdashIso
    ∧ ¬ FVdashIsoNondegenerate closedFVdashIso :=
  source_shape_and_squares_do_not_exclude_closed_unit

/-! ## 2. The two squares are independent -/

/-- Restatement of an existing theorem: compatibility with the labels of primes
and naturality of `ρ` are independent; either can hold while the other fails,
so having both is not automatic. -/
theorem two_squares_are_independent :
    (RhoNaturalitySquare toyWrongPrimeFVdashIso
      ∧ FVdashIsoNondegenerate toyWrongPrimeFVdashIso
      ∧ ¬ PrimeLabelSquare toyWrongPrimeFVdashIso)
    ∧ (PrimeLabelSquare toyWrongRhoFVdashIso
      ∧ FVdashIsoNondegenerate toyWrongRhoFVdashIso
      ∧ ¬ RhoNaturalitySquare toyWrongRhoFVdashIso) :=
  prime_and_rho_compatibility_are_independent

/-! ## 3. Non-degeneracy is an additional input -/

/-- Consequence: satisfying the shape and both squares does not give
non-degeneracy (`shape_admits_degenerate`), so non-degeneracy is an additional
input that the definition does not provide; it is supplied by the actual
construction (Hodge theatres, [IUTchI] §§4–6). -/
theorem nondegeneracy_is_an_extra_input :
    ∃ _ : Unit,
      (PrimeLabelSquare closedFVdashIso ∧ RhoNaturalitySquare closedFVdashIso)
      ∧ ¬ FVdashIsoNondegenerate closedFVdashIso :=
  ⟨(), ⟨shape_admits_degenerate.1, shape_admits_degenerate.2.1⟩,
   shape_admits_degenerate.2.2⟩

/-! ## 4. Summary -/

/-- Summary of 1–3: the shape and the two squares do not exclude the degenerate
case, and the two squares are independent of each other.  Identifying the
objects therefore needs the non-degeneracy input from the actual construction. -/
theorem summary :
    (PrimeLabelSquare closedFVdashIso
      ∧ RhoNaturalitySquare closedFVdashIso
      ∧ ¬ FVdashIsoNondegenerate closedFVdashIso)
    ∧ ((RhoNaturalitySquare toyWrongPrimeFVdashIso
          ∧ ¬ PrimeLabelSquare toyWrongPrimeFVdashIso)
        ∧ (PrimeLabelSquare toyWrongRhoFVdashIso
          ∧ ¬ RhoNaturalitySquare toyWrongRhoFVdashIso)) :=
  ⟨shape_admits_degenerate,
   ⟨⟨two_squares_are_independent.1.1, two_squares_are_independent.1.2.2⟩,
    ⟨two_squares_are_independent.2.1, two_squares_are_independent.2.2.2⟩⟩⟩

end IUTFormal.Bridge.ShapeDoesNotDecide
