import Cor312LogVolume.labels.FiniteLabelSymmetry

namespace CitedLV.Entanglement

noncomputable section

structure RingUnitSubquotient (K Q : Type*) [CommRing K] [Monoid Q] where
  carrier : Submonoid Kˣ
  quotient : carrier →* Q
  quotient_surjective : Function.Surjective quotient

def RingUnitSubquotient.IsNondegenerate
    {K Q : Type*} [CommRing K] [Monoid Q]
    (R : RingUnitSubquotient K Q) : Prop :=
  (∃ x y : R.carrier, R.quotient x ≠ R.quotient y) ∧
    (∃ x y : R.carrier, x ≠ y ∧ R.quotient x = R.quotient y)

def modFiveSignSubquotient :
    RingUnitSubquotient (ZMod 5) (CitedLV.Labels.FlStar 5) where
  carrier := ⊤
  quotient :=
    (QuotientGroup.mk' (CitedLV.Labels.plusMinusUnits 5)).comp
      (Submonoid.subtype ⊤)
  quotient_surjective := by
    intro q
    obtain ⟨u, rfl⟩ := Quotient.exists_rep q
    exact ⟨⟨u, trivial⟩, rfl⟩

theorem modFiveSignSubquotient_detects_a_distinction :
    ∃ x y : modFiveSignSubquotient.carrier,
      modFiveSignSubquotient.quotient x ≠
        modFiveSignSubquotient.quotient y := by
  refine ⟨⟨1, trivial⟩, ⟨CitedLV.Labels.twoUnitModFive, trivial⟩, ?_⟩
  exact CitedLV.Labels.flStar_mod_five_nontrivial

theorem modFiveSignSubquotient_forgets_a_distinction :
    ∃ x y : modFiveSignSubquotient.carrier,
      x ≠ y ∧
        modFiveSignSubquotient.quotient x =
          modFiveSignSubquotient.quotient y := by
  refine ⟨⟨1, trivial⟩, ⟨-1, trivial⟩, ?_, ?_⟩
  · intro h
    have hv := congrArg (fun z : modFiveSignSubquotient.carrier =>
      ((z.1 : (ZMod 5)ˣ) : ZMod 5)) h
    exact (by decide : (1 : ZMod 5) ≠ -1) hv
  · exact CitedLV.Labels.flStar_identifies_signs 5 1

theorem modFiveSignSubquotient_nondegenerate :
    modFiveSignSubquotient.IsNondegenerate := by
  exact ⟨modFiveSignSubquotient_detects_a_distinction,
    modFiveSignSubquotient_forgets_a_distinction⟩

end

end CitedLV.Entanglement
