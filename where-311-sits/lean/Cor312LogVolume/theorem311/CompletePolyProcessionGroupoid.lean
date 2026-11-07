import Cor312LogVolume.thetalink.CompletePolyIso
import Cor312LogVolume.theorem311.ProcessionFunctorialPolyTransport

set_option autoImplicit false
noncomputable section

namespace CitedLV.Theorem311.CompletePolyProcession

open CitedLV.ThetaLink

universe uG uO

theorem admissibleIso_ext
    {D E : RetainedThetaSide.{uG,uO}}
    {e f : AdmissibleIso D E}
    (hG : ∀ x, e.groupEquiv x = f.groupEquiv x)
    (hO : ∀ x, e.monoidEquiv x = f.monoidEquiv x) :
    e = f := by
  cases e with
  | mk eG eO eEq eLat =>
      cases f with
      | mk fG fO fEq fLat =>
          dsimp at hG hO
          have hg : eG = fG := by
            ext x
            exact hG x
          subst fG
          have ho : eO = fO := by
            ext x
            exact hO x
          subst fO
          rfl

def completePolyProcessionIsoRaw :
    ProcessionIsoRaw (RetainedThetaSide.{uG,uO}) where
  Hom D E := AdmissibleIso D E
  idHom D := AdmissibleIso.refl D
  comp e f := e.trans f
  inv e := e.symm

theorem completePoly_identityLaws :
    ProcessionIdentityLaws
      (completePolyProcessionIsoRaw.{uG, uO}) := by
  constructor
  · intro D E e
    apply admissibleIso_ext
    · intro x
      rfl
    · intro x
      rfl
  · intro D E e
    apply admissibleIso_ext
    · intro x
      rfl
    · intro x
      rfl

theorem completePoly_associative :
    ProcessionCompositionAssociative
      (completePolyProcessionIsoRaw.{uG, uO}) := by
  intro D E F H e f g
  apply admissibleIso_ext
  · intro x
    rfl
  · intro x
    rfl

theorem completePoly_inverseLaws :
    ProcessionInverseLaws
      (completePolyProcessionIsoRaw.{uG, uO}) := by
  constructor
  · intro D E e
    apply admissibleIso_ext
    · intro x
      exact e.groupEquiv.symm_apply_apply x
    · intro x
      exact e.monoidEquiv.symm_apply_apply x
  · intro D E e
    apply admissibleIso_ext
    · intro x
      exact e.groupEquiv.apply_symm_apply x
    · intro x
      exact e.monoidEquiv.apply_symm_apply x

theorem completePoly_groupoidLaws :
    ProcessionGroupoidLaws
      (completePolyProcessionIsoRaw.{uG, uO}) :=
  ⟨completePoly_identityLaws, completePoly_associative,
    completePoly_inverseLaws⟩

def EveryRetainedPairConnected : Prop :=
  ∀ D E : RetainedThetaSide.{uG,uO}, Nonempty (AdmissibleIso D E)

theorem completePoly_everyObjectPairConnected
    (h : EveryRetainedPairConnected.{uG, uO}) :
    EveryObjectPairConnected
      (completePolyProcessionIsoRaw.{uG, uO}) := by
  intro D E
  exact h D E

theorem completePoly_self_connected
    (D : RetainedThetaSide.{uG,uO}) :
    Nonempty
      ((completePolyProcessionIsoRaw.{uG, uO}).Hom D D) :=
  ⟨AdmissibleIso.refl D⟩

theorem completePoly_nonempty_iff
    (D E : RetainedThetaSide.{uG,uO}) :
    (CompletePolyIso D E).Nonempty ↔ Nonempty (AdmissibleIso D E) := by
  constructor
  · rintro ⟨e, _he⟩
    exact ⟨e⟩
  · rintro ⟨e⟩
    exact ⟨e, mem_completePolyIso e⟩

end CitedLV.Theorem311.CompletePolyProcession
end
