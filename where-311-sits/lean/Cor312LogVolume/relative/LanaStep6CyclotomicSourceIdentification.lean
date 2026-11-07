import Cor312LogVolume.relative.LanaStep6FactorialCofinalLimit
import Cor312LogVolume.relative.LanaStep6GenericKummerMap
import Mathlib.Algebra.Category.Grp.Limits

noncomputable section

namespace Src.CoreLayer.LanaStep6.CyclotomicSourceIdentification

open CategoryTheory CategoryTheory.Limits
open Src.CoreLayer.LanaStep6.FiniteKummerRatio
open Src.CoreLayer.LanaStep6.GenericKummerMap
open Src.CoreLayer.LanaStep6.GenericKummerMap.AlgClosureCarrier

universe u

variable (K : Type u) [Field K]

open Src.CoreLayer.LanaStep6.FactorialCofinalLimit

def asKummerDegree (d : CyclotomicDegree) : KummerDegree :=
  ⟨d.val, d.pos⟩

def asCyclotomicDegree (d : KummerDegree) : CyclotomicDegree :=
  ⟨d.val, d.pos⟩

@[simp] theorem asKummerDegree_val (d : CyclotomicDegree) :
    (asKummerDegree d).val = d.val := rfl

@[simp] theorem asCyclotomicDegree_val (d : KummerDegree) :
    (asCyclotomicDegree d).val = d.val := rfl

theorem rootsTransition_eq_torsionTransition
    {m n : CyclotomicDegree} (h : m ≤ n) :
    rootsTransition K h =
      torsionTransition (A := (Closure K)ˣ)
        (show asKummerDegree m ≤ asKummerDegree n from h) := by
  apply MonoidHom.ext
  intro z
  apply Subtype.ext
  rfl

def sourceCyclotomicProjection (d : CyclotomicDegree) :
    (closureCoefficientInput K).Lambda →*
      rootsOfUnity d.val (Closure K) :=
  (closureCoefficientInput K).lambdaProjection (asKummerDegree d)

def sourceCyclotomicCone :
    Cone (fullCyclotomicDiagram K) where
  pt := CommGrpCat.of ((closureCoefficientInput K).Lambda)
  π :=
    { app := fun j =>
        CommGrpCat.ofHom
          (sourceCyclotomicProjection K (OrderDual.ofDual j))
      naturality := by
        intro i j f
        apply CommGrpCat.Hom.ext
        apply MonoidHom.ext
        intro z
        let hC :
            OrderDual.ofDual j ≤ OrderDual.ofDual i :=
          leOfHom f
        let hK :
            asKummerDegree (OrderDual.ofDual j) ≤
              asKummerDegree (OrderDual.ofDual i) :=
          hC
        dsimp only [Functor.const_obj_map, Category.id_comp,
          CommGrpCat.hom_ofHom]
        show (sourceCyclotomicProjection K (OrderDual.ofDual j)) z
            = rootsTransition K hC
                ((sourceCyclotomicProjection K (OrderDual.ofDual i)) z)
        rw [rootsTransition_eq_torsionTransition K hC]
        exact
          (KummerCoefficientInput.lambdaProjection_transition
            (closureCoefficientInput K) hK z).symm }

noncomputable def sourceCyclotomicConeIsLimit :
    IsLimit (sourceCyclotomicCone K) where
  lift s :=
    CommGrpCat.ofHom
      { toFun := fun x =>
          ⟨fun d =>
              (s.π.app
                (OrderDual.toDual (asCyclotomicDegree d))).hom x,
            by
              intro m n hmn
              let f :
                  (OrderDual.toDual (asCyclotomicDegree n) : FullIndex) ⟶
                    OrderDual.toDual (asCyclotomicDegree m) :=
                homOfLE hmn
              have hs :=
                CategoryTheory.ConcreteCategory.congr_hom (s.w f) x
              let hC :
                  asCyclotomicDegree m ≤ asCyclotomicDegree n :=
                hmn
              change
                rootsTransition K hC
                    ((s.π.app
                      (OrderDual.toDual (asCyclotomicDegree n))).hom x) =
                  (s.π.app
                    (OrderDual.toDual (asCyclotomicDegree m))).hom x at hs
              rw [rootsTransition_eq_torsionTransition K hC] at hs
              exact hs⟩
        map_one' := by
          apply Subtype.ext
          funext d
          exact map_one
            (s.π.app (OrderDual.toDual (asCyclotomicDegree d))).hom
        map_mul' := by
          intro x y
          apply Subtype.ext
          funext d
          exact map_mul
            (s.π.app (OrderDual.toDual (asCyclotomicDegree d))).hom x y }
  fac s j := by
    apply CommGrpCat.Hom.ext
    apply MonoidHom.ext
    intro x
    rfl
  uniq s m hm := by
    apply CommGrpCat.Hom.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    funext d
    have h :=
      CategoryTheory.ConcreteCategory.congr_hom
        (hm (OrderDual.toDual (asCyclotomicDegree d))) x
    exact h

noncomputable def closureLambdaIsoFullCyclotomicLimit :
    CommGrpCat.of ((closureCoefficientInput K).Lambda) ≅
      limit (fullCyclotomicDiagram K) :=
  (sourceCyclotomicConeIsLimit K).conePointUniqueUpToIso
    (limit.isLimit (fullCyclotomicDiagram K))

noncomputable def closureLambdaEquivLanaCyclotomicLimit :
    (closureCoefficientInput K).Lambda ≃*
      (limit (fullCyclotomicDiagram K)).carrier :=
  (closureLambdaIsoFullCyclotomicLimit K).commGroupIsoToMulEquiv

theorem closureLambdaEquivLanaCyclotomicLimit_projection
    (z : (closureCoefficientInput K).Lambda)
    (d : CyclotomicDegree) :
    (limit.π (fullCyclotomicDiagram K) (OrderDual.toDual d)).hom
        (((closureLambdaIsoFullCyclotomicLimit K).hom).hom z) =
      sourceCyclotomicProjection K d z := by
  exact CategoryTheory.ConcreteCategory.congr_hom
    (CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp
      (sourceCyclotomicConeIsLimit K)
      (limit.isLimit (fullCyclotomicDiagram K))
      (OrderDual.toDual d)) z

end Src.CoreLayer.LanaStep6.CyclotomicSourceIdentification
