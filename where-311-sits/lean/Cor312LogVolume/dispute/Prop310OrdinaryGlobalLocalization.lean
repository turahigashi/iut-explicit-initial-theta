import Cor312LogVolume.dispute.Prop310OrdinaryLocalIntersection
import Cor312LogVolume.theorem311.LabeledGlobalNumberFieldInclusion

set_option autoImplicit false
noncomputable section
namespace Dispute.Prop310OrdinaryGlobalLocalization

open scoped NumberField
open NumberField
open Dispute.Prop310OrdinaryLocalIntersection
open Dispute.Prop310ActualIntersection
open CitedLV.Theorem311

universe u

variable (F : Type u) [Field F] [NumberField F]

abbrev Place := OrdinaryPlace F

abbrev LocalField : Place F → Type u
  | Sum.inl v => v.adicCompletion F
  | Sum.inr _ => ULift.{u} ℂ

noncomputable instance (w : Place F) : Field (LocalField F w) := by
  cases w <;> infer_instance

noncomputable instance normLocalField (w : Place F) : Norm (LocalField F w) := by
  cases w <;> infer_instance

@[simp] theorem norm_ulift_ringEquiv_symm (z : ℂ) :
    ‖(ULift.ringEquiv : ULift.{u} ℂ ≃+* ℂ).symm z‖ = ‖z‖ := by
  rw [ULift.norm_def]
  rfl

noncomputable def localEmbedding (w : Place F) : F →+* LocalField F w :=
  match w with
  | Sum.inl v => FinitePlace.embedding v
  | Sum.inr φ => (ULift.ringEquiv : ULift.{u} ℂ ≃+* ℂ).symm.toRingHom.comp φ

theorem localEmbedding_injective (w : Place F) :
    Function.Injective (localEmbedding F w) :=
  (localEmbedding F w).injective

def localizeUnits (w : Place F) : Fˣ →* (LocalField F w)ˣ :=
  Units.map (localEmbedding F w).toMonoidHom

abbrev Copy (_ : Unit) := Fˣ
abbrev LocalPacket (_ : Unit) (w : Place F) := (LocalField F w)ˣ

def ordinaryGlobalInclusionRaw :
    LabeledNumberFieldGlobalInclusionRaw
      Unit (Place F) (Copy F) (LocalPacket F) where
  embed := fun _ x w => localizeUnits F w x

theorem ordinaryGlobalInclusion_injective :
    GlobalInclusionInjective (ordinaryGlobalInclusionRaw F) := by
  intro j x y hxy
  let φ : F →+* ℂ := (inferInstance : Nonempty (F →+* ℂ)).some
  have hφ := congrFun hxy (Sum.inr φ)
  apply Units.ext
  apply φ.injective

  exact congrArg (fun u : (LocalField F (Sum.inr φ))ˣ => (ULift.down (u : LocalField F (Sum.inr φ)))) hφ

def localProductIntegral
    (y : GlobalLocalPacketProduct Unit (Place F) (LocalPacket F) ()) : Prop :=

  ∀ w : Place F, ‖((y w : (LocalField F w)ˣ) : LocalField F w)‖ ≤ 1

theorem localProductIntegral_embed_iff
    (x : Fˣ) :
    localProductIntegral F ((ordinaryGlobalInclusionRaw F).embed () x) ↔
      x ∈ localIntegralIntersection F := by
  constructor
  · intro h
    apply Set.mem_iInter.mpr
    intro w
    have hw := h w
    cases w with
    | inl v =>
        simpa [localProductIntegral, ordinaryGlobalInclusionRaw,
          localizeUnits, localEmbedding, LocalField, localIntegralLocus] using hw
    | inr φ =>
        simpa [localProductIntegral, ordinaryGlobalInclusionRaw,
          localizeUnits, localEmbedding, LocalField, localIntegralLocus] using hw
  · intro h w
    have hw := Set.mem_iInter.mp h w
    cases w with
    | inl v =>
        simpa [localProductIntegral, ordinaryGlobalInclusionRaw,
          localizeUnits, localEmbedding, LocalField, localIntegralLocus] using hw
    | inr φ =>
        simpa [localProductIntegral, ordinaryGlobalInclusionRaw,
          localizeUnits, localEmbedding, LocalField, localIntegralLocus] using hw

theorem globalLocalization_integral_preimage_eq_rootsOfUnity :
    {x : Fˣ |
      localProductIntegral F ((ordinaryGlobalInclusionRaw F).embed () x)} =
        rootOfUnityImage F := by
  ext x

  rw [Set.mem_setOf_eq, localProductIntegral_embed_iff F x,
    localIntegralIntersection_eq_rootOfUnityImage F]

end Dispute.Prop310OrdinaryGlobalLocalization
end
