import Cor312LogVolume.theorem311.DPrimeStripProcessionCapsule
import Mathlib.LinearAlgebra.PiTensorProduct.DirectSum
import Mathlib.Algebra.Module.PUnit
import Mathlib.Algebra.Category.ModuleCat.Basic

namespace CitedLV.Theorem311

open scoped TensorProduct

universe uD uBase uAbove uLocal

abbrev MonoanalyticOneFactorQ
    {DStrip : Type uD} {Base : Type uBase}
    (Above : Base -> Type uAbove)
    (Local : DStrip -> (q : Base) -> Above q -> ModuleCat.{uLocal} ℚ)
    {n : Nat} (C : FinDPrimeStripCapsuleRaw DStrip n)
    (q : Base) (alpha : Fin n) :=
  DirectSum (Above q) (fun v => Local (C.component alpha) q v)

abbrev AlgebraicMonoanalyticTensorQ
    {DStrip : Type uD} {Base : Type uBase}
    (Above : Base -> Type uAbove)
    (Local : DStrip -> (q : Base) -> Above q -> ModuleCat.{uLocal} ℚ)
    {n : Nat} (C : FinDPrimeStripCapsuleRaw DStrip n)
    (q : Base) :=
  PiTensorProduct ℚ
    (fun alpha : Fin n => MonoanalyticOneFactorQ Above Local C q alpha)

noncomputable def algebraicTensorDecomposition
    {DStrip : Type uD} {Base : Type uBase}
    (Above : Base -> Type uAbove)
    (Local : DStrip -> (q : Base) -> Above q -> ModuleCat.{uLocal} ℚ)
    {n : Nat} (C : FinDPrimeStripCapsuleRaw DStrip n)
    (q : Base) :
    AlgebraicMonoanalyticTensorQ Above Local C q ≃ₗ[ℚ]
      DirectSum ((alpha : Fin n) -> Above q)
        (fun selected => PiTensorProduct ℚ
          (fun alpha : Fin n =>
            Local (C.component alpha) q (selected alpha))) :=
  PiTensorProduct.ofDirectSumEquiv

theorem algebraicTensorDecomposition_maps_pure_summand
    {DStrip : Type uD} {Base : Type uBase}
    (Above : Base -> Type uAbove)
    (Local : DStrip -> (q : Base) -> Above q -> ModuleCat.{uLocal} ℚ)
    {n : Nat} (C : FinDPrimeStripCapsuleRaw DStrip n)
    (q : Base) [DecidableEq (Above q)]
    (selected : (alpha : Fin n) -> Above q)
    (x : (alpha : Fin n) ->
      Local (C.component alpha) q (selected alpha)) :
    algebraicTensorDecomposition Above Local C q
        (PiTensorProduct.tprod ℚ (fun alpha =>
          DirectSum.lof ℚ (Above q)
            (fun v => Local (C.component alpha) q v)
            (selected alpha) (x alpha))) =
      DirectSum.lof ℚ ((alpha : Fin n) -> Above q)
        (fun chosen => PiTensorProduct ℚ
          (fun alpha : Fin n =>
            Local (C.component alpha) q (chosen alpha)))
        selected (PiTensorProduct.tprod ℚ x) := by
  simpa [algebraicTensorDecomposition] using
    (PiTensorProduct.ofDirectSumEquiv_tprod_lof
      (R := ℚ) selected x)

def AlgebraicTensorHasFactor
    {DStrip : Type uD} {n : Nat}
    (_C : FinDPrimeStripCapsuleRaw DStrip n) : Prop :=
  Nonempty (Fin n)

def AlgebraicPacketVisible (M : Type uLocal) [Zero M] : Prop :=
  exists x : M, x ≠ 0

def LocalCarrierHasDStripContrast
    {DStrip : Type uD} {Base : Type uBase}
    (Above : Base -> Type uAbove)
    (Local : DStrip -> (q : Base) -> Above q -> ModuleCat.{uLocal} ℚ) : Prop :=
  exists d0 d1 q v,
    d0 ≠ d1 /\
      Subsingleton (Local d0 q v) /\
      Nontrivial (Local d1 q v)

theorem singleton_directSum_lof_ne_zero
    {M : Type uLocal} [AddCommMonoid M] [Module ℚ M]
    (x : M) (hx : x ≠ 0) :
    DirectSum.lof ℚ Unit (fun _ => M) () x ≠ 0 := by
  intro h
  have mapped := congrArg
    (fun z =>
      (DirectSum.linearEquivFunOnFintype ℚ Unit (fun _ => M) z) ()) h
  apply hx
  simpa using mapped

def boolDependentLocal (d : Bool) (_q _v : Unit) : ModuleCat ℚ :=
  if d then ModuleCat.of ℚ ℚ else ModuleCat.of ℚ PUnit

def falseSingletonCapsule : FinDPrimeStripCapsuleRaw Bool 1 where
  component := fun _ => false

def trueSingletonCapsule : FinDPrimeStripCapsuleRaw Bool 1 where
  component := fun _ => true

def emptyBoolCapsule : FinDPrimeStripCapsuleRaw Bool 0 where
  component := fun i => Fin.elim0 i

theorem bool_dependent_local_has_contrast :
    LocalCarrierHasDStripContrast (fun _ : Unit => Unit)
      boolDependentLocal := by
  refine ⟨false, true, (), (), by decide, ?_, ?_⟩
  · change Subsingleton PUnit
    infer_instance
  · change Nontrivial ℚ
    infer_instance

theorem constant_rational_local_fails_contrast :
    ¬ LocalCarrierHasDStripContrast (fun _ : Unit => Unit)
      (fun (_d : Bool) (_q _v : Unit) => ModuleCat.of ℚ ℚ) := by
  rintro ⟨d0, d1, q, v, hne, hsub, hntriv⟩
  letI : Subsingleton ℚ := hsub
  exact zero_ne_one (Subsingleton.elim (0 : ℚ) 1)

noncomputable def truePureTensor :
    AlgebraicMonoanalyticTensorQ (fun _ : Unit => Unit)
      boolDependentLocal trueSingletonCapsule () :=
  PiTensorProduct.tprod ℚ (fun alpha : Fin 1 =>
    DirectSum.lof ℚ Unit
      (fun v => boolDependentLocal
        (trueSingletonCapsule.component alpha) () v)
      () (1 : ℚ))

theorem true_one_factor_generator_ne_zero :
    DirectSum.lof ℚ Unit
      (fun v => boolDependentLocal
        (trueSingletonCapsule.component (0 : Fin 1)) () v)
      () (1 : ℚ) ≠ 0 := by
  simpa [trueSingletonCapsule, boolDependentLocal] using
    (singleton_directSum_lof_ne_zero (1 : ℚ) (by norm_num))

theorem true_pure_tensor_ne_zero : truePureTensor ≠ 0 := by
  intro h
  have mapped := congrArg
    (fun z => PiTensorProduct.subsingletonEquiv
      (R := ℚ)
      (s := fun alpha : Fin 1 =>
        MonoanalyticOneFactorQ (fun _ : Unit => Unit)
          boolDependentLocal trueSingletonCapsule () alpha)
      (0 : Fin 1) z) h
  apply true_one_factor_generator_ne_zero
  simpa [truePureTensor] using mapped

theorem true_packet_visible :
    AlgebraicPacketVisible
      (AlgebraicMonoanalyticTensorQ (fun _ : Unit => Unit)
        boolDependentLocal trueSingletonCapsule ()) :=
  ⟨truePureTensor, true_pure_tensor_ne_zero⟩

theorem false_packet_subsingleton
    (x y : AlgebraicMonoanalyticTensorQ (fun _ : Unit => Unit)
      boolDependentLocal falseSingletonCapsule ()) : x = y := by
  let e := PiTensorProduct.subsingletonEquiv
    (R := ℚ)
    (s := fun alpha : Fin 1 =>
      MonoanalyticOneFactorQ (fun _ : Unit => Unit)
        boolDependentLocal falseSingletonCapsule () alpha)
    (0 : Fin 1)
  apply e.injective
  apply DirectSum.ext_component ℚ
  intro i
  cases e x i
  cases e y i
  rfl

theorem false_packet_fails_visibility :
    ¬ AlgebraicPacketVisible
      (AlgebraicMonoanalyticTensorQ (fun _ : Unit => Unit)
        boolDependentLocal falseSingletonCapsule ()) := by
  rintro ⟨x, hx⟩
  exact hx (false_packet_subsingleton x 0)

theorem true_capsule_has_factor :
    AlgebraicTensorHasFactor trueSingletonCapsule :=
  ⟨0⟩

theorem empty_capsule_fails_has_factor :
    ¬ AlgebraicTensorHasFactor emptyBoolCapsule := by
  rintro ⟨i⟩
  exact Fin.elim0 i

theorem tensor_construction_does_not_bake_in_source_semantics :
    LocalCarrierHasDStripContrast (fun _ : Unit => Unit)
        boolDependentLocal /\
      AlgebraicPacketVisible
        (AlgebraicMonoanalyticTensorQ (fun _ : Unit => Unit)
          boolDependentLocal trueSingletonCapsule ()) /\
      ¬ AlgebraicPacketVisible
        (AlgebraicMonoanalyticTensorQ (fun _ : Unit => Unit)
          boolDependentLocal falseSingletonCapsule ()) /\
      ¬ LocalCarrierHasDStripContrast (fun _ : Unit => Unit)
        (fun (_d : Bool) (_q _v : Unit) => ModuleCat.of ℚ ℚ) /\
      ¬ AlgebraicTensorHasFactor emptyBoolCapsule :=
  ⟨bool_dependent_local_has_contrast,
    true_packet_visible,
    false_packet_fails_visibility,
    constant_rational_local_fails_contrast,
    empty_capsule_fails_has_factor⟩

end CitedLV.Theorem311
