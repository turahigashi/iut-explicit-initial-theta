import Mathlib.Data.Fin.Basic

namespace CitedLV.Theorem311

universe u

structure FinDPrimeStripCapsuleRaw (DStrip : Type u) (size : Nat) where
  component : Fin size -> DStrip

structure DPrimeStripProcessionCandidate (DStrip : Type u) (length : Nat) where
  stage : (k : Fin length) -> FinDPrimeStripCapsuleRaw DStrip (k.val + 1)

def prefixFullIndex {length : Nat} (k : Fin length) (i : Fin (k.val + 1)) :
    Fin length :=
  ⟨i.val, lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) k.isLt⟩

def StrictFrontCapsuleFull
    {DStrip : Type u} {sourceSize targetSize : Nat}
    (source : FinDPrimeStripCapsuleRaw DStrip sourceSize)
    (target : FinDPrimeStripCapsuleRaw DStrip targetSize) : Prop :=
  exists hSize : targetSize = sourceSize + 1,
    forall i,
      source.component i =
        target.component (Fin.cast hSize.symm (Fin.castSucc i))

def HasCapsuleFullSteps
    {DStrip : Type u} {length : Nat}
    (CapsuleFull : {r s : Nat} ->
      FinDPrimeStripCapsuleRaw DStrip r ->
      FinDPrimeStripCapsuleRaw DStrip s -> Prop)
    (P : DPrimeStripProcessionCandidate DStrip length) : Prop :=
  forall k (hk : k.val + 1 < length),
    CapsuleFull (P.stage k) (P.stage ⟨k.val + 1, hk⟩)

def ComesFromAmbientPrefix
    {DStrip : Type u} {length : Nat}
    (P : DPrimeStripProcessionCandidate DStrip length) : Prop :=
  exists ambient : Fin length -> DStrip,
    forall k i,
      (P.stage k).component i = ambient (prefixFullIndex k i)

def ProcessionHasStage
    {DStrip : Type u} {length : Nat}
    (_P : DPrimeStripProcessionCandidate DStrip length) : Prop :=
  Nonempty (Fin length)

def ProcessionStageVisible
    {DStrip : Type u} {length : Nat}
    (P : DPrimeStripProcessionCandidate DStrip length) : Prop :=
  exists k i j,
    i ≠ j /\ (P.stage k).component i ≠ (P.stage k).component j

def goodTwoStageProcession : DPrimeStripProcessionCandidate Bool 2 where
  stage := fun _ =>
    ⟨fun i => decide (i.val = 1)⟩

def badRetentionTwoStageProcession :
    DPrimeStripProcessionCandidate Bool 2 where
  stage := fun k =>
    ⟨fun i => if k.val = 0 then false else decide (i.val = 0)⟩

def closedTwoStageProcession : DPrimeStripProcessionCandidate Bool 2 where
  stage := fun _ => ⟨fun _ => false⟩

def emptyProcession : DPrimeStripProcessionCandidate Bool 0 where
  stage := fun k => Fin.elim0 k

theorem good_procession_has_stage :
    ProcessionHasStage goodTwoStageProcession :=
  ⟨0⟩

theorem empty_procession_fails_has_stage :
    ¬ ProcessionHasStage emptyProcession := by
  rintro ⟨k⟩
  exact Fin.elim0 k

theorem empty_procession_has_vacuous_strict_front_steps :
    HasCapsuleFullSteps StrictFrontCapsuleFull emptyProcession := by
  intro k
  exact Fin.elim0 k

theorem empty_procession_comes_from_vacuous_ambient_prefix :
    ComesFromAmbientPrefix emptyProcession := by
  refine ⟨fun k => Fin.elim0 k, ?_⟩
  intro k
  exact Fin.elim0 k

theorem positivity_is_not_definitionally_baked_in :
    HasCapsuleFullSteps StrictFrontCapsuleFull emptyProcession /\
      ComesFromAmbientPrefix emptyProcession /\
      ¬ ProcessionHasStage emptyProcession :=
  ⟨empty_procession_has_vacuous_strict_front_steps,
    empty_procession_comes_from_vacuous_ambient_prefix,
    empty_procession_fails_has_stage⟩

theorem good_procession_has_strict_front_steps :
    HasCapsuleFullSteps StrictFrontCapsuleFull goodTwoStageProcession := by
  intro k hk
  refine ⟨rfl, ?_⟩
  intro i
  rfl

theorem good_procession_comes_from_ambient_prefix :
    ComesFromAmbientPrefix goodTwoStageProcession := by
  refine ⟨fun i => decide (i.val = 1), ?_⟩
  intro k i
  rfl

theorem good_procession_stage_visible :
    ProcessionStageVisible goodTwoStageProcession := by
  refine ⟨(1 : Fin 2), (0 : Fin 2), (1 : Fin 2),
    (by decide : (0 : Fin 2) ≠ (1 : Fin 2)), ?_⟩
  decide

theorem bad_retention_fails_strict_front_steps :
    ¬ HasCapsuleFullSteps StrictFrontCapsuleFull
      badRetentionTwoStageProcession := by
  intro h
  have hStep := h (0 : Fin 2) (by decide)
  rcases hStep with ⟨hSize, hComponent⟩
  have hFront := hComponent (0 : Fin 1)
  have : false = true := by
    simpa [badRetentionTwoStageProcession] using hFront
  cases this

theorem bad_retention_fails_ambient_prefix :
    ¬ ComesFromAmbientPrefix badRetentionTwoStageProcession := by
  rintro ⟨ambient, hAmbient⟩
  have hZero := hAmbient (0 : Fin 2) (0 : Fin 1)
  have hOne := hAmbient (1 : Fin 2) (0 : Fin 2)
  have hz : false = ambient (0 : Fin 2) := by
    simpa [badRetentionTwoStageProcession, prefixFullIndex] using hZero
  have ho : true = ambient (0 : Fin 2) := by
    simpa [badRetentionTwoStageProcession, prefixFullIndex] using hOne
  exact Bool.noConfusion (hz.trans ho.symm)

theorem closed_procession_comes_from_ambient_prefix :
    ComesFromAmbientPrefix closedTwoStageProcession := by
  exact ⟨fun _ => false, by intro k i; rfl⟩

theorem closed_procession_has_strict_front_steps :
    HasCapsuleFullSteps StrictFrontCapsuleFull closedTwoStageProcession := by
  intro k hk
  exact ⟨rfl, by intro i; rfl⟩

theorem closed_procession_fails_visibility :
    ¬ ProcessionStageVisible closedTwoStageProcession := by
  rintro ⟨k, i, j, _, hij⟩
  exact hij rfl

theorem prefix_and_visibility_are_not_definitionally_baked_in :
    (ProcessionStageVisible badRetentionTwoStageProcession /\
      ¬ ComesFromAmbientPrefix badRetentionTwoStageProcession) /\
    (ComesFromAmbientPrefix closedTwoStageProcession /\
      ¬ ProcessionStageVisible closedTwoStageProcession) := by
  constructor
  · constructor
    · refine ⟨(1 : Fin 2), (0 : Fin 2), (1 : Fin 2),
        (by decide : (0 : Fin 2) ≠ (1 : Fin 2)), ?_⟩
      decide
    · exact bad_retention_fails_ambient_prefix
  · exact ⟨closed_procession_comes_from_ambient_prefix,
      closed_procession_fails_visibility⟩

end CitedLV.Theorem311
