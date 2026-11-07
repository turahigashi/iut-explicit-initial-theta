import Cor312LogVolume.theorem311.DPrimeStripProcessionCapsule
import Cor312LogVolume.theorem311.SourceSpanTensorPacket
import Cor312LogVolume.logshell.ProcessionOnConcrete
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

namespace CitedLV.Theorem311

open Finset

universe uPacket uStrip uBase uAbove uK

structure ProcessionPacketLogVolumeRaw
    {n : Nat} (Packet : Fin n -> Type uPacket) where
  region : (j : Fin n) -> Set (Packet j)
  packetLogVolume : (j : Fin n) -> Set (Packet j) -> Real

noncomputable def processionPacketValue
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (V : ProcessionPacketLogVolumeRaw Packet) (j : Fin n) : Real :=
  V.packetLogVolume j (V.region j)

noncomputable def ordinaryFinMean {n : Nat} (f : Fin n -> Real) : Real :=
  (1 / (n : Real)) * (∑ j, f j)

noncomputable def processionNormalizedLogVolume
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (V : ProcessionPacketLogVolumeRaw Packet) : Real :=
  ordinaryFinMean (fun j => processionPacketValue V j)

theorem procession_normalized_is_one_composition
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (V : ProcessionPacketLogVolumeRaw Packet) :
    processionNormalizedLogVolume V =
      ordinaryFinMean (fun j => V.packetLogVolume j (V.region j)) :=
  rfl

def finalNonzeroProcessionLabel
    {Strip : Type uStrip} {n : Nat}
    (P : DPrimeStripProcessionCandidate Strip (n + 1)) (j : Fin n) : Strip :=
  (P.stage (Fin.last n)).component (Fin.succ j)

abbrev SourceProcessionPacketQ
    {Strip : Type uStrip} {n : Nat}
    (P : DPrimeStripProcessionCandidate Strip (n + 1))
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {arity : Strip -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (Q : SourceShapedLocalMonoanalyticQSpanRaw Base Above Strip arity K)
    (vQ : Base) (j : Fin n) :=
  SourceSpanTensorPacketQ Q (finalNonzeroProcessionLabel P j) vQ

def sourceProcessionPacketLogVolumeRaw
    {Strip : Type uStrip} {n : Nat}
    (P : DPrimeStripProcessionCandidate Strip (n + 1))
    {Base : Type uBase} {Above : Base -> Type uAbove}
    {arity : Strip -> Nat}
    {K : Type uK} [AddCommGroup K] [Module ℚ K]
    (Q : SourceShapedLocalMonoanalyticQSpanRaw Base Above Strip arity K)
    (vQ : Base)
    (region : (j : Fin n) -> Set (SourceProcessionPacketQ P Q vQ j))
    (packetLogVolume :
      (j : Fin n) -> Set (SourceProcessionPacketQ P Q vQ j) -> Real) :
    ProcessionPacketLogVolumeRaw (SourceProcessionPacketQ P Q vQ) where
  region := region
  packetLogVolume := packetLogVolume

def canonicalFinLabelProcession (n : Nat) :
    DPrimeStripProcessionCandidate (Fin (n + 1)) (n + 1) where
  stage := fun k =>
    { component := fun i => prefixFullIndex k i }

theorem canonical_final_nonzero_label {n : Nat} (j : Fin n) :
    finalNonzeroProcessionLabel (canonicalFinLabelProcession n) j = Fin.succ j :=
  rfl

theorem canonical_final_nonzero_label_val {n : Nat} (j : Fin n) :
    (finalNonzeroProcessionLabel (canonicalFinLabelProcession n) j).val =
      j.val + 1 :=
  rfl

def ProcessionAverageHasStage (n : Nat) : Prop := Nonempty (Fin n)

def ProcessionAverageHasTwo (n : Nat) : Prop :=
  Exists fun i : Fin n => Exists fun j : Fin n => i ≠ j

def ProcessionPacketFamilyVisible
    {n : Nat} (Packet : Fin n -> Type uPacket) : Prop :=
  Exists fun j : Fin n => Exists fun x : Packet j => Exists fun y : Packet j => x ≠ y

def SelectedRegionsAdmissible
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (Admissible : (j : Fin n) -> Set (Packet j) -> Prop)
    (V : ProcessionPacketLogVolumeRaw Packet) : Prop :=
  forall j, Admissible j (V.region j)

def PacketLogVolumeInputSensitive
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (Admissible : (j : Fin n) -> Set (Packet j) -> Prop)
    (V : ProcessionPacketLogVolumeRaw Packet) : Prop :=
  Exists fun j => Exists fun S => Exists fun T =>
    Admissible j S /\ Admissible j T /\
      V.packetLogVolume j S ≠ V.packetLogVolume j T

def SelectedPacketProfileLabelVisible
    {n : Nat} {Packet : Fin n -> Type uPacket}
    (V : ProcessionPacketLogVolumeRaw Packet) : Prop :=
  Exists fun i => Exists fun j =>
    i ≠ j /\ processionPacketValue V i ≠ processionPacketValue V j

abbrev checkPacket (_j : Fin 2) : Type := ℚ

def checkAnchorQ (j : Fin 2) : ℚ := ((j.val + 1 : Nat) : ℚ)

def checkAnchorR (j : Fin 2) : Real := ((j.val + 1 : Nat) : Real)

def nonemptyCheckRegion (_j : Fin 2) (S : Set ℚ) : Prop := S.Nonempty

noncomputable def goodCheckPacketVolume :
    ProcessionPacketLogVolumeRaw checkPacket where
  region := fun j => {checkAnchorQ j}
  packetLogVolume := fun j S => by
    classical
    exact if checkAnchorQ j ∈ S then (checkAnchorR j) ^ 2 else -1

noncomputable def hardCodedCheckPacketVolume :
    ProcessionPacketLogVolumeRaw checkPacket where
  region := fun j => {checkAnchorQ j}
  packetLogVolume := fun j _S => (checkAnchorR j) ^ 2

noncomputable def indexErasedCheckPacketVolume :
    ProcessionPacketLogVolumeRaw checkPacket where
  region := fun _ => {1}
  packetLogVolume := fun _ S => by
    classical
    exact if (1 : ℚ) ∈ S then 1 else -1

noncomputable def emptyRegionCheckPacketVolume :
    ProcessionPacketLogVolumeRaw checkPacket where
  region := fun _ => ∅
  packetLogVolume := fun _ _ => 0

theorem two_stage_average_has_stage : ProcessionAverageHasStage 2 :=
  Nonempty.intro 0

theorem zero_stage_average_fails_stage : ¬ ProcessionAverageHasStage 0 := by
  rintro ⟨j⟩
  exact Fin.elim0 j

theorem two_stage_average_has_two : ProcessionAverageHasTwo 2 :=
  Exists.intro 0 (Exists.intro 1 (by decide))

theorem rational_packet_family_visible :
    ProcessionPacketFamilyVisible checkPacket :=
  Exists.intro 0 (Exists.intro 0 (Exists.intro 1 (by norm_num)))

theorem unit_packet_family_fails_visibility :
    ¬ ProcessionPacketFamilyVisible (fun _ : Fin 2 => Unit) := by
  rintro ⟨j, x, y, hxy⟩
  exact hxy (Subsingleton.elim x y)

theorem good_selected_regions_admissible :
    SelectedRegionsAdmissible nonemptyCheckRegion goodCheckPacketVolume := by
  intro j
  exact Set.singleton_nonempty _

theorem empty_selected_regions_fail_admissibility :
    ¬ SelectedRegionsAdmissible nonemptyCheckRegion
      emptyRegionCheckPacketVolume := by
  intro h
  simpa [emptyRegionCheckPacketVolume, nonemptyCheckRegion] using h 0

theorem good_packet_log_volume_input_sensitive :
    PacketLogVolumeInputSensitive nonemptyCheckRegion goodCheckPacketVolume := by
  refine ⟨0, ({1} : Set ℚ), ({2} : Set ℚ),
    Set.singleton_nonempty 1, Set.singleton_nonempty 2, ?_⟩
  norm_num [goodCheckPacketVolume, checkAnchorQ, checkAnchorR]

theorem hard_coded_packet_log_volume_fails_input_sensitivity :
    ¬ PacketLogVolumeInputSensitive nonemptyCheckRegion
      hardCodedCheckPacketVolume := by
  rintro ⟨j, S, T, _hS, _hT, hne⟩
  exact hne rfl

theorem index_erased_log_volume_remains_input_sensitive :
    PacketLogVolumeInputSensitive nonemptyCheckRegion
      indexErasedCheckPacketVolume := by
  refine ⟨0, ({1} : Set ℚ), ({2} : Set ℚ),
    Set.singleton_nonempty 1, Set.singleton_nonempty 2, ?_⟩
  norm_num [indexErasedCheckPacketVolume]

theorem good_selected_profile_label_visible :
    SelectedPacketProfileLabelVisible goodCheckPacketVolume := by
  refine ⟨0, 1, by decide, ?_⟩
  norm_num [processionPacketValue, goodCheckPacketVolume,
    checkAnchorQ, checkAnchorR]

theorem index_erased_profile_fails_label_visibility :
    ¬ SelectedPacketProfileLabelVisible indexErasedCheckPacketVolume := by
  rintro ⟨i, j, _hij, hvalue⟩
  apply hvalue
  fin_cases i <;> fin_cases j <;>
    norm_num [processionPacketValue, indexErasedCheckPacketVolume]

theorem good_check_value_profile (j : Fin 2) :
    processionPacketValue goodCheckPacketVolume j = (checkAnchorR j) ^ 2 := by
  fin_cases j <;>
    norm_num [processionPacketValue, goodCheckPacketVolume,
      checkAnchorQ, checkAnchorR]

theorem good_check_normalized_value :
    processionNormalizedLogVolume goodCheckPacketVolume = (5 : Real) / 2 := by
  norm_num [processionNormalizedLogVolume, ordinaryFinMean,
    processionPacketValue, goodCheckPacketVolume, checkAnchorQ, checkAnchorR,
    Fin.sum_univ_two]

noncomputable def biasedTwoMean (f : Fin 2 -> Real) : Real :=
  (f 0 + 3 * f 1) / 4

theorem biased_mean_differs_on_good_profile :
    biasedTwoMean (fun j => processionPacketValue goodCheckPacketVolume j) ≠
      processionNormalizedLogVolume goodCheckPacketVolume := by
  norm_num [biasedTwoMean, processionNormalizedLogVolume, ordinaryFinMean,
    processionPacketValue, goodCheckPacketVolume, checkAnchorQ, checkAnchorR,
    Fin.sum_univ_two]

theorem ordinaryFinMean_sqScaled_eq_processionAvg
    (c : Real) (n : Nat) :
    ordinaryFinMean (fun j : Fin n =>
      CitedLV.Procession.sqScaled c (j.val + 1)) =
      CitedLV.Procession.processionAvg c n := by
  unfold ordinaryFinMean CitedLV.Procession.processionAvg
  congr 1
  calc
    (∑ j : Fin n, CitedLV.Procession.sqScaled c (j.val + 1)) =
        ∑ m ∈ Finset.range n,
          CitedLV.Procession.sqScaled c (m + 1) :=
      Fin.sum_univ_eq_sum_range
        (fun m : Nat => CitedLV.Procession.sqScaled c (m + 1)) n
    _ = ∑ m ∈ Finset.range (n + 1),
          CitedLV.Procession.sqScaled c m := by
      symm
      simpa [CitedLV.Procession.sqScaled] using
        (Finset.sum_range_succ' (CitedLV.Procession.sqScaled c) n)

theorem ordinaryFinMean_sqScaled_formula
    (c : Real) (n : Nat) (hn : 1 <= n) :
    ordinaryFinMean (fun j : Fin n =>
      CitedLV.Procession.sqScaled c (j.val + 1)) =
      (1 / 6) * (2 * (n : Real) + 1) * ((n : Real) + 1) * c := by
  rw [ordinaryFinMean_sqScaled_eq_processionAvg]
  exact CitedLV.Procession.processionAvg_eq c n hn

end CitedLV.Theorem311
