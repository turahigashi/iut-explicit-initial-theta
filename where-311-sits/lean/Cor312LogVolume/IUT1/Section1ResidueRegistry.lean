import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.FinCases

namespace Src.IUT1.Residue

def Unresolved : Prop := (0 : ℕ) = 1

theorem unresolved_is_false : ¬ Unresolved := by
  intro h
  exact Nat.zero_ne_one h

def Open_F0_etale_fundamental_group : Prop := Unresolved

def Open_F0_semigraph_invariants : Prop := Unresolved

def Open_F0_height_function : Prop := Unresolved

def Open_F0_frobenioid : Prop := Unresolved

def Open_Rem122i_criterion_iff_totally_ramified : Prop := Unresolved

def Open_Rem122ii_dchi_characterizes_cusps : Prop := Unresolved

def Open_Rem122_correction_preserves_characterized_set : Prop := Unresolved

def Open_Rem122_original_exactness_status : Prop := Unresolved

def Open_Rem123_vertical_ramification_iff_equation : Prop := Unresolved

def Open_Rem123_deletion_is_safe : Prop := Unresolved

def Open_Rem123_remaining_corrections : Prop := Unresolved

def Open_Rem112_data_determines_arrow_curves : Prop := Unresolved

def Open_Rem121_aut_equals_deck : Prop := Unresolved

def Open_Cor12_step5_subgroup_equality : Prop := Unresolved

def Open_Thm311_theta_construction : Prop := Unresolved

def Open_Thm311_SHE_compatibility : Prop := Unresolved

def Open_Thm311_symmetry_establishment : Prop := Unresolved

def Open_Thm311_indeterminacy_to_logvolume : Prop := Unresolved

def Open_SS_reading_formalization : Prop := Unresolved

def Open_SSADFs_no_contradiction_without_identification : Prop := Unresolved

def Open_Thm311_symmetry_reduces_F_to_P : Prop := Unresolved

def Open_SS_reading_is_collapse : Prop := Unresolved

def Open_Sec2_prop21_profinite_conjugacy_of_compact : Prop := Unresolved

def Open_Sec2_prop22_commensurable_terminality : Prop := Unresolved

def Open_Sec2_cor23_slimness_and_inertia : Prop := Unresolved

def Open_Sec2_prop24_arithmetic_conjugacy : Prop := Unresolved

def Open_Sec2_cor25_weak_section_conjecture : Prop := Unresolved

def Open_Sec2_thm26_discrete_conjugacy : Prop := Unresolved

def Open_Sec2_lem27_free_surface_properties : Prop := Unresolved

def Open_Sec2_cor28_complex_hyperbolic : Prop := Unresolved

def residuesConstruction : List Prop :=
  [Open_F0_etale_fundamental_group,
   Open_F0_semigraph_invariants,
   Open_F0_height_function,
   Open_F0_frobenioid]

def residuesSourceClaim : List Prop :=
  [Open_Rem122i_criterion_iff_totally_ramified,
   Open_Rem122ii_dchi_characterizes_cusps,
   Open_Rem122_correction_preserves_characterized_set,
   Open_Rem122_original_exactness_status,
   Open_Rem112_data_determines_arrow_curves,
   Open_Rem121_aut_equals_deck,
   Open_Rem123_vertical_ramification_iff_equation,
   Open_Rem123_deletion_is_safe,
   Open_Rem123_remaining_corrections,
   Open_Cor12_step5_subgroup_equality]

def residuesDisputeCore : List Prop :=
  [Open_Thm311_theta_construction,
   Open_Thm311_SHE_compatibility,
   Open_Thm311_symmetry_establishment,
   Open_Thm311_indeterminacy_to_logvolume,
   Open_SS_reading_formalization,
   Open_SSADFs_no_contradiction_without_identification]

def residuesOwnReading : List Prop :=
  [Open_Thm311_symmetry_reduces_F_to_P,
   Open_SS_reading_is_collapse]

def residuesSec2 : List Prop :=
  [Open_Sec2_prop21_profinite_conjugacy_of_compact,
   Open_Sec2_prop22_commensurable_terminality,
   Open_Sec2_cor23_slimness_and_inertia,
   Open_Sec2_prop24_arithmetic_conjugacy,
   Open_Sec2_cor25_weak_section_conjecture,
   Open_Sec2_thm26_discrete_conjugacy,
   Open_Sec2_lem27_free_surface_properties,
   Open_Sec2_cor28_complex_hyperbolic]

def allResidues : List Prop :=
  residuesConstruction ++ residuesSourceClaim ++
    residuesDisputeCore ++ residuesOwnReading ++ residuesSec2

def residueCount : ℕ := allResidues.length

theorem residueCount_eq_thirty : residueCount = 30 := rfl

theorem classification_is_partition :
    residuesConstruction.length + residuesSourceClaim.length +
      residuesDisputeCore.length + residuesOwnReading.length +
      residuesSec2.length = residueCount := rfl

theorem all_residues_are_placeholders : ∀ p ∈ allResidues, p = Unresolved := by
  intro p hp
  fin_cases hp <;> rfl

theorem all_residues_are_currently_unprovable : ∀ p ∈ allResidues, ¬ p :=
  fun p hp hpp => unresolved_is_false ((all_residues_are_placeholders p hp) ▸ hpp)

end Src.IUT1.Residue
