import Cor312LogVolume.logshell.LogVolumeGrounded
import Mathlib.Order.Bounds.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic.Linarith

namespace CitedLV.StepXConcrete

open CitedLV.LogVolume

variable (p : ℕ) [hp : Fact p.Prime]

def NormBounded {ι : Type*} (f : ι → ℚ_[p]) (b : ℝ) : Prop :=
  ∀ i : ι, ‖f i‖ ≤ b

theorem bound_exists_of_bounded {ι : Type*} (f : ι → ℚ_[p]) (b : ℝ)
    (hb : NormBounded p f b) :
    ∃ B : ℝ, ∀ i : ι, ‖f i‖ ≤ B :=
  ⟨b, hb⟩

theorem le_bound {ι : Type*} (f : ι → ℚ_[p]) (b : ℝ)
    (hb : NormBounded p f b) (i : ι) : ‖f i‖ ≤ b := hb i

theorem bound_invariant_under_units {ι : Type*} (f : ι → ℚ_[p]) (b : ℝ)
    (hb : NormBounded p f b) (u : ℤ_[p]ˣ) :
    NormBounded p (fun i => (u : ℤ_[p]) • f i) b := by
  intro i
  have h1 : ‖(algebraMap ℤ_[p] ℚ_[p]) ((u : ℤ_[p]))‖ = 1 := by
    show ‖(((u : ℤ_[p]) : ℚ_[p]))‖ = 1
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.norm_units u
  have : ‖(u : ℤ_[p]) • f i‖ = ‖f i‖ := by
    rw [Algebra.smul_def, norm_mul, h1, one_mul]
  rw [this]
  exact hb i

def belowSet (b : ℝ) : Set ℝ := {lam : ℝ | lam ≤ b}

theorem belowSet_downward_closed {b x y : ℝ}
    (hx : x ∈ belowSet b) (hyx : y ≤ x) : y ∈ belowSet b :=
  le_trans hyx hx

theorem norm_mem_belowSet {ι : Type*} (f : ι → ℚ_[p]) (b : ℝ)
    (hb : NormBounded p f b) (i : ι) : ‖f i‖ ∈ belowSet b := hb i

theorem grounded_step_x_concrete {ι : Type*} (f : ι → ℚ_[p]) (b : ℝ)
    (hb : NormBounded p f b) (u : ℤ_[p]ˣ) (i : ι) :
    (∃ B : ℝ, ∀ j : ι, ‖f j‖ ≤ B) ∧
    (‖f i‖ ≤ b) ∧
    (NormBounded p (fun j => (u : ℤ_[p]) • f j) b) ∧
    (‖f i‖ ∈ belowSet b) ∧
    (∀ x y : ℝ, x ∈ belowSet b → y ≤ x → y ∈ belowSet b) :=
  ⟨bound_exists_of_bounded p f b hb,
   le_bound p f b hb i,
   bound_invariant_under_units p f b hb u,
   norm_mem_belowSet p f b hb i,
   fun _ _ hx hyx => belowSet_downward_closed hx hyx⟩

theorem left_end_closed {ι : Type*} (f : ι → ℚ_[p]) (b : ℝ)
    (hb : NormBounded p f b) :
    (∀ i : ι, ‖f i‖ ∈ belowSet b) ∧
    (∀ x y : ℝ, x ∈ belowSet b → y ≤ x → y ∈ belowSet b) ∧
    (∀ u : ℤ_[p]ˣ, NormBounded p (fun j => (u : ℤ_[p]) • f j) b) :=
  ⟨fun i => norm_mem_belowSet p f b hb i,
   fun _ _ hx hyx => belowSet_downward_closed hx hyx,
   fun u => bound_invariant_under_units p f b hb u⟩

end CitedLV.StepXConcrete
