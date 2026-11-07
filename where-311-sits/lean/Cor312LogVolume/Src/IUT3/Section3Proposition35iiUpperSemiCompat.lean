import Mathlib
import Cor312LogVolume.Src.IUT3.Section1Remark122LogShellInclusions

namespace Src.IUT3.Proposition35ii

open Metric Set SrcLib.LocalFieldLogIsometry Src.IUT3.Proposition39iv Src.IUT3.Remark122
open scoped TensorProduct

section Place

variable (p : ℕ) [Fact p.Prime] {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [CompleteSpace K]
  [IsUltrametricDist K]

def PrimeToPRoot (ζ : K) : Prop := ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ζ ^ N = 1

def LogRel (u x : K) : Prop :=
  ‖u‖ = 1 ∧ ∃ ζ : K, PrimeToPRoot p ζ ∧ ‖u * ζ⁻¹ - 1‖ < 1 ∧ x = logUnit (u * ζ⁻¹)

def LogIter : ℕ → K → K → Prop
  | 0, u, x => x = u
  | n + 1, u, x => ∃ w, LogIter n u w ∧ LogRel p w x

variable {p}

include p

theorem zero_mem_logShell : (0 : K) ∈ logShell (K := K) p := by
  refine ⟨1, one_mem_principalUnits (p := p), ?_⟩
  rw [mul_zero]
  unfold logUnit
  rw [sub_self]
  exact (log1p_zero (p := p)).symm

theorem unit_mem_logShell {u : K} (hu : ‖u‖ ≤ 1) : u ∈ logShell (K := K) p :=
  intO_subset_logShell (p := p) (by rw [intO, mem_closedBall_zero_iff]; exact hu)

theorem logRel_mem {u x : K} (h : LogRel p u x) : x ∈ logShell (K := K) p := by
  obtain ⟨_, ζ, _, hprin, rfl⟩ := h
  exact log_subset_logShell (p := p) ⟨u * ζ⁻¹, hprin, rfl⟩

theorem logIter_mem {m : ℕ} (hm : 1 ≤ m) {u x : K} (h : LogIter p m u x) : x ∈ logShell (K := K) p := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨w, _, hw⟩ := h
  exact logRel_mem hw

theorem kummer_logUnit (κ : K ≃ₐ[ℚ_[p]] K) (hκ : ∀ x, ‖κ x‖ = ‖x‖) {u : K} (hu : ‖u - 1‖ < 1) :
    κ (logUnit u) = logUnit (κ u) := by
  have hc : Continuous κ := (AddMonoidHomClass.isometry_of_norm κ hκ).continuous
  have hsub : κ u - 1 = κ (u - 1) := by simp
  unfold logUnit log1p
  rw [(summable_signed p (u - 1) hu).map_tsum κ hc, hsub]
  congr 1
  funext n
  simp [term, map_mul, map_pow, map_div₀, map_neg, map_one, map_natCast]

theorem kummer_mem_logShell (κ : K ≃ₐ[ℚ_[p]] K) (hκ : ∀ x, ‖κ x‖ = ‖x‖) {x : K}
    (hx : x ∈ logShell (K := K) p) : κ x ∈ logShell (K := K) p := by
  obtain ⟨u, hu, hux⟩ := hx
  have hu' : ‖u - 1‖ < 1 := hu
  refine ⟨κ u, ?_, ?_⟩
  · show ‖κ u - 1‖ < 1
    rw [show κ u - 1 = κ (u - 1) by simp, hκ]
    exact hu'
  · rw [← kummer_logUnit (p := p) κ hκ hu', ← hux, map_mul, map_natCast]

end Place

section Packet

variable (p : ℕ) [Fact p.Prime] {ι : Type*} [DecidableEq ι] (K : ι → Type*) [∀ v, NormedField (K v)]
  [∀ v, NormedAlgebra ℚ_[p] (K v)] [∀ v, CompleteSpace (K v)] [∀ v, IsUltrametricDist (K v)] (j : ℕ)

abbrev PlaceSum := (v : ι) → K v

def sumShell : Set (PlaceSum K) := {y | ∀ v, y v ∈ logShell (K := K v) p}

abbrev Packet := ⨂[ℚ_[p]] (_t : Fin (j + 1)), PlaceSum K

noncomputable def packetShell : AddSubgroup (Packet p K j) :=
  AddSubgroup.closure
    {z | ∃ y : Fin (j + 1) → PlaceSum K, (∀ t, y t ∈ sumShell p K) ∧ z = PiTensorProduct.tprod ℚ_[p] y}

variable {K}

noncomputable def sumMap (κ : (v : ι) → K v ≃ₐ[ℚ_[p]] K v) : PlaceSum K →ₗ[ℚ_[p]] PlaceSum K :=
  LinearMap.pi fun v => (κ v).toLinearMap.comp (LinearMap.proj v)

noncomputable def packetMap (κ : Fin (j + 1) → (v : ι) → K v ≃ₐ[ℚ_[p]] K v) : Packet p K j →ₗ[ℚ_[p]] Packet p K j :=
  PiTensorProduct.map fun t => sumMap p (κ t)

variable {p j}

omit [DecidableEq ι] [∀ v, CompleteSpace (K v)] [∀ v, IsUltrametricDist (K v)] in
theorem packetMap_tprod (κ : Fin (j + 1) → (v : ι) → K v ≃ₐ[ℚ_[p]] K v) (y : Fin (j + 1) → PlaceSum K) :
    packetMap p j κ (PiTensorProduct.tprod ℚ_[p] y) =
      PiTensorProduct.tprod ℚ_[p] (fun t => fun v => κ t v (y t v)) := by
  unfold packetMap
  rw [PiTensorProduct.map_tprod]
  rfl

omit [DecidableEq ι] [∀ v, CompleteSpace (K v)] [∀ v, IsUltrametricDist (K v)] in
theorem tprod_mem_packetShell {y : Fin (j + 1) → PlaceSum K} (hy : ∀ t, y t ∈ sumShell p K) :
    PiTensorProduct.tprod ℚ_[p] y ∈ packetShell p K j :=
  AddSubgroup.subset_closure ⟨y, hy, rfl⟩

omit [DecidableEq ι] in

theorem kummer_intO_mem (κ : Fin (j + 1) → (v : ι) → K v ≃ₐ[ℚ_[p]] K v)
    (hκ : ∀ t v x, ‖κ t v x‖ = ‖x‖) {y : Fin (j + 1) → PlaceSum K} (hy : ∀ t v, ‖y t v‖ ≤ 1) :
    packetMap p j κ (PiTensorProduct.tprod ℚ_[p] y) ∈ packetShell p K j := by
  rw [packetMap_tprod]
  exact tprod_mem_packetShell fun t v => unit_mem_logShell (p := p) (by rw [hκ]; exact hy t v)

omit [∀ v, CompleteSpace (K v)] [∀ v, IsUltrametricDist (K v)] in
theorem single_norm_le {v : ι} {u : K v} (hu : ‖u‖ ≤ 1) (w : ι) : ‖(Pi.single v u : PlaceSum K) w‖ ≤ 1 := by
  by_cases h : w = v
  · subst h; simpa using hu
  · rw [Pi.single_eq_of_ne h, norm_zero]; exact zero_le_one

theorem kummer_units_mem (κ : Fin (j + 1) → (v : ι) → K v ≃ₐ[ℚ_[p]] K v)
    (hκ : ∀ t v x, ‖κ t v x‖ = ‖x‖) (vs : Fin (j + 1) → ι) (u : (t : Fin (j + 1)) → K (vs t))
    (hu : ∀ t, ‖u t‖ = 1) :
    packetMap p j κ (PiTensorProduct.tprod ℚ_[p] fun t => (Pi.single (vs t) (u t) : PlaceSum K)) ∈
      packetShell p K j :=
  kummer_intO_mem κ hκ fun t => single_norm_le (le_of_eq (hu t))

theorem kummer_logIter_mem (κ : Fin (j + 1) → (v : ι) → K v ≃ₐ[ℚ_[p]] K v)
    (hκ : ∀ t v x, ‖κ t v x‖ = ‖x‖) {m' : ℕ} (hm' : 1 ≤ m') (vs : Fin (j + 1) → ι)
    (u x : (t : Fin (j + 1)) → K (vs t)) (hux : ∀ t, LogIter p m' (u t) (x t)) :
    packetMap p j κ (PiTensorProduct.tprod ℚ_[p] fun t => (Pi.single (vs t) (x t) : PlaceSum K)) ∈
      packetShell p K j := by
  rw [packetMap_tprod]
  refine tprod_mem_packetShell fun t w => ?_
  by_cases h : w = vs t
  · subst h
    simp only [Pi.single_eq_same]
    exact kummer_mem_logShell (p := p) (κ t (vs t)) (hκ t (vs t)) (logIter_mem hm' (hux t))
  · simp only [Pi.single_eq_of_ne h, map_zero]
    exact zero_mem_logShell (p := p)

end Packet

structure NonarchData : Type 1 where
  p : ℕ
  [hp : Fact p.Prime]
  ι : Type
  [de : DecidableEq ι]
  K : ι → Type
  [nf : ∀ v, NormedField (K v)]
  [na : ∀ v, NormedAlgebra ℚ_[p] (K v)]
  [cs : ∀ v, CompleteSpace (K v)]
  [ud : ∀ v, IsUltrametricDist (K v)]
  j : ℕ
  kummer : ℤ → Fin (j + 1) → (v : ι) → K v ≃ₐ[ℚ_[p]] K v
  kummer_norm : ∀ m t v x, ‖kummer m t v x‖ = ‖x‖

attribute [instance] NonarchData.hp NonarchData.de NonarchData.nf NonarchData.na NonarchData.cs NonarchData.ud

namespace NonarchData

variable (D : NonarchData)

def UpperSemiCompatible : Prop :=
  ∀ (m : ℤ) (vs : Fin (D.j + 1) → D.ι),
    (∀ u : (t : Fin (D.j + 1)) → D.K (vs t), (∀ t, ‖u t‖ = 1) →
      packetMap D.p D.j (D.kummer m) (PiTensorProduct.tprod ℚ_[D.p] fun t => (Pi.single (vs t) (u t) : PlaceSum D.K)) ∈
        packetShell D.p D.K D.j) ∧
    (∀ m' : ℕ, 1 ≤ m' → ∀ u x : (t : Fin (D.j + 1)) → D.K (vs t), (∀ t, LogIter D.p m' (u t) (x t)) →
      packetMap D.p D.j (D.kummer m) (PiTensorProduct.tprod ℚ_[D.p] fun t => (Pi.single (vs t) (x t) : PlaceSum D.K)) ∈
        packetShell D.p D.K D.j)

theorem upperSemiCompatible : D.UpperSemiCompatible := fun m vs =>
  ⟨fun u hu => kummer_units_mem (D.kummer m) (D.kummer_norm m) vs u hu,
    fun _ hm' u x hux => kummer_logIter_mem (D.kummer m) (D.kummer_norm m) hm' vs u x hux⟩

end NonarchData

section Model

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

noncomputable def modelNonarch : NonarchData where
  p := 3
  ι := Unit
  K := fun _ => ℚ_[3]
  j := 0
  kummer := fun _ _ _ => AlgEquiv.refl
  kummer_norm := fun _ _ _ _ => rfl

theorem padic3_principal_small {z : ℚ_[3]} (hz : ‖z‖ < 1) : ‖z‖ ≤ 1 / 3 := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ‖z‖ = (3 : ℝ) ^ (-n) ∨ z = 0 := by
    by_cases h0 : z = 0
    · exact ⟨0, Or.inr h0⟩
    · exact ⟨z.valuation, Or.inl (Padic.norm_eq_zpow_neg_valuation h0)⟩
  rcases hn with hn | hn
  · rw [hn] at hz ⊢
    have h1 : 0 < n := by
      by_contra hc
      rw [not_lt] at hc
      have : (1 : ℝ) ≤ (3 : ℝ) ^ (-n) := one_le_zpow₀ (by norm_num) (by omega)
      linarith
    have : (3 : ℝ) ^ (-n) ≤ (3 : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    simpa using this
  · subst hn; simp

theorem logShell_Q3_norm_le {x : ℚ_[3]} (hx : x ∈ logShell (K := ℚ_[3]) 3) : ‖x‖ ≤ 1 := by
  obtain ⟨u, hu, hux⟩ := hx
  have hu' : ‖u - 1‖ < 1 := hu
  have hsmall := padic3_principal_small hu'
  have hlog : ‖logUnit u‖ = ‖u - 1‖ := SrcLib.LocalFieldLogThird.norm_log1p_eq_third (p := 3) _ hsmall
  have hps : pStar 3 = 3 := by decide
  have h3 : ‖((pStar 3 : ℕ) : ℚ_[3])‖ = 1 / 3 := by
    rw [hps]; simpa using Padic.norm_p (p := 3)
  have := congrArg norm hux
  rw [norm_mul, h3, hlog] at this
  linarith

theorem norm_three_Q3 : ‖(3 : ℚ_[3])‖ = 1 / 3 := by
  have := Padic.norm_p (p := 3)
  simp only [Nat.cast_ofNat] at this
  rw [this, one_div]

theorem one_not_mem_log_principal : (1 : ℚ_[3]) ∉ logUnit '' principalUnits (K := ℚ_[3]) := by
  rintro ⟨u, hu, hu1⟩
  have hu' : ‖u - 1‖ < 1 := hu
  have hsmall := padic3_principal_small hu'
  have hlog : ‖logUnit u‖ = ‖u - 1‖ := SrcLib.LocalFieldLogThird.norm_log1p_eq_third (p := 3) _ hsmall
  rw [hu1, norm_one] at hlog
  linarith

theorem model_packetShell_proper :
    (PiTensorProduct.tprod ℚ_[3] fun _ : Fin 1 => fun _ : Unit => (1 / 3 : ℚ_[3])) ∉
      packetShell 3 (fun _ : Unit => ℚ_[3]) 0 := by
  let e := PiTensorProduct.subsingletonEquiv (R := ℚ_[3]) (s := fun _ : Fin 1 => (Unit → ℚ_[3])) (0 : Fin 1)
  let S : AddSubgroup (Packet 3 (fun _ : Unit => ℚ_[3]) 0) :=
    { carrier := {z | ‖e z ()‖ ≤ 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, Pi.add_apply] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using ha }
  have hle : packetShell 3 (fun _ : Unit => ℚ_[3]) 0 ≤ S := by
    rw [packetShell, AddSubgroup.closure_le]
    rintro z ⟨y, hy, rfl⟩
    show ‖e (PiTensorProduct.tprod ℚ_[3] y) ()‖ ≤ 1
    rw [PiTensorProduct.subsingletonEquiv_apply_tprod]
    exact logShell_Q3_norm_le (hy 0 ())
  intro h
  have h' : ‖e (PiTensorProduct.tprod ℚ_[3] fun _ : Fin 1 => fun _ : Unit => (1 / 3 : ℚ_[3])) ()‖ ≤ 1 := hle h
  rw [PiTensorProduct.subsingletonEquiv_apply_tprod, norm_div, norm_one, norm_three_Q3] at h'
  norm_num at h'

theorem model_nondegenerate :
    LogIter 3 1 (4 : ℚ_[3]) (logUnit (4 : ℚ_[3])) ∧ ((1 : ℚ_[3]) / 3) ∉ logShell (K := ℚ_[3]) 3 ∧
      (PiTensorProduct.tprod ℚ_[3] fun _ : Fin 1 => fun _ : Unit => (1 / 3 : ℚ_[3])) ∉
        packetShell 3 (fun _ : Unit => ℚ_[3]) 0 ∧
      (1 : ℚ_[3]) ∉ logUnit '' principalUnits (K := ℚ_[3]) := by
  refine ⟨?_, ?_, model_packetShell_proper, one_not_mem_log_principal⟩
  · refine ⟨4, rfl, ?_, 1, ⟨1, one_pos, by norm_num, one_pow 1⟩, ?_, by rw [inv_one, mul_one]⟩
    · have h4 : ((4 : ℚ_[3])) = 1 + 3 := by norm_num
      rw [h4]
      have hne : ‖(1 : ℚ_[3])‖ ≠ ‖(3 : ℚ_[3])‖ := by rw [norm_three_Q3, norm_one]; norm_num
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_three_Q3, norm_one]
      norm_num
    · rw [inv_one, mul_one]
      have : (4 : ℚ_[3]) - 1 = 3 := by norm_num
      rw [this, norm_three_Q3]
      norm_num
  · intro h
    have := logShell_Q3_norm_le h
    rw [norm_div, norm_one, norm_three_Q3] at this
    norm_num at this

end Model

end Src.IUT3.Proposition35ii

section Check
open Src.IUT3.Proposition35ii
end Check
