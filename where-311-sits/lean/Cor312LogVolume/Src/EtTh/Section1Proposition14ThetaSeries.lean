import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.Int.Interval
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

namespace Src.EtTh.Prop14

section Series

variable {R : Type*} [CommRing R]

abbrev USeries (R : Type*) := ℤ → R

def scale (c : Rˣ) (f : USeries R) : USeries R := fun k => ((c ^ k : Rˣ) : R) * f k

def invert (f : USeries R) : USeries R := fun k => f (-k)

def monoMul (c : R) (m : ℤ) (f : USeries R) : USeries R := fun k => c * f (k - m)

def thetaCoeff (s : R) (k : ℤ) : R :=
  if k % 2 = 1 then
    ((((-1 : Rˣ) ^ (k / 2) : Rˣ)) : R) * s ^ ((k / 2) * (k / 2 + 1)).toNat
  else 0

theorem thetaCoeff_odd (s : R) (n : ℤ) :
    thetaCoeff s (2 * n + 1) = ((((-1 : Rˣ) ^ n : Rˣ)) : R) * s ^ (n * (n + 1)).toNat := by
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  simp [thetaCoeff, h1, h2]

theorem thetaCoeff_even (s : R) (n : ℤ) : thetaCoeff s (2 * n) = 0 := by
  have h1 : ¬ (2 * n) % 2 = 1 := by omega
  rw [thetaCoeff, if_neg h1]

theorem mul_succ_nonneg (n : ℤ) : 0 ≤ n * (n + 1) := by
  rcases le_or_gt 0 n with h | h
  · positivity
  · nlinarith

theorem val_pow_toNat (s : Rˣ) {m : ℤ} (hm : 0 ≤ m) :
    (s : R) ^ m.toNat = ((s ^ m : Rˣ) : R) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  simp

theorem neg_one_zpow_val_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (n : ℤ) :
    f (((-1 : Aˣ) ^ n : Aˣ) : A) = (((-1 : Bˣ) ^ n : Bˣ) : B) := by
  rcases Int.even_or_odd n with h | h
  · simp [h.neg_one_zpow]
  · simp [h.neg_one_zpow]

theorem thetaCoeff_odd_unit (s : Rˣ) (n : ℤ) :
    thetaCoeff (s : R) (2 * n + 1) = (((-1 : Rˣ) ^ n * s ^ (n * (n + 1)) : Rˣ) : R) := by
  rw [thetaCoeff_odd, val_pow_toNat s (mul_succ_nonneg n), Units.val_mul]

theorem neg_one_zpow_two : ((-1 : Rˣ) ^ (2 : ℤ)) = 1 := by
  rw [zpow_two]; simp

theorem quasiperiodic_units (s : Rˣ) (a n : ℤ) :
    s ^ (a * (2 * n + 1)) * ((-1) ^ n * s ^ (n * (n + 1))) =
      ((-1) ^ a * s ^ (-(a ^ 2))) * ((-1) ^ (n + a) * s ^ ((n + a) * (n + a + 1))) := by
  have hsign : ((-1 : Rˣ)) ^ (a + (n + a)) = (-1) ^ n := by
    rw [show a + (n + a) = n + 2 * a by ring, zpow_add, zpow_mul, neg_one_zpow_two]
    simp
  have hexp : a * (2 * n + 1) + n * (n + 1) = -(a ^ 2) + (n + a) * (n + a + 1) := by ring
  rw [mul_left_comm, ← zpow_add, mul_mul_mul_comm, ← zpow_add, ← zpow_add, hsign, hexp]

theorem theta_quasiperiodic (s : Rˣ) (a : ℤ) :
    scale (s ^ a) (thetaCoeff (s : R)) =
      monoMul ((((-1 : Rˣ) ^ a * s ^ (-(a ^ 2)) : Rˣ)) : R) (-2 * a) (thetaCoeff (s : R)) := by
  funext k
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · simp only [scale, monoMul]
    rw [show 2 * n - -2 * a = 2 * (n + a) by ring, thetaCoeff_even, thetaCoeff_even]
    simp
  · simp only [scale, monoMul]
    rw [show 2 * n + 1 - -2 * a = 2 * (n + a) + 1 by ring, thetaCoeff_odd_unit,
      thetaCoeff_odd_unit, ← Units.val_mul, ← Units.val_mul, ← zpow_mul, quasiperiodic_units]

theorem theta_invert (s : Rˣ) :
    invert (thetaCoeff (s : R)) = monoMul (-1) 0 (thetaCoeff (s : R)) := by
  funext k
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · simp only [invert, monoMul]
    rw [show -(2 * n) = 2 * (-n) by ring, thetaCoeff_even, sub_zero, thetaCoeff_even]
    simp
  · simp only [invert, monoMul]
    rw [show -(2 * n + 1) = 2 * (-n - 1) + 1 by ring, sub_zero, thetaCoeff_odd_unit,
      thetaCoeff_odd_unit]
    have hsign : ((-1 : Rˣ)) ^ (-n - 1) = -((-1) ^ n) := by
      rw [show -n - 1 = (n + 1) + 2 * (-n - 1) by ring, zpow_add, zpow_mul, neg_one_zpow_two]
      simp [zpow_add_one]
    rw [hsign, show (-n - 1) * (-n - 1 + 1) = n * (n + 1) by ring]
    simp

theorem theta_negate (s : Rˣ) :
    scale (-1) (thetaCoeff (s : R)) = monoMul (-1) 0 (thetaCoeff (s : R)) := by
  funext k
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · simp [scale, monoMul, thetaCoeff_even]
  · simp only [scale, monoMul, sub_zero]
    rw [zpow_add_one, zpow_mul, neg_one_zpow_two]
    simp

end Series

structure TateParameter : Type 1 where
  O : Type
  K : Type
  kappa : Type
  [ringO : CommRing O]
  [fieldK : Field K]
  [fieldKappa : Field kappa]

  [charZeroK : CharZero K]
  ι : O →+* K
  ι_injective : Function.Injective ι
  red : O →+* kappa
  s : O
  s_ne_zero : ι s ≠ 0

  red_s : red s = 0

attribute [instance] TateParameter.ringO TateParameter.fieldK TateParameter.fieldKappa
  TateParameter.charZeroK

namespace TateParameter

variable (T : TateParameter)

def sK : T.Kˣ := Units.mk0 (T.ι T.s) T.s_ne_zero

def thetaK : USeries T.K := fun k => T.ι (thetaCoeff T.s k)

theorem thetaK_eq : T.thetaK = thetaCoeff ((T.sK : T.K)) := by
  funext k
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · simp [thetaK, thetaCoeff_even]
  · simp only [thetaK, thetaCoeff_odd, map_mul, map_pow]
    rw [neg_one_zpow_val_map]
    rfl

theorem thetaK_quasiperiodic (a : ℤ) :
    scale (T.sK ^ a) T.thetaK =
      monoMul ((((-1 : T.Kˣ) ^ a * T.sK ^ (-(a ^ 2)) : T.Kˣ)) : T.K) (-2 * a) T.thetaK := by
  rw [thetaK_eq]; exact theta_quasiperiodic T.sK a

def uMinusUInv : USeries T.kappa := fun k => if k = 1 then 1 else if k = -1 then -1 else 0

theorem theta_restriction_label_zero :
    (fun k => T.red (thetaCoeff T.s k)) = T.uMinusUInv := by
  funext k
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · have h1 : 2 * n ≠ 1 := by omega
    have h2 : 2 * n ≠ -1 := by omega
    simp [uMinusUInv, thetaCoeff_even, h1, h2]
  · rw [thetaCoeff_odd, map_mul, map_pow, T.red_s]
    by_cases h : n * (n + 1) = 0
    · rcases mul_eq_zero.mp h with h0 | h0
      · subst h0; simp [uMinusUInv]
      · have hn : n = -1 := by omega
        subst hn
        simp [uMinusUInv]
    · have hpos : 0 < (n * (n + 1)).toNat := by
        have := mul_succ_nonneg n
        omega
      have h1 : 2 * n + 1 ≠ 1 := by
        intro h'; apply h; have : n = 0 := by omega
        simp [this]
      have h2 : 2 * n + 1 ≠ -1 := by
        intro h'; apply h; have : n = -1 := by omega
        simp [this]
      simp [uMinusUInv, h1, h2, zero_pow hpos.ne']

theorem uMinusUInv_ne_zero : T.uMinusUInv 1 ≠ 0 := by simp [uMinusUInv]

def IsRestricted (g : USeries T.O) : Prop := ∀ N : ℕ, {k : ℤ | ¬ T.s ^ N ∣ g k}.Finite

theorem theta_restricted (N : ℕ) :
    {k : ℤ | ¬ T.s ^ N ∣ thetaCoeff T.s k}.Finite := by
  refine (Set.finite_Icc (-(2 * (N : ℤ) + 1)) (2 * N + 1)).subset ?_
  intro k hk
  simp only [Set.mem_setOf_eq] at hk
  simp only [Set.mem_Icc]
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · exact absurd (by rw [thetaCoeff_even]; exact dvd_zero _) hk
  · by_contra hout
    apply hk
    have hN : (N : ℤ) ≤ n * (n + 1) := by
      rcases le_or_gt 0 n with h | h
      · have : (N : ℤ) ≤ n := by omega
        nlinarith
      · have : n ≤ -(N : ℤ) - 1 := by omega
        nlinarith
    rw [thetaCoeff_odd]
    exact Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _

def HasVerticalOrder (f : USeries T.K) (e : ℤ) : Prop :=
  ∃ g : USeries T.O, IsRestricted T g ∧ (∃ k0, T.red (g k0) ≠ 0) ∧
    ∀ k, f k = ((T.sK ^ e : T.Kˣ) : T.K) * T.ι (g k)

def verticalOrderAlong (a : ℤ) (f : USeries T.K) (e : ℤ) : Prop :=
  T.HasVerticalOrder (scale (T.sK ^ a) f) e

def D1mult (j : ℤ) : ℤ := j ^ 2

theorem sK_pow_natCast (m : ℕ) : ((T.sK ^ (m : ℤ) : T.Kˣ) : T.K) = T.ι (T.s ^ m) := by
  simp [sK, map_pow]

theorem verticalOrder_unique {f : USeries T.K} {e e' : ℤ}
    (h : T.HasVerticalOrder f e) (h' : T.HasVerticalOrder f e') : e = e' := by

  have key : ∀ {e e' : ℤ}, T.HasVerticalOrder f e → T.HasVerticalOrder f e' → ¬ e < e' := by
    intro e e' ⟨g, _, ⟨k0, hk0⟩, hg⟩ ⟨g', _, _, hg'⟩ hlt
    apply hk0
    have hm : 0 ≤ e' - e := by omega
    obtain ⟨m, hm'⟩ := Int.eq_ofNat_of_zero_le hm
    have hpos : 0 < m := by omega
    have heq : g k0 = T.s ^ m * g' k0 := by
      apply T.ι_injective
      have h1 := hg k0
      have h2 := hg' k0
      rw [h2] at h1
      rw [map_mul, ← T.sK_pow_natCast, ← hm']
      have hu : ((T.sK ^ e : T.Kˣ) : T.K) ≠ 0 := Units.ne_zero _
      apply mul_left_cancel₀ hu
      rw [← mul_assoc, ← Units.val_mul, ← zpow_add, show e + (e' - e) = e' by ring]
      exact h1.symm
    rw [heq, map_mul, map_pow, T.red_s, zero_pow hpos.ne', zero_mul]
  rcases lt_trichotomy e e' with hlt | heq | hgt
  · exact absurd hlt (key h h')
  · exact heq
  · exact absurd hgt (key h' h)

theorem pole_divisor_is_D1 (a : ℤ) : T.verticalOrderAlong a T.thetaK (-(D1mult a)) := by
  refine ⟨monoMul (((-1 : T.Oˣ) ^ a : T.Oˣ) : T.O) (-2 * a) (thetaCoeff T.s), ?_,
    ⟨1 - 2 * a, ?_⟩, ?_⟩
  · intro N
    refine ((T.theta_restricted N).preimage (f := fun k : ℤ => k - -2 * a)
      (fun x _ y _ h => by simpa using h)).subset ?_
    intro k hk
    simp only [Set.mem_setOf_eq, Set.mem_preimage, monoMul] at hk ⊢
    exact fun hd => hk (Dvd.dvd.mul_left hd _)
  · simp only [monoMul, show 1 - 2 * a - -2 * a = 1 by ring, map_mul]
    have h := congrFun T.theta_restriction_label_zero 1
    simp only at h
    rw [h]
    refine mul_ne_zero ?_ (T.uMinusUInv_ne_zero)
    exact (Units.map (T.red : T.O →* T.kappa) ((-1 : T.Oˣ) ^ a)).ne_zero
  · intro k
    rw [thetaK_quasiperiodic]
    simp only [monoMul, map_mul, thetaK, D1mult, Units.val_mul, mul_assoc]
    rw [mul_left_comm, neg_one_zpow_val_map]

def nodeWeight (a j : ℤ) : T.Kˣ := if 0 ≤ j then T.sK ^ (a * j) else T.sK ^ ((a + 1) * j)

def IsNodeRegular (a : ℤ) (f : USeries T.K) : Prop :=
  ∀ j, ∃ c : T.O, ((T.nodeWeight a j : T.Kˣ) : T.K) * f j = T.ι c

def IsNodeUnit (a : ℤ) (f : USeries T.K) : Prop :=
  T.IsNodeRegular a f ∧ ∃ c : T.Oˣ, f 0 = T.ι c

def mulD1NodeEquation (a : ℤ) (f : USeries T.K) : USeries T.K :=
  monoMul ((T.sK ^ (-(a ^ 2) - a) : T.Kˣ) : T.K) (2 * a + 1) f

theorem D1NodeEquation_orders (a : ℤ) :
    D1mult a = a ^ 2 ∧ D1mult (a + 1) = a ^ 2 + (2 * a + 1) := by
  refine ⟨by simp [D1mult], by simp only [D1mult]; ring⟩

theorem thetaK_odd (n : ℤ) :
    T.thetaK (2 * n + 1) = (((-1 : T.Kˣ) ^ n * T.sK ^ (n * (n + 1)) : T.Kˣ) : T.K) := by
  rw [thetaK_eq, thetaCoeff_odd_unit]

theorem thetaK_even (n : ℤ) : T.thetaK (2 * n) = 0 := by
  rw [thetaK_eq, thetaCoeff_even]

theorem units_value_integral (n E : ℤ) (hE : 0 ≤ E) :
    (((-1 : T.Kˣ) ^ n * T.sK ^ E : T.Kˣ) : T.K) =
      T.ι ((((-1 : T.Oˣ) ^ n : T.Oˣ) : T.O) * T.s ^ E.toNat) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hE
  rw [Units.val_mul, map_mul, neg_one_zpow_val_map, Int.toNat_natCast, ← sK_pow_natCast]

theorem sK_rearrange (e c d : ℤ) (y : T.Kˣ) :
    T.sK ^ e * (T.sK ^ c * (y * T.sK ^ d)) = y * T.sK ^ (e + c + d) := by
  rw [zpow_add, zpow_add]
  simp only [mul_left_comm, mul_assoc]

theorem pole_divisor_at_node (a : ℤ) : T.IsNodeUnit a (T.mulD1NodeEquation a T.thetaK) := by
  constructor
  · intro j
    obtain ⟨t, rfl | rfl⟩ := Int.even_or_odd' j
    · have hodd : 2 * t - (2 * a + 1) = 2 * (t - a - 1) + 1 := by ring
      simp only [mulD1NodeEquation, monoMul, nodeWeight]
      rw [hodd, thetaK_odd, ← Units.val_mul, ← Units.val_mul]
      split_ifs with hj
      · rw [sK_rearrange]
        have hE : a * (2 * t) + (-(a ^ 2) - a) + (t - a - 1) * (t - a - 1 + 1) = t * (t - 1) := by
          ring
        rw [hE]
        refine ⟨_, T.units_value_integral _ _ ?_⟩
        have := mul_succ_nonneg (t - 1)
        linarith [show (t - 1) * (t - 1 + 1) = t * (t - 1) by ring]
      · rw [sK_rearrange]
        have hE : (a + 1) * (2 * t) + (-(a ^ 2) - a) + (t - a - 1) * (t - a - 1 + 1) =
            t * (t + 1) := by
          ring
        rw [hE]
        exact ⟨_, T.units_value_integral _ _ (mul_succ_nonneg t)⟩
    · have heven : 2 * t + 1 - (2 * a + 1) = 2 * (t - a) := by ring
      refine ⟨0, ?_⟩
      simp [mulD1NodeEquation, monoMul, heven, thetaK_even]
  · refine ⟨(-1 : T.Oˣ) ^ (-a - 1), ?_⟩
    have h0 : (0 : ℤ) - (2 * a + 1) = 2 * (-a - 1) + 1 := by ring
    simp only [mulD1NodeEquation, monoMul]
    rw [h0, thetaK_odd, ← Units.val_mul, neg_one_zpow_val_map]
    congr 1
    rw [mul_left_comm, ← zpow_add, show -(a ^ 2) - a + (-a - 1) * (-a - 1 + 1) = 0 by ring,
      zpow_zero, mul_one]

def PoleDivisorIsD1 : Prop :=
  ∀ a : ℤ, T.verticalOrderAlong a T.thetaK (-(D1mult a)) ∧
    T.IsNodeUnit a (T.mulD1NodeEquation a T.thetaK)

theorem poleDivisorIsD1 : T.PoleDivisorIsD1 := fun a =>
  ⟨T.pole_divisor_is_D1 a, T.pole_divisor_at_node a⟩

theorem pole_order_label_zero : T.verticalOrderAlong 0 T.thetaK 0 := by
  simpa [D1mult] using T.pole_divisor_is_D1 0

theorem pole_order_eq {a e : ℤ} (h : T.verticalOrderAlong a T.thetaK e) : e = -(a ^ 2) :=
  T.verticalOrder_unique h (T.pole_divisor_is_D1 a)

end TateParameter

section Model

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

noncomputable def padicTate : TateParameter where
  O := ℤ_[5]
  K := ℚ_[5]
  kappa := ZMod 5
  ringO := inferInstance
  fieldK := inferInstance
  fieldKappa := inferInstance
  charZeroK := inferInstance
  ι := PadicInt.Coe.ringHom
  ι_injective := fun _ _ h => Subtype.ext h
  red := PadicInt.toZMod
  s := 5
  s_ne_zero := by
    change ((5 : ℤ_[5]) : ℚ_[5]) ≠ 0
    norm_num
  red_s := by
    change PadicInt.toZMod (5 : ℤ_[5]) = 0
    rw [map_ofNat]; rfl

theorem padic_pole_orders :
    padicTate.PoleDivisorIsD1 ∧
    padicTate.verticalOrderAlong 1 padicTate.thetaK (-1) ∧
    padicTate.verticalOrderAlong 2 padicTate.thetaK (-4) ∧
    (∀ e, padicTate.verticalOrderAlong 0 padicTate.thetaK e → e = 0) ∧
    (∀ e, padicTate.verticalOrderAlong 1 padicTate.thetaK e → e = -1) := by
  refine ⟨padicTate.poleDivisorIsD1,
    by simpa [TateParameter.D1mult] using padicTate.pole_divisor_is_D1 1,
    by simpa [TateParameter.D1mult] using padicTate.pole_divisor_is_D1 2, ?_, ?_⟩
  · intro e h; simpa using padicTate.pole_order_eq h
  · intro e h; simpa using padicTate.pole_order_eq h

def oneSeries (T : TateParameter) : USeries T.K := fun k => if k = 0 then 1 else 0

theorem oneSeries_order_zero (T : TateParameter) (a : ℤ) :
    T.verticalOrderAlong a (oneSeries T) 0 := by
  refine ⟨fun k => if k = 0 then 1 else 0, ?_, ⟨0, by simp⟩, ?_⟩
  · intro N
    refine (Set.finite_singleton (0 : ℤ)).subset ?_
    intro k hk
    simp only [Set.mem_setOf_eq] at hk
    by_contra h
    have h' : k ≠ 0 := by simpa using h
    exact hk (by simp [h'])
  · intro k
    by_cases h : k = 0 <;> simp [scale, oneSeries, h]

theorem oneSeries_not_pole_D1 (T : TateParameter) :
    ¬ (∀ a : ℤ, T.verticalOrderAlong a (oneSeries T) (-(TateParameter.D1mult a))) := by
  intro h
  have := T.verticalOrder_unique (h 1) (oneSeries_order_zero T 1)
  simp [TateParameter.D1mult] at this

end Model

end Src.EtTh.Prop14

section Check
open Src.EtTh.Prop14
end Check
