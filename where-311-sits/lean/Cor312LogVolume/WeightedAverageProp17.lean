import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Src.CoreLayer.WeightedAvg

open Finset

variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

def lamProd (n : ℕ) (lam : E → ℝ) (v : Fin n → E) : ℝ := ∏ j, lam (v j)

def betaSum (n : ℕ) (beta : E → ℝ) (v : Fin n → E) : ℝ := ∑ j, beta (v j)

noncomputable def lamE (lam : E → ℝ) : ℝ := ∑ e, lam e

noncomputable def betaE (beta lam : E → ℝ) : ℝ := ∑ e, beta e * lam e

theorem lamE_pow (n : ℕ) (lam : E → ℝ) :
    (lamE lam) ^ n = ∑ v : Fin n → E, lamProd n lam v := by
  classical
  simp only [lamE, lamProd]
  have h := Finset.sum_pow' (Finset.univ : Finset E) lam n
  rw [Fintype.piFinset_univ] at h
  exact h

theorem betaE_mul_lamE_pow (n : ℕ) (lam beta : E → ℝ) (i : Fin (n + 1)) :
    (betaE beta lam) * (lamE lam) ^ n
      = ∑ v : Fin (n + 1) → E, beta (v i) * lamProd (n + 1) lam v := by
  classical
  set g : Fin (n + 1) → E → ℝ := fun j e => if j = i then beta e * lam e else lam e with hg

  have ha : ∀ v : Fin (n + 1) → E,
      beta (v i) * lamProd (n + 1) lam v = ∏ j, g j (v j) := by
    intro v
    have h1 : ∏ j, g j (v j)
        = g i (v i) * ∏ j ∈ Finset.univ.erase i, g j (v j) :=
      (Finset.mul_prod_erase Finset.univ (fun j => g j (v j)) (Finset.mem_univ i)).symm
    have h2 : ∏ j ∈ Finset.univ.erase i, g j (v j)
        = ∏ j ∈ Finset.univ.erase i, lam (v j) := by
      refine Finset.prod_congr rfl ?_
      intro j hj
      have : j ≠ i := Finset.ne_of_mem_erase hj
      simp [hg, this]
    have h3 : lamProd (n + 1) lam v = lam (v i) * ∏ j ∈ Finset.univ.erase i, lam (v j) := by
      simp only [lamProd]
      exact (Finset.mul_prod_erase Finset.univ (fun j => lam (v j)) (Finset.mem_univ i)).symm
    rw [h1, h2, h3]
    simp only [hg, if_pos rfl]
    ring

  have hb : ∑ v : Fin (n + 1) → E, ∏ j, g j (v j) = ∏ j : Fin (n + 1), ∑ e, g j e := by
    have h := Finset.prod_univ_sum (fun _ : Fin (n + 1) => (Finset.univ : Finset E)) g
    rw [Fintype.piFinset_univ] at h
    exact h.symm

  have hc : ∏ j : Fin (n + 1), ∑ e, g j e = (betaE beta lam) * (lamE lam) ^ n := by
    have h1 : ∏ j : Fin (n + 1), (∑ e, g j e)
        = (∑ e, g i e) * ∏ j ∈ Finset.univ.erase i, (∑ e, g j e) :=
      (Finset.mul_prod_erase Finset.univ (fun j => ∑ e, g j e) (Finset.mem_univ i)).symm
    have h2 : ∀ j ∈ Finset.univ.erase i, (∑ e, g j e) = lamE lam := by
      intro j hj
      have : j ≠ i := Finset.ne_of_mem_erase hj
      simp [hg, this, lamE]
    have h2' : ∏ j ∈ Finset.univ.erase i, (∑ e, g j e)
        = ∏ _j ∈ Finset.univ.erase i, (lamE lam) := Finset.prod_congr rfl h2
    have h4 : ((Finset.univ : Finset (Fin (n + 1))).erase i).card = n := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    have h5 : (∑ e, g i e) = betaE beta lam := by simp [hg, betaE]
    rw [h1, h2', Finset.prod_const, h4, h5]
  rw [← hc, ← hb]
  exact Finset.sum_congr rfl (fun v _ => (ha v).symm)

theorem weighted_average_core (n : ℕ) (lam beta : E → ℝ)
    (hid : ∀ j : Fin n, (betaE beta lam) * (lamE lam) ^ (n - 1)
              = ∑ v : Fin n → E, beta (v j) * lamProd n lam v) :
    ∑ v : Fin n → E, betaSum n beta v * lamProd n lam v
      = (n : ℝ) * ((betaE beta lam) * (lamE lam) ^ (n - 1)) := by
  classical
  have hswap : ∑ v : Fin n → E, betaSum n beta v * lamProd n lam v
      = ∑ j : Fin n, ∑ v : Fin n → E, beta (v j) * lamProd n lam v := by
    simp only [betaSum, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hswap]
  rw [Finset.sum_congr rfl (fun j _ => (hid j).symm)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem weighted_average (n : ℕ) (lam beta : E → ℝ)
    (hlam : ∀ e, 0 < lam e) (hn : 0 < n)
    (hid : ∀ j : Fin n, (betaE beta lam) * (lamE lam) ^ (n - 1)
              = ∑ v : Fin n → E, beta (v j) * lamProd n lam v) :
    (∑ v : Fin n → E, betaSum n beta v * lamProd n lam v)
        / (∑ v : Fin n → E, lamProd n lam v)
      = (n : ℝ) * ((betaE beta lam) / (lamE lam)) := by
  classical
  have hlamE : 0 < lamE lam := by
    simp only [lamE]
    exact Finset.sum_pos (fun e _ => hlam e) Finset.univ_nonempty
  have hden : ∑ v : Fin n → E, lamProd n lam v = (lamE lam) ^ n := (lamE_pow n lam).symm
  have hnum := weighted_average_core n lam beta hid
  rw [hnum, hden]
  have hne : (lamE lam) ≠ 0 := ne_of_gt hlamE
  have hpow : (lamE lam) ^ n = (lamE lam) ^ (n - 1) * (lamE lam) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow]
  field_simp

theorem proposition17 (n : ℕ) (hn : 0 < n) (lam beta : E → ℝ) (hlam : ∀ e, 0 < lam e) (i : Fin n) :
    (∑ v : Fin n → E, betaSum n beta v * lamProd n lam v) / (∑ v : Fin n → E, lamProd n lam v)
        = (∑ v : Fin n → E, (n : ℝ) * beta (v i) * lamProd n lam v) / (∑ v : Fin n → E, lamProd n lam v) ∧
      (∑ v : Fin n → E, (n : ℝ) * beta (v i) * lamProd n lam v) / (∑ v : Fin n → E, lamProd n lam v)
        = (n : ℝ) * ((betaE beta lam) / (lamE lam)) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hid : ∀ j : Fin (m + 1), (betaE beta lam) * (lamE lam) ^ (m + 1 - 1)
      = ∑ v : Fin (m + 1) → E, beta (v j) * lamProd (m + 1) lam v := by
    intro j
    rw [Nat.add_sub_cancel]
    exact betaE_mul_lamE_pow m lam beta j
  have hlamE : 0 < lamE lam := by
    simp only [lamE]
    exact Finset.sum_pos (fun e _ => hlam e) Finset.univ_nonempty
  have hmid : (∑ v : Fin (m + 1) → E, ((m + 1 : ℕ) : ℝ) * beta (v i) * lamProd (m + 1) lam v)
      / (∑ v : Fin (m + 1) → E, lamProd (m + 1) lam v)
      = ((m + 1 : ℕ) : ℝ) * ((betaE beta lam) / (lamE lam)) := by
    have hnum : (∑ v : Fin (m + 1) → E, ((m + 1 : ℕ) : ℝ) * beta (v i) * lamProd (m + 1) lam v)
        = ((m + 1 : ℕ) : ℝ) * ((betaE beta lam) * (lamE lam) ^ m) := by
      rw [betaE_mul_lamE_pow m lam beta i, Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hnum, ← lamE_pow, pow_succ]
    field_simp
  exact ⟨(weighted_average (m + 1) lam beta hlam hn hid).trans hmid.symm, hmid⟩

end Src.CoreLayer.WeightedAvg
