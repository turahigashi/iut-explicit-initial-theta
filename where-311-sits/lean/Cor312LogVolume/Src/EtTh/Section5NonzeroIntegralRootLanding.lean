import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

namespace Src.EtTh.NonzeroIntegral

variable (R L : Type*) [CommRing R] [Field L] [Algebra R L]

def nonzeroIntegral : Submonoid Lˣ where
  carrier := {u | IsIntegral R (u : L)}
  one_mem' := isIntegral_one
  mul_mem' := by
    intro u v hu hv
    change IsIntegral R ((u : L) * (v : L))
    exact hu.mul hv

theorem mem_of_pow_mem {u : Lˣ} {n : ℕ} (hn : 0 < n)
    (h : u ^ n ∈ nonzeroIntegral R L) :
    u ∈ nonzeroIntegral R L := by
  change IsIntegral R (u : L)
  apply IsIntegral.of_pow hn
  change IsIntegral R ((u ^ n : Lˣ) : L) at h
  simpa only [Units.val_pow_eq_pow_val] using h

theorem normalized_profile_mem
    (ell : ℕ) (hell : 0 < ell) (q qRoot : Lˣ)
    (hq : q ∈ nonzeroIntegral R L)
    (hroot : qRoot ^ (2 * ell) = q)
    (z : ℕ → Lˣ) (hz : ∀ j, z j ^ (2 * ell) = 1) (j : ℕ) :
    z j * qRoot ^ (j * j) ∈ nonzeroIntegral R L := by
  have hpos : 0 < 2 * ell := Nat.mul_pos (by decide) hell
  have hqRoot : qRoot ∈ nonzeroIntegral R L := by
    apply mem_of_pow_mem R L hpos
    rw [hroot]
    exact hq
  have hzj : z j ∈ nonzeroIntegral R L := by
    apply mem_of_pow_mem R L hpos
    rw [hz j]
    exact (nonzeroIntegral R L).one_mem
  exact (nonzeroIntegral R L).mul_mem hzj
    ((nonzeroIntegral R L).pow_mem hqRoot (j * j))

theorem normalized_profile_root_mem
    (ell : ℕ) (hell : 0 < ell) (q qRoot : Lˣ)
    (hq : q ∈ nonzeroIntegral R L)
    (hroot : qRoot ^ (2 * ell) = q)
    (z : ℕ → Lˣ) (hz : ∀ j, z j ^ (2 * ell) = 1)
    (j : ℕ) (u : Lˣ) (n : ℕ) (hn : 0 < n)
    (hu : u ^ n = z j * qRoot ^ (j * j)) :
    u ∈ nonzeroIntegral R L := by
  apply mem_of_pow_mem R L hn
  rw [hu]
  exact normalized_profile_mem R L ell hell q qRoot hq hroot z hz j

end Src.EtTh.NonzeroIntegral
