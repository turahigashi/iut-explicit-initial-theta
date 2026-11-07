import Mathlib

namespace SrcLib.LatticeLogIndex

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

def Comm (H K : AddSubgroup V) : Prop := K.relIndex H ≠ 0 ∧ H.relIndex K ≠ 0

noncomputable def lidx (H K : AddSubgroup V) : ℝ :=
  Real.log (K.relIndex H) - Real.log (H.relIndex K)

variable {H K L : AddSubgroup V}

theorem Comm.symm (h : Comm H K) : Comm K H := ⟨h.2, h.1⟩

theorem comm_refl (H : AddSubgroup V) : Comm H H := by
  simp [Comm, AddSubgroup.relIndex_self]

theorem Comm.trans (hHK : Comm H K) (hKL : Comm K L) : Comm H L :=
  ⟨AddSubgroup.relIndex_ne_zero_trans hKL.1 hHK.1, AddSubgroup.relIndex_ne_zero_trans hHK.2 hKL.2⟩

theorem comm_of_le (h : H ≤ K) (hf : H.relIndex K ≠ 0) : Comm H K :=
  ⟨by rw [AddSubgroup.relIndex_eq_one.mpr h]; exact one_ne_zero, hf⟩

theorem lidx_self (H : AddSubgroup V) : lidx H H = 0 := by simp [lidx]

theorem lidx_symm (H K : AddSubgroup V) : lidx H K = -lidx K H := by
  simp only [lidx]; ring

theorem lidx_of_le (h : H ≤ K) : lidx H K = -Real.log (H.relIndex K) := by
  rw [lidx, AddSubgroup.relIndex_eq_one.mpr h]; simp

theorem lidx_nonpos_of_le (h : H ≤ K) : lidx H K ≤ 0 := by
  rw [lidx_of_le h]; exact neg_nonpos.mpr (Real.log_natCast_nonneg _)

theorem lidx_trans (hHK : Comm H K) (hKL : Comm K L) : lidx H L = lidx H K + lidx K L := by
  set a := K.relIndex H
  set b := H.relIndex K
  set c := L.relIndex K
  set d := K.relIndex L
  set e := L.relIndex H
  set f := H.relIndex L
  set x := L.relIndex (H ⊓ K)
  set y := H.relIndex (K ⊓ L)
  set z := K.relIndex (H ⊓ L)
  have hHL := hHK.trans hKL

  have i1 : y * d = (H ⊓ K).relIndex L := AddSubgroup.relIndex_inf_mul_relIndex H K L
  have i2 : z * f = (K ⊓ H).relIndex L := AddSubgroup.relIndex_inf_mul_relIndex K H L

  have i3 : K.relIndex (L ⊓ H) * e = (K ⊓ L).relIndex H := AddSubgroup.relIndex_inf_mul_relIndex K L H
  have i4 : L.relIndex (K ⊓ H) * a = (L ⊓ K).relIndex H := AddSubgroup.relIndex_inf_mul_relIndex L K H

  have i5 : H.relIndex (L ⊓ K) * c = (H ⊓ L).relIndex K := AddSubgroup.relIndex_inf_mul_relIndex H L K
  have i6 : L.relIndex (H ⊓ K) * b = (L ⊓ H).relIndex K := AddSubgroup.relIndex_inf_mul_relIndex L H K
  rw [inf_comm K H] at i2
  rw [inf_comm L H] at i3
  rw [inf_comm K H, inf_comm L K] at i4
  rw [inf_comm L K] at i5
  rw [inf_comm L H] at i6
  have e1 : y * d = z * f := i1.trans i2.symm
  have e2 : z * e = x * a := i3.trans i4.symm
  have e3 : y * c = x * b := i5.trans i6.symm
  have hx : x ≠ 0 := mt (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_right) hKL.1
  have hy : y ≠ 0 := mt (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left) hHK.2
  have hz : z ≠ 0 := mt (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left) hHK.1
  have key : e * b * d = f * a * c := by
    have h : (x * y * z) * (e * b * d) = (x * y * z) * (f * a * c) := by
      calc (x * y * z) * (e * b * d) = (z * e) * (y * d) * (x * b) := by ring
        _ = (x * a) * (z * f) * (y * c) := by rw [e2, e1, e3]
        _ = (x * y * z) * (f * a * c) := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (by positivity)) h
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast hHK.1
  have hb : (b : ℝ) ≠ 0 := by exact_mod_cast hHK.2
  have hc : (c : ℝ) ≠ 0 := by exact_mod_cast hKL.1
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast hKL.2
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast hHL.1
  have hf : (f : ℝ) ≠ 0 := by exact_mod_cast hHL.2
  have key' : Real.log (e * b * d) = Real.log (f * a * c) := by exact_mod_cast congrArg (fun n : ℕ => Real.log n) key
  rw [Real.log_mul (mul_ne_zero he hb) hd, Real.log_mul he hb, Real.log_mul (mul_ne_zero hf ha) hc,
    Real.log_mul hf ha] at key'
  simp only [lidx]
  linarith

theorem lidx_mono {M : AddSubgroup V} (hH : Comm H M) (hK : Comm K M) (hHK : H ≤ K) :
    lidx H M ≤ lidx K M := by
  have hc : Comm H K := comm_of_le hHK (AddSubgroup.relIndex_ne_zero_trans hH.2 hK.1)
  rw [lidx_trans hc hK]
  linarith [lidx_nonpos_of_le hHK]

theorem lidx_map (φ : V →+ W) (hφ : Function.Injective φ) (H K : AddSubgroup V) :
    lidx (H.map φ) (K.map φ) = lidx H K := by
  simp only [lidx, AddSubgroup.relIndex_map_map_of_injective _ _ hφ]

theorem Comm.map (φ : V →+ W) (hφ : Function.Injective φ) (h : Comm H K) : Comm (H.map φ) (K.map φ) := by
  simp only [Comm, AddSubgroup.relIndex_map_map_of_injective _ _ hφ]
  exact h

end SrcLib.LatticeLogIndex

section Check
end Check
