import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Automorphisms of `F(a, b, c, d)` fixing `δ = [a, b][c, d]`

The automorphisms `Z`, `H`, `J` of the free group `F4` on `a, b, c, d` (with inverses `Zinv`, `Hinv`,
`Jinv`) fix `δ = [a, b][c, d]` (Lemma 4.3 of the note; `H⁻¹` is the swap of the two pairs of
Lemma 4.2(ii)). With `Ψ = J ∘ H`, the mixing word `M = Ψ ∘ Z ∘ Ψ⁻¹` is an automorphism (`Mequiv`)
with `M(a) = a` (`M_a`) and `M(δ) = δ` (`M_delta`); on the abelianization (`vec`) it acts by
`a ↦ a`, `b ↦ a + b + d`, `c ↦ c - a - d`, `d ↦ d` (`M_ab`).

Adapted from an earlier, unpublished Lean development of the author: the comments were
rewritten, the namespace was renamed and a few unused summary statements were removed; the
remaining definitions and proofs are unchanged.
-/

set_option autoImplicit false

namespace LogShellEdge.ShearFreeGroup

abbrev F4 : Type := FreeGroup (Fin 4)

def ga : F4 := FreeGroup.of 0
def gb : F4 := FreeGroup.of 1
def gc : F4 := FreeGroup.of 2
def gd : F4 := FreeGroup.of 3

def comm (u v : F4) : F4 := u * v * u⁻¹ * v⁻¹

def R : F4 := comm ga gb
def Q : F4 := comm gc gd

def delta : F4 := R * Q
def k : F4 := gb⁻¹ * gc * gd * gc⁻¹

def zGen : Fin 4 → F4
  | 0 => ga * k
  | 1 => k⁻¹ * gb * k
  | 2 => k⁻¹ * gc
  | 3 => gd

def zInvGen : Fin 4 → F4
  | 0 => ga * k⁻¹
  | 1 => k * gb * k⁻¹
  | 2 => k * gc
  | 3 => gd

def hGen : Fin 4 → F4
  | 0 => R * gc * R⁻¹
  | 1 => R * gd * R⁻¹
  | 2 => ga
  | 3 => gb

def hInvGen : Fin 4 → F4
  | 0 => gc
  | 1 => gd
  | 2 => Q⁻¹ * ga * Q
  | 3 => Q⁻¹ * gb * Q

def jGen : Fin 4 → F4
  | 0 => ga * gb * ga⁻¹
  | 1 => ga⁻¹
  | 2 => gc
  | 3 => gd

def jInvGen : Fin 4 → F4
  | 0 => gb⁻¹
  | 1 => gb * ga * gb⁻¹
  | 2 => gc
  | 3 => gd

def Z : F4 →* F4 := FreeGroup.lift zGen
def Zinv : F4 →* F4 := FreeGroup.lift zInvGen
def H : F4 →* F4 := FreeGroup.lift hGen
def Hinv : F4 →* F4 := FreeGroup.lift hInvGen
def J : F4 →* F4 := FreeGroup.lift jGen
def Jinv : F4 →* F4 := FreeGroup.lift jInvGen

section Values

@[simp] theorem Z_a : Z ga = ga * k := FreeGroup.lift_apply_of
@[simp] theorem Z_b : Z gb = k⁻¹ * gb * k := FreeGroup.lift_apply_of
@[simp] theorem Z_c : Z gc = k⁻¹ * gc := FreeGroup.lift_apply_of
@[simp] theorem Z_d : Z gd = gd := FreeGroup.lift_apply_of
@[simp] theorem Zinv_a : Zinv ga = ga * k⁻¹ := FreeGroup.lift_apply_of
@[simp] theorem Zinv_b : Zinv gb = k * gb * k⁻¹ := FreeGroup.lift_apply_of
@[simp] theorem Zinv_c : Zinv gc = k * gc := FreeGroup.lift_apply_of
@[simp] theorem Zinv_d : Zinv gd = gd := FreeGroup.lift_apply_of
@[simp] theorem H_a : H ga = R * gc * R⁻¹ := FreeGroup.lift_apply_of
@[simp] theorem H_b : H gb = R * gd * R⁻¹ := FreeGroup.lift_apply_of
@[simp] theorem H_c : H gc = ga := FreeGroup.lift_apply_of
@[simp] theorem H_d : H gd = gb := FreeGroup.lift_apply_of
@[simp] theorem Hinv_a : Hinv ga = gc := FreeGroup.lift_apply_of
@[simp] theorem Hinv_b : Hinv gb = gd := FreeGroup.lift_apply_of
@[simp] theorem Hinv_c : Hinv gc = Q⁻¹ * ga * Q := FreeGroup.lift_apply_of
@[simp] theorem Hinv_d : Hinv gd = Q⁻¹ * gb * Q := FreeGroup.lift_apply_of
@[simp] theorem J_a : J ga = ga * gb * ga⁻¹ := FreeGroup.lift_apply_of
@[simp] theorem J_b : J gb = ga⁻¹ := FreeGroup.lift_apply_of
@[simp] theorem J_c : J gc = gc := FreeGroup.lift_apply_of
@[simp] theorem J_d : J gd = gd := FreeGroup.lift_apply_of
@[simp] theorem Jinv_a : Jinv ga = gb⁻¹ := FreeGroup.lift_apply_of
@[simp] theorem Jinv_b : Jinv gb = gb * ga * gb⁻¹ := FreeGroup.lift_apply_of
@[simp] theorem Jinv_c : Jinv gc = gc := FreeGroup.lift_apply_of
@[simp] theorem Jinv_d : Jinv gd = gd := FreeGroup.lift_apply_of

end Values

theorem hom_ext4 {G : Type*} [Group G] {f g : F4 →* G}
    (h0 : f ga = g ga) (h1 : f gb = g gb) (h2 : f gc = g gc) (h3 : f gd = g gd) : f = g := by
  apply FreeGroup.ext_hom
  intro i
  match i with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3

theorem Z_k : Z k = k := by
  simp only [k, map_mul, map_inv, Z_b, Z_c, Z_d]
  group

theorem Z_delta : Z delta = delta := by
  simp only [delta, R, Q, comm, map_mul, map_inv, Z_a, Z_b, Z_c, Z_d, k]
  group

theorem H_delta : H delta = delta := by
  simp only [delta, R, Q, comm, map_mul, map_inv, H_a, H_b, H_c, H_d]
  group

theorem J_delta : J delta = delta := by
  simp only [delta, R, Q, comm, map_mul, map_inv, J_a, J_b, J_c, J_d]
  group

theorem Z_comp_Zinv : Z.comp Zinv = MonoidHom.id F4 := by
  apply hom_ext4 <;>
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, Zinv_a, Zinv_b, Zinv_c, Zinv_d, map_mul, map_inv,
      Z_a, Z_b, Z_c, Z_d, Z_k] <;> group

theorem Zinv_k : Zinv k = k := by
  simp only [k, map_mul, map_inv, Zinv_b, Zinv_c, Zinv_d]
  group

theorem Zinv_comp_Z : Zinv.comp Z = MonoidHom.id F4 := by
  apply hom_ext4 <;>
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, Z_a, Z_b, Z_c, Z_d, map_mul, map_inv,
      Zinv_a, Zinv_b, Zinv_c, Zinv_d, Zinv_k] <;> group

theorem H_R : H R = R * Q * R⁻¹ := by
  simp only [R, Q, comm, map_mul, map_inv, H_a, H_b]
  group

theorem H_Q : H Q = R := by
  simp only [R, Q, comm, map_mul, map_inv, H_c, H_d]

theorem Hinv_R : Hinv R = Q := by
  simp only [R, Q, comm, map_mul, map_inv, Hinv_a, Hinv_b]

theorem Hinv_Q : Hinv Q = Q⁻¹ * R * Q := by
  simp only [R, Q, comm, map_mul, map_inv, Hinv_c, Hinv_d]
  group

theorem H_comp_Hinv : H.comp Hinv = MonoidHom.id F4 := by
  apply hom_ext4 <;>
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, Hinv_a, Hinv_b, Hinv_c, Hinv_d, map_mul, map_inv,
      H_a, H_b, H_c, H_d, H_Q] <;> group

theorem Hinv_comp_H : Hinv.comp H = MonoidHom.id F4 := by
  apply hom_ext4 <;>
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, H_a, H_b, H_c, H_d, map_mul, map_inv,
      Hinv_a, Hinv_b, Hinv_c, Hinv_d, Hinv_R] <;> group

theorem J_comp_Jinv : J.comp Jinv = MonoidHom.id F4 := by
  apply hom_ext4 <;>
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, Jinv_a, Jinv_b, Jinv_c, Jinv_d, map_mul, map_inv,
      J_a, J_b, J_c, J_d] <;> group

theorem Jinv_comp_J : Jinv.comp J = MonoidHom.id F4 := by
  apply hom_ext4 <;>
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, J_a, J_b, J_c, J_d, map_mul, map_inv,
      Jinv_a, Jinv_b, Jinv_c, Jinv_d] <;> group

def Zequiv : F4 ≃* F4 :=
  MonoidHom.toMulEquiv Z Zinv Zinv_comp_Z Z_comp_Zinv

def Hequiv : F4 ≃* F4 :=
  MonoidHom.toMulEquiv H Hinv Hinv_comp_H H_comp_Hinv

def Jequiv : F4 ≃* F4 :=
  MonoidHom.toMulEquiv J Jinv Jinv_comp_J J_comp_Jinv

theorem Zinv_delta : Zinv delta = delta := by
  have h := congrArg Zinv Z_delta
  rwa [← MonoidHom.comp_apply, Zinv_comp_Z, MonoidHom.id_apply, eq_comm] at h

theorem Hinv_delta : Hinv delta = delta := by
  have h := congrArg Hinv H_delta
  rwa [← MonoidHom.comp_apply, Hinv_comp_H, MonoidHom.id_apply, eq_comm] at h

theorem Jinv_delta : Jinv delta = delta := by
  have h := congrArg Jinv J_delta
  rwa [← MonoidHom.comp_apply, Jinv_comp_J, MonoidHom.id_apply, eq_comm] at h

def M : F4 →* F4 := J.comp (H.comp (Z.comp (Hinv.comp Jinv)))

def Minv : F4 →* F4 := J.comp (H.comp (Zinv.comp (Hinv.comp Jinv)))

theorem M_a : M ga = ga := by
  simp only [M, MonoidHom.comp_apply, Jinv_a, map_inv, Hinv_b, Z_d, H_d, J_b, inv_inv]

theorem M_delta : M delta = delta := by
  simp only [M, MonoidHom.comp_apply, Jinv_delta, Hinv_delta, Z_delta, H_delta, J_delta]

theorem M_comp_Minv : M.comp Minv = MonoidHom.id F4 := by
  ext x
  simp only [M, Minv, MonoidHom.comp_apply, MonoidHom.id_apply]
  have hJ : ∀ y, Jinv (J y) = y := fun y => by
    rw [← MonoidHom.comp_apply, Jinv_comp_J, MonoidHom.id_apply]
  have hH : ∀ y, Hinv (H y) = y := fun y => by
    rw [← MonoidHom.comp_apply, Hinv_comp_H, MonoidHom.id_apply]
  have hZ : ∀ y, Z (Zinv y) = y := fun y => by
    rw [← MonoidHom.comp_apply, Z_comp_Zinv, MonoidHom.id_apply]
  have hH' : ∀ y, H (Hinv y) = y := fun y => by
    rw [← MonoidHom.comp_apply, H_comp_Hinv, MonoidHom.id_apply]
  have hJ' : ∀ y, J (Jinv y) = y := fun y => by
    rw [← MonoidHom.comp_apply, J_comp_Jinv, MonoidHom.id_apply]
  rw [hJ, hH, hZ, hH', hJ']

theorem Minv_comp_M : Minv.comp M = MonoidHom.id F4 := by
  ext x
  simp only [M, Minv, MonoidHom.comp_apply, MonoidHom.id_apply]
  have hJ : ∀ y, Jinv (J y) = y := fun y => by
    rw [← MonoidHom.comp_apply, Jinv_comp_J, MonoidHom.id_apply]
  have hH : ∀ y, Hinv (H y) = y := fun y => by
    rw [← MonoidHom.comp_apply, Hinv_comp_H, MonoidHom.id_apply]
  have hZ : ∀ y, Zinv (Z y) = y := fun y => by
    rw [← MonoidHom.comp_apply, Zinv_comp_Z, MonoidHom.id_apply]
  have hH' : ∀ y, H (Hinv y) = y := fun y => by
    rw [← MonoidHom.comp_apply, H_comp_Hinv, MonoidHom.id_apply]
  have hJ' : ∀ y, J (Jinv y) = y := fun y => by
    rw [← MonoidHom.comp_apply, J_comp_Jinv, MonoidHom.id_apply]
  rw [hJ, hH, hZ, hH', hJ']

def Mequiv : F4 ≃* F4 :=
  MonoidHom.toMulEquiv M Minv Minv_comp_M M_comp_Minv

def ab : F4 →* Multiplicative (Fin 4 → ℤ) :=
  FreeGroup.lift (fun j => Multiplicative.ofAdd (Pi.single j (1 : ℤ)))

def vec (x : F4) : Fin 4 → ℤ := Multiplicative.toAdd (ab x)

theorem vec_mul (x y : F4) : vec (x * y) = vec x + vec y := by
  simp only [vec, map_mul, toAdd_mul]

theorem vec_inv (x : F4) : vec x⁻¹ = -vec x := by
  simp only [vec, map_inv, toAdd_inv]

set_option linter.unusedSimpArgs false in

theorem M_ab :
    vec (M ga) = vec ga ∧ vec (M gb) = vec ga + vec gb + vec gd ∧
      vec (M gc) = vec gc - vec ga - vec gd ∧ vec (M gd) = vec gd := by
  refine ⟨by rw [M_a], ?_, ?_, ?_⟩
  · simp only [M, MonoidHom.comp_apply, Jinv_a, Jinv_b, Jinv_c, Jinv_d, Hinv_a, Hinv_b, Hinv_c, Hinv_d,
      Z_a, Z_b, Z_c, Z_d, H_a, H_b, H_c, H_d, J_a, J_b, J_c, J_d, map_mul, map_inv, R, Q, comm, k,
      vec_mul, vec_inv]
    abel
  · simp only [M, MonoidHom.comp_apply, Jinv_a, Jinv_b, Jinv_c, Jinv_d, Hinv_a, Hinv_b, Hinv_c, Hinv_d,
      Z_a, Z_b, Z_c, Z_d, H_a, H_b, H_c, H_d, J_a, J_b, J_c, J_d, map_mul, map_inv, R, Q, comm, k,
      vec_mul, vec_inv]
    abel
  · simp only [M, MonoidHom.comp_apply, Jinv_a, Jinv_b, Jinv_c, Jinv_d, Hinv_a, Hinv_b, Hinv_c, Hinv_d,
      Z_a, Z_b, Z_c, Z_d, H_a, H_b, H_c, H_d, J_a, J_b, J_c, J_d, map_mul, map_inv, R, Q, comm, k,
      vec_mul, vec_inv]
    abel

theorem vec_gen : vec ga = Pi.single 0 1 ∧ vec gb = Pi.single 1 1 ∧ vec gc = Pi.single 2 1 ∧
    vec gd = Pi.single 3 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [vec, ab, ga, gb, gc, gd, FreeGroup.lift_apply_of, toAdd_ofAdd]

end LogShellEdge.ShearFreeGroup
