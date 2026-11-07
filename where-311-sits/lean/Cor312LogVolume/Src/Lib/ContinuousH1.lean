import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Tactic.Abel

noncomputable section

namespace SrcContinuous.ContinuousH1

universe u

variable (G A : Type u)
  [Group G] [AddCommGroup A]
  [TopologicalSpace G] [TopologicalSpace A]
  [DistribMulAction G A] [ContinuousSMul G A]

structure Cocycle where
  toContinuousMap : ContinuousMap G A
  cocycle' : ∀ g h,
    toContinuousMap (g * h) =
      g • toContinuousMap h + toContinuousMap g

instance : CoeFun (Cocycle G A) (fun _ => G → A) :=
  ⟨fun f => f.toContinuousMap⟩

@[ext]
theorem Cocycle.ext {f g : Cocycle G A} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      congr
      ext x
      exact h x

def Cohomologous (f g : Cocycle G A) : Prop :=
  ∃ a : A, ∀ x : G, g x = f x + (x • a - a)

theorem cohomologous_refl (f : Cocycle G A) : Cohomologous G A f f := by
  refine ⟨0, ?_⟩
  intro x
  simp

theorem cohomologous_symm {f g : Cocycle G A}
    (h : Cohomologous G A f g) : Cohomologous G A g f := by
  obtain ⟨a, ha⟩ := h
  refine ⟨-a, ?_⟩
  intro x
  rw [ha x]
  simp only [smul_neg, sub_neg_eq_add]
  abel

theorem cohomologous_trans {f g h : Cocycle G A}
    (hfg : Cohomologous G A f g) (hgh : Cohomologous G A g h) :
    Cohomologous G A f h := by
  obtain ⟨a, ha⟩ := hfg
  obtain ⟨b, hb⟩ := hgh
  refine ⟨a + b, ?_⟩
  intro x
  rw [hb x, ha x]
  simp only [smul_add]
  abel

def cohomologySetoid : Setoid (Cocycle G A) where
  r := Cohomologous G A
  iseqv := ⟨cohomologous_refl G A, cohomologous_symm G A,
    cohomologous_trans G A⟩

abbrev H1 := Quotient (cohomologySetoid G A)

variable {G A}
variable {H B : Type u}
  [Group H] [AddCommGroup B]
  [TopologicalSpace H] [TopologicalSpace B]
  [DistribMulAction H B] [ContinuousSMul H B]

structure TransportData where
  groupEquiv : G ≃ₜ* H
  coeffEquiv : A ≃ₜ+ B
  equivariant : ∀ g a,
    coeffEquiv (g • a) = groupEquiv g • coeffEquiv a

def TransportData.symm (T : TransportData (G := G) (A := A) (H := H) (B := B)) :
    TransportData (G := H) (A := B) (H := G) (B := A) where
  groupEquiv := T.groupEquiv.symm
  coeffEquiv := T.coeffEquiv.symm
  equivariant := by
    intro h b
    apply T.coeffEquiv.injective
    calc
      T.coeffEquiv (T.coeffEquiv.symm (h • b)) = h • b :=
        T.coeffEquiv.apply_symm_apply (h • b)
      _ = T.groupEquiv (T.groupEquiv.symm h) •
          T.coeffEquiv (T.coeffEquiv.symm b) := by simp
      _ = T.coeffEquiv
          (T.groupEquiv.symm h • T.coeffEquiv.symm b) :=
        (T.equivariant (T.groupEquiv.symm h) (T.coeffEquiv.symm b)).symm

def transportCocycle
    (T : TransportData (G := G) (A := A) (H := H) (B := B))
    (f : Cocycle G A) : Cocycle H B where
  toContinuousMap :=
    { toFun := fun h => T.coeffEquiv (f (T.groupEquiv.symm h))
      continuous_toFun :=
        T.coeffEquiv.continuous.comp
          (f.toContinuousMap.continuous.comp T.groupEquiv.symm.continuous) }
  cocycle' := by
    intro h₁ h₂
    calc
      T.coeffEquiv (f (T.groupEquiv.symm (h₁ * h₂))) =
          T.coeffEquiv
            (f (T.groupEquiv.symm h₁ * T.groupEquiv.symm h₂)) := by
              rw [map_mul]
      _ = T.coeffEquiv
            (T.groupEquiv.symm h₁ • f (T.groupEquiv.symm h₂) +
              f (T.groupEquiv.symm h₁)) := by
              rw [f.cocycle']
      _ = T.coeffEquiv
            (T.groupEquiv.symm h₁ • f (T.groupEquiv.symm h₂)) +
              T.coeffEquiv (f (T.groupEquiv.symm h₁)) := by
              rw [map_add]
      _ = h₁ • T.coeffEquiv (f (T.groupEquiv.symm h₂)) +
              T.coeffEquiv (f (T.groupEquiv.symm h₁)) := by
              rw [T.equivariant]
              simp

@[simp]
theorem transport_symm_transport
    (T : TransportData (G := G) (A := A) (H := H) (B := B))
    (f : Cocycle G A) :
    transportCocycle T.symm (transportCocycle T f) = f := by
  ext g
  simp [transportCocycle, TransportData.symm]

@[simp]
theorem transport_transport_symm
    (T : TransportData (G := G) (A := A) (H := H) (B := B))
    (f : Cocycle H B) :
    transportCocycle T (transportCocycle T.symm f) = f := by
  ext h
  simp [transportCocycle, TransportData.symm]

def cocycleEquiv
    (T : TransportData (G := G) (A := A) (H := H) (B := B)) :
    Cocycle G A ≃ Cocycle H B where
  toFun := transportCocycle T
  invFun := transportCocycle T.symm
  left_inv := transport_symm_transport T
  right_inv := transport_transport_symm T

theorem transport_cohomologous
    (T : TransportData (G := G) (A := A) (H := H) (B := B))
    {f g : Cocycle G A} (hfg : Cohomologous G A f g) :
    Cohomologous H B (transportCocycle T f) (transportCocycle T g) := by
  obtain ⟨a, ha⟩ := hfg
  refine ⟨T.coeffEquiv a, ?_⟩
  intro y
  change T.coeffEquiv (g (T.groupEquiv.symm y)) =
    T.coeffEquiv (f (T.groupEquiv.symm y)) +
      (y • T.coeffEquiv a - T.coeffEquiv a)
  rw [ha, map_add, map_sub, T.equivariant]
  simp

def transportH1
    (T : TransportData (G := G) (A := A) (H := H) (B := B)) :
    H1 G A → H1 H B :=
  Quotient.map (transportCocycle T) (fun _ _ =>
    transport_cohomologous T)

def h1Equiv
    (T : TransportData (G := G) (A := A) (H := H) (B := B)) :
    H1 G A ≃ H1 H B where
  toFun := transportH1 T
  invFun := transportH1 T.symm
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro f
    change Quotient.mk _ (transportCocycle T.symm (transportCocycle T f)) =
      Quotient.mk _ f
    rw [transport_symm_transport]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro f
    change Quotient.mk _ (transportCocycle T (transportCocycle T.symm f)) =
      Quotient.mk _ f
    rw [transport_transport_symm]

end SrcContinuous.ContinuousH1
