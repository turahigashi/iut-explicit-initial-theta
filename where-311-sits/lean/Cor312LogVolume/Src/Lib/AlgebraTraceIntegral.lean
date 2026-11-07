import Mathlib

namespace SrcLib.AlgebraTraceIntegral

open Polynomial

theorem isIntegral_trace_of_finite {R K A : Type*} [CommRing R] [Field K] [CommRing A]
    [Algebra R K] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [Module.Finite K A]
    {y : A} (hy : IsIntegral R y) : IsIntegral R (Algebra.trace K A y) := by
  classical
  obtain ⟨g, hgmonic, hgy⟩ := hy
  let F := AlgebraicClosure K
  let b := Module.Free.chooseBasis K A
  set M := Algebra.leftMulMatrix b y with hM
  set gK : K[X] := g.map (algebraMap R K) with hgK
  have hgKy : aeval y gK = 0 := by
    rw [hgK, aeval_map_algebraMap, aeval_def]
    exact hgy
  have hgKM : aeval M gK = 0 := by
    rw [hM, aeval_algHom_apply, hgKy, map_zero]
  set M' := M.map (algebraMap K F) with hM'
  let φ : Matrix (Module.Free.ChooseBasisIndex K A) (Module.Free.ChooseBasisIndex K A) K →ₐ[K]
      Matrix (Module.Free.ChooseBasisIndex K A) (Module.Free.ChooseBasisIndex K A) F := (Algebra.ofId K F).mapMatrix
  have hφ : φ M = M' := rfl
  set gF : F[X] := gK.map (algebraMap K F) with hgF
  have hgFM' : aeval M' gF = 0 := by
    rw [hgF, aeval_map_algebraMap, ← hφ, aeval_algHom_apply, hgKM, map_zero]
  have htrace : algebraMap K F (Algebra.trace K A y) = M'.trace := by
    rw [Algebra.trace_eq_matrix_trace b y, ← hM, hM', Matrix.trace, Matrix.trace, map_sum]
    rfl
  have hroots : ∀ μ ∈ (Matrix.charpoly M').roots, IsIntegral R μ := by
    intro μ hμ
    have hroot : (Matrix.charpoly M').IsRoot μ := (Polynomial.mem_roots'.mp hμ).2
    have hev : Module.End.HasEigenvalue (Matrix.toLin' M') μ := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
      exact hroot
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := gF) hv
    have h0 : aeval (Matrix.toLin' M') gF = 0 := by
      have := aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := F) (n := Module.Free.ChooseBasisIndex K A))
        M' gF
      change aeval (Matrix.toLinAlgEquiv' M') gF = 0
      rw [this, hgFM', map_zero]
    rw [h0, LinearMap.zero_apply] at h1
    have hne : v ≠ 0 := hv.2
    have hevalzero : eval μ gF = 0 := by
      rcases smul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h hne
    refine ⟨g, hgmonic, ?_⟩
    rw [hgF, hgK, Polynomial.map_map, eval_map, ← IsScalarTower.algebraMap_eq] at hevalzero
    exact hevalzero
  have hint : IsIntegral R (algebraMap K F (Algebra.trace K A y)) := by
    rw [htrace, Matrix.trace_eq_sum_roots_charpoly]
    exact IsIntegral.multiset_sum hroots
  exact (isIntegral_algebraMap_iff (algebraMap K F).injective).mp hint

end SrcLib.AlgebraTraceIntegral

section Check
end Check
