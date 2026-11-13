-- IUT-STATEMENT: IUT-III Remark 3.9.5
/-
# 注意3.9.5(ii) の包の一意性：条件付き集合論

[S] Mochizuki, IUT III, May 2020, Remark 3.9.5(ii)–(iii), pp.126–128。
`ronbun8625/file.html:3356–3416`（今回の全節照合は2087–5282）。

[P] `HullOperator` は定義域と包の族、作用素、(P1)–(P3)を入力とする。
その条件から共通部分表示・一意性・冪等性、Phiの合併が包に入ることを示す。
`quantifier_choice_dissolved_by_uniqueness` は同じ族に着地する二つの包の値の等式。
指定qがその包に入ることや原典の比較不等式は述べていない。

位相はこの型に無い。`indeterminacy_is_bounded` は集合の包含であって、
コンパクト性の証明ではない。`without_the_condition_unbounded` は退化した
集合模型での非包含の証明であり、位相的な非有界性を述べていない。
実lambda-O包・有限log体積・コンパクト性と、原典の全可能像族への接続は別途必要。
既存の証明本体は変更していない。D-168-112、独立点検なし。
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Kouchiku.M3.Theorem311.Remark395

variable {α : Type*}

/-- ★原典の `ℙ`（直積領域の全体）と `ℍ`（包の全体、`ℍ ⊆ ℙ`）、および
包を作る操作 `φ : ℙ → ℍ` を、原典 (ii) の (P1)(P2)(P3) だけで公理化した構造。 -/
structure HullOperator (α : Type*) where
  /-- `ℙ`: log 体積を適用しうる領域の全体。 -/
  isDomain : Set α → Prop
  /-- `ℍ`: 包の全体。 -/
  isHull   : Set α → Prop
  /-- `ℍ ⊆ ℙ`。 -/
  hull_sub_domain : ∀ {H}, isHull H → isDomain H
  /-- 包を作る操作。 -/
  φ : Set α → Set α
  /-- `φ` は `ℍ` に着地する。 -/
  φ_isHull : ∀ {P}, isDomain P → isHull (φ P)
  /-- **(P1)** 包の上では恒等。 -/
  P1 : ∀ {H}, isHull H → φ H = H
  /-- **(P2)** 拡大的。 -/
  P2 : ∀ {P}, isDomain P → P ⊆ φ P
  /-- **(P3)** 単調。 -/
  P3 : ∀ {P₁ P₂}, isDomain P₁ → isDomain P₂ → P₁ ⊆ P₂ → φ P₁ ⊆ φ P₂

namespace HullOperator

variable (Ω : HullOperator α)

/-- ★★★原典「(P1)–(P3) から**形式的に**従う」を実際に証明した。
`φ(P) = ⋂ {H ∈ ℍ | P ⊆ H}`。 -/
theorem hull_eq_iInter {P : Set α} (hP : Ω.isDomain P) :
    Ω.φ P = ⋂ (H : Set α) (_ : Ω.isHull H ∧ P ⊆ H), H := by
  apply Set.Subset.antisymm
  · -- φ P は右辺の各 H に含まれる
    simp only [Set.subset_iInter_iff]
    rintro H ⟨hH, hPH⟩
    calc Ω.φ P ⊆ Ω.φ H := Ω.P3 hP (Ω.hull_sub_domain hH) hPH
    _ = H := Ω.P1 hH
  · -- φ P 自身が右辺の共通部分に現れる項の一つ
    have hmem : Ω.isHull (Ω.φ P) ∧ P ⊆ Ω.φ P := ⟨Ω.φ_isHull hP, Ω.P2 hP⟩
    intro x hx
    exact Set.mem_iInter₂.mp hx (Ω.φ P) hmem

/-- ★★(P1)–(P3) を満たす作用素は**一意**（原典「一意に特徴づけられる」）。 -/
theorem hull_unique (Ω' : HullOperator α)
    (hdom : Ω.isDomain = Ω'.isDomain) (hhull : Ω.isHull = Ω'.isHull)
    {P : Set α} (hP : Ω.isDomain P) :
    Ω.φ P = Ω'.φ P := by
  have hP' : Ω'.isDomain P := hdom ▸ hP
  rw [Ω.hull_eq_iInter hP, Ω'.hull_eq_iInter hP', hhull]

/-- ★閉包作用素であること（冪等）。 -/
theorem hull_idempotent {P : Set α} (hP : Ω.isDomain P) :
    Ω.φ (Ω.φ P) = Ω.φ P :=
  Ω.P1 (Ω.φ_isHull hP)

/-- ★包は元の領域を含む（(P2) の言い換え・log 体積の単調性の根拠）。 -/
theorem domain_subset_hull {P : Set α} (hP : Ω.isDomain P) : P ⊆ Ω.φ P := Ω.P2 hP

/-! ## §2 Phiの合併包含（コンパクト性は別義務） -/

/-- 原典 `Φ(P)`: `φ(P)` に**含まれる**包で、log 体積が `P` 以上のもの。
★条件 `H ⊆ φ(P)` が入っていることが要点。 -/
def Phi (μ : Set α → ℝ) (P : Set α) : Set (Set α) :=
  { H | Ω.isHull H ∧ H ⊆ Ω.φ P ∧ μ H ≥ μ P }

/-- Phiに定義上課された包含から、その全合併も包に入る。位相的主張ではない。 -/
theorem indeterminacy_is_bounded (μ : Set α → ℝ) (P : Set α) :
    ⋃ H ∈ Ω.Phi μ P, H ⊆ Ω.φ P := by
  simp only [Set.iUnion_subset_iff]
  rintro H ⟨-, hsub, -⟩
  exact hsub

/-- 条件 `H ⊆ φ(P)` を**外した**版。 -/
def PhiWithoutCondition (μ : Set α → ℝ) (P : Set α) : Set (Set α) :=
  { H | Ω.isHull H ∧ μ H ≥ μ P }

end HullOperator

/-! ## §3 包への包含条件を外した集合模型 -/

/-- ★反例に使う退化した包作用素: `ℍ = ℙ = すべての部分集合`・`φ = id`。 -/
def trivialHull : HullOperator ℝ where
  isDomain := fun _ => True
  isHull   := fun _ => True
  hull_sub_domain := fun _ => trivial
  φ := id
  φ_isHull := fun _ => trivial
  P1 := fun _ => rfl
  P2 := fun _ => subset_rfl
  P3 := fun _ _ h => h

/-- 退化した集合模型で、包への包含条件を外すと合併が元の包からはみ出す。 -/
theorem without_the_condition_unbounded :
    (⋃ H ∈ trivialHull.Phi (fun _ => (0:ℝ)) {0}, H) ⊆ trivialHull.φ {0} ∧
    ¬ ((⋃ H ∈ trivialHull.PhiWithoutCondition (fun _ => (0:ℝ)) {0}, H)
        ⊆ trivialHull.φ {0}) := by
  constructor
  · exact HullOperator.indeterminacy_is_bounded _ _ _
  · intro h
    have h1 : (1 : ℝ) ∈ ⋃ H ∈ trivialHull.PhiWithoutCondition (fun _ => (0:ℝ)) {0}, H :=
      Set.mem_iUnion₂.mpr ⟨{1}, ⟨trivial, le_refl 0⟩, rfl⟩
    have h2 := h h1
    simp [trivialHull] at h2

/-! ## §4 同じ包の族を用いる二構成の値の一致 -/

/-- 同じ定義域・包の族・(P1)–(P3)から得られる包は一致し、任意の実数値関数も同じ値を返す。指定qとの比較は含まない。 -/
theorem quantifier_choice_dissolved_by_uniqueness
    (Ω Ω' : HullOperator α)
    (hdom : Ω.isDomain = Ω'.isDomain) (hhull : Ω.isHull = Ω'.isHull)
    (μ : Set α → ℝ) {P : Set α} (hP : Ω.isDomain P) :
    -- ★どの標準的構成を取っても同じ集合＝同じ体積になる
    μ (Ω.φ P) = μ (Ω'.φ P) := by
  rw [Ω.hull_unique Ω' hdom hhull hP]

#print axioms HullOperator.hull_eq_iInter
#print axioms HullOperator.hull_unique
#print axioms HullOperator.hull_idempotent
#print axioms HullOperator.indeterminacy_is_bounded
#print axioms without_the_condition_unbounded
#print axioms quantifier_choice_dissolved_by_uniqueness

end Kouchiku.M3.Theorem311.Remark395
