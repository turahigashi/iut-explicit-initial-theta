/-
★★★★★ Phase E-4o：`F^Vdash` global/place/rho structured skeleton

原典 HTML の境界：

* [IUTchI], [IUT I], Definition 5.2(iv)：
  `F^Vdash` prime-strip は四つ組
  `(global Frobenioid C^Vdash, Prime(C^Vdash) ≃ V,
    {local F^vdash_v}, {rho_v})` である。各 `rho_v` は global divisor
  monoid と local realified Frobenioid monoid の topological monoid
  isomorphism であり、射はこの全データの isomorphism である。
* [IUTchI], Remark 3.5.2：データの isomorphism は
  構成データ間の「obvious compatibility」を満たすが、個々の式は省略される。
  category components は equivalence の isomorphism class として読む。
* [IUTchII], [IUT II], Corollary 4.6(iv),(v)：
  local Env／Gau evaluation は action／splitting と両立し、global evaluation
  は prime bijections と local `rho` の下で local evaluation と両立する。
* [IUTchII], Definition 4.9(viii)：enhanced
  `F^(Vdash blacktriangleright times-mu)` strip も同じ四つ組 shape を持つ。
* [IUTchII], Corollary 4.10(ii)：actual Env／Gau
  four-tuples と、それら全データの evaluation isomorphism が構成される。

本ファイルは四つ組の dependent type skeleton と、その射を property-free raw
data として構成する。`PrimeLabelSquare` と `RhoNaturalitySquare` は Remark 3.5.2
の compatibility を pointwise strict equality で展開した [P] interface であって、
原典に表示された逐語式ではない。

`Global`／`Local v` は既に structured Frobenioid objects を表す入力型とする。
従って裸の carrier equivalence へ潰さない。一方、このファイルは actual
Frobenioid、Definition 5.2(iv)(a),(f) の model-identification、各 fiber の
`R_{>=0}` model、Corollary 4.6 の actual constructor を与えない。末尾の finite
Bool／C3 模型は SOURCE object の模型ではなく、二 compatibility predicates と
closed-fiber degeneration の [P/audit] だけを検査する。
-/

import M3.thetalink.CompletePolyIso

namespace Grounding.ThetaLink

noncomputable section

universe uV uGlobal uPrime uLocal uGLoc uLRlf uGIso uLIso

/-! ## 1. The dependent four-tuple, without source properties embedded -/

/-- Property-free shape of a global realified mono-analytic Frobenioid
prime-strip.  Both `rho` endpoints depend on the actual global/local object
values and on the place label. -/
structure FVdashPrimeStripRaw
    (V : Type uV) (Global : Type uGlobal)
    (Prime : Global → Type uPrime)
    (Local : V → Type uLocal)
    (GlobalLoc : (C : Global) → Prime C → Type uGLoc)
    (LocalRlf : (v : V) → Local v → Type uLRlf)
    [∀ C p, TopologicalSpace (GlobalLoc C p)]
    [∀ C p, CommMonoid (GlobalLoc C p)]
    [∀ v L, TopologicalSpace (LocalRlf v L)]
    [∀ v L, CommMonoid (LocalRlf v L)] where
  global : Global
  primeEquiv : Prime global ≃ V
  localObj : (v : V) → Local v
  rho : (v : V) →
    GlobalLoc global (primeEquiv.symm v) ≃ₜ* LocalRlf v (localObj v)

/-! ## 2. A property-free isomorphism of all four components -/

/-- Raw component maps between two four-tuples.

`GlobalIso` and `LocalIso` are external structured-isomorphism types.  They
are deliberately not replaced by equality or a bare carrier equivalence.
The global/local monoid maps are indexed by the same explicit place `v`, so
their naturality can be asked only after all raw maps have been constructed. -/
structure FVdashIsoRaw
    {V : Type uV} {Global : Type uGlobal}
    {Prime : Global → Type uPrime}
    {Local : V → Type uLocal}
    {GlobalLoc : (C : Global) → Prime C → Type uGLoc}
    {LocalRlf : (v : V) → Local v → Type uLRlf}
    [∀ C p, TopologicalSpace (GlobalLoc C p)]
    [∀ C p, CommMonoid (GlobalLoc C p)]
    [∀ v L, TopologicalSpace (LocalRlf v L)]
    [∀ v L, CommMonoid (LocalRlf v L)]
    (S T : FVdashPrimeStripRaw V Global Prime Local GlobalLoc LocalRlf)
    (GlobalIso : Global → Global → Type uGIso)
    (LocalIso : (v : V) → Local v → Local v → Type uLIso) where
  globalIso : GlobalIso S.global T.global
  primeIso : Prime S.global ≃ Prime T.global
  localIso : (v : V) → LocalIso v (S.localObj v) (T.localObj v)
  globalLocIso : (v : V) →
    GlobalLoc S.global (S.primeEquiv.symm v) ≃ₜ*
      GlobalLoc T.global (T.primeEquiv.symm v)
  localRlfIso : (v : V) →
    LocalRlf v (S.localObj v) ≃ₜ* LocalRlf v (T.localObj v)

/-! ## 3. The two omitted compatibility squares are external -/

/-- [P/unpacking] The prime-component isomorphism respects the fixed place
labels supplied by the two `Prime ≃ V` maps. -/
def PrimeLabelSquare
    {V : Type uV} {Global : Type uGlobal}
    {Prime : Global → Type uPrime}
    {Local : V → Type uLocal}
    {GlobalLoc : (C : Global) → Prime C → Type uGLoc}
    {LocalRlf : (v : V) → Local v → Type uLRlf}
    [∀ C p, TopologicalSpace (GlobalLoc C p)]
    [∀ C p, CommMonoid (GlobalLoc C p)]
    [∀ v L, TopologicalSpace (LocalRlf v L)]
    [∀ v L, CommMonoid (LocalRlf v L)]
    {S T : FVdashPrimeStripRaw V Global Prime Local GlobalLoc LocalRlf}
    {GlobalIso : Global → Global → Type uGIso}
    {LocalIso : (v : V) → Local v → Local v → Type uLIso}
    (R : FVdashIsoRaw S T GlobalIso LocalIso) : Prop :=
  ∀ p, T.primeEquiv (R.primeIso p) = S.primeEquiv p

/-- [P/unpacking] The placewise global and local monoid isomorphisms commute
with the two independently supplied `rho_v` maps. -/
def RhoNaturalitySquare
    {V : Type uV} {Global : Type uGlobal}
    {Prime : Global → Type uPrime}
    {Local : V → Type uLocal}
    {GlobalLoc : (C : Global) → Prime C → Type uGLoc}
    {LocalRlf : (v : V) → Local v → Type uLRlf}
    [∀ C p, TopologicalSpace (GlobalLoc C p)]
    [∀ C p, CommMonoid (GlobalLoc C p)]
    [∀ v L, TopologicalSpace (LocalRlf v L)]
    [∀ v L, CommMonoid (LocalRlf v L)]
    {S T : FVdashPrimeStripRaw V Global Prime Local GlobalLoc LocalRlf}
    {GlobalIso : Global → Global → Type uGIso}
    {LocalIso : (v : V) → Local v → Local v → Type uLIso}
    (R : FVdashIsoRaw S T GlobalIso LocalIso) : Prop :=
  ∀ v x,
    T.rho v (R.globalLocIso v x) = R.localRlfIso v (S.rho v x)

/-- [P/audit] The prime, global-local, and local-realified inputs each contain
a visible distinction which the corresponding equivalence does not collapse.
This rejects a closed `Unit`-fiber witness without adding the guard to the
source-shaped raw structure.  The abstract `GlobalIso`／`LocalIso` types expose
no uniform readout, so their visibility is intentionally not audited here. -/
def FVdashIsoNondegenerate
    {V : Type uV} {Global : Type uGlobal}
    {Prime : Global → Type uPrime}
    {Local : V → Type uLocal}
    {GlobalLoc : (C : Global) → Prime C → Type uGLoc}
    {LocalRlf : (v : V) → Local v → Type uLRlf}
    [∀ C p, TopologicalSpace (GlobalLoc C p)]
    [∀ C p, CommMonoid (GlobalLoc C p)]
    [∀ v L, TopologicalSpace (LocalRlf v L)]
    [∀ v L, CommMonoid (LocalRlf v L)]
    {S T : FVdashPrimeStripRaw V Global Prime Local GlobalLoc LocalRlf}
    {GlobalIso : Global → Global → Type uGIso}
    {LocalIso : (v : V) → Local v → Local v → Type uLIso}
    (R : FVdashIsoRaw S T GlobalIso LocalIso) : Prop :=
  (∃ p q, p ≠ q ∧ R.primeIso p ≠ R.primeIso q) ∧
    (∃ v x y, x ≠ y ∧ R.globalLocIso v x ≠ R.globalLocIso v y) ∧
    (∃ v x y, x ≠ y ∧ R.localRlfIso v x ≠ R.localRlfIso v y)

/-- A partial interface promoted only after the two displayed compatibility
squares have separately been proved.  This is deliberately not called a full
source arrow: it does not yet say that `globalLocIso`／`localRlfIso` are induced
by `globalIso`／`localIso`, nor encode category-equivalence coherence from
Remark 3.5.2.  Nondegeneracy remains a separate audit. -/
structure TwoSquareFVdashIso
    {V : Type uV} {Global : Type uGlobal}
    {Prime : Global → Type uPrime}
    {Local : V → Type uLocal}
    {GlobalLoc : (C : Global) → Prime C → Type uGLoc}
    {LocalRlf : (v : V) → Local v → Type uLRlf}
    [∀ C p, TopologicalSpace (GlobalLoc C p)]
    [∀ C p, CommMonoid (GlobalLoc C p)]
    [∀ v L, TopologicalSpace (LocalRlf v L)]
    [∀ v L, CommMonoid (LocalRlf v L)]
    (S T : FVdashPrimeStripRaw V Global Prime Local GlobalLoc LocalRlf)
    (GlobalIso : Global → Global → Type uGIso)
    (LocalIso : (v : V) → Local v → Local v → Type uLIso) where
  raw : FVdashIsoRaw S T GlobalIso LocalIso
  primeCompatible : PrimeLabelSquare raw
  rhoCompatible : RhoNaturalitySquare raw

def FVdashIsoRaw.toTwoSquare
    {V : Type uV} {Global : Type uGlobal}
    {Prime : Global → Type uPrime}
    {Local : V → Type uLocal}
    {GlobalLoc : (C : Global) → Prime C → Type uGLoc}
    {LocalRlf : (v : V) → Local v → Type uLRlf}
    [∀ C p, TopologicalSpace (GlobalLoc C p)]
    [∀ C p, CommMonoid (GlobalLoc C p)]
    [∀ v L, TopologicalSpace (LocalRlf v L)]
    [∀ v L, CommMonoid (LocalRlf v L)]
    {S T : FVdashPrimeStripRaw V Global Prime Local GlobalLoc LocalRlf}
    {GlobalIso : Global → Global → Type uGIso}
    {LocalIso : (v : V) → Local v → Local v → Type uLIso}
    (R : FVdashIsoRaw S T GlobalIso LocalIso)
    (hPrime : PrimeLabelSquare R) (hRho : RhoNaturalitySquare R) :
    TwoSquareFVdashIso S T GlobalIso LocalIso :=
  ⟨R, hPrime, hRho⟩

/-! ## 4. Finite audit models; these are not SOURCE Frobenioids -/

def boolFlipEquiv : Bool ≃ Bool where
  toFun b := !b
  invFun b := !b
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

abbrev ToyPrime (_ : Bool) := Bool
abbrev ToyLocal (_ : Bool) := Bool
abbrev ToyGlobalLoc (_ : Bool) (_ : Bool) := C3Square
abbrev ToyLocalRlf (_ : Bool) (_ : Bool) := C3Square
abbrev ToyGlobalIso (_ _ : Bool) := Unit
abbrev ToyLocalIso (_ : Bool) (_ _ : Bool) := Unit

abbrev ToyFVdash :=
  FVdashPrimeStripRaw Bool Bool ToyPrime ToyLocal ToyGlobalLoc ToyLocalRlf

theorem toy_c3_axis_ne_one : c3AxisWitness ≠ (1 : C3Square) := by
  decide

theorem toy_c3_swap_axis_ne_self :
    c3SquareSwap c3AxisWitness ≠ c3AxisWitness := by
  decide

def toyFVdashSource : ToyFVdash where
  global := false
  primeEquiv := Equiv.refl Bool
  localObj := fun _ ↦ false
  rho := fun _ ↦ ContinuousMulEquiv.refl C3Square

def toyFVdashTarget : ToyFVdash where
  global := true
  primeEquiv := boolFlipEquiv
  localObj := fun _ ↦ true
  rho := fun _ ↦ ContinuousMulEquiv.refl C3Square

def toySynchronizedFVdashIso :
    FVdashIsoRaw toyFVdashSource toyFVdashTarget
      ToyGlobalIso ToyLocalIso where
  globalIso := ()
  primeIso := boolFlipEquiv
  localIso := fun _ ↦ ()
  globalLocIso := fun _ ↦ c3SquareSwap
  localRlfIso := fun _ ↦ c3SquareSwap

theorem toy_synchronized_prime_square :
    PrimeLabelSquare toySynchronizedFVdashIso := by
  intro p
  cases p <;> rfl

theorem toy_synchronized_rho_square :
    RhoNaturalitySquare toySynchronizedFVdashIso := by
  intro v x
  rfl

theorem toy_synchronized_nondegenerate :
    FVdashIsoNondegenerate toySynchronizedFVdashIso := by
  exact ⟨
    ⟨false, true, by decide,
      toySynchronizedFVdashIso.primeIso.injective.ne (by decide)⟩,
    ⟨false, c3AxisWitness, 1, toy_c3_axis_ne_one,
      (toySynchronizedFVdashIso.globalLocIso false).injective.ne
        toy_c3_axis_ne_one⟩,
    ⟨false, c3AxisWitness, 1, toy_c3_axis_ne_one,
      (toySynchronizedFVdashIso.localRlfIso false).injective.ne
        toy_c3_axis_ne_one⟩⟩

def toyTwoSquareFVdashIso :
    TwoSquareFVdashIso toyFVdashSource toyFVdashTarget
      ToyGlobalIso ToyLocalIso :=
  toySynchronizedFVdashIso.toTwoSquare
    toy_synchronized_prime_square toy_synchronized_rho_square

/-! ## 5. Independent failure of the two compatibility obligations -/

def toyWrongPrimeFVdashIso :
    FVdashIsoRaw toyFVdashSource toyFVdashTarget
      ToyGlobalIso ToyLocalIso where
  globalIso := ()
  primeIso := Equiv.refl Bool
  localIso := fun _ ↦ ()
  globalLocIso := fun _ ↦ c3SquareSwap
  localRlfIso := fun _ ↦ c3SquareSwap

theorem toy_wrong_prime_rho_square_still_holds :
    RhoNaturalitySquare toyWrongPrimeFVdashIso := by
  intro v x
  rfl

theorem toy_wrong_prime_is_nondegenerate :
    FVdashIsoNondegenerate toyWrongPrimeFVdashIso := by
  exact ⟨
    ⟨false, true, by decide,
      toyWrongPrimeFVdashIso.primeIso.injective.ne (by decide)⟩,
    ⟨false, c3AxisWitness, 1, toy_c3_axis_ne_one,
      (toyWrongPrimeFVdashIso.globalLocIso false).injective.ne
        toy_c3_axis_ne_one⟩,
    ⟨false, c3AxisWitness, 1, toy_c3_axis_ne_one,
      (toyWrongPrimeFVdashIso.localRlfIso false).injective.ne
        toy_c3_axis_ne_one⟩⟩

theorem toy_wrong_prime_fails_label_square :
    ¬ PrimeLabelSquare toyWrongPrimeFVdashIso := by
  intro h
  have hw := h false
  cases hw

def toyWrongRhoFVdashIso :
    FVdashIsoRaw toyFVdashSource toyFVdashTarget
      ToyGlobalIso ToyLocalIso where
  globalIso := ()
  primeIso := boolFlipEquiv
  localIso := fun _ ↦ ()
  globalLocIso := fun _ ↦ c3SquareSwap
  localRlfIso := fun _ ↦ ContinuousMulEquiv.refl C3Square

theorem toy_wrong_rho_prime_square_still_holds :
    PrimeLabelSquare toyWrongRhoFVdashIso := by
  intro p
  cases p <;> rfl

theorem toy_wrong_rho_is_nondegenerate :
    FVdashIsoNondegenerate toyWrongRhoFVdashIso := by
  exact ⟨
    ⟨false, true, by decide,
      toyWrongRhoFVdashIso.primeIso.injective.ne (by decide)⟩,
    ⟨false, c3AxisWitness, 1, toy_c3_axis_ne_one,
      (toyWrongRhoFVdashIso.globalLocIso false).injective.ne
        toy_c3_axis_ne_one⟩,
    ⟨false, c3AxisWitness, 1, toy_c3_axis_ne_one,
      (toyWrongRhoFVdashIso.localRlfIso false).injective.ne
        toy_c3_axis_ne_one⟩⟩

theorem toy_wrong_rho_fails_naturality :
    ¬ RhoNaturalitySquare toyWrongRhoFVdashIso := by
  intro h
  have hw := h false c3AxisWitness
  exact toy_c3_swap_axis_ne_self (by
    simpa [toyWrongRhoFVdashIso, toyFVdashSource, toyFVdashTarget] using hw)

theorem prime_and_rho_compatibility_are_independent :
    (RhoNaturalitySquare toyWrongPrimeFVdashIso ∧
        FVdashIsoNondegenerate toyWrongPrimeFVdashIso ∧
        ¬ PrimeLabelSquare toyWrongPrimeFVdashIso) ∧
      (PrimeLabelSquare toyWrongRhoFVdashIso ∧
        FVdashIsoNondegenerate toyWrongRhoFVdashIso ∧
        ¬ RhoNaturalitySquare toyWrongRhoFVdashIso) :=
  ⟨⟨toy_wrong_prime_rho_square_still_holds,
      toy_wrong_prime_is_nondegenerate,
      toy_wrong_prime_fails_label_square⟩,
    ⟨toy_wrong_rho_prime_square_still_holds,
      toy_wrong_rho_is_nondegenerate,
      toy_wrong_rho_fails_naturality⟩⟩

/-! ## 6. Both squares alone admit a closed one-point degeneration -/

abbrev ClosedPrime (_ : Unit) := Unit
abbrev ClosedLocal (_ : Unit) := Unit
abbrev ClosedGlobalLoc (_ : Unit) (_ : Unit) := ZMod 1
abbrev ClosedLocalRlf (_ : Unit) (_ : Unit) := ZMod 1
abbrev ClosedGlobalIso (_ _ : Unit) := Unit
abbrev ClosedLocalIso (_ : Unit) (_ _ : Unit) := Unit

abbrev ClosedFVdash :=
  FVdashPrimeStripRaw Unit Unit ClosedPrime ClosedLocal
    ClosedGlobalLoc ClosedLocalRlf

def closedFVdash : ClosedFVdash where
  global := ()
  primeEquiv := Equiv.refl Unit
  localObj := fun _ ↦ ()
  rho := fun _ ↦ ContinuousMulEquiv.refl (ZMod 1)

def closedFVdashIso :
    FVdashIsoRaw closedFVdash closedFVdash
      ClosedGlobalIso ClosedLocalIso where
  globalIso := ()
  primeIso := Equiv.refl Unit
  localIso := fun _ ↦ ()
  globalLocIso := fun _ ↦ ContinuousMulEquiv.refl (ZMod 1)
  localRlfIso := fun _ ↦ ContinuousMulEquiv.refl (ZMod 1)

theorem closed_fvdash_prime_square :
    PrimeLabelSquare closedFVdashIso := by
  intro p
  rfl

theorem closed_fvdash_rho_square :
    RhoNaturalitySquare closedFVdashIso := by
  intro v x
  rfl

theorem closed_fvdash_fails_nondegeneracy :
    ¬ FVdashIsoNondegenerate closedFVdashIso := by
  rintro ⟨⟨p, q, hpq, _⟩, _⟩
  exact hpq (Subsingleton.elim p q)

theorem source_shape_and_squares_do_not_exclude_closed_unit :
    PrimeLabelSquare closedFVdashIso ∧
      RhoNaturalitySquare closedFVdashIso ∧
      ¬ FVdashIsoNondegenerate closedFVdashIso :=
  ⟨closed_fvdash_prime_square, closed_fvdash_rho_square,
    closed_fvdash_fails_nondegeneracy⟩

#print axioms FVdashPrimeStripRaw
#print axioms FVdashIsoRaw
#print axioms PrimeLabelSquare
#print axioms RhoNaturalitySquare
#print axioms FVdashIsoNondegenerate
#print axioms TwoSquareFVdashIso
#print axioms FVdashIsoRaw.toTwoSquare
#print axioms boolFlipEquiv
#print axioms ToyPrime
#print axioms ToyLocal
#print axioms ToyGlobalLoc
#print axioms ToyLocalRlf
#print axioms ToyGlobalIso
#print axioms ToyLocalIso
#print axioms ToyFVdash
#print axioms toy_c3_axis_ne_one
#print axioms toy_c3_swap_axis_ne_self
#print axioms toyFVdashSource
#print axioms toyFVdashTarget
#print axioms toySynchronizedFVdashIso
#print axioms toy_synchronized_prime_square
#print axioms toy_synchronized_rho_square
#print axioms toy_synchronized_nondegenerate
#print axioms toyTwoSquareFVdashIso
#print axioms toyWrongPrimeFVdashIso
#print axioms toy_wrong_prime_rho_square_still_holds
#print axioms toy_wrong_prime_is_nondegenerate
#print axioms toy_wrong_prime_fails_label_square
#print axioms toyWrongRhoFVdashIso
#print axioms toy_wrong_rho_prime_square_still_holds
#print axioms toy_wrong_rho_is_nondegenerate
#print axioms toy_wrong_rho_fails_naturality
#print axioms prime_and_rho_compatibility_are_independent
#print axioms ClosedPrime
#print axioms ClosedLocal
#print axioms ClosedGlobalLoc
#print axioms ClosedLocalRlf
#print axioms ClosedGlobalIso
#print axioms ClosedLocalIso
#print axioms ClosedFVdash
#print axioms closedFVdash
#print axioms closedFVdashIso
#print axioms closed_fvdash_prime_square
#print axioms closed_fvdash_rho_square
#print axioms closed_fvdash_fails_nondegeneracy
#print axioms source_shape_and_squares_do_not_exclude_closed_unit

end

end Grounding.ThetaLink
