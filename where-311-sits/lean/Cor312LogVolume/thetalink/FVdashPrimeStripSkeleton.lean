import Cor312LogVolume.thetalink.CompletePolyIso

namespace CitedLV.ThetaLink

noncomputable section

universe uV uGlobal uPrime uLocal uGLoc uLRlf uGIso uLIso

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

end

end CitedLV.ThetaLink
