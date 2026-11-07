import Cor312LogVolume.thetalink.FVdashPrimeStripSkeleton

namespace CitedLV.ThetaLink.Cor410iAssembly

noncomputable section

universe uT uV uGlobal uPrime uLocal uGLoc uLRlf

structure Cor46ConstantLocalOutput
    (T : Type uT)
    (V : Type uV)
    (Local : V → Type uLocal) where

  localObj : (t : T) → (v : V) → Local v

abbrev step6LocalMonoid
    {T : Type uT}
    {V : Type uV}
    {Local : V → Type uLocal}
    (LocalRlf : (v : V) → Local v → Type uLRlf)
    [∀ v L, TopologicalSpace (LocalRlf v L)]
    [∀ v L, CommMonoid (LocalRlf v L)]
    (D : Cor46ConstantLocalOutput T V Local)
    (t : T) (v : V) : Type uLRlf :=
  LocalRlf v (D.localObj t v)

structure Cor410iGlobalizationOutput
    (T : Type uT)
    (V : Type uV)
    (Global : Type uGlobal)
    (Prime : Global → Type uPrime)
    (Local : V → Type uLocal)
    (GlobalLoc : (C : Global) → Prime C → Type uGLoc)
    (LocalRlf : (v : V) → Local v → Type uLRlf)
    [∀ C p, TopologicalSpace (GlobalLoc C p)]
    [∀ C p, CommMonoid (GlobalLoc C p)]
    [∀ v L, TopologicalSpace (LocalRlf v L)]
    [∀ v L, CommMonoid (LocalRlf v L)] where
  localData : Cor46ConstantLocalOutput T V Local

  global : T → Global

  primeEquiv : (t : T) → Prime (global t) ≃ V

  rho : (t : T) → (v : V) →
    GlobalLoc (global t) ((primeEquiv t).symm v) ≃ₜ*
      LocalRlf v (localData.localObj t v)

def constantPrimeStrip
    {T : Type uT}
    {V : Type uV}
    {Global : Type uGlobal}
    {Prime : Global → Type uPrime}
    {Local : V → Type uLocal}
    {GlobalLoc : (C : Global) → Prime C → Type uGLoc}
    {LocalRlf : (v : V) → Local v → Type uLRlf}
    [∀ C p, TopologicalSpace (GlobalLoc C p)]
    [∀ C p, CommMonoid (GlobalLoc C p)]
    [∀ v L, TopologicalSpace (LocalRlf v L)]
    [∀ v L, CommMonoid (LocalRlf v L)]
    (D : Cor410iGlobalizationOutput
      T V Global Prime Local GlobalLoc LocalRlf)
    (t : T) :
    FVdashPrimeStripRaw V Global Prime Local GlobalLoc LocalRlf where
  global := D.global t
  primeEquiv := D.primeEquiv t
  localObj := D.localData.localObj t
  rho := D.rho t

@[simp] theorem constantPrimeStrip_global
    {T : Type uT}
    {V : Type uV}
    {Global : Type uGlobal}
    {Prime : Global → Type uPrime}
    {Local : V → Type uLocal}
    {GlobalLoc : (C : Global) → Prime C → Type uGLoc}
    {LocalRlf : (v : V) → Local v → Type uLRlf}
    [∀ C p, TopologicalSpace (GlobalLoc C p)]
    [∀ C p, CommMonoid (GlobalLoc C p)]
    [∀ v L, TopologicalSpace (LocalRlf v L)]
    [∀ v L, CommMonoid (LocalRlf v L)]
    (D : Cor410iGlobalizationOutput
      T V Global Prime Local GlobalLoc LocalRlf)
    (t : T) :
    (constantPrimeStrip D t).global = D.global t := rfl

@[simp] theorem constantPrimeStrip_localObj
    {T : Type uT}
    {V : Type uV}
    {Global : Type uGlobal}
    {Prime : Global → Type uPrime}
    {Local : V → Type uLocal}
    {GlobalLoc : (C : Global) → Prime C → Type uGLoc}
    {LocalRlf : (v : V) → Local v → Type uLRlf}
    [∀ C p, TopologicalSpace (GlobalLoc C p)]
    [∀ C p, CommMonoid (GlobalLoc C p)]
    [∀ v L, TopologicalSpace (LocalRlf v L)]
    [∀ v L, CommMonoid (LocalRlf v L)]
    (D : Cor410iGlobalizationOutput
      T V Global Prime Local GlobalLoc LocalRlf)
    (t : T) (v : V) :
    (constantPrimeStrip D t).localObj v = D.localData.localObj t v := rfl

def step6Localization
    {T : Type uT}
    {V : Type uV}
    {Global : Type uGlobal}
    {Prime : Global → Type uPrime}
    {Local : V → Type uLocal}
    {GlobalLoc : (C : Global) → Prime C → Type uGLoc}
    {LocalRlf : (v : V) → Local v → Type uLRlf}
    [∀ C p, TopologicalSpace (GlobalLoc C p)]
    [∀ C p, CommMonoid (GlobalLoc C p)]
    [∀ v L, TopologicalSpace (LocalRlf v L)]
    [∀ v L, CommMonoid (LocalRlf v L)]
    (D : Cor410iGlobalizationOutput
      T V Global Prime Local GlobalLoc LocalRlf)
    (t : T) (v : V) :
    GlobalLoc (D.global t) ((D.primeEquiv t).symm v) ≃ₜ*
      step6LocalMonoid LocalRlf D.localData t v :=
  D.rho t v

theorem constantPrimeStrip_ne_of_localObj_ne
    {T : Type uT}
    {V : Type uV}
    {Global : Type uGlobal}
    {Prime : Global → Type uPrime}
    {Local : V → Type uLocal}
    {GlobalLoc : (C : Global) → Prime C → Type uGLoc}
    {LocalRlf : (v : V) → Local v → Type uLRlf}
    [∀ C p, TopologicalSpace (GlobalLoc C p)]
    [∀ C p, CommMonoid (GlobalLoc C p)]
    [∀ v L, TopologicalSpace (LocalRlf v L)]
    [∀ v L, CommMonoid (LocalRlf v L)]
    (D : Cor410iGlobalizationOutput
      T V Global Prime Local GlobalLoc LocalRlf)
    {s t : T} {v : V}
    (h : D.localData.localObj s v ≠ D.localData.localObj t v) :
    constantPrimeStrip D s ≠ constantPrimeStrip D t := by
  intro hst
  apply h
  exact congrArg (fun X => X.localObj v) hst

end

end CitedLV.ThetaLink.Cor410iAssembly
