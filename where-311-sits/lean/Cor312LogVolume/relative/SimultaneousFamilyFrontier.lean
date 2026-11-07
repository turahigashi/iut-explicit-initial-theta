import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

namespace Src.CoreLayer.RelativeXiFFamily

universe u

structure FamilyPresentation (Base : Type u)
    (J V : Base → Type u) where
  QInput : Base → Type u
  OutputFiber : (b : Base) → J b → V b → Type u
  RegionFiber : (b : Base) → J b → V b → Type u
  Trace : {b : Base} → QInput b →
    ((j : J b) → (v : V b) → OutputFiber b j v) → Type u
  outputRegion : {b : Base} → {j : J b} → {v : V b} →
    OutputFiber b j v → RegionFiber b j v
  rawLogVol : {b : Base} → {j : J b} → {v : V b} →
    RegionFiber b j v → WithBot ℝ
  qLogVolume : {b : Base} → QInput b → ℝ

variable {Base : Type u} {J V : Base → Type u}

abbrev OutputFamily (P : FamilyPresentation Base J V) (b : Base) :=
  (j : J b) → (v : V b) → P.OutputFiber b j v

abbrev RegionFamily (P : FamilyPresentation Base J V) (b : Base) :=
  (j : J b) → (v : V b) → P.RegionFiber b j v

def outputRegionFamily (P : FamilyPresentation Base J V) {b : Base}
    (o : OutputFamily P b) : RegionFamily P b :=
  fun j v => P.outputRegion (o j v)

def rawLogVolumeProfile (P : FamilyPresentation Base J V) {b : Base}
    (r : RegionFamily P b) : (j : J b) → (v : V b) → WithBot ℝ :=
  fun j v => P.rawLogVol (r j v)

@[simp] theorem outputRegionFamily_apply
    (P : FamilyPresentation Base J V) {b : Base}
    (o : OutputFamily P b) (j : J b) (v : V b) :
    outputRegionFamily P o j v = P.outputRegion (o j v) := rfl

@[simp] theorem rawLogVolumeProfile_apply
    (P : FamilyPresentation Base J V) {b : Base}
    (r : RegionFamily P b) (j : J b) (v : V b) :
    rawLogVolumeProfile P r j v = P.rawLogVol (r j v) := rfl

structure ProducedFamily (P : FamilyPresentation Base J V)
    {b : Base} (i : P.QInput b) where
  output : OutputFamily P b
  trace : P.Trace i output

def possibleRegionFamilies (P : FamilyPresentation Base J V)
    {b : Base} (i : P.QInput b) : Set (RegionFamily P b) :=
  Set.range (fun z : ProducedFamily P i => outputRegionFamily P z.output)

structure RegularHull (P : FamilyPresentation Base J V) where
  Derivation : {b : Base} →
    Set (RegionFamily P b) → RegionFamily P b → Type u

def regularHullSet (P : FamilyPresentation Base J V)
    (H : RegularHull P) {b : Base} (s : Set (RegionFamily P b)) :
    Set (RegionFamily P b) :=
  {r | Nonempty (H.Derivation s r)}

structure HulledFamily (P : FamilyPresentation Base J V)
    (H : RegularHull P) {b : Base} (i : P.QInput b) where
  seed : ProducedFamily P i
  region : RegionFamily P b
  derivation : H.Derivation (possibleRegionFamilies P i) region

theorem HulledFamily.region_mem
    {P : FamilyPresentation Base J V} {H : RegularHull P}
    {b : Base} {i : P.QInput b} (w : HulledFamily P H i) :
    w.region ∈ regularHullSet P H (possibleRegionFamilies P i) :=
  ⟨w.derivation⟩

structure ProcessionNormalization (P : FamilyPresentation Base J V) where
  normalize : {b : Base} →
    ((j : J b) → (v : V b) → WithBot ℝ) → WithTop ℝ

def extendedFamilyReadout (P : FamilyPresentation Base J V)
    (N : ProcessionNormalization P) {b : Base}
    (r : RegionFamily P b) : WithTop ℝ :=
  N.normalize (rawLogVolumeProfile P r)

structure FiniteFamilyReadout (P : FamilyPresentation Base J V)
    (H : RegularHull P) (N : ProcessionNormalization P)
    {b : Base} (i : P.QInput b) where
  hulled : HulledFamily P H i
  value : ℝ
  value_spec : (value : WithTop ℝ) =
    extendedFamilyReadout P N hulled.region

def pipelineScalars (P : FamilyPresentation Base J V)
    (H : RegularHull P) (N : ProcessionNormalization P)
    {b : Base} (i : P.QInput b) : Set ℝ :=
  Set.range (fun w : FiniteFamilyReadout P H N i => w.value)

structure OutputShape (P : FamilyPresentation Base J V)
    (H : RegularHull P) (N : ProcessionNormalization P)
    {b : Base} (i : P.QInput b) where
  thetaBound : ℝ
  shape : pipelineScalars P H N i = Set.Iic thetaBound

structure XiFGenerated (P : FamilyPresentation Base J V)
    (H : RegularHull P) (N : ProcessionNormalization P)
    {b : Base} (i : P.QInput b) where
  readout : FiniteFamilyReadout P H N i
  generates_q : readout.value = P.qLogVolume i

theorem qLogVolume_mem_pipelineScalars
    (P : FamilyPresentation Base J V) (H : RegularHull P)
    (N : ProcessionNormalization P) {b : Base} {i : P.QInput b}
    (w : XiFGenerated P H N i) :
    P.qLogVolume i ∈ pipelineScalars P H N i := by
  exact ⟨w.readout, w.generates_q⟩

theorem qLogVolume_le_thetaBound
    (P : FamilyPresentation Base J V) (H : RegularHull P)
    (N : ProcessionNormalization P) {b : Base} {i : P.QInput b}
    (shape : OutputShape P H N i) (w : XiFGenerated P H N i) :
    P.qLogVolume i ≤ shape.thetaBound := by
  have hmem := qLogVolume_mem_pipelineScalars P H N w
  rw [shape.shape] at hmem
  exact hmem

theorem halfLine_shape_does_not_force_arbitrary_membership :
    ∃ (s : Set ℝ) (theta q : ℝ),
      s = Set.Iic theta ∧ q ∉ s := by
  refine ⟨Set.Iic 0, 0, 1, rfl, ?_⟩
  norm_num

structure StrictMorphism
    (P Q : FamilyPresentation Base J V) where
  mapQInput : {b : Base} → P.QInput b → Q.QInput b
  mapOutputFiber : {b : Base} → (j : J b) → (v : V b) →
    P.OutputFiber b j v → Q.OutputFiber b j v
  mapRegionFiber : {b : Base} → (j : J b) → (v : V b) →
    P.RegionFiber b j v → Q.RegionFiber b j v
  outputRegion_commutes : ∀ {b : Base} (j : J b) (v : V b)
    (o : P.OutputFiber b j v),
    Q.outputRegion (mapOutputFiber j v o) =
      mapRegionFiber j v (P.outputRegion o)
  rawLogVol_commutes : ∀ {b : Base} (j : J b) (v : V b)
    (r : P.RegionFiber b j v),
    Q.rawLogVol (mapRegionFiber j v r) = P.rawLogVol r
  qLogVolume_commutes : ∀ {b : Base} (i : P.QInput b),
    Q.qLogVolume (mapQInput i) = P.qLogVolume i
  trace_forward : ∀ {b : Base} {i : P.QInput b}
    {o : OutputFamily P b}, P.Trace i o →
      Q.Trace (mapQInput i)
        (fun j v => mapOutputFiber j v (o j v))

def StrictMorphism.mapOutputFamily
    {P Q : FamilyPresentation Base J V} (f : StrictMorphism P Q)
    {b : Base} (o : OutputFamily P b) : OutputFamily Q b :=
  fun j v => f.mapOutputFiber j v (o j v)

def StrictMorphism.mapRegionFamily
    {P Q : FamilyPresentation Base J V} (f : StrictMorphism P Q)
    {b : Base} (r : RegionFamily P b) : RegionFamily Q b :=
  fun j v => f.mapRegionFiber j v (r j v)

@[simp] theorem StrictMorphism.mapOutputFamily_apply
    {P Q : FamilyPresentation Base J V} (f : StrictMorphism P Q)
    {b : Base} (o : OutputFamily P b) (j : J b) (v : V b) :
    f.mapOutputFamily o j v = f.mapOutputFiber j v (o j v) := rfl

@[simp] theorem StrictMorphism.mapRegionFamily_apply
    {P Q : FamilyPresentation Base J V} (f : StrictMorphism P Q)
    {b : Base} (r : RegionFamily P b) (j : J b) (v : V b) :
    f.mapRegionFamily r j v = f.mapRegionFiber j v (r j v) := rfl

theorem StrictMorphism.outputRegionFamily_commutes
    {P Q : FamilyPresentation Base J V} (f : StrictMorphism P Q)
    {b : Base} (o : OutputFamily P b) :
    outputRegionFamily Q (f.mapOutputFamily o) =
      f.mapRegionFamily (outputRegionFamily P o) := by
  funext j v
  exact f.outputRegion_commutes j v (o j v)

theorem StrictMorphism.rawLogVolumeProfile_commutes
    {P Q : FamilyPresentation Base J V} (f : StrictMorphism P Q)
    {b : Base} (r : RegionFamily P b) :
    rawLogVolumeProfile Q (f.mapRegionFamily r) =
      rawLogVolumeProfile P r := by
  funext j v
  exact f.rawLogVol_commutes j v (r j v)

def StrictMorphism.mapProducedFamily
    {P Q : FamilyPresentation Base J V} (f : StrictMorphism P Q)
    {b : Base} {i : P.QInput b} (z : ProducedFamily P i) :
    ProducedFamily Q (f.mapQInput i) where
  output := f.mapOutputFamily z.output
  trace := f.trace_forward z.trace

theorem possibleRegionFamilies_subset
    {P Q : FamilyPresentation Base J V} (f : StrictMorphism P Q)
    {b : Base} (i : P.QInput b) :
    f.mapRegionFamily '' possibleRegionFamilies P i ⊆
      possibleRegionFamilies Q (f.mapQInput i) := by
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  exact ⟨f.mapProducedFamily z, f.outputRegionFamily_commutes z.output⟩

structure HullCompatible
    {P Q : FamilyPresentation Base J V} (f : StrictMorphism P Q)
    (HP : RegularHull P) (HQ : RegularHull Q) where
  derivation_forward : ∀ {b : Base} {i : P.QInput b}
    {r : RegionFamily P b},
    HP.Derivation (possibleRegionFamilies P i) r →
      HQ.Derivation (possibleRegionFamilies Q (f.mapQInput i))
        (f.mapRegionFamily r)

structure NormalizationCompatible
    {P Q : FamilyPresentation Base J V} (f : StrictMorphism P Q)
    (NP : ProcessionNormalization P) (NQ : ProcessionNormalization Q) : Prop where
  normalize_mapped : ∀ {b : Base} (r : RegionFamily P b),
    extendedFamilyReadout Q NQ (f.mapRegionFamily r) =
      extendedFamilyReadout P NP r

def StrictMorphism.mapHulledFamily
    {P Q : FamilyPresentation Base J V} (f : StrictMorphism P Q)
    {HP : RegularHull P} {HQ : RegularHull Q}
    (hCompat : HullCompatible f HP HQ)
    {b : Base} {i : P.QInput b} (w : HulledFamily P HP i) :
    HulledFamily Q HQ (f.mapQInput i) where
  seed := f.mapProducedFamily w.seed
  region := f.mapRegionFamily w.region
  derivation := hCompat.derivation_forward w.derivation

def StrictMorphism.mapFiniteReadout
    {P Q : FamilyPresentation Base J V} (f : StrictMorphism P Q)
    {HP : RegularHull P} {HQ : RegularHull Q}
    {NP : ProcessionNormalization P} {NQ : ProcessionNormalization Q}
    (hCompat : HullCompatible f HP HQ)
    (hNorm : NormalizationCompatible f NP NQ)
    {b : Base} {i : P.QInput b} (w : FiniteFamilyReadout P HP NP i) :
    FiniteFamilyReadout Q HQ NQ (f.mapQInput i) where
  hulled := f.mapHulledFamily hCompat w.hulled
  value := w.value
  value_spec := by
    change (w.value : WithTop ℝ) =
      extendedFamilyReadout Q NQ (f.mapRegionFamily w.hulled.region)
    rw [hNorm.normalize_mapped]
    exact w.value_spec

def StrictMorphism.mapXiFGenerated
    {P Q : FamilyPresentation Base J V} (f : StrictMorphism P Q)
    {HP : RegularHull P} {HQ : RegularHull Q}
    {NP : ProcessionNormalization P} {NQ : ProcessionNormalization Q}
    (hCompat : HullCompatible f HP HQ)
    (hNorm : NormalizationCompatible f NP NQ)
    {b : Base} {i : P.QInput b} (w : XiFGenerated P HP NP i) :
    XiFGenerated Q HQ NQ (f.mapQInput i) where
  readout := f.mapFiniteReadout hCompat hNorm w.readout
  generates_q := by
    calc
      w.readout.value = P.qLogVolume i := w.generates_q
      _ = Q.qLogVolume (f.mapQInput i) := (f.qLogVolume_commutes i).symm

abbrev MutantIndex : Unit → Type := fun _ => Unit

def emptyTracePresentation :
    FamilyPresentation Unit MutantIndex MutantIndex where
  QInput := fun _ => Unit
  OutputFiber := fun _ _ _ => Unit
  RegionFiber := fun _ _ _ => Unit
  Trace := fun _ _ => Empty
  outputRegion := id
  rawLogVol := fun _ => (0 : ℝ)
  qLogVolume := fun _ => 0

def universalMutantHull : RegularHull emptyTracePresentation where
  Derivation := fun _ _ => Unit

theorem empty_trace_has_no_produced_family :
    ¬ Nonempty (ProducedFamily emptyTracePresentation (b := ()) ()) := by
  rintro ⟨⟨_, h⟩⟩
  exact Empty.elim h

theorem universal_hull_cannot_hide_empty_trace :
    ¬ Nonempty
      (HulledFamily emptyTracePresentation universalMutantHull (b := ()) ()) := by
  rintro ⟨w⟩
  exact empty_trace_has_no_produced_family ⟨w.seed⟩

end Src.CoreLayer.RelativeXiFFamily
