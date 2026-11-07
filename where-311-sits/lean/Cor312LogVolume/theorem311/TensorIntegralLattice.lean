import Cor312LogVolume.theorem311.PadicNormDifferent
import Cor312LogVolume.theorem311.NormalizedHaarCore
import Mathlib.Topology.Algebra.Module.Compact

noncomputable section
set_option autoImplicit false

namespace CitedLV.Theorem311.TensorIntegralLattice

open Src.IUT4.Proposition11
open CitedLV.Theorem311.PadicNormIntegerRing
open CitedLV.Theorem311.PadicNormedRamification
open scoped TensorProduct Topology

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (p : ℕ) [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Type*)
  [∀ i, NormedField (L i)] [∀ i, NormedAlgebra ℚ_[p] (L i)]
  [∀ i, IsUltrametricDist (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]

def Packet := ⨂[ℚ_[p]] i, L i

instance packetCommRing : CommRing (Packet p L) :=
  inferInstanceAs (CommRing (⨂[ℚ_[p]] i, L i))

instance packetAlgebra : Algebra ℚ_[p] (Packet p L) :=
  inferInstanceAs (Algebra ℚ_[p] (⨂[ℚ_[p]] i, L i))

instance packetIntegerAlgebra : Algebra ℤ_[p] (Packet p L) :=
  inferInstanceAs (Algebra ℤ_[p] (⨂[ℚ_[p]] i, L i))

instance packetScalarTower : IsScalarTower ℤ_[p] ℚ_[p] (Packet p L) :=
  inferInstanceAs (IsScalarTower ℤ_[p] ℚ_[p] (⨂[ℚ_[p]] i, L i))

instance packetFiniteDimensional : FiniteDimensional ℚ_[p] (Packet p L) :=
  inferInstanceAs (FiniteDimensional ℚ_[p] (⨂[ℚ_[p]] i, L i))

instance packetNormedAddCommGroup : NormedAddCommGroup (Packet p L) :=
  NormedAddCommGroup.induced (Packet p L)
    (Fin (Module.finrank ℚ_[p] (Packet p L)) → ℚ_[p])
    (Module.finBasis ℚ_[p] (Packet p L)).equivFun
    (Module.finBasis ℚ_[p] (Packet p L)).equivFun.injective

instance packetNormedSpace : NormedSpace ℚ_[p] (Packet p L) :=
  NormedSpace.induced ℚ_[p] (Packet p L)
    (Fin (Module.finrank ℚ_[p] (Packet p L)) → ℚ_[p])
    (Module.finBasis ℚ_[p] (Packet p L)).equivFun

instance packetProperSpace : ProperSpace (Packet p L) :=
  FiniteDimensional.proper ℚ_[p] (Packet p L)

instance packetContinuousIntegerSMul : ContinuousSMul ℤ_[p] (Packet p L) where
  continuous_smul := by
    have hc : Continuous (fun z : ℤ_[p] × Packet p L =>
        (algebraMap ℤ_[p] ℚ_[p] z.1) • z.2) :=
      (PadicInt.isOpenEmbedding_coe.continuous.comp continuous_fst).smul continuous_snd
    simpa only [algebraMap_smul] using hc

instance packetMeasurableSpace : MeasurableSpace (Packet p L) := borel _
instance packetBorelSpace : BorelSpace (Packet p L) := ⟨rfl⟩

def integralLattice : Submodule ℤ_[p] (Packet p L) :=
  (integralClosure ℤ_[p] (Packet p L)).toSubmodule

@[simp] theorem mem_integralLattice (x : Packet p L) :
    x ∈ integralLattice p L ↔ IsIntegral ℤ_[p] x := Iff.rfl

theorem integralLattice_fg : (integralLattice p L).FG := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
    fun i => normIntegers_discreteValuationRing p (L i)
  let b' := packetDualBasis ℤ_[p] ℚ_[p] L (fun i => Integers (L i))
  apply (Submodule.fg_span (Set.finite_range b')).of_le
  intro z hz
  exact mem_span_packetDual_of_isIntegral
    (B := fun i => Integers (L i)) z hz

theorem integralLattice_compact : IsCompact (integralLattice p L : Set (Packet p L)) :=
  Submodule.isCompact_of_fg (integralLattice_fg p L)

private def integralBasis :
    Module.Basis (∀ i, Module.Free.ChooseBasisIndex ℤ_[p] (Integers (L i)))
      ℚ_[p] (Packet p L) :=
  packetBasis ℤ_[p] ℚ_[p] L (fun i => Integers (L i))

private def basisBox : Set (Packet p L) :=
  (integralBasis p L).equivFunL ⁻¹'
    Set.univ.pi (fun _ => Metric.closedBall (0 : ℚ_[p]) 1)

private theorem basisBox_open : IsOpen (basisBox p L) := by
  apply IsOpen.preimage (integralBasis p L).equivFunL.continuous
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    IsUltrametricDist.isOpen_closedBall _ one_ne_zero

private theorem zero_mem_basisBox : (0 : Packet p L) ∈ basisBox p L := by
  simp [basisBox, Set.mem_pi]

private theorem basisBox_subset : basisBox p L ⊆ integralLattice p L := by
  letI : ∀ i, IsDiscreteValuationRing (Integers (L i)) :=
    fun i => normIntegers_discreteValuationRing p (L i)
  intro x hx
  change IsIntegral ℤ_[p] x
  let b := integralBasis p L
  rw [← b.sum_repr x]
  change (∑ j, b.repr x j • b j) ∈ integralClosure ℤ_[p] (Packet p L)
  apply Subalgebra.sum_mem
  intro j _
  have hcoef : ‖b.repr x j‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hx j (Set.mem_univ j))
  let a : ℤ_[p] := ⟨b.repr x j, hcoef⟩
  have hb : IsIntegral ℤ_[p] (b j) :=
    packetBasis_isIntegral (B := fun i => Integers (L i)) j
  change IsIntegral ℤ_[p] ((algebraMap ℤ_[p] ℚ_[p] a) • b j)
  rw [algebraMap_smul]
  exact hb.smul a

theorem integralLattice_open : IsOpen (integralLattice p L : Set (Packet p L)) := by
  apply (integralLattice p L).toAddSubgroup.isOpen_of_mem_nhds (g := 0)
  exact Filter.mem_of_superset ((basisBox_open p L).mem_nhds (zero_mem_basisBox p L))
    (basisBox_subset p L)

def integralAnchor : NormalizedHaarRegion (Packet p L) :=
  ⟨integralLattice p L, ⟨integralLattice_compact p L, integralLattice_open p L⟩,
    ⟨0, (integralLattice p L).zero_mem⟩⟩

theorem integralAnchor_measure_one :
    normalizedAddHaar (integralAnchor p L) {x : Packet p L | IsIntegral ℤ_[p] x} = 1 :=
  normalizedAddHaar_anchor (integralAnchor p L)

end CitedLV.Theorem311.TensorIntegralLattice
