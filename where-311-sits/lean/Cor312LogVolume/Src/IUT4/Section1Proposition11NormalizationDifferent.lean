import Mathlib
import Cor312LogVolume.Src.Lib.AlgebraTraceIntegral

namespace Src.IUT4.Proposition11

open TensorProduct

variable (O K L S : Type*) [CommRing O] [Field K] [Field L] [CommRing S]
  [Algebra O K] [Algebra K L] [Algebra K S] [Algebra O L] [IsScalarTower O K L]
  [Algebra O S] [IsScalarTower O K S]

def integralTensorSpan : Submodule O (L ⊗[K] S) :=
  Submodule.span O {w | ∃ (x : L) (y : S), IsIntegral O x ∧ IsIntegral O y ∧ w = x ⊗ₜ[K] y}

variable {O K L S}

theorem trace_one_tmul [Module.Finite K S] (s : S) :
    Algebra.trace L (L ⊗[K] S) (1 ⊗ₜ[K] s) = algebraMap K L (Algebra.trace K S s) := by
  have h : Algebra.lmul L (L ⊗[K] S) (1 ⊗ₜ[K] s) = (Algebra.lmul K S s).baseChange L := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp [LinearMap.baseChange_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]

theorem coeff_eq_trace [Module.Finite K S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b b' : Module.Basis ι K S) (hdual : ∀ i j, Algebra.trace K S (b' j * b i) = if j = i then 1 else 0)
    (z : L ⊗[K] S) (i : ι) :
    (Algebra.TensorProduct.basis L b').repr z i = Algebra.trace L (L ⊗[K] S) (z * (1 ⊗ₜ[K] b i)) := by
  set B := Algebra.TensorProduct.basis L b'
  conv_rhs => rw [← B.sum_repr z]
  rw [Finset.sum_mul, map_sum]
  simp_rw [smul_mul_assoc, LinearMap.map_smul_of_tower]
  have hterm : ∀ j, Algebra.trace L (L ⊗[K] S) (B j * (1 ⊗ₜ[K] b i)) = if j = i then 1 else 0 := by
    intro j
    rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul, hdual]
    split_ifs <;> simp
  simp_rw [hterm, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem coeff_isIntegral [Module.Finite K S]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b b' : Module.Basis ι K S) (hdual : ∀ i j, Algebra.trace K S (b' j * b i) = if j = i then 1 else 0)
    (hb : ∀ i, IsIntegral O (b i)) (z : L ⊗[K] S) (hz : IsIntegral O z) (i : ι) :
    IsIntegral O ((Algebra.TensorProduct.basis L b').repr z i) := by
  rw [coeff_eq_trace b b' hdual z i]
  apply SrcLib.AlgebraTraceIntegral.isIntegral_trace_of_finite (R := O) (K := L)
  have hbi : IsIntegral O ((1 : L) ⊗ₜ[K] b i) := by
    have := (hb i).map ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := S)).restrictScalars O)
    simpa using this
  exact hz.mul hbi

theorem mul_mem_integralTensorSpan [Module.Finite K S]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b b' : Module.Basis ι K S) (hdual : ∀ i j, Algebra.trace K S (b' j * b i) = if j = i then 1 else 0)
    (hb : ∀ i, IsIntegral O (b i)) (δ : S) (hδ : ∀ j, IsIntegral O (δ * b' j))
    (z : L ⊗[K] S) (hz : IsIntegral O z) :
    z * (1 ⊗ₜ[K] δ) ∈ integralTensorSpan O K L S := by
  set B := Algebra.TensorProduct.basis L b'
  rw [← B.sum_repr z, Finset.sum_mul]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hexp : (B.repr z j • B j) * (1 ⊗ₜ[K] δ) = (B.repr z j) ⊗ₜ[K] (δ * b' j) := by
    rw [Algebra.TensorProduct.basis_apply, smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_comm (b' j) δ, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hexp]
  exact Submodule.subset_span ⟨_, _, coeff_isIntegral b b' hdual hb z hz j, hδ j, rfl⟩

theorem mul_mem_span_tmul [Module.Finite K S]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b b' : Module.Basis κ K S) (hdual : ∀ i j, Algebra.trace K S (b' j * b i) = if j = i then 1 else 0)
    (hb : ∀ i, IsIntegral O (b i)) (T : Set S) (δ : S) (hδ : ∀ j, δ * b' j ∈ T)
    (z : L ⊗[K] S) (hz : IsIntegral O z) :
    z * (1 ⊗ₜ[K] δ) ∈ Submodule.span O {w | ∃ (x : L) (y : S), IsIntegral O x ∧ y ∈ T ∧ w = x ⊗ₜ[K] y} := by
  set B := Algebra.TensorProduct.basis L b'
  rw [← B.sum_repr z, Finset.sum_mul]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hexp : (B.repr z j • B j) * (1 ⊗ₜ[K] δ) = (B.repr z j) ⊗ₜ[K] (δ * b' j) := by
    rw [Algebra.TensorProduct.basis_apply, smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_comm (b' j) δ, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hexp]
  exact Submodule.subset_span ⟨_, _, coeff_isIntegral b b' hdual hb z hz j, hδ j, rfl⟩

section Dedekind

variable {O K L₁ L₂ B₂ : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  [IsIntegrallyClosed O]
  [Field L₁] [Algebra K L₁] [Algebra O L₁] [IsScalarTower O K L₁]
  [Field L₂] [Algebra K L₂] [Algebra O L₂] [IsScalarTower O K L₂] [FiniteDimensional K L₂]
  [Algebra.IsSeparable K L₂]
  [CommRing B₂] [IsDomain B₂] [Algebra O B₂] [Algebra B₂ L₂] [IsScalarTower O B₂ L₂]
  [IsIntegralClosure B₂ O L₂] [IsDedekindDomain B₂] [IsFractionRing B₂ L₂] [Module.IsTorsionFree O B₂]
  [Module.Free O B₂] [Module.Finite O B₂]
  [IsLocalization (Algebra.algebraMapSubmonoid B₂ (nonZeroDivisors O)) L₂]

theorem prop11_two_factors (δ : B₂) (hδ : δ ∈ differentIdeal O B₂) (z : L₁ ⊗[K] L₂) (hz : IsIntegral O z) :
    z * (1 ⊗ₜ[K] algebraMap B₂ L₂ δ) ∈ integralTensorSpan O K L₁ L₂ := by
  classical
  let b₀ := Module.Free.chooseBasis O B₂
  let b : Module.Basis _ K L₂ := b₀.localizationLocalization K (nonZeroDivisors O) L₂
  have hb : ∀ i, IsIntegral O (b i) := by
    intro i
    rw [Module.Basis.localizationLocalization_apply]
    exact (IsIntegralClosure.isIntegral O L₂ (b₀ i)).algebraMap
  have hdual : ∀ i j, Algebra.trace K L₂ (b.traceDual j * b i) = if j = i then 1 else 0 := by
    intro i j
    rw [b.trace_traceDual_mul j i]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; exact h2 h1.symm) | (exfalso; exact h1 h2.symm)
  have hspan : (1 : Submodule B₂ L₂).restrictScalars O = Submodule.span O (Set.range b) := by
    rw [Module.Basis.localizationLocalization_span K (nonZeroDivisors O) L₂]
    ext
    simp
  have hdualmem : ∀ j, b.traceDual j ∈ Submodule.traceDual O K (1 : Submodule B₂ L₂) := by
    intro j
    have h := Submodule.traceDual_span_of_basis O (1 : Submodule B₂ L₂) b hspan
    have hmem : b.traceDual j ∈ (Submodule.traceDual O K (1 : Submodule B₂ L₂)).restrictScalars O := by
      rw [h]; exact Submodule.subset_span ⟨j, rfl⟩
    exact hmem
  have hδ' : ∀ j, IsIntegral O (algebraMap B₂ L₂ δ * b.traceDual j) := by
    intro j
    have hcoe : algebraMap B₂ L₂ δ ∈ IsLocalization.coeSubmodule L₂ (differentIdeal O B₂) := ⟨δ, hδ, rfl⟩
    rw [coeSubmodule_differentIdeal O K] at hcoe
    have hmul := (Submodule.mem_div_iff_forall_mul_mem.mp hcoe) _ (hdualmem j)
    rw [Submodule.mem_one] at hmul
    obtain ⟨y, hy⟩ := hmul
    rw [← hy]
    exact (IsIntegralClosure.isIntegral O L₂ y).algebraMap
  exact mul_mem_integralTensorSpan b b.traceDual hdual hb (algebraMap B₂ L₂ δ) hδ' z hz

end Dedekind

section Multiple

open PiTensorProduct

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, Field (L i)] [∀ i, Algebra K (L i)] [∀ i, FiniteDimensional K (L i)]

instance instFiniteTensorPacket : Module.Finite K (⨂[K] i, L i) :=
  Module.Finite.of_basis (Basis.piTensorProduct fun i => Module.Free.chooseBasis K (L i))

theorem trace_tprod (x : ∀ i, L i) :
    Algebra.trace K (⨂[K] i, L i) (tprod K x) = ∏ i, Algebra.trace K (L i) (x i) := by
  classical
  let b := fun i => Module.Free.chooseBasis K (L i)
  let B := Basis.piTensorProduct b
  rw [Algebra.trace_eq_matrix_trace B, Matrix.trace]
  simp_rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, B, Basis.piTensorProduct_apply, tprod_mul_tprod,
    Basis.piTensorProduct_repr_tprod_apply, Pi.mul_apply]
  rw [← Fintype.prod_sum (fun i k => (b i).repr (x i * b i k) k)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b i), Matrix.trace]
  simp [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]

theorem tprod_eq_prod_single (y : ∀ i, L i) :
    tprod K y = ∏ i, singleAlgHom (R := K) (A := L) i (y i) := by
  simp only [singleAlgHom_apply]
  change tprodMonoidHom (R := K) (A := L) y = ∏ i, tprodMonoidHom (R := K) (A := L) (MonoidHom.mulSingle L i (y i))
  rw [← map_prod (tprodMonoidHom (R := K) (A := L))]
  congr 1
  simp only [MonoidHom.mulSingle_apply]
  exact (Finset.univ_prod_mulSingle y).symm

variable {O : Type*} [CommRing O] [Algebra O K] [∀ i, Algebra O (L i)] [∀ i, IsScalarTower O K (L i)]

theorem isIntegral_tprod (y : ∀ i, L i) (hy : ∀ i, IsIntegral O (y i)) :
    IsIntegral O (tprod K y) := by
  rw [tprod_eq_prod_single]
  refine IsIntegral.prod _ fun i _ => ?_
  exact (hy i).map ((singleAlgHom (R := K) (A := L) i).restrictScalars O)

end Multiple

section MultipleDedekind

open PiTensorProduct

variable {O K : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  [IsIntegrallyClosed O]
  {L₀ : Type*} [Field L₀] [Algebra K L₀] [Algebra O L₀] [IsScalarTower O K L₀]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {L B : ι → Type*}
  [∀ i, Field (L i)] [∀ i, Algebra K (L i)] [∀ i, Algebra O (L i)] [∀ i, IsScalarTower O K (L i)]
  [∀ i, FiniteDimensional K (L i)] [∀ i, Algebra.IsSeparable K (L i)]
  [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, Algebra O (B i)] [∀ i, Algebra (B i) (L i)]
  [∀ i, IsScalarTower O (B i) (L i)] [∀ i, IsIntegralClosure (B i) O (L i)] [∀ i, IsDedekindDomain (B i)]
  [∀ i, IsFractionRing (B i) (L i)] [∀ i, Module.IsTorsionFree O (B i)] [∀ i, Module.Free O (B i)]
  [∀ i, Module.Finite O (B i)]
  [∀ i, IsLocalization (Algebra.algebraMapSubmonoid (B i) (nonZeroDivisors O)) (L i)]

variable (O K L₀ L) in

def tensorPacketOrder : Submodule O (L₀ ⊗[K] (⨂[K] i, L i)) :=
  Submodule.span O {w | ∃ (x : L₀) (y : ∀ i, L i), IsIntegral O x ∧ (∀ i, IsIntegral O (y i)) ∧
    w = x ⊗ₜ[K] tprod K y}

theorem prop11 (δ : ∀ i, B i) (hδ : ∀ i, δ i ∈ differentIdeal O (B i))
    (z : L₀ ⊗[K] (⨂[K] i, L i)) (hz : IsIntegral O z) :
    z * (1 ⊗ₜ[K] tprod K (fun i => algebraMap (B i) (L i) (δ i))) ∈ tensorPacketOrder O K L₀ L := by
  classical
  let b₀ := fun i => Module.Free.chooseBasis O (B i)
  let b : ∀ i, Module.Basis _ K (L i) := fun i => (b₀ i).localizationLocalization K (nonZeroDivisors O) (L i)
  have hb : ∀ i k, IsIntegral O (b i k) := by
    intro i k
    rw [Module.Basis.localizationLocalization_apply]
    exact (IsIntegralClosure.isIntegral O (L i) (b₀ i k)).algebraMap
  have hδ' : ∀ i k, IsIntegral O (algebraMap (B i) (L i) (δ i) * (b i).traceDual k) := by
    intro i k
    have hspan : (1 : Submodule (B i) (L i)).restrictScalars O = Submodule.span O (Set.range (b i)) := by
      rw [Module.Basis.localizationLocalization_span K (nonZeroDivisors O) (L i)]
      ext
      simp
    have hmem : (b i).traceDual k ∈ (Submodule.traceDual O K (1 : Submodule (B i) (L i))).restrictScalars O := by
      rw [Submodule.traceDual_span_of_basis O (1 : Submodule (B i) (L i)) (b i) hspan]
      exact Submodule.subset_span ⟨k, rfl⟩
    have hcoe : algebraMap (B i) (L i) (δ i) ∈ IsLocalization.coeSubmodule (L i) (differentIdeal O (B i)) :=
      ⟨δ i, hδ i, rfl⟩
    rw [coeSubmodule_differentIdeal O K] at hcoe
    have hmul := (Submodule.mem_div_iff_forall_mul_mem.mp hcoe) _ hmem
    rw [Submodule.mem_one] at hmul
    obtain ⟨y, hy⟩ := hmul
    rw [← hy]
    exact (IsIntegralClosure.isIntegral O (L i) y).algebraMap
  let Bs := Basis.piTensorProduct b
  let Bs' := Basis.piTensorProduct fun i => (b i).traceDual
  have hdual : ∀ m n, Algebra.trace K (⨂[K] i, L i) (Bs' n * Bs m) = if n = m then 1 else 0 := by
    intro m n
    simp only [Bs, Bs', Basis.piTensorProduct_apply, tprod_mul_tprod, trace_tprod, Pi.mul_apply,
      Module.Basis.trace_traceDual_mul]
    rw [Fintype.prod_boole]
    by_cases h : n = m
    · subst h; simp
    · rw [if_neg h, if_neg]
      intro hall
      exact h (funext fun i => (hall i).symm)
  have hB : ∀ m, IsIntegral O (Bs m) := fun m => by
    simpa [Bs] using isIntegral_tprod (O := O) _ fun i => hb i (m i)
  have hmem := mul_mem_span_tmul (O := O) (K := K) (L := L₀) Bs Bs' hdual hB
    {y | ∃ y' : ∀ i, L i, (∀ i, IsIntegral O (y' i)) ∧ y = tprod K y'}
    (tprod K (fun i => algebraMap (B i) (L i) (δ i)))
    (fun n => ⟨fun i => algebraMap (B i) (L i) (δ i) * (b i).traceDual (n i), fun i => hδ' i (n i), by
      simp only [Bs', Basis.piTensorProduct_apply, tprod_mul_tprod]; rfl⟩) z hz
  refine Submodule.span_mono ?_ hmem
  rintro w ⟨x, y, hx, ⟨y', hy', rfl⟩, rfl⟩
  exact ⟨x, y', hx, hy', rfl⟩

theorem isIntegral_of_mem_tensorPacketOrder {w : L₀ ⊗[K] (⨂[K] i, L i)}
    (hw : w ∈ tensorPacketOrder O K L₀ L) : IsIntegral O w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, y, hx, hy, rfl⟩ := hw
    have h1 : IsIntegral O (x ⊗ₜ[K] (1 : ⨂[K] i, L i)) :=
      hx.map ((Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := L₀) (B := ⨂[K] i, L i)).restrictScalars O)
    have h2 : IsIntegral O ((1 : L₀) ⊗ₜ[K] tprod K y) :=
      (isIntegral_tprod (O := O) y hy).map
        ((Algebra.TensorProduct.includeRight (R := K) (A := L₀) (B := ⨂[K] i, L i)).restrictScalars O)
    have h3 := h1.mul h2
    rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h3
  | zero => exact isIntegral_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul r x _ hx =>
    exact hx.smul r

end MultipleDedekind

section FactorDedekind

variable {O K : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  [IsIntegrallyClosed O]
  {L₁ B₁ : Type*} [Field L₁] [Algebra K L₁] [Algebra O L₁] [IsScalarTower O K L₁] [FiniteDimensional K L₁]
  [Algebra.IsSeparable K L₁]
  [CommRing B₁] [IsDomain B₁] [Algebra O B₁] [Algebra B₁ L₁] [IsScalarTower O B₁ L₁]
  [IsIntegralClosure B₁ O L₁] [IsDedekindDomain B₁] [IsFractionRing B₁ L₁] [Module.IsTorsionFree O B₁]
  [Module.Free O B₁] [Module.Finite O B₁]
  [IsLocalization (Algebra.algebraMapSubmonoid B₁ (nonZeroDivisors O)) L₁]

variable (O K L₁ B₁) in

noncomputable def integralBasis : Module.Basis (Module.Free.ChooseBasisIndex O B₁) K L₁ :=
  (Module.Free.chooseBasis O B₁).localizationLocalization K (nonZeroDivisors O) L₁

omit [IsIntegrallyClosed O] [FiniteDimensional K L₁] [Algebra.IsSeparable K L₁] [IsDomain B₁]
  [IsDedekindDomain B₁] [IsFractionRing B₁ L₁] [Module.IsTorsionFree O B₁] [Module.Finite O B₁] in
theorem integralBasis_isIntegral (k : Module.Free.ChooseBasisIndex O B₁) :
    IsIntegral O (integralBasis O K L₁ B₁ k) := by
  rw [integralBasis, Module.Basis.localizationLocalization_apply]
  exact (IsIntegralClosure.isIntegral O L₁ _).algebraMap

theorem different_mul_traceDual_isIntegral (δ : B₁) (hδ : δ ∈ differentIdeal O B₁)
    (k : Module.Free.ChooseBasisIndex O B₁) :
    IsIntegral O (algebraMap B₁ L₁ δ * (integralBasis O K L₁ B₁).traceDual k) := by
  have hspan : (1 : Submodule B₁ L₁).restrictScalars O = Submodule.span O (Set.range (integralBasis O K L₁ B₁)) := by
    rw [integralBasis, Module.Basis.localizationLocalization_span K (nonZeroDivisors O) L₁]
    ext
    simp
  have hmem : (integralBasis O K L₁ B₁).traceDual k ∈
      (Submodule.traceDual O K (1 : Submodule B₁ L₁)).restrictScalars O := by
    rw [Submodule.traceDual_span_of_basis O (1 : Submodule B₁ L₁) (integralBasis O K L₁ B₁) hspan]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hcoe : algebraMap B₁ L₁ δ ∈ IsLocalization.coeSubmodule L₁ (differentIdeal O B₁) := ⟨δ, hδ, rfl⟩
  rw [coeSubmodule_differentIdeal O K] at hcoe
  have hmul := (Submodule.mem_div_iff_forall_mul_mem.mp hcoe) _ hmem
  rw [Submodule.mem_one] at hmul
  obtain ⟨y, hy⟩ := hmul
  rw [← hy]
  exact (IsIntegralClosure.isIntegral O L₁ y).algebraMap

end FactorDedekind

section PureDedekind

open PiTensorProduct

variable {O K : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  [IsIntegrallyClosed O]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {L B : ι → Type*}
  [∀ i, Field (L i)] [∀ i, Algebra K (L i)] [∀ i, Algebra O (L i)] [∀ i, IsScalarTower O K (L i)]
  [∀ i, FiniteDimensional K (L i)] [∀ i, Algebra.IsSeparable K (L i)]
  [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, Algebra O (B i)] [∀ i, Algebra (B i) (L i)]
  [∀ i, IsScalarTower O (B i) (L i)] [∀ i, IsIntegralClosure (B i) O (L i)] [∀ i, IsDedekindDomain (B i)]
  [∀ i, IsFractionRing (B i) (L i)] [∀ i, Module.IsTorsionFree O (B i)] [∀ i, Module.Free O (B i)]
  [∀ i, Module.Finite O (B i)]
  [∀ i, IsLocalization (Algebra.algebraMapSubmonoid (B i) (nonZeroDivisors O)) (L i)]

variable (O K L) in

def packetOrder : Submodule O (⨂[K] i, L i) :=
  Submodule.span O {w | ∃ y : ∀ i, L i, (∀ i, IsIntegral O (y i)) ∧ w = tprod K y}

variable (O K L B) in

noncomputable def packetBasis :
    Module.Basis (∀ i, Module.Free.ChooseBasisIndex O (B i)) K (⨂[K] i, L i) :=
  Basis.piTensorProduct fun i => integralBasis O K (L i) (B i)

variable (O K L B) in

noncomputable def packetDualBasis :
    Module.Basis (∀ i, Module.Free.ChooseBasisIndex O (B i)) K (⨂[K] i, L i) :=
  Basis.piTensorProduct fun i => (integralBasis O K (L i) (B i)).traceDual

theorem trace_packetDual_mul (m n : ∀ i, Module.Free.ChooseBasisIndex O (B i)) :
    Algebra.trace K (⨂[K] i, L i) (packetDualBasis O K L B n * packetBasis O K L B m) =
      if n = m then 1 else 0 := by
  simp only [packetBasis, packetDualBasis, Basis.piTensorProduct_apply, tprod_mul_tprod, trace_tprod,
    Pi.mul_apply, Module.Basis.trace_traceDual_mul]
  rw [Fintype.prod_boole]
  by_cases h : n = m
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro hall
    exact h (funext fun i => (hall i).symm)

theorem packetDual_repr_eq_trace (z : ⨂[K] i, L i) (n : ∀ i, Module.Free.ChooseBasisIndex O (B i)) :
    (packetDualBasis O K L B).repr z n = Algebra.trace K (⨂[K] i, L i) (z * packetBasis O K L B n) := by
  set B' := packetDualBasis O K L B
  conv_rhs => rw [← B'.sum_repr z]
  rw [Finset.sum_mul, map_sum]
  simp_rw [smul_mul_assoc, LinearMap.map_smul_of_tower]
  simp_rw [B', trace_packetDual_mul, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem packetBasis_isIntegral (m : ∀ i, Module.Free.ChooseBasisIndex O (B i)) :
    IsIntegral O (packetBasis O K L B m) := by
  rw [packetBasis, Basis.piTensorProduct_apply]
  exact isIntegral_tprod _ fun i => integralBasis_isIntegral (m i)

theorem exists_algebraMap_eq_packetDual_repr (z : ⨂[K] i, L i) (hz : IsIntegral O z)
    (n : ∀ i, Module.Free.ChooseBasisIndex O (B i)) :
    ∃ o : O, algebraMap O K o = (packetDualBasis O K L B).repr z n := by
  rw [packetDual_repr_eq_trace]
  have hint : IsIntegral O (Algebra.trace K (⨂[K] i, L i) (z * packetBasis O K L B n)) :=
    SrcLib.AlgebraTraceIntegral.isIntegral_trace_of_finite (R := O) (K := K)
      (hz.mul (packetBasis_isIntegral n))
  exact IsIntegrallyClosed.isIntegral_iff.mp hint

theorem sum_packetDual_of_isIntegral (z : ⨂[K] i, L i) (hz : IsIntegral O z) :
    ∃ o : (∀ i, Module.Free.ChooseBasisIndex O (B i)) → O, z = ∑ n, o n • packetDualBasis O K L B n := by
  classical
  choose o ho using exists_algebraMap_eq_packetDual_repr (B := B) z hz
  refine ⟨o, ?_⟩
  conv_lhs => rw [← (packetDualBasis O K L B).sum_repr z]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← ho n, algebraMap_smul]

theorem mem_span_packetDual_of_isIntegral (z : ⨂[K] i, L i) (hz : IsIntegral O z) :
    z ∈ Submodule.span O (Set.range (packetDualBasis O K L B)) := by
  obtain ⟨o, rfl⟩ := sum_packetDual_of_isIntegral (B := B) z hz
  exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

theorem prop11_all_factors (δ : ∀ i, B i) (hδ : ∀ i, δ i ∈ differentIdeal O (B i))
    (z : ⨂[K] i, L i) (hz : IsIntegral O z) :
    tprod K (fun i => algebraMap (B i) (L i) (δ i)) * z ∈ packetOrder O K L := by
  classical
  obtain ⟨o, rfl⟩ := sum_packetDual_of_isIntegral (B := B) z hz
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun n _ => ?_
  rw [mul_smul_comm]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun i =>
    algebraMap (B i) (L i) (δ i) * (integralBasis O K (L i) (B i)).traceDual (n i),
    fun i => different_mul_traceDual_isIntegral (δ i) (hδ i) (n i), ?_⟩)
  rw [packetDualBasis, Basis.piTensorProduct_apply, tprod_mul_tprod]
  rfl

omit [IsDomain O] [IsFractionRing O K] [IsIntegrallyClosed O] [∀ i, Algebra.IsSeparable K (L i)] in

theorem isIntegral_of_mem_packetOrder {w : ⨂[K] i, L i} (hw : w ∈ packetOrder O K L) : IsIntegral O w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, rfl⟩ := hw
    exact isIntegral_tprod y hy
  | zero => exact isIntegral_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul r x _ hx => exact hx.smul r

end PureDedekind

section Model

variable (p : ℕ) [Fact p.Prime]

theorem model_prop11 :
    ∃ δ : ℤ_[p], δ ≠ 0 ∧ δ ∈ differentIdeal ℤ_[p] ℤ_[p] ∧
      ∀ z : ℚ_[p] ⊗[ℚ_[p]] ℚ_[p], IsIntegral ℤ_[p] z →
        z * (1 ⊗ₜ[ℚ_[p]] algebraMap ℤ_[p] ℚ_[p] δ) ∈ integralTensorSpan ℤ_[p] ℚ_[p] ℚ_[p] ℚ_[p] := by
  have hne : differentIdeal ℤ_[p] ℤ_[p] ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨δ, hδ0, hδ, fun z hz => prop11_two_factors (O := ℤ_[p]) (K := ℚ_[p]) (L₁ := ℚ_[p]) (L₂ := ℚ_[p])
    (B₂ := ℤ_[p]) δ hδ z hz⟩

end Model

section Model3

open PiTensorProduct

variable (p : ℕ) [Fact p.Prime]

theorem model_prop11_three_factors :
    ∃ δ : Fin 2 → ℤ_[p], (∀ i, δ i ≠ 0 ∧ δ i ∈ differentIdeal ℤ_[p] ℤ_[p]) ∧
      ∀ z : ℚ_[p] ⊗[ℚ_[p]] (⨂[ℚ_[p]] _ : Fin 2, ℚ_[p]), IsIntegral ℤ_[p] z →
        z * (1 ⊗ₜ[ℚ_[p]] tprod ℚ_[p] (fun i => algebraMap ℤ_[p] ℚ_[p] (δ i))) ∈
          tensorPacketOrder ℤ_[p] ℚ_[p] ℚ_[p] (fun _ : Fin 2 => ℚ_[p]) := by
  have hne : differentIdeal ℤ_[p] ℤ_[p] ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨fun _ => δ, fun _ => ⟨hδ0, hδ⟩, fun z hz =>
    prop11 (O := ℤ_[p]) (K := ℚ_[p]) (L₀ := ℚ_[p]) (L := fun _ : Fin 2 => ℚ_[p]) (B := fun _ : Fin 2 => ℤ_[p])
      (fun _ => δ) (fun _ => hδ) z hz⟩

end Model3

end Src.IUT4.Proposition11

section Check
open Src.IUT4.Proposition11
end Check
