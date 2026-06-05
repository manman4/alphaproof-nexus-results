/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option maxHeartbeats 200000

universe u v w


class IsSeparablyGenerated (k K : Type*) [Field k] [Field K] [Algebra k K] : Prop where
  out : ∃ (s : Set K), IsTranscendenceBasis k (fun x : s ↦ (x : K)) ∧
    Algebra.IsSeparable (IntermediateField.adjoin k s) K

class IsSeparableExtensionSP (k K : Type*) [Field k] [Field K] [Algebra k K] : Prop where
  out : ∀ (K' : IntermediateField k K) [Algebra.EssFiniteType k ↥K'], IsSeparablyGenerated k ↥K'

class IsSeparablyFinitelyGenerated (k K : Type*) [Field k] [Field K] [Algebra k K] : Prop where
  out : ∃ (s : Finset K), IsTranscendenceBasis k (fun x : (s : Set K) ↦ (x : K)) ∧
    Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K


open TensorProduct
open TensorProduct Polynomial


variable (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
variable {k S}
variable {R : Type w} [CommRing R] [Algebra k R]

-- EVOLVE-BLOCK-START
#check LinearMap.BilinForm.apply_dualBasis_left
#check LinearMap.BilinForm.apply_dualBasis_right

lemma isReduced_tensorProduct_symm_helper (k A B : Type*) [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] (h : IsReduced (A ⊗[k] B)) : IsReduced (B ⊗[k] A) := by
  have e : B ⊗[k] A ≃ₐ[k] A ⊗[k] B := Algebra.TensorProduct.comm k B A
  have h_inj : Function.Injective e := e.injective
  exact isReduced_of_injective e h_inj

lemma isReduced_mvPolynomial_tensor (k S : Type*) [Field k] [CommRing S] [Algebra k S] [IsReduced S] (s : Type*) :
    IsReduced (MvPolynomial s k ⊗[k] S) := by
  letI : DecidableEq s := Classical.typeDecidableEq s
  have e : MvPolynomial s k ⊗[k] S ≃ₐ[k] MvPolynomial s S := MvPolynomial.scalarRTensorAlgEquiv
  have h_inj : Function.Injective e := e.injective
  have h_red : IsReduced (MvPolynomial s S) := by infer_instance
  exact isReduced_of_injective e h_inj

lemma helper_isReduced_of_isLocalization {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (M : Submonoid A) [IsLocalization M B] [IsReduced A] : IsReduced B := by
  use fun and ⟨a, C⟩=>((IsLocalization.mk'_surjective M and).elim fun and true => true▸by_contradiction fun and' =>absurd C (@true▸?_) )
  norm_num[←IsLocalization.mk'_pow,IsLocalization.mk'_eq_zero_iff]at and'⊢
  exact (fun R L h=>and' R L (IsReduced.eq_zero _ ⟨a+1,by linear_combination2 h*_^a*and.1⟩))

lemma helper_tensor_isLocalization {k A F S : Type*} [Field k] [CommRing S] [Algebra k S] [CommRing A] [Algebra k A] [Field F] [Algebra k F] [Algebra A F] [IsScalarTower k A F] [IsFractionRing A F] :
    letI : Algebra (A ⊗[k] S) (F ⊗[k] S) := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A F) (AlgHom.id k S)).toAlgebra
    IsLocalization ((nonZeroDivisors A).map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] S).toMonoidHom) (F ⊗[k] S) := by
  apply by_contradiction
  use(. (?_))
  use(? _),? _,?_
  · norm_num[RingHom.algebraMap_toAlgebra]
    norm_num[isUnit_iff_exists,funext_iff]
    use fun a s=>⟨(algebraMap A F a)⁻¹ ⊗ₜ[k]1,?_⟩
    norm_num[funext_iff]
    cases@subsingleton_or_nontrivial A with| inl=>cases not_subsingleton F (Module.subsingleton A _)| inr=>_
    norm_num[nonZeroDivisors.ne_zero s,Pi.mul_def,Pi.inv_def]
    rfl
  · use(TensorProduct.induction_on · ⟨(0,1),zero_mul _,⟩ (?_) ? _)
    · use fun and x =>(IsFractionRing.div_surjective (A:=A) and).elim fun and ⟨a, _⟩=>?_
      norm_num[←And.right (by valid),←TensorProduct.smul_tmul']
      use and ⊗ₜ[k]x,a, And.left (by assumption)
      norm_num[RingHom.algebraMap_toAlgebra]
      cases subsingleton_or_nontrivial A with| inl=>norm_num[Subsingleton.elim and 0]| inr=>rw[div_mul_cancel₀ _ (by norm_num[nonZeroDivisors.ne_zero (And.left (by valid))])]
    · refine fun and n ⟨(a, b), _⟩ ⟨(x, y), _⟩=>⟨(a*y+x*b,b*y),?_⟩
      zify[mul_comm y.1, add_mul,←‹and*_ = _›,←by valid,mul_assoc]
      exact (congr_arg _) ((congr_arg _)<|mul_comm _ _)
  · norm_num[RingHom.algebraMap_toAlgebra]
    use fun and=>⟨1,by cases subsingleton_or_nontrivial A with| inl=>rcases not_subsingleton F ↑(Module.subsingleton A F) | inr =>norm_num,?_⟩
    revert‹A ⊗[k]S›‹¬_›
    use fun and R M=>congrArg _ ?_
    convert Module.Flat.rTensor_preserves_injective_linearMap (IsScalarTower.toAlgHom k A F).toLinearMap (IsFractionRing.injective _ _) M

lemma isReduced_tensorProduct_of_algebra_adjoin_transcendental
    (k S K' : Type*) [Field k] [CommRing S] [Algebra k S] [Field K'] [Algebra k K']
    (s : Set K') (hs : IsTranscendenceBasis k (fun x : s ↦ (x : K'))) [IsReduced S] :
    IsReduced (Algebra.adjoin k s ⊗[k] S) := by
  have h_indep : AlgebraicIndependent k (fun x : s ↦ (x : K')) := hs.1
  let e1 : MvPolynomial s k ≃ₐ[k] Algebra.adjoin k (Set.range (fun x : s ↦ (x : K'))) := AlgebraicIndependent.aevalEquiv h_indep
  have h_range : Set.range (fun x : s ↦ (x : K')) = s := Subtype.range_val
  let e2 : MvPolynomial s k ≃ₐ[k] Algebra.adjoin k s := AlgEquiv.trans e1 (Subalgebra.equivOfEq _ _ (by rw [h_range]))
  let e_tensor : MvPolynomial s k ⊗[k] S ≃ₐ[k] Algebra.adjoin k s ⊗[k] S := Algebra.TensorProduct.congr e2 (AlgEquiv.refl)
  have h_red : IsReduced (MvPolynomial s k ⊗[k] S) := isReduced_mvPolynomial_tensor k S s
  exact isReduced_of_injective e_tensor.symm e_tensor.symm.injective

lemma helper_isFractionRing {k K' : Type*} [Field k] [Field K'] [Algebra k K'] (s : Set K') :
    let A := Algebra.adjoin k s
    let F := IntermediateField.adjoin k s
    letI : Algebra A F := (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin k s)).toAlgebra
    IsFractionRing A F := by
  nontriviality Real
  use(? _),? _,?_
  · use fun and=>Ne.isUnit (nonZeroDivisors.ne_zero and.2 ∘and.1.eq ∘congr_arg Subtype.val)
  · norm_num(config := {singlePass:=1})[IntermediateField.mem_adjoin_simple_iff,funext_iff]
    norm_num
    intros
    rw[IntermediateField.mem_adjoin_iff]at*
    simp_all[funext_iff,Subtype.eq_iff,MvPolynomial.aeval_def,Algebra.adjoin_eq_range]
    obtain ⟨A, B, rfl⟩ := by valid
    by_cases h:B.eval₂ (algebraMap _ _) Subtype.val=0
    · use 0, ⟨0, rfl⟩,1,one_ne_zero, ⟨1,by bound⟩,show _=0 by norm_num[h]
    · exact ⟨_, ⟨A, rfl⟩,_,h, ⟨B, rfl⟩,div_mul_cancel₀ _ h⟩
  · simp_all only[ implies_true,Subtype.eq_iff,Subtype.exists, and_self,exists_prop]
    use fun and=>⟨1,one_mem _,one_mem _,.trans (congr_arg _ (one_mul _)) (and.trans (congr_arg _ (one_mul _).symm) :)⟩

lemma isReduced_tensorProduct_of_transcendence_basis (k S K' : Type*) [Field k] [CommRing S] [Algebra k S] [Field K'] [Algebra k K']
    (s : Set K') (hs : IsTranscendenceBasis k (fun x : s ↦ (x : K'))) [IsReduced S] :
    IsReduced (IntermediateField.adjoin k s ⊗[k] S) := by
  let A := Algebra.adjoin k s
  let F := IntermediateField.adjoin k s
  have h_le : A ≤ F.toSubalgebra := IntermediateField.algebra_adjoin_le_adjoin k s
  letI : Algebra A F := (Subalgebra.inclusion h_le).toAlgebra
  haveI : IsScalarTower k A F := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsFractionRing A F := helper_isFractionRing s
  have h_A_red : IsReduced (A ⊗[k] S) := isReduced_tensorProduct_of_algebra_adjoin_transcendental k S K' s hs
  letI alg_AF : Algebra (A ⊗[k] S) (F ⊗[k] S) := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A F) (AlgHom.id k S)).toAlgebra
  have h_loc : IsLocalization ((nonZeroDivisors A).map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] S).toMonoidHom) (F ⊗[k] S) := helper_tensor_isLocalization
  exact @helper_isReduced_of_isLocalization (A ⊗[k] S) (F ⊗[k] S) _ _ alg_AF _ h_loc h_A_red

lemma isReduced_tensorProduct_of_separable_algebraic_iso (k S F K' : Type*) [Field k] [CommRing S] [Algebra k S] [Field F] [Field K'] [Algebra k F] [Algebra k K']
    [Algebra F K'] [IsScalarTower k F K'] : Nonempty (K' ⊗[k] S ≃ₐ[k] K' ⊗[F] (F ⊗[k] S)) := by
  let e1 : (K' ⊗[F] F) ⊗[k] S ≃ₐ[F] K' ⊗[F] (F ⊗[k] S) := Algebra.TensorProduct.assoc k F K' F S
  let e2 : K' ⊗[F] F ≃ₐ[F] K' := Algebra.TensorProduct.rid F F K'
  let e3 : (K' ⊗[F] F) ⊗[k] S ≃ₐ[k] K' ⊗[k] S := Algebra.TensorProduct.congr (e2.restrictScalars k) (AlgEquiv.refl : S ≃ₐ[k] S)
  let e4 : K' ⊗[k] S ≃ₐ[k] K' ⊗[F] (F ⊗[k] S) := AlgEquiv.trans e3.symm (e1.restrictScalars k)
  exact ⟨e4⟩

lemma exists_intermediateField_fg_over_F {F K : Type*} [Field F] [Field K] [Algebra F K] (B : Subalgebra F K) (hB : B.FG) :
    ∃ (K'' : IntermediateField F K), B ≤ K''.toSubalgebra ∧ K''.FG := by
  rcases hB with ⟨s, hs⟩
  use IntermediateField.adjoin F (s : Set K)
  constructor
  · rw [← hs]
    exact IntermediateField.algebra_adjoin_le_adjoin F (s : Set K)
  · exact IntermediateField.fg_adjoin_finset s

lemma helper_tensor_map_injective_over_F {F A K : Type*} [Field F] [CommRing A] [Algebra F A] [Field K] [Algebra F K]
    (B : Subalgebra F K) (K'' : IntermediateField F K) (h_le : B ≤ K''.toSubalgebra) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id F A) (Subalgebra.inclusion h_le)) := by
  exact (Module.Flat.lTensor_preserves_injective_linearMap _) ((B.inclusion_injective) (h_le))

lemma isReduced_iff_sq_eq_zero {R : Type*} [CommRing R] : IsReduced R ↔ ∀ x : R, x ^ 2 = 0 → x = 0 := by
  exact (isReduced_iff_pow_one_lt _) (by constructor)

lemma helper_module_free {F K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsSeparable F K] {A : Type*} [CommRing A] [Algebra F A] [IsReduced A] [FiniteDimensional F K] :
    Module.Free A (A ⊗[F] K) := by
  apply inferInstance

lemma helper_module_finite {F K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsSeparable F K] {A : Type*} [CommRing A] [Algebra F A] [IsReduced A] [FiniteDimensional F K] :
    Module.Finite A (A ⊗[F] K) := by
  apply inferInstance

lemma isReduced_tensorProduct_of_finite_separable_trace {F K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsSeparable F K] {A : Type*} [CommRing A] [Algebra F A] [IsReduced A] [FiniteDimensional F K] [Module.Free A (A ⊗[F] K)] [Module.Finite A (A ⊗[F] K)] (z : A ⊗[F] K) (hz : z ^ 2 = 0) :
    Algebra.trace A (A ⊗[F] K) z = 0 := by
  have h_lmul_nilp : IsNilpotent (Algebra.lmul A (A ⊗[F] K) z) := by
    use 2
    apply LinearMap.ext
    intro x
    calc ((Algebra.lmul A (A ⊗[F] K) z) ^ 2) x = z * (z * x) := rfl
      _ = (z * z) * x := (mul_assoc z z x).symm
      _ = z ^ 2 * x := by rw [← sq]
      _ = 0 * x := by rw [hz]
      _ = 0 := MulZeroClass.zero_mul x
      _ = (0 : Module.End A (A ⊗[F] K)) x := rfl
  have h_trace_nilp := LinearMap.isNilpotent_trace_of_isNilpotent h_lmul_nilp
  exact IsReduced.eq_zero _ h_trace_nilp

lemma helper_lmul_tensor {F K A : Type*} [Field F] [Field K] [Algebra F K] [CommRing A] [Algebra F A] (a : A) (k : K) :
    Algebra.lmul A (A ⊗[F] K) (a ⊗ₜ[F] k) = a • (LinearMap.baseChange A (Algebra.lmul F K k)) := by
  norm_num[LinearMap.ext_iff,Algebra.algebraMap_eq_smul_one]
  use (by induction. with simp_all[TensorProduct.smul_tmul',mul_left_comm, mul_add, SModEq])

lemma helper_trace_tensor {F K A : Type*} [Field F] [Field K] [Algebra F K] [CommRing A] [Algebra F A] [FiniteDimensional F K] [Module.Free A (A ⊗[F] K)] [Module.Finite A (A ⊗[F] K)] (a : A) (k : K) :
    Algebra.trace A (A ⊗[F] K) (a ⊗ₜ[F] k) = a * algebraMap F A (Algebra.trace F K k) := by
  have h_trace_def : Algebra.trace A (A ⊗[F] K) (a ⊗ₜ[F] k) = LinearMap.trace A (A ⊗[F] K) (Algebra.lmul A (A ⊗[F] K) (a ⊗ₜ[F] k)) := rfl
  rw [h_trace_def]
  have h1 : Algebra.lmul A (A ⊗[F] K) (a ⊗ₜ[F] k) = a • (LinearMap.baseChange A (Algebra.lmul F K k)) := helper_lmul_tensor a k
  rw [h1]
  rw [LinearMap.map_smul]
  have h2 : LinearMap.trace A (A ⊗[F] K) (LinearMap.baseChange A (Algebra.lmul F K k)) = algebraMap F A (Algebra.trace F K k) := by
    exact LinearMap.trace_baseChange (Algebra.lmul F K k) A
  rw [h2]
  rfl

lemma helper_z_eq_sum {F K A : Type*} [Field F] [Field K] [Algebra F K] [CommRing A] [Algebra F A] (z : A ⊗[F] K)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F K) :
    ∃ c : ι → A, z = ∑ i, c i ⊗ₜ[F] b i := by
  refine z.induction_on ⟨0,by simp_all [ Finset.univ]⟩ ↑(?_) ?_
  · refine fun and μ =>b.sum_repr μ▸⟨ _,.trans (TensorProduct.tmul_sum _ _ _) ( Fintype.sum_congr _ _ fun and=>TensorProduct.tmul_smul _ _ _)⟩
  · use fun and i a s=>a.choose_spec▸s.choose_spec▸⟨ _, Finset.sum_add_distrib.symm.trans ( Fintype.sum_congr _ _ fun and=>TensorProduct.add_tmul _ _ _).symm⟩

lemma helper_exists_dual_basis {F K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsSeparable F K] [FiniteDimensional F K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F K) :
    ∃ b' : ι → K, ∀ i j, Algebra.trace F K (b i * b' j) = if i = j then (1 : F) else (0 : F) := by
  have h_nondeg := traceForm_nondegenerate F K
  let b' := LinearMap.BilinForm.dualBasis (Algebra.traceForm F K) h_nondeg b
  use b'
  intro i j
  have h1 : Algebra.trace F K (b i * b' j) = Algebra.trace F K (b' j * b i) := by rw [mul_comm]
  rw [h1]
  have h2 : Algebra.trace F K (b' j * b i) = (Algebra.traceForm F K) (b' j) (b i) := rfl
  rw [h2]
  have h3 : (Algebra.traceForm F K) (b' j) (b i) = if i = j then (1 : F) else (0 : F) := LinearMap.BilinForm.apply_dualBasis_left h_nondeg b j i
  exact h3

lemma helper_trace_sum {F K A : Type*} [Field F] [Field K] [Algebra F K] [CommRing A] [Algebra F A] [FiniteDimensional F K] [Module.Free A (A ⊗[F] K)] [Module.Finite A (A ⊗[F] K)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → A) (k1 k2 : ι → K)
    (h_dual : ∀ i j, Algebra.trace F K (k1 i * k2 j) = if i = j then (1 : F) else (0 : F)) (j : ι) :
    Algebra.trace A (A ⊗[F] K) ((∑ i, c i ⊗ₜ[F] k1 i) * (1 ⊗ₜ[F] k2 j)) = c j := by
  have h1 : (∑ i, c i ⊗ₜ[F] k1 i) * (1 ⊗ₜ[F] k2 j) = ∑ i, c i ⊗ₜ[F] (k1 i * k2 j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    have h_mul : (c i ⊗ₜ[F] k1 i : A ⊗[F] K) * (1 ⊗ₜ[F] k2 j) = (c i * 1) ⊗ₜ[F] (k1 i * k2 j) := Algebra.TensorProduct.tmul_mul_tmul (c i) 1 (k1 i) (k2 j)
    rw [h_mul, mul_one]
  rw [h1]
  rw [map_sum]
  have h2 : ∀ i, Algebra.trace A (A ⊗[F] K) (c i ⊗ₜ[F] (k1 i * k2 j)) = c i * (if i = j then (1 : A) else (0 : A)) := by
    intro i
    rw [helper_trace_tensor (c i) (k1 i * k2 j)]
    rw [h_dual i j]
    split_ifs with hij
    · simp
    · simp
  have h3 : ∑ i, Algebra.trace A (A ⊗[F] K) (c i ⊗ₜ[F] (k1 i * k2 j)) = ∑ i, c i * (if i = j then (1 : A) else (0 : A)) := Finset.sum_congr rfl (fun i _ => h2 i)
  rw [h3]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · intro hj
    exfalso
    exact hj (Finset.mem_univ j)

lemma helper_trace_zero_implies_zero {F K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsSeparable F K] {A : Type*} [CommRing A] [Algebra F A] [IsReduced A] [FiniteDimensional F K] [Module.Free A (A ⊗[F] K)] [Module.Finite A (A ⊗[F] K)] (z : A ⊗[F] K) (h_trace : ∀ y, Algebra.trace A (A ⊗[F] K) (z * y) = 0) :
    z = 0 := by
  let ι := Module.Free.ChooseBasisIndex F K
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype F K
  haveI : DecidableEq ι := Classical.typeDecidableEq ι
  let b : Module.Basis ι F K := Module.Free.chooseBasis F K
  have h1 : ∃ c : ι → A, z = ∑ i, c i ⊗ₜ[F] b i := helper_z_eq_sum z b
  rcases h1 with ⟨c, hc⟩
  have h2 : ∃ b' : ι → K, ∀ i j, Algebra.trace F K (b i * b' j) = if i = j then (1 : F) else (0 : F) := helper_exists_dual_basis b
  rcases h2 with ⟨b', hb'⟩
  have hc0 : ∀ j, c j = 0 := by
    intro j
    have h_eval := h_trace (1 ⊗ₜ[F] b' j)
    rw [hc] at h_eval
    have h_sum := helper_trace_sum c b b' hb' j
    rw [h_eval] at h_sum
    exact h_sum.symm
  rw [hc]
  have hz0 : (∑ i, c i ⊗ₜ[F] b i) = 0 := by
    have h_c_zero : ∀ i, c i ⊗ₜ[F] b i = 0 := by
      intro i
      rw [hc0 i, zero_tmul]
    exact Finset.sum_eq_zero (fun i _ => h_c_zero i)
  exact hz0

lemma isReduced_tensorProduct_of_finite_separable_field
    (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Algebra.IsSeparable F K]
    (A : Type*) [CommRing A] [Algebra F A] [IsReduced A] : IsReduced (A ⊗[F] K) := by
  letI : Module.Free A (A ⊗[F] K) := helper_module_free
  letI : Module.Finite A (A ⊗[F] K) := helper_module_finite
  rw [isReduced_iff_sq_eq_zero]
  intro z hz
  have h_trace_all : ∀ y, Algebra.trace A (A ⊗[F] K) (z * y) = 0 := by
    intro y
    have h_nilp : (z * y) ^ 2 = 0 := by
      calc (z * y) ^ 2 = z ^ 2 * y ^ 2 := by ring
      _ = 0 * y ^ 2 := by rw [hz]
      _ = 0 := MulZeroClass.zero_mul _
    exact isReduced_tensorProduct_of_finite_separable_trace (z * y) h_nilp
  exact helper_trace_zero_implies_zero z h_trace_all

lemma helper_fin_dim_of_fg_algebraic {F K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K] (K'' : IntermediateField F K) (h : K''.FG) :
    FiniteDimensional F K'' := by
  obtain ⟨s, rfl⟩:=h
  exact (IntermediateField.finiteDimensional_adjoin fun and c=>(Algebra.IsIntegral.isIntegral and))

lemma helper_is_separable_subfield {F K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsSeparable F K] (K'' : IntermediateField F K) :
    Algebra.IsSeparable F K'' := by
  refine inferInstance

lemma isReduced_tensorProduct_of_separable_algebraic_helper
    (k S F K' : Type*) [Field k] [CommRing S] [Algebra k S] [Field F] [Field K'] [Algebra k F] [Algebra k K']
    [Algebra F K'] [IsScalarTower k F K']
    [Algebra.IsSeparable F K'] [Algebra.IsAlgebraic F K']
    (hF : IsReduced (F ⊗[k] S)) : IsReduced ((F ⊗[k] S) ⊗[F] K') := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg (R := F) (C := F ⊗[k] S) (A := K')
  intro B hB
  rcases exists_intermediateField_fg_over_F B hB with ⟨K'', h_le, hK''_fg⟩
  have h_fin : FiniteDimensional F K'' := helper_fin_dim_of_fg_algebraic K'' hK''_fg
  have h_sep : Algebra.IsSeparable F K'' := helper_is_separable_subfield K''
  have h_red_K'' : IsReduced ((F ⊗[k] S) ⊗[F] K'') := isReduced_tensorProduct_of_finite_separable_field F K'' (F ⊗[k] S)
  have h_inj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id F (F ⊗[k] S)) (Subalgebra.inclusion h_le)) := helper_tensor_map_injective_over_F B K'' h_le
  exact isReduced_of_injective _ h_inj

lemma isReduced_tensorProduct_of_separable_algebraic (k S F K' : Type*) [Field k] [CommRing S] [Algebra k S] [Field F] [Algebra k F] [Field K'] [Algebra k K'] [Algebra F K'] [IsScalarTower k F K'] [Algebra.IsSeparable F K'] [Algebra.IsAlgebraic F K']
    (h_F_red : IsReduced (F ⊗[k] S)) : IsReduced (K' ⊗[k] S) := by
  have ⟨e⟩ := isReduced_tensorProduct_of_separable_algebraic_iso k S F K'
  have h_red : IsReduced (K' ⊗[F] (F ⊗[k] S)) := by
    have h1 := isReduced_tensorProduct_of_separable_algebraic_helper k S F K' h_F_red
    exact isReduced_tensorProduct_symm_helper F (F ⊗[k] S) K' h1
  exact isReduced_of_injective e e.injective

lemma isReduced_tensorProduct_of_separably_generated
    (k S K' : Type*) [Field k] [CommRing S] [Algebra k S] [Field K'] [Algebra k K'] [IsSeparablyGenerated k K']
    [IsReduced S] : IsReduced (K' ⊗[k] S) := by
  have ⟨s, hs_trans, hs_sep⟩ := IsSeparablyGenerated.out (k := k) (K := K')
  have h_F_red : IsReduced (IntermediateField.adjoin k s ⊗[k] S) := isReduced_tensorProduct_of_transcendence_basis k S K' s hs_trans
  have h_alg_step := isReduced_tensorProduct_of_separable_algebraic k S (IntermediateField.adjoin k s) K' h_F_red
  exact h_alg_step

lemma helper_ess_finite (k K : Type*) [Field k] [Field K] [Algebra k K] (s : Finset K) :
    Algebra.EssFiniteType k (IntermediateField.adjoin k (s : Set K)) := by
  apply IntermediateField.essFiniteType_iff.mpr
  exact IntermediateField.fg_adjoin_finset s

lemma helper_subalgebra_le (k K : Type*) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K)
    (s : Finset K) (hs : Algebra.adjoin k (s : Set K) = B) :
    B ≤ (IntermediateField.adjoin k (s : Set K)).toSubalgebra := by
  use hs▸IntermediateField.algebra_adjoin_le_adjoin _ _

lemma helper_map_injective (k S K : Type*) [Field k] [CommRing S] [Algebra k S] [Field K] [Algebra k K]
    (B : Subalgebra k K) (K' : IntermediateField k K) (h_le : B ≤ K'.toSubalgebra) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id k S) (Subalgebra.inclusion h_le)) := by
  apply Module.Flat.lTensor_preserves_injective_linearMap _<|B.inclusion_injective h_le

lemma helper_is_reduced (k S K : Type*) [Field k] [CommRing S] [Algebra k S] [Field K] [Algebra k K]
    [IsSeparableExtensionSP k K] [IsReduced S] : IsReduced (K ⊗[k] S) := by
  apply isReduced_tensorProduct_symm_helper k S K
  apply IsReduced.tensorProduct_of_flat_of_forall_fg (R := k) (C := S) (A := K)
  intro B hB
  rcases hB with ⟨s, hs⟩
  let K' := IntermediateField.adjoin k (s : Set K)
  have h_ess : Algebra.EssFiniteType k K' := helper_ess_finite k K s
  have h_sep : IsSeparablyGenerated k K' := IsSeparableExtensionSP.out K'
  have h_red_K' : IsReduced (K' ⊗[k] S) := isReduced_tensorProduct_of_separably_generated k S K'
  have h_red_SK' : IsReduced (S ⊗[k] K') := isReduced_tensorProduct_symm_helper k K' S h_red_K'
  have h_le : B ≤ K'.toSubalgebra := helper_subalgebra_le k K B s hs
  have h_inj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id k S) (Subalgebra.inclusion h_le)) := helper_map_injective k S K B K' h_le
  exact isReduced_of_injective _ h_inj

-- EVOLVE-BLOCK-END

theorem isReduced_tensorProduct_of_separable
    (K : Type u) [Field K] [Algebra k K] [IsSeparableExtensionSP k K]
    [IsReduced S] : IsReduced (K ⊗[k] S) := by
  -- EVOLVE-BLOCK-START
  exact helper_is_reduced k S K
  -- EVOLVE-BLOCK-END
