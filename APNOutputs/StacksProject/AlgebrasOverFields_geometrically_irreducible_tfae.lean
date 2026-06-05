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

open PrimeSpectrum Set TensorProduct Polynomial

class GeometricallyIrreducibleAlgebra (k : Type u) (S : Type v)
    [Field k] [CommRing S] [Algebra k S] : Prop where
  out : ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'],
    IrreducibleSpace (PrimeSpectrum (S ⊗[k] k'))

noncomputable def alg_dir_lim
    (k : Type u) [Field k] (ι : Type w) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type (max u v)) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
    (f : ∀ i j, i ≤ j → G i →ₐ[k] G j) :
    Algebra k (Ring.DirectLimit G fun i j h => f i j h) :=
  let i := Classical.arbitrary ι
  let of_i := Ring.DirectLimit.of G (fun i j h => f i j h) i
  RingHom.toAlgebra (RingHom.comp of_i (algebraMap k (G i)))


open TensorProduct Polynomial
open PrimeSpectrum Set TensorProduct Polynomial

-- EVOLVE-BLOCK-START
lemma irreducibleSpace_of_surjective_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hs : Function.Surjective f) (hc : Continuous f) [IrreducibleSpace X] :
    IrreducibleSpace Y := by
  simp_rw [irreducibleSpace_def] at*
  apply hs.image_preimage ⊤▸‹IsIrreducible ⊤›.image f hc.continuousOn

lemma test_nilradical_prime (A : Type*) [CommRing A] :
    IrreducibleSpace (PrimeSpectrum A) ↔ (nilradical A).IsPrime := by
  use fun and=>? _, fun and=>or_self_iff.1 (by_contra (absurd (Fact.mk and) fun and' =>. (?_)))
  · simp_rw [nilradical_eq_sInf,irreducibleSpace_def] at *
    simp_rw [Ideal.isPrime_iff,Ideal.mem_sInf,IsIrreducible,IsPreirreducible]at *
    use (and.1.elim fun and R L=>? _),or_iff_not_imp_left.2 ∘ fun and R L M=>by_contra (R ∘fun C A B=>(B.2 (and B)).resolve_right fun and' =>? _)
    · use and.2.1.comp (eq_top_mono (sInf_le (by use and.2.1, and.2.2))) L
    revert‹by valid›A
    use @fun K V A B a s=> (and.2 {s |by apply_rules ∉s.1} {s |K ∉s.1} (isOpen_iff_mem_nhds.2 fun and x =>?_) (isOpen_iff_mem_nhds.2 fun and x =>?_) ?_ ? _).elim ?_
    · exact ( PrimeSpectrum.isOpen_basicOpen.mem_nhds x)
    · apply PrimeSpectrum.isOpen_basicOpen.mem_nhds ↑x
    · exact (by_contra (R ∘ fun and A B=>by_contra (and ⟨⟨A,Ideal.isPrime_iff.2 B⟩,trivial,.⟩)))
    · exists⟨ L,Ideal.isPrime_iff.2 M⟩
    · use fun and true => true.2.elim (and.2.2 (V ⟨and.2.1, and.2.2⟩) ).elim
  · rw[irreducibleSpace_def, or_self]
    norm_num[IsIrreducible,isPreirreducible_iff_isClosed_union_isClosed]
    simp_rw [ PrimeSpectrum.isClosed_iff_zeroLocus,not_or]at *
    use (by exists⟨_, and⟩),fun K V ⟨a, E⟩⟨A, B⟩H=>(H▸Set.mem_univ (by use(?_))).imp (top_unique ∘?_) (top_unique ∘? _)
    · use E▸fun R M y a s=>M.2.mem_of_pow_mem _ ((R s).choose_spec▸zero_mem _)
    · use B▸ fun and R L a s=>R.2.radical_le_iff.2 bot_le (and s)

lemma test_integral_surj {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.IsIntegral) (hinj : Function.Injective f) :
    Function.Surjective (PrimeSpectrum.comap f) := by
  apply RingHom.IsIntegral.comap_surjective hf
  omega

lemma isIntegral_tmul_one (k R k' L : Type*)
    [Field k] [CommRing R] [Algebra k R]
    [Field k'] [Algebra k k'] [Field L] [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    (r : R) :
    let f := (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k k' L)).toRingHom
    letI : Algebra (R ⊗[k] k') (R ⊗[k] L) := f.toAlgebra
    IsIntegral (R ⊗[k] k') (r ⊗ₜ[k] (1 : L)) := by use .X-.C (r ⊗ₜ[k] 1),Polynomial.monic_X_sub_C _,?_
                                                   norm_num[RingHom.algebraMap_toAlgebra]

lemma isIntegral_one_tmul (k R k' L : Type*)
    [Field k] [CommRing R] [Algebra k R]
    [Field k'] [Algebra k k'] [Field L] [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    (l : L) (hl : IsIntegral k' l) :
    let f := (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k k' L)).toRingHom
    letI : Algebra (R ⊗[k] k') (R ⊗[k] L) := f.toAlgebra
    IsIntegral (R ⊗[k] k') ((1 : R) ⊗ₜ[k] l) := by choose _ _ _simpa using(id) @hl
                                                   simp_all -contextual [eval₂_eq_sum_range]
                                                   use∑ a ∈.range (natDegree (by valid)+1),monomial a (.tmul k (1) (coeff (by valid) a)),monic_of_degree_le (natDegree (by valid)) ((degree_sum_le _ _).trans ( Finset.sup_le fun and x =>? _)) ?_
                                                   · simp_all[eval₂_finset_sum,TensorProduct.smul_tmul',funext_iff,Algebra.algebraMap_eq_smul_one]
                                                     linear_combination2(norm:=norm_num[TensorProduct.tmul_sum, Algebra.smul_def])congr_arg (TensorProduct.tmul k (1 : R)) (_simpa)
                                                     norm_num[RingHom.algebraMap_toAlgebra]
                                                   · exact (degree_monomial_le _ _).trans (WithBot.coe_mono (Finset.mem_range_succ_iff.1 x))
                                                   · simp_all[coeff_monomial]
                                                     rfl

lemma tmul_eq_mul (k R k' L : Type*)
    [Field k] [CommRing R] [Algebra k R]
    [Field k'] [Algebra k k'] [Field L] [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    (r : R) (l : L) : r ⊗ₜ[k] l = (r ⊗ₜ[k] (1 : L)) * ((1 : R) ⊗ₜ[k] l) := by simp_all[TensorProduct.smul_tmul']

lemma integral_tensor_extension (k R k' L : Type*)
    [Field k] [CommRing R] [Algebra k R]
    [Field k'] [Algebra k k'] [Field L] [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    (halg : Algebra.IsIntegral k' L) :
    (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k k' L)).toRingHom.IsIntegral := by
  let f := (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k k' L)).toRingHom
  letI : Algebra (R ⊗[k] k') (R ⊗[k] L) := f.toAlgebra
  intro x
  have H : x ∈ integralClosure (R ⊗[k] k') (R ⊗[k] L) := by
    induction x using TensorProduct.induction_on with
    | zero => exact (integralClosure (R ⊗[k] k') (R ⊗[k] L)).zero_mem
    | tmul r l =>
      have hl : IsIntegral k' l := Algebra.IsIntegral.isIntegral l
      have hr1 : IsIntegral (R ⊗[k] k') (r ⊗ₜ[k] (1 : L)) := isIntegral_tmul_one k R k' L r
      have h1l : IsIntegral (R ⊗[k] k') ((1 : R) ⊗ₜ[k] l) := isIntegral_one_tmul k R k' L l hl
      have heq : r ⊗ₜ[k] l = (r ⊗ₜ[k] (1 : L)) * ((1 : R) ⊗ₜ[k] l) := tmul_eq_mul k R k' L r l
      rw [heq]
      exact (integralClosure (R ⊗[k] k') (R ⊗[k] L)).mul_mem hr1 h1l
    | add y z hy hz => exact (integralClosure (R ⊗[k] k') (R ⊗[k] L)).add_mem hy hz
  exact H

lemma injective_tensor_extension (k : Type u) (R : Type v) (k' L : Type (max u v))
    [Field k] [CommRing R] [Algebra k R]
    [Field k'] [Algebra k k'] [Field L] [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k k' L)).toRingHom := by
  apply Module.Flat.lTensor_preserves_injective_linearMap (IsScalarTower.toAlgHom _ _ _).toLinearMap (algebraMap k' L).injective

lemma irreducible_of_isIntegral_surj (k : Type u) (R : Type v) (k' L : Type (max u v))
    [Field k] [CommRing R] [Algebra k R]
    [Field k'] [Algebra k k'] [Field L] [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    (halg : Algebra.IsIntegral k' L)
    (hL : IrreducibleSpace (PrimeSpectrum (R ⊗[k] L))) :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] k')) := by
  have h_map_int := integral_tensor_extension k R k' L halg
  have h_inj := injective_tensor_extension k R k' L
  have h_surj := test_integral_surj _ h_map_int h_inj
  have hc := PrimeSpectrum.continuous_comap (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k k' L)).toRingHom
  exact irreducibleSpace_of_surjective_continuous _ h_surj hc

lemma irreducible_of_algebraic_closed_extension (k : Type u) (R : Type v)
    [Field k] [CommRing R] [Algebra k R]
    (h4 : ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [IsAlgClosed k'], IrreducibleSpace (PrimeSpectrum (R ⊗[k] k')))
    (k' : Type (max u v)) [Field k'] [Algebra k k'] : IrreducibleSpace (PrimeSpectrum (R ⊗[k] k')) := by
  let L := AlgebraicClosure k'
  haveI : IsAlgClosed L := inferInstance
  have h_irred : IrreducibleSpace (PrimeSpectrum (R ⊗[k] L)) := h4 L
  have h_int : Algebra.IsIntegral k' L := (AlgebraicClosure.isAlgebraic k').isIntegral
  exact irreducible_of_isIntegral_surj k R k' L h_int h_irred

lemma isPrime_of_power {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (h_inj : Function.Injective f)
    (h_pow : ∀ x : B, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f) (h_prime : (nilradical A).IsPrime) :
    (nilradical B).IsPrime := by
  contrapose h_pow with S
  delta nilradical Function.Injective at*
  simp_rw [not_forall,Set.mem_range,Ideal.isPrime_iff,Ideal.mem_radical_iff]at*
  contrapose! S
  norm_num[Ideal.eq_top_iff_one,Ideal.mem_radical_iff,mul_pow] at h_prime S⊢
  use h_prime.1 ∘? _,@fun R M a s=>(S R).elim fun and⟨A, B, _⟩=>(S M).elim fun andexact ⟨D,E, _⟩=>(@h_prime.2 B E (and * a) (h_inj ?_)).imp (?_) ?_
  · use(h_inj.comp (f.map_one).trans<|·.trans f.map_zero.symm)
  · norm_num[show f B = _∧f E = _ by tauto, A.ne',pow_mul',pow_right_comm _ _ a,←mul_pow,D.ne',show R^a*_=0 from s]
    norm_num[pow_right_comm _ _ a, A.ne',mul_pow, mul_mul_mul_comm _ _ (M^ _),D.ne',show R^a*_=0 from s]
    norm_num[←mul_pow, A.ne',Nat.sub_add_cancel A▸pow_succ _ _ ,Nat.sub_add_cancel D▸pow_succ _ _, mul_mul_mul_comm _ (R^ _),show R^a*_=0 from s]
    exact (mul_mul_mul_comm _ _ _ _).trans.comp (mul_eq_zero_of_right _) ((mul_mul_mul_comm _ _ _ _).trans (by rw [s,mul_zero]))
  · use .rec (by use and*.,pow_mul R _ _▸‹_ = _^and›▸f.map_pow _ _▸.▸f.map_zero)
  · exact ( ⟨ _,pow_mul M _ _▸‹_ = _›▸f.map_pow _ _▸·.choose_spec▸f.map_zero⟩)

lemma isPrime_of_images {A : Type*} [CommRing A]
    {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirected ι (· ≤ ·)]
    (A_i : ι → Type*) [∀ i, CommRing (A_i i)]
    (f : ∀ i, A_i i →+* A)
    (h_prime : ∀ i, (nilradical (A_i i)).IsPrime)
    (h_surj : ∀ x : A, ∃ i, ∃ y : A_i i, f i y = x)
    (h_inj : ∀ i, Function.Injective (f i))
    (h_dir : ∀ i j, i ≤ j → ∃ g : A_i i →+* A_i j, (f j).comp g = f i) :
    (nilradical A).IsPrime := by
  have h_ne_top : nilradical A ≠ ⊤ := by
    intro h_top
    have h1 : (1 : A) ∈ nilradical A := by
      rw [h_top]
      trivial
    obtain ⟨n, hn⟩ := h1
    obtain ⟨i⟩ := (‹Nonempty ι›)
    have hp := h_prime i
    have h_ne_top_i := hp.ne_top
    have h1_i : (1 : A_i i) ∈ nilradical (A_i i) := by
      use n
      have hf1 : f i 1 = 1 := map_one (f i)
      have hf0 : f i 0 = 0 := map_zero (f i)
      have hf_pow : f i (1 ^ n) = 0 := by
        rw [map_pow, hf1, one_pow, ← one_pow n, hn]
      exact h_inj i (by rwa [map_zero])
    have h_top_i : nilradical (A_i i) = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      exact h1_i
    exact h_ne_top_i h_top_i
  have h_mem : ∀ {x y : A}, x * y ∈ nilradical A → x ∈ nilradical A ∨ y ∈ nilradical A := by
    intro x y hxy
    obtain ⟨ix, xi, hxi⟩ := h_surj x
    obtain ⟨iy, yi, hyi⟩ := h_surj y
    obtain ⟨k, hkx, hky⟩ := directed_of (· ≤ ·) ix iy
    obtain ⟨gx, hgx⟩ := h_dir ix k hkx
    obtain ⟨gy, hgy⟩ := h_dir iy k hky
    let xk := gx xi
    let yk := gy yi
    have hxk : f k xk = x := by
      calc f k (gx xi) = (f k).comp gx xi := rfl
           _ = f ix xi := by rw [hgx]
           _ = x := hxi
    have hyk : f k yk = y := by
      calc f k (gy yi) = (f k).comp gy yi := rfl
           _ = f iy yi := by rw [hgy]
           _ = y := hyi
    obtain ⟨n, hn⟩ := hxy
    have hxy_k : xk * yk ∈ nilradical (A_i k) := by
      use n
      have h_f : f k ((xk * yk) ^ n) = 0 := by
        rw [map_pow, map_mul, hxk, hyk, hn]
      exact h_inj k (by rwa [map_zero])
    have hp := h_prime k
    cases hp.mem_or_mem hxy_k with
    | inl h =>
      left
      obtain ⟨m, hm⟩ := h
      use m
      have hm_eq : xk ^ m = 0 := hm
      show x ^ m = 0
      rw [← hxk, ← map_pow, hm_eq, map_zero]
    | inr h =>
      right
      obtain ⟨m, hm⟩ := h
      use m
      have hm_eq : yk ^ m = 0 := hm
      show y ^ m = 0
      rw [← hyk, ← map_pow, hm_eq, map_zero]
  exact { ne_top' := h_ne_top, mem_or_mem' := h_mem }

abbrev FinSepSubext (k k' : Type*) [Field k] [Field k'] [Algebra k k'] :=
  { E : IntermediateField k k' // Module.Finite k E ∧ Algebra.IsSeparable k E }

instance (k k' : Type*) [Field k] [Field k'] [Algebra k k'] : Preorder (FinSepSubext k k') :=
  Subtype.preorder _

lemma tfae_2_to_3_directed (k k' : Type*) [Field k] [Field k'] [Algebra k k'] :
    IsDirected (FinSepSubext k k') (· ≤ ·) := by nontriviality ℝ
                                                 use fun R M=>?_
                                                 by_contra!
                                                 cases R
                                                 rcases M
                                                 cases‹_∧_›
                                                 cases‹_∧_›
                                                 simp_all[.≤.]
                                                 specialize this (by bound⊔by valid)
                                                 convert(this inferInstance inferInstance fun and=>le_sup_left (α:=IntermediateField _ _)|>.comp (.)).elim fun and true => true.2<|le_sup_right (α:=IntermediateField _ _) true.1

instance (k k' : Type*) [Field k] [Field k'] [Algebra k k'] : IsDirected (FinSepSubext k k') (· ≤ ·) :=
  tfae_2_to_3_directed k k'

lemma tfae_2_to_3_nonempty (k k' : Type*) [Field k] [Field k'] [Algebra k k'] :
    Nonempty (FinSepSubext k k') := by iterate constructor
                                       exact show Module.Finite k ↑(⊥:IntermediateField _ _)by infer_instance
                                       infer_instance

instance (k k' : Type*) [Field k] [Field k'] [Algebra k k'] : Nonempty (FinSepSubext k k') :=
  tfae_2_to_3_nonempty k k'

abbrev tfae_2_to_3_A_i (k k' : Type*) [Field k] [Field k'] [Algebra k k'] (R : Type*) [CommRing R] [Algebra k R] (E : FinSepSubext k k') :=
  R ⊗[k] E.val

noncomputable abbrev tfae_2_to_3_f (k k' : Type*) [Field k] [Field k'] [Algebra k k'] (R : Type*) [CommRing R] [Algebra k R] (E : FinSepSubext k k') :
    tfae_2_to_3_A_i k k' R E →+* R ⊗[k] k' :=
  (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k E.val k')).toRingHom

lemma tfae_2_to_3_inj (k k' : Type*) [Field k] [Field k'] [Algebra k k'] (R : Type*) [CommRing R] [Algebra k R] (E : FinSepSubext k k') :
    Function.Injective (tfae_2_to_3_f k k' R E) := by delta tfae_2_to_3_A_i tfae_2_to_3_f Real
                                                      apply Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.coe_injective

lemma tfae_2_to_3_dir (k k' : Type*) [Field k] [Field k'] [Algebra k k'] (R : Type*) [CommRing R] [Algebra k R]
    (i j : FinSepSubext k k') (hij : i ≤ j) :
    ∃ g : tfae_2_to_3_A_i k k' R i →+* tfae_2_to_3_A_i k k' R j, (tfae_2_to_3_f k k' R j).comp g = tfae_2_to_3_f k k' R i := by
  let g_alg : i.val →ₐ[k] j.val := Subalgebra.inclusion hij
  use (Algebra.TensorProduct.map (AlgHom.id k R) g_alg).toRingHom
  norm_num[g_alg,tfae_2_to_3_f,RingHom.ext_iff]
  aesop
  exact (TensorProduct.map_map ..).trans (by aesop)

lemma tfae_2_to_3_surj_zero (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [IsSepClosure k k'] (R : Type*) [CommRing R] [Algebra k R] :
    ∃ i : FinSepSubext k k', ∃ y : tfae_2_to_3_A_i k k' R i, tfae_2_to_3_f k k' R i y = 0 := by cases‹IsSepClosure _ _›
                                                                                                norm_num[ tfae_2_to_3_A_i,tfae_2_to_3_f, false_iff]
                                                                                                use⊥, ⟨ inferInstance, inferInstance⟩,? _,?_
                                                                                                norm_num[ tfae_2_to_3_A_i]
                                                                                                use 0
                                                                                                bound

lemma tfae_2_to_3_surj_tmul (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [IsSepClosure k k'] (R : Type*) [CommRing R] [Algebra k R] (r : R) (c : k') :
    ∃ i : FinSepSubext k k', ∃ y : tfae_2_to_3_A_i k k' R i, tfae_2_to_3_f k k' R i y = r ⊗ₜ[k] c := by norm_num[ tfae_2_to_3_A_i,tfae_2_to_3_f]
                                                                                                        cases‹ IsSepClosure _ _›
                                                                                                        use .adjoin k {@c}
                                                                                                        exists⟨IntermediateField.adjoin.finiteDimensional (Algebra.IsSeparable.isIntegral _ _), inferInstance⟩,.tmul k r ⟨ _,IntermediateField.subset_adjoin _ _ rfl⟩

lemma tfae_2_to_3_surj_add (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [IsSepClosure k k'] (R : Type*) [CommRing R] [Algebra k R] (x1 x2 : R ⊗[k] k')
    (hx1 : ∃ i : FinSepSubext k k', ∃ y : tfae_2_to_3_A_i k k' R i, tfae_2_to_3_f k k' R i y = x1)
    (hx2 : ∃ i : FinSepSubext k k', ∃ y : tfae_2_to_3_A_i k k' R i, tfae_2_to_3_f k k' R i y = x2) :
    ∃ i : FinSepSubext k k', ∃ y : tfae_2_to_3_A_i k k' R i, tfae_2_to_3_f k k' R i y = x1 + x2 := by
  rcases hx1 with ⟨i1, y1, hy1⟩
  rcases hx2 with ⟨i2, y2, hy2⟩
  obtain ⟨i3, h1, h2⟩ := @directed_of _ _ (tfae_2_to_3_directed k k') i1 i2
  have h_dir1 := tfae_2_to_3_dir k k' R i1 i3 h1
  have h_dir2 := tfae_2_to_3_dir k k' R i2 i3 h2
  rcases h_dir1 with ⟨g1, hg1⟩
  rcases h_dir2 with ⟨g2, hg2⟩
  use i3
  use g1 y1 + g2 y2
  have h_map1 : (tfae_2_to_3_f k k' R i3) (g1 y1) = x1 := by
    calc (tfae_2_to_3_f k k' R i3) (g1 y1) = ((tfae_2_to_3_f k k' R i3).comp g1) y1 := rfl
         _ = (tfae_2_to_3_f k k' R i1) y1 := by rw [hg1]
         _ = x1 := hy1
  have h_map2 : (tfae_2_to_3_f k k' R i3) (g2 y2) = x2 := by
    calc (tfae_2_to_3_f k k' R i3) (g2 y2) = ((tfae_2_to_3_f k k' R i3).comp g2) y2 := rfl
         _ = (tfae_2_to_3_f k k' R i2) y2 := by rw [hg2]
         _ = x2 := hy2
  rw [RingHom.map_add, h_map1, h_map2]

lemma tfae_2_to_3_surj (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [IsSepClosure k k'] (R : Type*) [CommRing R] [Algebra k R] (x : R ⊗[k] k') :
    ∃ i : FinSepSubext k k', ∃ y : tfae_2_to_3_A_i k k' R i, tfae_2_to_3_f k k' R i y = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact tfae_2_to_3_surj_zero k k' R
  | tmul r c => exact tfae_2_to_3_surj_tmul k k' R r c
  | add x y hx hy => exact tfae_2_to_3_surj_add k k' R x y hx hy

lemma tfae_2_to_3 (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    (h2 : ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [Module.Finite k k']
        [Algebra.IsSeparable k k'], IrreducibleSpace (PrimeSpectrum (R ⊗[k] k')))
    (k' : Type (max u v)) [Field k'] [Algebra k k'] [IsSepClosure k k'] :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] k')) := by
  have h_prime : ∀ E : FinSepSubext k k', (nilradical (tfae_2_to_3_A_i k k' R E)).IsPrime := by
    intro E
    haveI : Module.Finite k E.val := E.property.1
    haveI : Algebra.IsSeparable k E.val := E.property.2
    have h_irr := h2 E.val
    exact (test_nilradical_prime (tfae_2_to_3_A_i k k' R E)).mp h_irr
  have h_surj := tfae_2_to_3_surj k k' R
  have h_inj := tfae_2_to_3_inj k k' R
  have h_dir := tfae_2_to_3_dir k k' R
  have h_prime_lim : (nilradical (R ⊗[k] k')).IsPrime :=
    @isPrime_of_images (R ⊗[k] k') _ (FinSepSubext k k') _ _ _
      (tfae_2_to_3_A_i k k' R) (fun i => inferInstance)
      (tfae_2_to_3_f k k' R) h_prime h_surj h_inj h_dir
  exact (test_nilradical_prime (R ⊗[k] k')).mpr h_prime_lim

lemma test_is_sep_closure (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [IsAlgClosed k'] :
    IsSepClosure k (separableClosure k k') := by
  try infer_instance



lemma purely_insep_exists_pow_zero (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [Algebra.IsAlgebraic k k'] (c : k') [CharZero k] :
    IsSeparable k c := by
  apply (minpoly.irreducible (Algebra.IsIntegral.isIntegral c)).separable

lemma purely_insep_pow_add_expChar (k R k' : Type*)
    [Field k] [CommRing R] [Algebra k R] [Field k'] [Algebra k k'] (x y : R ⊗[k] k')
    (p m : ℕ) [ExpChar k p] :
    (x + y) ^ (p ^ m) = x ^ (p ^ m) + y ^ (p ^ m) := by
  cases (by assumption)
  · norm_num
  cases CharP.exists k'
  simp_all only [CharP.eq k' (by valid) ( charP_of_injective_algebraMap (algebraMap k k').injective _),Fact.mk, add_pow_char_pow]
  refine m.rec (by simp_all) fun and h=>pow_mul (x +y) (p ^ _) p▸pow_mul x (p ^ _) p▸pow_mul y (p ^ _) p▸h▸by_contra (absurd (Fact.mk ‹p.Prime›) fun and=>. (?_))
  convert add_pow_char ..
  · congr
  cases@subsingleton_or_nontrivial R with| inl=>rcases‹¬_› (by·subsingleton) | inr=>_
  apply charP_of_injective_algebraMap (algebraMap k _).injective

lemma test_is_purely_insep (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [Algebra.IsAlgebraic k k'] :
    IsPurelyInseparable (separableClosure k k') k' := by
  focus infer_instance

lemma purely_insep_exists_pow_expChar (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [Algebra.IsAlgebraic k k'] (c : k') (p : ℕ) [ExpChar k p] :
    ∃ m : ℕ, c ^ (p ^ m) ∈ separableClosure k k' := by
  have h_insep := test_is_purely_insep k k'
  simp_rw [isPurelyInseparable_iff_pow_mem ↑(separableClosure k k') p] at*
  exact ⟨ _,(h_insep c).choose_spec.elim fun and true => true.subst and.2⟩

lemma tfae_3_to_4_pow_zero (k R k' : Type*)
    [Field k] [CommRing R] [Algebra k R] [Field k'] [Algebra k k'] [Algebra.IsAlgebraic k k'] (p : ℕ) [ExpChar k p] :
    let K := separableClosure k k'
    let f := (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k K k')).toRingHom
    ∃ m : ℕ, (0 : R ⊗[k] k') ^ (p ^ m) ∈ Set.range f := by
  use 0
  have h_eq : (0 : R ⊗[k] k') ^ (p ^ 0) = 0 := by
    rw [pow_zero, pow_one]
  rw [h_eq]
  exact ⟨0, map_zero _⟩

lemma tfae_3_to_4_pow_tmul (k R k' : Type*)
    [Field k] [CommRing R] [Algebra k R] [Field k'] [Algebra k k'] [Algebra.IsAlgebraic k k'] (r : R) (c : k') (p : ℕ) [ExpChar k p] :
    let K := separableClosure k k'
    let f := (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k K k')).toRingHom
    ∃ m : ℕ, (r ⊗ₜ[k] c) ^ (p ^ m) ∈ Set.range f := by
  have hc := purely_insep_exists_pow_expChar k k' c p
  rcases hc with ⟨m, hm⟩
  use m
  use (r ^ (p ^ m)) ⊗ₜ[k] ⟨c ^ (p ^ m), hm⟩
  norm_num

lemma tfae_3_to_4_pow_add (k R k' : Type*)
    [Field k] [CommRing R] [Algebra k R] [Field k'] [Algebra k k'] [Algebra.IsAlgebraic k k'] (x y : R ⊗[k] k') (p : ℕ) [ExpChar k p]
    (hx : let K := separableClosure k k'
          let f := (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k K k')).toRingHom
          ∃ m : ℕ, x ^ (p ^ m) ∈ Set.range f)
    (hy : let K := separableClosure k k'
          let f := (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k K k')).toRingHom
          ∃ m : ℕ, y ^ (p ^ m) ∈ Set.range f) :
    let K := separableClosure k k'
    let f := (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k K k')).toRingHom
    ∃ m : ℕ, (x + y) ^ (p ^ m) ∈ Set.range f := by
  push_cast only [Set.mem_range, add_pow_expChar_pow]at *
  refine hy.elim fun and ⟨a, _⟩=>hx.elim fun x⟨b, _⟩=>⟨x⊔and,?_⟩
  replace:∃y,(Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k (separableClosure k k') k')).toRingHom y=by bound^p^max x and
  · exact (le_max_left x and).rec (by valid) fun and⟨A, B⟩=>⟨ _,.trans (map_pow _ _ _) (B▸pow_mul _ _ _).symm⟩
  replace hy : ∃ A, (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k ↑(separableClosure k k') k')).toRingHom A=y ^ p ^max x and
  · exact and.add_sub_of_le ↑(le_max_right x _)▸pow_add p _ _▸pow_mul y _ _▸‹_=y^_›▸⟨ _,map_pow _ _ _⟩
  cases‹ExpChar _ _›
  · use b+a,by simp_all
  cases CharP.exists (R ⊗[k]k')
  obtain ⟨rfl⟩ :=eq_or_ne (by valid) p
  · match Fact.mk @‹Nat.Prime _› with | S =>exact hy.elim.comp this.elim fun and h K V =>⟨and+ K,by zify[ *, map_add, add_pow_char_pow]⟩
  cases subsingleton_or_nontrivial R
  · use@a,by subsingleton
  replace:CharP (R ⊗[k]k') p
  · apply charP_of_injective_algebraMap (algebraMap k _).injective
  · rcases‹¬_› (CharP.eq ↑_ (by valid) this)

lemma tfae_3_to_4_pow_expChar (k R k' : Type*)
    [Field k] [CommRing R] [Algebra k R] [Field k'] [Algebra k k'] [Algebra.IsAlgebraic k k'] (p : ℕ) [ExpChar k p] :
    let K := separableClosure k k'
    let f := (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k K k')).toRingHom
    ∀ x : R ⊗[k] k', ∃ m : ℕ, x ^ (p ^ m) ∈ Set.range f := by
  intro K f x
  induction x using TensorProduct.induction_on with
  | zero => exact tfae_3_to_4_pow_zero k R k' p
  | tmul r c => exact tfae_3_to_4_pow_tmul k R k' r c p
  | add x y hx hy => exact tfae_3_to_4_pow_add k R k' x y p hx hy

lemma tfae_3_to_4_pow (k R k' : Type*)
    [Field k] [CommRing R] [Algebra k R] [Field k'] [Algebra k k'] [Algebra.IsAlgebraic k k'] :
    let K := separableClosure k k'
    let f := (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k K k')).toRingHom
    ∀ x : R ⊗[k] k', ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f := by
  intro K f x
  let p := ringExpChar k
  have h := tfae_3_to_4_pow_expChar k R k' p x
  rcases h with ⟨m, hm⟩
  use p ^ m
  constructor
  · bound[expChar_pos k]
  · exact hm

lemma ideal_map_nilpotent {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (I : Ideal R)
    (h_nil : ∀ x ∈ I, IsNilpotent x) (y : S) (hy : y ∈ Ideal.map f I) :
    IsNilpotent y := by
  cases Submodule.mem_span_image_iff_exists_fun S|>.1 hy
  exact (by valid:).elim fun and⟨A, B⟩=>B▸isNilpotent_sum fun a s=>Commute.isNilpotent_mul_left (.all _ _) ((h_nil a (and a.2)).map _)

lemma ker_quotient_tensor {K A L : Type*} [Field K] [CommRing A] [Algebra K A] [CommRing L] [Algebra K L] (I : Ideal A) :
    RingHom.ker (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K I) (AlgHom.id K L)).toRingHom = Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] L).toRingHom I := by
  let f_alg := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K I) (AlgHom.id K L)
  let f := f_alg.toRingHom
  let iL := (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] L).toRingHom
  let J := Ideal.map iL I
  apply le_antisymm
  · intro x hx
    let pi_alg : A ⊗[K] L →ₐ[K] (A ⊗[K] L) ⧸ J := Ideal.Quotient.mkₐ K J
    let gA : A ⧸ I →ₐ[K] (A ⊗[K] L) ⧸ J := Ideal.Quotient.liftₐ I (pi_alg.comp (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] L)) (by
      intro a ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem iL ha)
    )
    let gL : L →ₐ[K] (A ⊗[K] L) ⧸ J := pi_alg.comp (Algebra.TensorProduct.includeRight : L →ₐ[K] A ⊗[K] L)
    have h_comm : ∀ x y, gA x * gL y = gL y * gA x := fun x y => mul_comm (gA x) (gL y)
    let g := Algebra.TensorProduct.lift gA gL h_comm
    have h_gf : g.comp f_alg = pi_alg := by
      apply Algebra.TensorProduct.ext
      · ext a
        simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply]
        change g (f_alg (a ⊗ₜ[K] (1 : L))) = pi_alg (a ⊗ₜ[K] (1 : L))
        rw [Algebra.TensorProduct.map_tmul, map_one]
        change g (((Ideal.Quotient.mkₐ K I) a) ⊗ₜ[K] (1 : L)) = pi_alg (a ⊗ₜ[K] (1 : L))
        rw [Algebra.TensorProduct.lift_tmul]
        change gA ((Ideal.Quotient.mkₐ K I) a) * gL 1 = pi_alg (a ⊗ₜ[K] (1 : L))
        rw [map_one, mul_one]
        rfl
      · ext l
        simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply, AlgHom.restrictScalars_apply]
        change g (f_alg ((1 : A) ⊗ₜ[K] l)) = pi_alg ((1 : A) ⊗ₜ[K] l)
        rw [Algebra.TensorProduct.map_tmul, map_one]
        change g ((1 : A ⧸ I) ⊗ₜ[K] l) = pi_alg ((1 : A) ⊗ₜ[K] l)
        rw [Algebra.TensorProduct.lift_tmul]
        change gA 1 * gL l = pi_alg ((1 : A) ⊗ₜ[K] l)
        rw [map_one, one_mul]
        rfl
    have h_gf_x : g (f x) = pi_alg x := by
      have hz : g (f x) = (g.comp f_alg) x := rfl
      rw [hz, h_gf]
    have h_f_zero : f x = 0 := hx
    have h_pi_zero : pi_alg x = 0 := by
      rw [← h_gf_x, h_f_zero, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h_pi_zero
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    have h1 : f (iL y) = (Ideal.Quotient.mkₐ K I) y ⊗ₜ[K] (1 : L) := rfl
    have h2 : (Ideal.Quotient.mkₐ K I) y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
    rw [Ideal.mem_comap, RingHom.mem_ker, h1, h2, TensorProduct.zero_tmul]

lemma tensorProduct_injective_of_field {K A B L : Type*} [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] [CommRing L] [Algebra K L]
    (f : A →ₐ[K] B) (h_inj : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map f (AlgHom.id K L)) := by
  apply (Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap (by assumption))



lemma isSepClosure_self (K : Type*) [Field K] [IsAlgClosed K] : IsSepClosure K K := by
  constructor
  · infer_instance
  · infer_instance

lemma quotient_max_ideal_equiv_K (K S : Type*) [Field K] [IsAlgClosed K] [CommRing S] [Algebra K S] [Algebra.FiniteType K S]
    (m : Ideal S) [Ideal.IsMaximal m] : Nonempty ((S ⧸ m) ≃ₐ[K] K) := by
  let:=Ideal.Quotient.maximal_ideal_iff_isField_quotient m
  let' :=(this.1 (by assumption)).toField
  replace B:FiniteDimensional K (S⧸m)
  · apply Module.finite_of_isArtinianRing
  · exact ⟨.symm ((AlgEquiv.ofBijective (Algebra.ofId _ _) ⟨ RingHom.injective _, fun and=> (minpoly.degree_eq_one_iff.1) (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible (.of_finite _ _)))⟩))⟩

lemma ideal_jacobson_bot_of_finiteType_field (K S : Type*) [Field K] [IsAlgClosed K] [CommRing S] [IsDomain S] [Algebra K S] [Algebra.FiniteType K S] :
    Ideal.jacobson (⊥ : Ideal S) = ⊥ := by
  haveI h : IsJacobsonRing S := @isJacobsonRing_of_finiteType K S _ _ _ _ _
  rcases ↑h
  apply_rules[Ideal.isRadical_bot]

lemma quotient_tensor_domain (K A L : Type*) [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [Field L] [Algebra K L] (m : Ideal A) [Ideal.IsMaximal m] :
    IsDomain ((A ⧸ m) ⊗[K] L) := by
  have ⟨e⟩ := quotient_max_ideal_equiv_K K A m
  let f_alg := Algebra.TensorProduct.congr e (AlgEquiv.refl : L ≃ₐ[K] L)
  let g_alg := Algebra.TensorProduct.lid K L
  let e_ring : ((A ⧸ m) ⊗[K] L) ≃+* L := (f_alg.trans g_alg).toRingEquiv
  haveI : Nontrivial ((A ⧸ m) ⊗[K] L) := {
    exists_pair_ne := by
      use e_ring.symm 0, e_ring.symm 1
      intro h
      have h1 : e_ring (e_ring.symm 0) = e_ring (e_ring.symm 1) := by rw [h]
      rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at h1
      exact zero_ne_one h1
  }
  haveI : NoZeroDivisors ((A ⧸ m) ⊗[K] L) := {
    eq_zero_or_eq_zero_of_mul_eq_zero := by
      intro x y hxy
      have h_eval : e_ring (x * y) = e_ring 0 := by rw [hxy]
      rw [map_mul, map_zero] at h_eval
      cases mul_eq_zero.mp h_eval with
      | inl hx => left; exact (EquivLike.injective e_ring) (hx.trans (map_zero _).symm)
      | inr hy => right; exact (EquivLike.injective e_ring) (hy.trans (map_zero _).symm)
  }
  exact ⟨⟩

lemma ideal_prod_zero_of_max {A ι : Type*} [CommRing A] [IsDomain A]
    (h_jacobson : Ideal.jacobson (⊥ : Ideal A) = ⊥)
    (sx sy : Finset ι) (ax ay : ι → A)
    (h_max : ∀ m : Ideal A, m.IsMaximal → (∀ a ∈ sx, ax a ∈ m) ∨ (∀ b ∈ sy, ay b ∈ m)) :
    (∀ a ∈ sx, ax a = 0) ∨ (∀ b ∈ sy, ay b = 0) := by
  simp_rw [Ideal.jacobson,Ideal.ext_iff,Ideal.mem_sInf]at*
  use or_iff_not_imp_left.2 fun and K V=>by_contra (and ∘ fun and R L=>(mul_eq_zero.mp.comp (h_jacobson _).mp fun and (N) =>by cases h_max and N.2 with push_cast[*, and.mul_mem_right, and.mul_mem_left]).resolve_right and)

lemma tensor_eq_sum_finite {K A L : Type*} [Field K] [CommRing A] [Algebra K A] [Field L] [Algebra K L] (x : A ⊗[K] L) :
    ∃ (s : Finset L) (a : L → A), x = ∑ e ∈ s, a e ⊗ₜ[K] e := by
  refine x.induction_on ⟨∅, 1,rfl⟩ (fun a s=>⟨{s}, fun and=>a,by simp_all⟩) fun and x ⟨a, A, _⟩=>?_
  classical use fun⟨R, S, _⟩=> ⟨a∪ R,fun M=>ite (M ∈a) (A M) 0+ite (M ∈R) (S M) 0,by simp_all[TensorProduct.add_tmul, Finset.sum_union_eq_left, Finset.sum_union_eq_right, Finset.sum_add_distrib]⟩





lemma test_basis_again (K L : Type*) [Field K] [Field L] [Algebra K L] (s : Finset L) :
    ∃ (s' : Finset L), (s' ⊆ s) ∧ LinearIndependent K (fun e : s' => (e : L)) ∧ Submodule.span K (s' : Set L) = Submodule.span K (s : Set L) := by
  apply↑(exists_linearIndependent K (s).toSet).elim
  use fun and h=> (s.finite_toSet.subset h.1).exists_finset_coe.imp (by bound)

lemma tensor_eq_sum_indep_of_span {K A L : Type*} [Field K] [CommRing A] [Algebra K A] [Field L] [Algebra K L]
    (s s' : Finset L) (a : L → A) (h_span : Submodule.span K (s : Set L) ≤ Submodule.span K (s' : Set L)) :
    ∃ a' : L → A, ∑ e ∈ s, a e ⊗ₜ[K] e = ∑ e ∈ s', a' e ⊗ₜ[K] e := by
  push_cast [ Submodule.span_le, Submodule.mem_span_finset] at h_span h_span
  replace h_span : ∀ (x), x ∈s →∃S:L →A,a x ⊗ₜ[K]x =∑ a ∈s',S a ⊗ₜ[K]a:= fun and(a)=>Submodule.mem_span_finset.1 (h_span a) |>.elim fun and f=>?_
  · choose! I R using‹_›
    refine ⟨ _, (s.sum_congr rfl R).trans (s.sum_comm.trans (s'.sum_congr rfl fun and x =>by rw [TensorProduct.sum_tmul]))⟩
  · exact ⟨ _,(f.2▸TensorProduct.tmul_sum _ _ _).trans (s'.sum_congr rfl fun and x =>(TensorProduct.smul_tmul _ _ _).symm)⟩

lemma tensor_eq_sum_indep {K A L : Type*} [Field K] [CommRing A] [Algebra K A] [Field L] [Algebra K L] (x : A ⊗[K] L) :
    ∃ (s : Finset L) (a : L → A), (LinearIndependent K (fun e : s => (e : L))) ∧ x = ∑ e ∈ s, a e ⊗ₜ[K] e := by
  obtain ⟨s, a, hx⟩ := tensor_eq_sum_finite x
  obtain ⟨s', hs'sub, h_ind, h_span⟩ := test_basis_again K L s
  have h_le : Submodule.span K (s : Set L) ≤ Submodule.span K (s' : Set L) := by rw [h_span]
  obtain ⟨a', ha'⟩ := tensor_eq_sum_indep_of_span s s' a h_le
  use s'
  use a'
  constructor
  · exact h_ind
  · rw [hx, ha']

lemma sum_tensor_in_ker_iff {K A L ι : Type*} [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [Field L] [Algebra K L]
    (m : Ideal A) [Ideal.IsMaximal m]
    (s : Finset ι) (a : ι → A) (e : ι → L) (h_ind : LinearIndependent K (fun i : s => e i)) :
    (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K m) (AlgHom.id K L)).toRingHom (∑ i ∈ s, a i ⊗ₜ[K] e i) = 0 ↔
    ∀ i ∈ s, a i ∈ m := by
  norm_num [←Ideal.Quotient.eq_zero_iff_mem,←s.sum_attach]
  have:=Module.Free.chooseBasis K<|A⧸m
  simp_rw [this.tensorProduct (Module.Free.chooseBasis _ _)|>.ext_elem_iff]
  norm_num[this.tensorProduct (Module.Free.chooseBasis _ _)|>.1.map_zero]
  use fun and A B=>this.ext_elem fun and' =>by_contra (absurd (Fintype.linearIndependent_iff.1 h_ind fun and=>this.1 (Ideal.Quotient.mk _ (a and)) and') ∘? _), (by norm_num[.])
  exact (mt (by norm_num[. ( (Module.Free.chooseBasis K L).ext_elem (by norm_num[mul_comm (this.repr _ _ ), and])) ⟨A, B⟩]))

lemma sum_tensor_eq_zero_of_coeff_zero {K A L ι : Type*} [Field K] [CommRing A] [Algebra K A] [Field L] [Algebra K L]
    (s : Finset ι) (a : ι → A) (e : ι → L) (h : ∀ i ∈ s, a i = 0) :
    ∑ i ∈ s, a i ⊗ₜ[K] e i = 0 := by
  have H : ∀ i ∈ s, a i ⊗ₜ[K] e i = 0 := by
    intro i hi
    rw [h i hi, TensorProduct.zero_tmul]
  exact Finset.sum_eq_zero H

lemma isDomain_tensorProduct_of_fg_domain {K S L : Type*} [Field K] [IsAlgClosed K]
  [CommRing S] [IsDomain S] [Algebra K S] [Algebra.FiniteType K S] [Field L] [Algebra K L] :
  IsDomain (S ⊗[K] L) := by
  haveI : Nontrivial (S ⊗[K] L) := inferInstance
  haveI h_nzd : NoZeroDivisors (S ⊗[K] L) := by
    constructor
    intro x y hxy
    obtain ⟨sx, ax, hx_ind, hx_eq⟩ := tensor_eq_sum_indep x
    obtain ⟨sy, ay, hy_ind, hy_eq⟩ := tensor_eq_sum_indep y
    have h_max : ∀ m : Ideal S, m.IsMaximal → (∀ e ∈ sx, ax e ∈ m) ∨ (∀ f ∈ sy, ay f ∈ m) := by
      intro m hm
      haveI : m.IsMaximal := hm
      let f := (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K m) (AlgHom.id K L)).toRingHom
      have h_dom := quotient_tensor_domain K S L m
      have h_fxy : f x * f y = 0 := by rw [← map_mul, hxy, map_zero]
      cases mul_eq_zero.mp h_fxy with
      | inl hx0 =>
        left
        have hx0' : f (∑ e ∈ sx, ax e ⊗ₜ[K] (e : L)) = 0 := by rwa [← hx_eq]
        exact (sum_tensor_in_ker_iff m sx ax (fun e => (e : L)) hx_ind).mp hx0'
      | inr hy0 =>
        right
        have hy0' : f (∑ f ∈ sy, ay f ⊗ₜ[K] (f : L)) = 0 := by rwa [← hy_eq]
        exact (sum_tensor_in_ker_iff m sy ay (fun f => (f : L)) hy_ind).mp hy0'
    have h_jac := ideal_jacobson_bot_of_finiteType_field K S
    cases ideal_prod_zero_of_max h_jac sx sy ax ay h_max with
    | inl hx_zero =>
      left
      rw [hx_eq]
      exact sum_tensor_eq_zero_of_coeff_zero sx ax (fun e => (e : L)) hx_zero
    | inr hy_zero =>
      right
      rw [hy_eq]
      exact sum_tensor_eq_zero_of_coeff_zero sy ay (fun f => (f : L)) hy_zero
  exact ⟨⟩








def InSubalgebra {K F L : Type*} [Field K] [CommRing F] [Algebra K F] [CommRing L] [Algebra K L] (A : Subalgebra K F) (x : F ⊗[K] L) : Prop :=
  x ∈ LinearMap.range (Algebra.TensorProduct.map A.val (AlgHom.id K L)).toLinearMap

lemma inSubalgebra_mono {K F L : Type*} [Field K] [CommRing F] [Algebra K F] [CommRing L] [Algebra K L]
    (A B : Subalgebra K F) (hAB : A ≤ B) (x : F ⊗[K] L) (hx : InSubalgebra A x) :
    InSubalgebra B x := by
  obtain ⟨x', hx'⟩ := hx
  use Algebra.TensorProduct.map (Subalgebra.inclusion hAB) (AlgHom.id K L) x'
  rw [← hx']
  have h_comp : (Algebra.TensorProduct.map B.val (AlgHom.id K L)).comp (Algebra.TensorProduct.map (Subalgebra.inclusion hAB) (AlgHom.id K L)) = Algebra.TensorProduct.map A.val (AlgHom.id K L) := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext; intro a; rfl
    · apply AlgHom.ext; intro l; rfl
  have hz : (Algebra.TensorProduct.map B.val (AlgHom.id K L)).toLinearMap.comp (Algebra.TensorProduct.map (Subalgebra.inclusion hAB) (AlgHom.id K L)).toLinearMap = (Algebra.TensorProduct.map A.val (AlgHom.id K L)).toLinearMap := by
    exact congrArg AlgHom.toLinearMap h_comp
  have hw := LinearMap.congr_fun hz x'
  exact hw

lemma isDomain_of_subalgebra {K F : Type*} [Field K] [Field F] [Algebra K F] (A : Subalgebra K F) : IsDomain A :=
  Subalgebra.isDomain A

open Classical in
lemma exists_subalgebra_of_tensor {K F L : Type*} [Field K] [CommRing F] [Algebra K F] [CommRing L] [Algebra K L] (x : F ⊗[K] L) :
    ∃ (s : Finset F), InSubalgebra (Algebra.adjoin K (s : Set F)) x := by
  induction x using TensorProduct.induction_on with
  | zero =>
    use ∅
    exact ⟨0, map_zero _⟩
  | tmul a l =>
    use {a}
    have ha : a ∈ Algebra.adjoin K (({a} : Finset F) : Set F) := Algebra.subset_adjoin (by simp)
    let a' : Algebra.adjoin K (({a} : Finset F) : Set F) := ⟨a, ha⟩
    use a' ⊗ₜ[K] l
    rfl
  | add x y hx hy =>
    obtain ⟨sx, hx_sub⟩ := hx
    obtain ⟨sy, hy_sub⟩ := hy
    use sx ∪ sy
    have h_le_x : Algebra.adjoin K (sx : Set F) ≤ Algebra.adjoin K ((sx ∪ sy : Finset F) : Set F) := by
      rw [Finset.coe_union]
      exact Algebra.adjoin_mono Set.subset_union_left
    have h_le_y : Algebra.adjoin K (sy : Set F) ≤ Algebra.adjoin K ((sx ∪ sy : Finset F) : Set F) := by
      rw [Finset.coe_union]
      exact Algebra.adjoin_mono Set.subset_union_right
    have hx_new := inSubalgebra_mono _ _ h_le_x x hx_sub
    have hy_new := inSubalgebra_mono _ _ h_le_y y hy_sub
    obtain ⟨x', hx'⟩ := hx_new
    obtain ⟨y', hy'⟩ := hy_new
    use x' + y'
    rw [map_add, hx', hy']

lemma finiteType_adjoin_finset {K F : Type*} [Field K] [CommRing F] [Algebra K F] (s : Finset F) : Algebra.FiniteType K (Algebra.adjoin K (s : Set F)) := by
  use(s).preimage _ Subtype.coe_injective.injOn
  norm_num[Subalgebra.ext_iff,Algebra.mem_adjoin_iff]

lemma isDomain_tensorProduct_of_isAlgClosed_field {K L F : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
    [Field F] [Algebra K F] : IsDomain (F ⊗[K] L) := by
  haveI h_no_zero_div : NoZeroDivisors (F ⊗[K] L) := by
    letI : DecidableEq F := Classical.decEq F
    constructor
    intro x y hxy
    have hx_sub := exists_subalgebra_of_tensor x
    have hy_sub := exists_subalgebra_of_tensor y
    obtain ⟨sx, hx_in⟩ := hx_sub
    obtain ⟨sy, hy_in⟩ := hy_sub
    let A := Algebra.adjoin K ((sx ∪ sy : Finset F) : Set F)
    have h_le_x : Algebra.adjoin K (sx : Set F) ≤ A := by
      apply Algebra.adjoin_mono
      intro z hz
      simp only [Finset.coe_union, Set.mem_union]
      left
      exact hz
    have h_le_y : Algebra.adjoin K (sy : Set F) ≤ A := by
      apply Algebra.adjoin_mono
      intro z hz
      simp only [Finset.coe_union, Set.mem_union]
      right
      exact hz
    have hx_A := inSubalgebra_mono _ _ h_le_x x hx_in
    have hy_A := inSubalgebra_mono _ _ h_le_y y hy_in
    obtain ⟨x', hx'⟩ := hx_A
    obtain ⟨y', hy'⟩ := hy_A
    haveI h_fin : Algebra.FiniteType K A := finiteType_adjoin_finset (sx ∪ sy)




    haveI : IsDomain A := isDomain_of_subalgebra A
    haveI : IsDomain (A ⊗[K] L) := isDomain_tensorProduct_of_fg_domain
    let f := (Algebra.TensorProduct.map A.val (AlgHom.id K L)).toRingHom
    have h_inj : Function.Injective f := tensorProduct_injective_of_field A.val Subtype.val_injective
    have hf_xy : f (x' * y') = 0 := by
      rw [map_mul]
      have h1 : f x' = x := hx'
      have h2 : f y' = y := hy'
      rw [h1, h2]
      exact hxy
    have h_xy_zero : x' * y' = 0 := by
      have hz : f 0 = 0 := map_zero f
      rw [← hz] at hf_xy
      exact h_inj hf_xy
    cases eq_zero_or_eq_zero_of_mul_eq_zero h_xy_zero with
    | inl hx0 =>
      left
      rw [← hx', hx0, map_zero]
    | inr hy0 =>
      right
      rw [← hy', hy0, map_zero]
  exact NoZeroDivisors.to_isDomain (F ⊗[K] L)


















lemma alg_closed_alg_ext_equiv_self (K k' : Type*) [Field K] [IsAlgClosed K] [Field k'] [Algebra K k'] [Algebra.IsAlgebraic K k'] : Nonempty (k' ≃ₐ[K] K) := by
  exact ⟨.symm ↑(AlgEquiv.ofBijective (Algebra.ofId _ _) (by use RingHom.injective _, fun and=> (minpoly.degree_eq_one_iff.1 (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible (Algebra.IsIntegral.isIntegral and))))))⟩

lemma isDomain_of_injective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (h_inj : Function.Injective f) [IsDomain B] : IsDomain A := by
  haveI h_nontrivial : Nontrivial A := by
    constructor
    use 1, 0
    intro h
    have h1 : f 1 = f 0 := by rw [h]
    have h_bot : (1 : B) = 0 := by
      calc (1 : B) = f 1 := (map_one f).symm
           _ = f 0 := h1
           _ = 0 := map_zero f
    exact zero_ne_one h_bot.symm
  haveI h_no_zero_divisors : NoZeroDivisors A := by
    constructor
    intro a b hab
    have h_f : f (a * b) = f 0 := by rw [hab, map_zero]
    rw [map_mul, map_zero] at h_f
    cases eq_zero_or_eq_zero_of_mul_eq_zero h_f with
    | inl ha => left; exact h_inj (ha.trans (map_zero f).symm)
    | inr hb => right; exact h_inj (hb.trans (map_zero f).symm)
  exact ⟨⟩

lemma isDomain_tensorProduct_of_isAlgClosed {K L A : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [IsDomain A] : IsDomain (A ⊗[K] L) := by
  let F := FractionRing A
  let f : A ⊗[K] L →ₐ[K] F ⊗[K] L := Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A F) (AlgHom.id K L)
  have h_inj : Function.Injective f := tensorProduct_injective_of_field _ (IsFractionRing.injective A F)
  haveI : IsDomain (F ⊗[K] L) := isDomain_tensorProduct_of_isAlgClosed_field
  exact isDomain_of_injective f.toRingHom h_inj

lemma ker_Phi_nil {K F L A : Type*} [Field K] [CommRing A] [Algebra K A] [Field F] [Algebra K F] [Field L] [Algebra K L]
    (psi : A →ₐ[K] F) (h_nil : ∀ x ∈ RingHom.ker psi.toRingHom, IsNilpotent x)
    (Phi : A ⊗[K] L →ₐ[K] F ⊗[K] L) (h_Phi : Phi = Algebra.TensorProduct.map psi (AlgHom.id K L)) :
    ∀ x ∈ RingHom.ker Phi.toRingHom, IsNilpotent x := by
  let I := RingHom.ker psi.toRingHom
  let A_red := A ⧸ I
  let mk := Ideal.Quotient.mkₐ K I
  let psi_bar : A_red →ₐ[K] F := Ideal.Quotient.liftₐ I psi (fun a ha => ha)
  have h_comp : psi = psi_bar.comp mk := by ext; rfl
  have h_inj : Function.Injective psi_bar := by
    intro a b hab
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    have h_eq : psi a' = psi b' := hab
    have h_sub : a' - b' ∈ I := by
      have h1 : psi a' - psi b' = 0 := by rw [h_eq, sub_self]
      have h2 : psi (a' - b') = 0 := by rw [map_sub, h1]
      exact h2
    exact Ideal.Quotient.eq.mpr h_sub
  let Phi_mk := Algebra.TensorProduct.map mk (AlgHom.id K L)
  let Phi_bar := Algebra.TensorProduct.map psi_bar (AlgHom.id K L)
  have h_Phi_comp : Phi = Phi_bar.comp Phi_mk := by
    rw [h_Phi, h_comp]
    apply Algebra.TensorProduct.ext
    · ext x
      rfl
    · ext x
      rfl
  have h_Phi_bar_inj : Function.Injective Phi_bar := tensorProduct_injective_of_field psi_bar h_inj
  intro x hx
  have hx_ker : x ∈ RingHom.ker Phi_mk.toRingHom := by
    have hx_Phi : Phi x = 0 := hx
    have hx_Phi_bar : Phi_bar (Phi_mk x) = 0 := by
      calc Phi_bar (Phi_mk x) = Phi x := by rw [h_Phi_comp]; rfl
           _ = 0 := hx_Phi
    have hz : Phi_bar 0 = 0 := map_zero _
    rw [← hz] at hx_Phi_bar
    exact h_Phi_bar_inj hx_Phi_bar
  have hx_map : x ∈ Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] L).toRingHom I := by
    rw [← ker_quotient_tensor I]
    exact hx_ker
  exact ideal_map_nilpotent _ I h_nil x hx_map

lemma isPrime_nilradical_of_ker {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (h_ker_nil : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    [IsDomain S] : (nilradical R).IsPrime := by
  have h_ker_prime : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have h_eq : nilradical R = RingHom.ker f := by
    apply le_antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := hx
      have h_pow : f (x ^ n) = 0 := by
        rw [Ideal.mem_bot.mp hn, map_zero]
      rw [map_pow] at h_pow
      have h_nil : IsNilpotent (f x) := ⟨n, h_pow⟩
      have h_zero : f x = 0 := IsNilpotent.eq_zero h_nil
      exact h_zero
    · exact h_ker_nil
  rw [h_eq]
  exact h_ker_prime

lemma isPrime_tensorProduct_of_isAlgClosed {K L A : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
    [CommRing A] [Algebra K A] (h_prime : (nilradical A).IsPrime) :
    (nilradical (A ⊗[K] L)).IsPrime := by
  let I := nilradical A
  let A_red := A ⧸ I
  haveI : IsDomain A_red := (Ideal.Quotient.isDomain_iff_prime I).mpr h_prime
  let F := FractionRing A_red
  let f : A →ₐ[K] A_red := Ideal.Quotient.mkₐ K I
  let g : A_red →ₐ[K] F := IsScalarTower.toAlgHom K A_red F
  let psi : A →ₐ[K] F := g.comp f
  let Phi_alg : A ⊗[K] L →ₐ[K] F ⊗[K] L := Algebra.TensorProduct.map psi (AlgHom.id K L)
  let Phi : A ⊗[K] L →+* F ⊗[K] L := Phi_alg.toRingHom
  have h_domain : IsDomain (F ⊗[K] L) := isDomain_tensorProduct_of_isAlgClosed
  have h_ker_nil : ∀ x ∈ RingHom.ker Phi, IsNilpotent x := by
    apply ker_Phi_nil psi _ Phi_alg rfl
    intro x hx
    have hx_eq : g (f x) = 0 := hx
    have h_f : f x = 0 := by
      have h_inj : Function.Injective (algebraMap A_red F) := IsFractionRing.injective A_red F
      have h_map_zero : (algebraMap A_red F) 0 = 0 := map_zero _
      have h_eq : (algebraMap A_red F) (f x) = (algebraMap A_red F) 0 := by
        rw [h_map_zero]
        exact hx_eq
      exact h_inj h_eq
    have h_mem : x ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp h_f
    exact h_mem
  exact isPrime_nilradical_of_ker Phi h_ker_nil

lemma integralClosure_inv_mem (k k' : Type*) [Field k] [Field k'] [Algebra k k'] (x : k') (hx : x ∈ integralClosure k k') :
    x⁻¹ ∈ integralClosure k k' := by apply IsIntegral.inv ↑hx

noncomputable def integralClosure_to_IntermediateField (k k' : Type*) [Field k] [Field k'] [Algebra k k'] :
    IntermediateField k k' :=
  { toSubalgebra := integralClosure k k',
    inv_mem' := fun x hx => integralClosure_inv_mem k k' x hx }

lemma isAlgClosed_IntermediateField (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [IsAlgClosed k'] :
    IsAlgClosed (integralClosure_to_IntermediateField k k') := by
  try apply IsAlgClosed.of_exists_root
  use fun and A B=>(IsAlgClosed.exists_root (and.map (algebraMap (integralClosure_to_IntermediateField k k') k')) (by norm_num[degree_pos_of_irreducible B|>.ne'])).elim fun and j=>?_
  by_cases h:IsIntegral k and
  · use⟨ _,h⟩,Subtype.eq (j▸eval_map _ _|>.trans (by ·norm_num [eval₂_eq_sum_range,eval_eq_sum_range])).symm
  convert h.elim (isIntegral_trans (@ _) ⟨ _,A,(eval_map _ _).symm.trans j⟩)
  use fun and=>and.2.imp (by norm_num[eval₂_eq_sum_range,Subtype.eq_iff])

lemma isAlgebraic_IntermediateField (k k' : Type*) [Field k] [Field k'] [Algebra k k'] :
    Algebra.IsAlgebraic k (integralClosure_to_IntermediateField k k') := by
  constructor
  intro x
  have h_int : IsIntegral k (x : k') := x.property
  obtain ⟨p, hp_monic, hp_root⟩ := h_int
  use p
  constructor
  · exact hp_monic.ne_zero
  · apply Subtype.ext
    have hz : (Polynomial.aeval (x : k')) p = 0 := hp_root
    -- (aeval x) p = 0
    -- The map A → B respects aeval
    simp_all[aeval_eq_sum_range,funext_iff]

lemma isPrime_nilradical_of_injective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) (hB : (nilradical B).IsPrime) :
    (nilradical A).IsPrime := by
  constructor
  · intro h
    have h1 : (1 : A) ∈ nilradical A := by rw [h]; exact Submodule.mem_top
    obtain ⟨n, hn⟩ := h1
    have h1_eq : (1 : A) = 0 := by
      have hz : (1 : A) ^ n = 1 := one_pow n
      rw [hz] at hn
      exact Ideal.mem_bot.mp hn
    have hB_1 : (1 : B) = 0 := by
      calc (1 : B) = f 1 := (map_one f).symm
           _ = f 0 := by rw [h1_eq]
           _ = 0 := map_zero f
    have hB_top : nilradical B = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      rw [hB_1]
      exact Ideal.zero_mem _
    exact hB.ne_top hB_top
  · intro x y hxy
    obtain ⟨n, hn⟩ := hxy
    have hn_eq : (x * y) ^ n = 0 := Ideal.mem_bot.mp hn
    have h_f : f ((x * y) ^ n) = 0 := by rw [hn_eq, map_zero]
    rw [map_pow, map_mul] at h_f
    have h_f_nilp : f x * f y ∈ nilradical B := ⟨n, Ideal.mem_bot.mpr h_f⟩
    cases hB.mem_or_mem h_f_nilp with
    | inl hx =>
      obtain ⟨m, hm⟩ := hx
      left
      use m
      have hm_eq : (f x) ^ m = 0 := Ideal.mem_bot.mp hm
      have h_fx : f (x ^ m) = 0 := by rw [map_pow, hm_eq]
      exact Ideal.mem_bot.mpr (hf (h_fx.trans (map_zero f).symm))
    | inr hy =>
      obtain ⟨m, hm⟩ := hy
      right
      use m
      have hm_eq : (f y) ^ m = 0 := Ideal.mem_bot.mp hm
      have h_fy : f (y ^ m) = 0 := by rw [map_pow, hm_eq]
      exact Ideal.mem_bot.mpr (hf (h_fy.trans (map_zero f).symm))

lemma isPrime_nilradical_equiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (hA : (nilradical A).IsPrime) :
    (nilradical B).IsPrime :=
  isPrime_nilradical_of_injective e.symm.toRingHom (EquivLike.injective e.symm) hA

noncomputable def tensor_baseChange_map (k R K L : Type*)
    [Field k] [CommRing R] [Algebra k R] [Field K] [Algebra k K]
    [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra K (R ⊗[k] K)] [IsScalarTower k K (R ⊗[k] K)] :
    R ⊗[k] L →+* ((R ⊗[k] K) ⊗[K] L) :=
  let A := (R ⊗[k] K) ⊗[K] L
  let i_RK : R →ₐ[k] R ⊗[k] K := Algebra.TensorProduct.includeLeft
  let i_A : R ⊗[k] K →ₐ[K] A := Algebra.TensorProduct.includeLeft
  let fR : R →ₐ[k] A := (i_A.restrictScalars k).comp i_RK
  let fL : L →ₐ[k] A := (Algebra.TensorProduct.includeRight : L →ₐ[K] A).restrictScalars k
  have h_comm : ∀ x y, fR x * fL y = fL y * fR x := fun x y => mul_comm (fR x) (fL y)
  (Algebra.TensorProduct.lift fR fL h_comm).toRingHom

lemma tensor_baseChange_inj (k R K L : Type*)
    [Field k] [CommRing R] [Algebra k R] [Field K] [Algebra k K]
    [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra K (R ⊗[k] K)] [IsScalarTower k K (R ⊗[k] K)]
    (halg : ∀ c, algebraMap K (R ⊗[k] K) c = (1 : R) ⊗ₜ[k] c) :
    Function.Injective (tensor_baseChange_map k R K L) := by
  let f := tensor_baseChange_map k R K L
  let A := (R ⊗[k] K) ⊗[K] L
  let i_RK : R →ₐ[k] R ⊗[k] K := Algebra.TensorProduct.includeLeft
  let i_A : R ⊗[k] K →ₐ[K] A := Algebra.TensorProduct.includeLeft
  let fR : R →ₐ[k] A := (i_A.restrictScalars k).comp i_RK
  let fL : L →ₐ[k] A := (Algebra.TensorProduct.includeRight : L →ₐ[K] A).restrictScalars k
  have h_comm : ∀ x y, fR x * fL y = fL y * fR x := fun x y => mul_comm (fR x) (fL y)
  let f_alg : R ⊗[k] L →ₐ[k] A := Algebra.TensorProduct.lift fR fL h_comm
  letI algK : Algebra K (R ⊗[k] L) := ((Algebra.TensorProduct.includeRight : L →ₐ[k] R ⊗[k] L).comp (IsScalarTower.toAlgHom k K L)).toAlgebra
  let g1_k : R ⊗[k] K →ₐ[k] R ⊗[k] L := Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k K L)
  have h_g1_comm : ∀ c, g1_k (algebraMap K (R ⊗[k] K) c) = algebraMap K (R ⊗[k] L) c := by
    intro c
    have hA : algebraMap K (R ⊗[k] K) c = (1 : R) ⊗ₜ[k] c := halg c
    have hB : algebraMap K (R ⊗[k] L) c = (1 : R) ⊗ₜ[k] (algebraMap K L c) := rfl
    rw [hA, hB]
    change (1 : R) ⊗ₜ[k] (IsScalarTower.toAlgHom k K L c) = (1 : R) ⊗ₜ[k] (algebraMap K L c)
    simp only [IsScalarTower.toAlgHom_apply]
  let g1 : R ⊗[k] K →ₐ[K] R ⊗[k] L := { g1_k with commutes' := h_g1_comm }
  let g2_k : L →ₐ[k] R ⊗[k] L := Algebra.TensorProduct.includeRight
  have h_g2_comm : ∀ c, g2_k (algebraMap K L c) = algebraMap K (R ⊗[k] L) c := by
    intro c
    rfl
  let g2 : L →ₐ[K] R ⊗[k] L := { g2_k with commutes' := h_g2_comm }
  have h_comm_g : ∀ x y, g1 x * g2 y = g2 y * g1 x := by
    intro x y
    exact mul_comm (g1 x) (g2 y)
  let g_alg : (R ⊗[k] K) ⊗[K] L →ₐ[K] R ⊗[k] L := Algebra.TensorProduct.lift g1 g2 h_comm_g
  let g := g_alg.toRingHom
  have h_gf : ∀ x, g (f x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul r l =>
      change g (f_alg (r ⊗ₜ[k] l)) = r ⊗ₜ[k] l
      have h1 : f_alg (r ⊗ₜ[k] l) = fR r * fL l := rfl
      rw [h1, map_mul]
      have h3 : g (fR r) = r ⊗ₜ[k] (1 : L) := by
        change g_alg (fR r) = r ⊗ₜ[k] (1 : L)
        have h3a : fR r = (r ⊗ₜ[k] (1 : K)) ⊗ₜ[K] (1 : L) := rfl
        rw [h3a]
        have h3a_lift : g_alg ((r ⊗ₜ[k] (1 : K)) ⊗ₜ[K] (1 : L)) = g1 (r ⊗ₜ[k] (1 : K)) * g2 (1 : L) := rfl
        rw [h3a_lift]
        have h3b : g1 (r ⊗ₜ[k] (1 : K)) = r ⊗ₜ[k] (1 : L) := by
          change g1_k (r ⊗ₜ[k] (1 : K)) = r ⊗ₜ[k] (1 : L)
          simp only [g1_k, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
        have h3c : g2 (1 : L) = 1 := map_one g2
        rw [h3b, h3c, mul_one]
      have h4 : g (fL l) = (1 : R) ⊗ₜ[k] l := by
        change g_alg (fL l) = (1 : R) ⊗ₜ[k] l
        have h4a : fL l = (1 : R ⊗[k] K) ⊗ₜ[K] l := rfl
        rw [h4a]
        have h4a_lift : g_alg ((1 : R ⊗[k] K) ⊗ₜ[K] l) = g1 1 * g2 l := rfl
        rw [h4a_lift]
        have h4b : g1 1 = 1 := map_one g1
        have h4c : g2 l = (1 : R) ⊗ₜ[k] l := rfl
        rw [h4b, h4c, one_mul]
      rw [h3, h4]
      exact Algebra.TensorProduct.tmul_mul_tmul r 1 1 l |>.trans (by rw [mul_one, one_mul])
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact Function.LeftInverse.injective h_gf

lemma irreducibleSpace_baseChange_of_algClosed (k : Type u) (R : Type v) (K L : Type (max u v))
    [Field k] [CommRing R] [Algebra k R] [Field K] [Algebra k K] [IsAlgClosed K] [Algebra.IsAlgebraic k K]
    [Field L] [Algebra k L] [IsAlgClosed L] [Algebra K L] [IsScalarTower k K L]
    (h_K_irr : IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))) :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] L)) := by
  have h_prime := (test_nilradical_prime (R ⊗[k] K)).mp h_K_irr
  letI : Algebra K (R ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  have h_prime2 : (nilradical ((R ⊗[k] K) ⊗[K] L)).IsPrime :=
    @isPrime_tensorProduct_of_isAlgClosed K L (R ⊗[k] K) _ _ _ _ _ _ h_prime
  let f := tensor_baseChange_map k R K L
  have h_inj : Function.Injective f := tensor_baseChange_inj k R K L (fun c => rfl)
  have h_prime3 : (nilradical (R ⊗[k] L)).IsPrime :=
    @isPrime_nilradical_of_injective (R ⊗[k] L) ((R ⊗[k] K) ⊗[K] L) _ _ f h_inj h_prime2
  exact (test_nilradical_prime (R ⊗[k] L)).mpr h_prime3

lemma irreducibleSpace_baseChange_algClosed {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    (h_alg_closed : ∀ (K : Type (max u v)) [Field K] [Algebra k K] [IsAlgClosed K] [Algebra.IsAlgebraic k K], IrreducibleSpace (PrimeSpectrum (R ⊗[k] K)))
    (L : Type (max u v)) [Field L] [Algebra k L] [IsAlgClosed L] :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] L)) := by
  let K := integralClosure_to_IntermediateField k L
  haveI : IsAlgClosed K := isAlgClosed_IntermediateField k L
  haveI : Algebra.IsAlgebraic k K := isAlgebraic_IntermediateField k L
  have hK_irr := h_alg_closed K
  exact irreducibleSpace_baseChange_of_algClosed k R K L hK_irr

lemma tfae_3_to_1 (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    (h3 : ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [IsSepClosure k k'], IrreducibleSpace (PrimeSpectrum (R ⊗[k] k'))) :
    GeometricallyIrreducibleAlgebra k R := by
  have h_alg_closed : ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [IsAlgClosed k'] [Algebra.IsAlgebraic k k'], IrreducibleSpace (PrimeSpectrum (R ⊗[k] k')) := by
    intro k' _ _ _ _
    let K := separableClosure k k'
    haveI : IsSepClosure k K := test_is_sep_closure k k'
    have h_irr := h3 K
    have h_prime := (test_nilradical_prime (R ⊗[k] K)).mp h_irr
    let f := (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k K k')).toRingHom
    have h_inj : Function.Injective f := injective_tensor_extension k R K k'
    have h_pow := tfae_3_to_4_pow k R k'
    have h_prime_k' := isPrime_of_power f h_inj h_pow h_prime
    exact (test_nilradical_prime (R ⊗[k] k')).mpr h_prime_k'
  constructor
  intro k' hk' hk'_alg
  let L := AlgebraicClosure k'
  haveI : IsAlgClosed L := inferInstance
  have h_irr_L : IrreducibleSpace (PrimeSpectrum (R ⊗[k] L)) := irreducibleSpace_baseChange_algClosed h_alg_closed L
  have h_int : Algebra.IsIntegral k' L := (AlgebraicClosure.isAlgebraic k').isIntegral
  exact irreducible_of_isIntegral_surj k R k' L h_int h_irr_L

lemma isPrime_nilradical_localization {A : Type*} [CommRing A] (M : Submonoid A) (h_prime : (nilradical A).IsPrime) (h_disj : Disjoint (M : Set A) (nilradical A)) :
    (nilradical (Localization M)).IsPrime := by
  replace h_provej:nilradical (Localization M)=(nilradical A).map (algebraMap _ _)
  · use le_antisymm (IsLocalization.mk'_surjective M ·|>.elim fun and A B=>A▸?_) (Ideal.map_le_iff_le_comap.2 fun and=>.imp ↑(by simp_all [ ←map_pow]))
    norm_num[nilradical,←A,←IsLocalization.mk'_pow,IsLocalization.mk'_mem_map_algebraMap_iff,IsLocalization.mk'_eq_zero_iff] at B⊢
    norm_num[Ideal.mem_radical_iff,←IsLocalization.mk'_pow, mul_pow,IsLocalization.mk'_eq_zero_iff] at B⊢
    apply((IsLocalization.mk'_eq_zero_iff _ _).1 B.choose_spec).elim
    exact ( ⟨ _,·.2,B.choose+1,by linear_combination2.*_^_*and.1⟩)
  · apply and_self_iff.mp
    exact and_self_iff.mpr (by assumption▸IsLocalization.isPrime_of_isPrime_disjoint M _ _ (by assumption) (by bound))

lemma isPrime_nilradical_polynomial {A : Type*} [CommRing A] (h_prime : (nilradical A).IsPrime) :
    (nilradical A[X]).IsPrime := by
  let p := nilradical A
  haveI hp : p.IsPrime := h_prime
  let f := Polynomial.mapRingHom (Ideal.Quotient.mk p)
  have h_ker_prime : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have h_eq : RingHom.ker f = nilradical A[X] := by
    ext q
    constructor
    · intro hq
      have h_f : f q = 0 := hq
      have h_coeff : ∀ n, IsNilpotent (q.coeff n) := by
        intro n
        have h1 : (f q).coeff n = 0 := by rw [h_f, Polynomial.coeff_zero]
        have h2 : (Ideal.Quotient.mk p) (q.coeff n) = 0 := by
          have hz : (f q).coeff n = (Ideal.Quotient.mk p) (q.coeff n) := by
            exact Polynomial.coeff_map _ n
          rw [← hz, h1]
        exact Ideal.Quotient.eq_zero_iff_mem.mp h2
      have h_nilp : IsNilpotent q := Polynomial.isNilpotent_iff.mpr h_coeff
      exact h_nilp
    · intro hq
      have h_nilp : IsNilpotent q := hq
      have h_coeff : ∀ n, IsNilpotent (q.coeff n) := Polynomial.isNilpotent_iff.mp h_nilp
      have h_f_coeff : ∀ n, (f q).coeff n = 0 := by
        intro n
        have hz : (f q).coeff n = (Ideal.Quotient.mk p) (q.coeff n) := by
          exact Polynomial.coeff_map _ n
        rw [hz]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (h_coeff n)
      apply Polynomial.ext
      intro n
      rw [h_f_coeff n, Polynomial.coeff_zero]
  rw [← h_eq]
  exact h_ker_prime


-- EVOLVE-BLOCK-END

theorem geometrically_irreducible_tfae
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R] :
    List.TFAE [
      GeometricallyIrreducibleAlgebra k R,
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [Module.Finite k k']
        [Algebra.IsSeparable k k'], IrreducibleSpace (PrimeSpectrum (R ⊗[k] k')),
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [IsSepClosure k k'],
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] k')),
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [IsAlgClosed k'],
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] k'))
    ] := by
  -- EVOLVE-BLOCK-START
  tfae_have 1 → 2 := by
    intro h k' _ _ _ _
    exact h.out k'
  tfae_have 1 → 3 := by
    intro h k' _ _ _
    exact h.out k'
  tfae_have 1 → 4 := by
    intro h k' _ _ _
    exact h.out k'
  tfae_have 2 → 3 := by
    intro h k' _ _ _
    exact tfae_2_to_3 k R h k'
  tfae_have 4 → 1 := by
    intro h
    exact ⟨fun k' _ _ => irreducible_of_algebraic_closed_extension k R h k'⟩
  tfae_have 3 → 1 := by
    intro h
    exact tfae_3_to_1 k R h
  tfae_finish
  -- EVOLVE-BLOCK-END
