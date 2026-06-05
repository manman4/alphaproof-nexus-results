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
universe u_1 u_2

lemma isNilpotent_of_mem_ideal_gen_by_nilpotents {R : Type*} [CommRing R]
    (s : Set R) (hs : ∀ x ∈ s, IsNilpotent x) :
    ∀ x ∈ Ideal.span s, IsNilpotent x := by
  use fun and=>Submodule.span_induction hs .zero (by simp_all[Commute.isNilpotent_add (.all (_ : R) _)]) ((by simp_all[Commute.isNilpotent_mul_left (.all (_ : R) _)]))

lemma isPrime_nilradical_of_irreducibleSpace {A : Type*} [CommRing A] [IrreducibleSpace (PrimeSpectrum A)] :
    (nilradical A).IsPrime := by
  simp_rw [nilradical_eq_sInf,irreducibleSpace_def]at *
  simp_rw [Ideal.isPrime_iff,Ideal.mem_sInf,IsIrreducible] at *
  rw[IsPreirreducible]at*
  use (by valid:).elim fun and R M=>? _,or_iff_not_imp_left.2 ∘ fun and h K V=>by_contra (h ∘ fun and R L=>by_contra fun and=>? _)
  · use and.elim fun A B=>A.2.1 (eq_top_mono (sInf_le (by use A.2.1,A.2.2)) M)
  revert‹A›R K
  use@ fun and R L K V a s x =>(‹_∧∀ (x _ _ _ _ _),∃_, _›.2 {x : PrimeSpectrum A|by apply_rules ∉x.1} {x : PrimeSpectrum A|and ∉x.1} (?_) ?_ (?_) ? _).elim ?_
  · constructor
    exact (Set.ext fun and=>Set.singleton_subset_iff.trans not_not.symm)
  · exact ( PrimeSpectrum.isOpen_basicOpen).preimage (by(fun_prop) )
  · exists⟨a,Ideal.isPrime_iff.mpr @s⟩
  · exists⟨ L,Ideal.isPrime_iff.2 K⟩
  · use fun and true => true.2.elim (and.2.2 (R ⟨and.2.1, and.2.2⟩)).elim

lemma nil_of_base_change_surjective {K A A_red S : Type*} [Field K] [CommRing A] [CommRing A_red] [CommRing S]
    [Algebra K A] [Algebra K A_red] [Algebra K S]
    (pi : A →ₐ[K] A_red) (hpi_surj : Function.Surjective pi) (h_nil : ∀ x, pi x = 0 → IsNilpotent x) :
    ∀ x, (Algebra.TensorProduct.map (AlgHom.id K S) pi) x = 0 → IsNilpotent x := by
  intro x hx
  let I := RingHom.ker (pi : A →+* A_red)
  let pi_lin : A →ₗ[K] A_red := pi.toLinearMap
  have h_surj_lin : Function.Surjective pi_lin := hpi_surj
  obtain ⟨inv, h_inv⟩ := LinearMap.exists_rightInverse_of_surjective pi_lin (LinearMap.range_eq_top.mpr h_surj_lin)
  let P : A →ₗ[K] A := LinearMap.id - inv.comp pi_lin
  have hP_ker : ∀ a : A, pi (P a) = 0 := by
    intro a
    have h1 : pi_lin (P a) = pi_lin a - pi_lin (inv (pi_lin a)) := by
      change pi_lin (a - inv (pi_lin a)) = pi_lin a - pi_lin (inv (pi_lin a))
      rw [map_sub]
    have h2 : pi_lin (inv (pi_lin a)) = pi_lin a := by
      calc pi_lin (inv (pi_lin a)) = (pi_lin.comp inv) (pi_lin a) := rfl
      _ = LinearMap.id (pi_lin a) := by rw [h_inv]
      _ = pi_lin a := rfl
    rw [h2, sub_self] at h1
    exact h1
  let map_P := TensorProduct.map (LinearMap.id : S →ₗ[K] S) P
  have h_x_eq : x = map_P x := by
    have hx_pi : (TensorProduct.map (LinearMap.id : S →ₗ[K] S) pi_lin) x = 0 := hx
    have h_map_eq : map_P = (LinearMap.id : S ⊗[K] A →ₗ[K] S ⊗[K] A) - (TensorProduct.map (LinearMap.id : S →ₗ[K] S) inv).comp (TensorProduct.map (LinearMap.id : S →ₗ[K] S) pi_lin) := by
      apply TensorProduct.ext'
      intro s a
      simp only [map_P, P, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul]
      simp only [LinearMap.id_apply, LinearMap.sub_apply, LinearMap.comp_apply]
      rw [TensorProduct.tmul_sub]
    have h_eval : map_P x = x - (TensorProduct.map (LinearMap.id : S →ₗ[K] S) inv) ((TensorProduct.map (LinearMap.id : S →ₗ[K] S) pi_lin) x) := by
      rw [h_map_eq]
      simp
    rw [hx_pi] at h_eval
    simp at h_eval
    exact h_eval.symm
  have h_ker : x ∈ Ideal.span (Set.range (fun (a : I) => (Algebra.TensorProduct.includeRight : A →ₐ[K] S ⊗[K] A) a)) := by
    rw [h_x_eq]
    have h_im : ∀ y : S ⊗[K] A, map_P y ∈ Ideal.span (Set.range (fun (a : I) => (Algebra.TensorProduct.includeRight : A →ₐ[K] S ⊗[K] A) a)) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul s a =>
        have h_P_a : P a ∈ I := hP_ker a
        have h_eq : map_P (s ⊗ₜ[K] a) = (Algebra.TensorProduct.includeLeft : S →ₐ[K] S ⊗[K] A) s * (Algebra.TensorProduct.includeRight : A →ₐ[K] S ⊗[K] A) (P a) := by
          simp [map_P]
        rw [h_eq]
        apply Ideal.mul_mem_left
        apply Ideal.subset_span
        simp only [Set.mem_range]
        use ⟨P a, h_P_a⟩
      | add y1 y2 hy1 hy2 =>
        rw [map_add]
        exact Ideal.add_mem _ hy1 hy2
    exact h_im x
  have h_nil_gens : ∀ y ∈ Set.range (fun (a : I) => (Algebra.TensorProduct.includeRight : A →ₐ[K] S ⊗[K] A) a), IsNilpotent y := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    have h_nil_a : IsNilpotent a := h_nil a ha
    obtain ⟨n, hn⟩ := h_nil_a
    use n
    rw [← map_pow, hn, map_zero]
  exact isNilpotent_of_mem_ideal_gen_by_nilpotents _ h_nil_gens x h_ker

lemma injective_of_base_change {K A_red L S : Type*} [Field K] [CommRing A_red] [CommRing L] [CommRing S]
    [Algebra K A_red] [Algebra K L] [Algebra K S]
    (f : A_red →ₐ[K] L) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id K S) f) := by
  apply Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf

lemma irreducibleSpace_of_denseRange {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [IrreducibleSpace X] (f : X → Y) (hc : Continuous f) (hd : DenseRange f) :
    IrreducibleSpace Y := by
  rw [irreducibleSpace_def]
  have h1 : IsIrreducible (Set.univ : Set X) := (irreducibleSpace_def X).mp ‹_›
  have h2 : IsIrreducible (f '' Set.univ) := IsIrreducible.image h1 f hc.continuousOn
  have h3 : f '' Set.univ = Set.range f := Set.image_univ
  rw [h3] at h2
  have h4 : IsIrreducible (closure (Set.range f)) := IsIrreducible.closure h2
  have h5 : closure (Set.range f) = Set.univ := hd.closure_range
  rw [h5] at h4
  exact h4

lemma irreducibleSpace_of_nilradical_isPrime {A : Type*} [CommRing A] (h : (nilradical A).IsPrime) :
    IrreducibleSpace (PrimeSpectrum A) := by
  simp_rw [irreducibleSpace_def,IsIrreducible,isPreirreducible_iff_isClosed_union_isClosed]
  simp_rw [ PrimeSpectrum.isClosed_iff_zeroLocus,@forall_comm (Set _),]
  use (by exists⟨ _,h⟩), fun and ⟨a, H⟩b⟨A, B⟩ R=>H▸B▸or_iff_not_imp_left.2 fun and K V=>by_contra (and ∘ fun and a s W Z=>by_contra fun and' =>absurd (@R ⟨ _,h⟩ s) (H▸B▸?_))
  exact (·.elim (and' ∘(a.2.mem_of_pow_mem _<|. Z|>.choose_spec▸zero_mem _)) (and ∘ fun and R M=> (K.2.mem_of_pow_mem _) ((and M).choose_spec▸zero_mem _) ) )

lemma nilradical_comap_injective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    (nilradical B).comap f = nilradical A := by
  ext x
  simp only [Ideal.mem_comap, mem_nilradical]
  constructor
  · rintro ⟨n, hn⟩
    use n
    apply hf
    rw [map_pow, map_zero]
    exact hn
  · rintro ⟨n, hn⟩
    use n
    rw [← map_pow, hn, map_zero]

lemma irreducibleSpace_of_injective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) [IrreducibleSpace (PrimeSpectrum B)] :
    IrreducibleSpace (PrimeSpectrum A) := by
  have hb : (nilradical B).IsPrime := isPrime_nilradical_of_irreducibleSpace
  have h_pre : (nilradical B).comap f = nilradical A := nilradical_comap_injective f hf
  have ha : (nilradical A).IsPrime := by
    rw [← h_pre]
    exact Ideal.comap_isPrime f (nilradical B)
  exact irreducibleSpace_of_nilradical_isPrime ha

lemma nilradical_comap_surjective_nil {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hnil : ∀ x, f x = 0 → IsNilpotent x) :
    (nilradical B).comap f = nilradical A := by
  ext x
  simp only [Ideal.mem_comap, mem_nilradical]
  constructor
  · rintro ⟨n, hn⟩
    have h1 : f (x ^ n) = 0 := by
      rw [map_pow, hn]
    rcases hnil _ h1 with ⟨m, hm⟩
    use n * m
    rw [pow_mul]
    exact hm
  · rintro ⟨n, hn⟩
    use n
    rw [← map_pow, hn, map_zero]

lemma irreducibleSpace_of_surjective_nil {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Surjective f)
    (hnil : ∀ x, f x = 0 → IsNilpotent x) [IrreducibleSpace (PrimeSpectrum B)] :
    IrreducibleSpace (PrimeSpectrum A) := by
  have hb : (nilradical B).IsPrime := isPrime_nilradical_of_irreducibleSpace
  have h_pre : (nilradical B).comap f = nilradical A := nilradical_comap_surjective_nil f hnil
  have ha : (nilradical A).IsPrime := by
    rw [← h_pre]
    exact Ideal.comap_isPrime f (nilradical B)
  exact irreducibleSpace_of_nilradical_isPrime ha

lemma irreducibleSpace_of_equiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) [IrreducibleSpace (PrimeSpectrum B)] :
    IrreducibleSpace (PrimeSpectrum A) := by
  rewrite[@irreducibleSpace_def]at*
  delta IsIrreducible IsPreirreducible Ne at *
  simp_rw [ PrimeSpectrum.isOpen_iff]at*
  use ? _,?_
  · norm_num[Set.nonempty_def]at‹_›⊢
    exact ⟨ (by valid:).1.some.comap e⟩
  use (by valid:).elim fun and h K V ⟨a, H⟩ hexact ⟨A, B, M⟩⟨x,D,N⟩=>(h (K.image (⟨ _,·.2.comap e.symm⟩)) (V.image (⟨ _,·.2.comap e.symm⟩)) (?_) ?_ (?_) ? _).elim ?_
  · norm_num[ H,←e|>.forall_congr_right,Set.ext_iff]
    use (e ''a), fun and=>⟨Set.image_subset_iff.2 ∘fun R M α=>by_contra fun and' =>? _,fun R M a s=> H.ge (fun A B=>by_contra (absurd (R ⟨A, B, rfl⟩) ∘ (s▸?_))) a⟩
    · use and' ↑( H.subset (R ⟨ _,and.2.comap e⟩ · (by norm_num[Ideal.map_comap_of_surjective,e.surjective])) α)
    · norm_num[Ideal.mem_map_iff_of_surjective,e.surjective]
  · refine hexact.elim fun a s=> ⟨a.image e,Set.ext fun and=>?_⟩
    norm_num[s,←e.eq_symm_apply,Set.ext_iff]
    use fun and' =>s.subset (and' ⟨ _,and.2.comap e⟩ · (by norm_num[Ideal.map_comap_of_surjective,e.surjective])),fun R M A B=>s.ge ( fun and=>? _) A
    exact (e.injective.mem_set_image.1).comp (M.1.mem_map_iff_of_surjective e e.surjective).1 ∘by apply B▸R
  · exact ⟨ _,B,A,M, rfl⟩
  · exact ⟨_,D,x,N, rfl⟩
  · refine fun and ⟨a, ⟨A, B, C⟩,D,E,F⟩=>⟨A,a,B,A.ext (A.1.comap_injective_of_surjective e.symm e.symm.surjective ↑(congr_arg PrimeSpectrum.asIdeal (C.trans F.symm)))▸E⟩

lemma exists_mvpolynomial_preimage_two {k K k' : Type*} [Field k] [CommRing K] [CommRing k'] [Algebra k K] [Algebra k k']
    (x y : K ⊗[k] k') :
  ∃ (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] k') (x' y' : K ⊗[k] MvPolynomial (Fin n) k),
    (Algebra.TensorProduct.map (AlgHom.id k K) f) x' = x ∧
    (Algebra.TensorProduct.map (AlgHom.id k K) f) y' = y := by
  simp_all[forall_and_right]
  by_contra!
  cases x.exists_finset (R:=k)
  let α := Finset.equivFin (by valid)
  rcases y.exists_finset (R:=k)
  let α := Finset.equivFin (by valid)
  specialize this (Finset.card (by apply_rules)+ Finset.card (by assumption))
  specialize this (MvPolynomial.aeval (Fin.addCases (‹(_:Finset (K ×k')) ≃Fin _›.symm ·|>.1.2) (α.symm ·|>.1.2)))
  simp_rw [forall_exists_index] at this
  specialize this (∑ R,(‹(_: Finset (K ×k')) ≃_›.symm R).1.1 ⊗ₜ[k].X ((.castAdd _ R)))
  norm_num[*, true, ←α.sum_comp _,←Equiv.sum_comp (by apply_rules),← Finset.sum_attach (by assumption), ← Finset.sum_attach (by apply_rules)] at this
  use this (∑ a ∈.attach _,.tmul k a.1.1 (.X ((α a).natAdd _) ) ) (by norm_num[←α.sum_comp])

lemma lift_irred {k K : Type u_1} [Field k] [Field K] [Algebra k K]
    [GeometricallyIrreducibleAlgebra k K]
    (k' : Type (max u_1 u_2)) [Field k'] [Algebra k k'] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[k] k')) := by
  have h_nontrivial : Nontrivial (K ⊗[k] k') := inferInstance
  have h_prime : (nilradical (K ⊗[k] k')).IsPrime := by
    constructor
    · intro h_top
      have h1 : (1 : K ⊗[k] k') ∈ nilradical (K ⊗[k] k') := by
        rw [h_top]
        trivial
      obtain ⟨n, hn⟩ := h1
      have h2 : (1 : K ⊗[k] k') ^ n = 1 := one_pow n
      rw [hn] at h2
      exact zero_ne_one h2
    · intro x y hxy
      obtain ⟨n, f, x', y', hx', hy'⟩ := exists_mvpolynomial_preimage_two x y
      let I := RingHom.ker (f : MvPolynomial (Fin n) k →+* k')
      let A := MvPolynomial (Fin n) k ⧸ I
      let pi : MvPolynomial (Fin n) k →ₐ[k] A := Ideal.Quotient.mkₐ k I
      let f_bar : A →ₐ[k] k' := Ideal.Quotient.liftₐ I f (fun a ha => ha)
      have h_f_bar_inj : Function.Injective f_bar := by
        intro a b hab
        -- we just need to say it's true by definition of ker
        exact (Ideal.Quotient.mk_surjective a).elim.comp (Ideal.Quotient.mk_surjective b).elim fun and true R L => true▸L▸Ideal.Quotient.eq.mpr.comp (f.map_sub _ _).trans (sub_eq_zero.mpr (by apply true▸L▸hab) )
      haveI h_no_zero : NoZeroDivisors A := by
        constructor
        intro a b hab
        have h1 : f_bar (a * b) = f_bar 0 := by rw [hab]
        rw [map_mul, map_zero] at h1
        cases eq_zero_or_eq_zero_of_mul_eq_zero h1 with
        | inl ha => left; exact h_f_bar_inj (by rw [ha, map_zero])
        | inr hb => right; exact h_f_bar_inj (by rw [hb, map_zero])
      haveI h_nontrivial_A : Nontrivial A := by
        constructor
        use 0, 1
        intro h
        have h1 : f_bar 0 = f_bar 1 := by rw [h]
        rw [map_zero, map_one] at h1
        exact zero_ne_one h1
      haveI h_dom_A : IsDomain A := NoZeroDivisors.to_isDomain A
      have h_exists_field : ∃ (L : Type u_1) (_ : Field L) (_ : Algebra k L) (to_L : A →ₐ[k] L), Function.Injective to_L := by
        use FractionRing A
        use @FractionRing.field A _ h_dom_A
        use inferInstance
        use IsScalarTower.toAlgHom k A (FractionRing A)
        exact IsFractionRing.injective A (FractionRing A)

      obtain ⟨L, h_field_L, h_alg_L, to_L, h_to_L_inj⟩ := h_exists_field

      let to_L_K := Algebra.TensorProduct.map (AlgHom.id k K) to_L
      have h_to_L_K_inj : Function.Injective to_L_K := injective_of_base_change to_L h_to_L_inj

      have h_irr_L : IrreducibleSpace (PrimeSpectrum (K ⊗[k] L)) :=
        @GeometricallyIrreducibleAlgebra.out k K _ _ _ _ L h_field_L h_alg_L
      have h_irr_A : IrreducibleSpace (PrimeSpectrum (K ⊗[k] A)) :=
        @irreducibleSpace_of_injective (K ⊗[k] A) (K ⊗[k] L) _ _ to_L_K.toRingHom h_to_L_K_inj h_irr_L
      have h_prime_A : (nilradical (K ⊗[k] A)).IsPrime :=
        @isPrime_nilradical_of_irreducibleSpace (K ⊗[k] A) _ h_irr_A


      let pi_K := Algebra.TensorProduct.map (AlgHom.id k K) pi
      let f_bar_K := Algebra.TensorProduct.map (AlgHom.id k K) f_bar
      have h_f_bar_K_inj : Function.Injective f_bar_K := injective_of_base_change f_bar h_f_bar_inj

      have hf_comp : f = f_bar.comp pi := by ext; rfl
      have hf_K_comp : f_bar_K.comp pi_K = Algebra.TensorProduct.map (AlgHom.id k K) f := by
        apply Algebra.TensorProduct.ext
        · ext x; simp [f_bar_K, pi_K]
        · ext x; simp [f_bar_K, pi_K]
          have h1 : f (MvPolynomial.X x) = f_bar (pi (MvPolynomial.X x)) := by
            calc f (MvPolynomial.X x) = (f_bar.comp pi) (MvPolynomial.X x) := by rw [hf_comp]
            _ = f_bar (pi (MvPolynomial.X x)) := rfl
          rw [h1]

      have hx_A : f_bar_K (pi_K x') = x := by
        have h1 : f_bar_K (pi_K x') = (f_bar_K.comp pi_K) x' := rfl
        rw [h1, hf_K_comp, hx']

      have hy_A : f_bar_K (pi_K y') = y := by
        have h1 : f_bar_K (pi_K y') = (f_bar_K.comp pi_K) y' := rfl
        rw [h1, hf_K_comp, hy']

      have hxy_A : pi_K x' * pi_K y' ∈ nilradical (K ⊗[k] A) := by
        rw [mem_nilradical] at hxy ⊢
        obtain ⟨m, hm⟩ := hxy
        use m
        apply h_f_bar_K_inj
        rw [map_pow, map_zero, map_mul]
        rw [hx_A, hy_A]
        exact hm

      cases h_prime_A.mem_or_mem hxy_A with
      | inl hx_nil =>
        left
        rw [mem_nilradical] at hx_nil ⊢
        obtain ⟨m, hm⟩ := hx_nil
        use m
        rw [← hx_A, ← map_pow, hm, map_zero]
      | inr hy_nil =>
        right
        rw [mem_nilradical] at hy_nil ⊢
        obtain ⟨m, hm⟩ := hy_nil
        use m
        rw [← hy_A, ← map_pow, hm, map_zero]
  exact irreducibleSpace_of_nilradical_isPrime h_prime

lemma irreducibleSpace_of_algEquiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) [IrreducibleSpace (PrimeSpectrum B)] :
    IrreducibleSpace (PrimeSpectrum A) :=
  irreducibleSpace_of_equiv (e : A ≃+* B)

-- EVOLVE-BLOCK-END

theorem GeometricallyIrreducibleAlgebra.transitive
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {S : Type v} [CommRing S] [Algebra K S] [Algebra k S] [IsScalarTower k K S]
    [GeometricallyIrreducibleAlgebra k K]
    [GeometricallyIrreducibleAlgebra K S] :
    GeometricallyIrreducibleAlgebra k S := by
  -- EVOLVE-BLOCK-START
  constructor
  intro k' _ _
  have hA : IrreducibleSpace (PrimeSpectrum (K ⊗[k] k')) := lift_irred k'
  let A := K ⊗[k] k'
  have h_irrA : IrreducibleSpace (PrimeSpectrum A) := hA
  have hN : (nilradical A).IsPrime := isPrime_nilradical_of_irreducibleSpace
  have h_exists_A_red : ∃ (A_red : Type (max u v)) (_ : CommRing A_red) (_ : IsDomain A_red) (_ : Algebra K A_red) (pi : A →ₐ[K] A_red), Function.Surjective pi ∧ (∀ x, pi x = 0 → IsNilpotent x) := by
    use (A ⧸ nilradical A)
    use inferInstance
    have h_dom : IsDomain (A ⧸ nilradical A) := by apply inferInstance
    use h_dom
    use inferInstance
    use Ideal.Quotient.mkₐ K (nilradical A)
    constructor
    · exact Ideal.Quotient.mk_surjective
    · intro x hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  obtain ⟨A_red, h_comm_A_red, h_dom_A_red, h_alg_A_red, pi, hpi_surj, hpi_nil⟩ := h_exists_A_red
  have h_exists_field : ∃ (L : Type (max u v)) (_ : Field L) (_ : Algebra K L) (f : A_red →ₐ[K] L), Function.Injective f := by
    use FractionRing A_red
    use inferInstance
    use inferInstance
    use IsScalarTower.toAlgHom K A_red (FractionRing A_red)
    exact IsFractionRing.injective A_red (FractionRing A_red)
  obtain ⟨L, h_field_L, h_alg_K_L, f, hf_inj⟩ := h_exists_field
  have h_irrSL : IrreducibleSpace (PrimeSpectrum (S ⊗[K] L)) := @GeometricallyIrreducibleAlgebra.out K S _ _ _ _ L h_field_L h_alg_K_L
  let f_tens : S ⊗[K] A_red →+* S ⊗[K] L := (Algebra.TensorProduct.map (AlgHom.id K S) f).toRingHom
  have h_f_tens_inj : Function.Injective f_tens := injective_of_base_change f hf_inj
  have h_irrS_A_red : IrreducibleSpace (PrimeSpectrum (S ⊗[K] A_red)) :=
    @irreducibleSpace_of_injective (S ⊗[K] A_red) (S ⊗[K] L) _ _ f_tens h_f_tens_inj h_irrSL
  let pi_tens : S ⊗[K] A →+* S ⊗[K] A_red := (Algebra.TensorProduct.map (AlgHom.id K S) pi).toRingHom
  have h_pi_tens_surj : Function.Surjective pi_tens := TensorProduct.map_surjective Function.surjective_id hpi_surj
  have h_pi_tens_nil : ∀ x, pi_tens x = 0 → IsNilpotent x := nil_of_base_change_surjective pi hpi_surj hpi_nil
  haveI h_irrS_A : IrreducibleSpace (PrimeSpectrum (S ⊗[K] A)) :=
    @irreducibleSpace_of_surjective_nil (S ⊗[K] A) (S ⊗[K] A_red) _ _ pi_tens h_pi_tens_surj h_pi_tens_nil h_irrS_A_red
  let e := Algebra.TensorProduct.cancelBaseChange k K S S k'
  exact irreducibleSpace_of_algEquiv e.symm
  -- EVOLVE-BLOCK-END
