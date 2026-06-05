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
noncomputable def tensor_basis {k R S : Type*} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] :
    Module.Basis (Module.Free.ChooseBasisIndex k S) R (R ⊗[k] S) :=
  Algebra.TensorProduct.basis R (Module.Free.chooseBasis k S)

lemma sum_in_Q {k R S : Type*} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (Q : Ideal (R ⊗[k] S)) (f_v : Module.Free.ChooseBasisIndex k S →₀ R)
    (h : ∀ i ∈ f_v.support, f_v i ∈ Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q) :
    tensor_basis.repr.symm f_v ∈ Q := by
  revert h
  refine Finsupp.induction f_v ?_ ?_
  · intro _
    simp only [map_zero, Submodule.zero_mem]
  · intro i c v_rest hi hc_zero h_ind h_all
    have h_c : c ∈ Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q := by
      have h1 : i ∈ (Finsupp.single i c + v_rest).support := by
        apply Finsupp.mem_support_iff.mpr
        rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl]
        have h_v_rest_i : v_rest i = 0 := by
          by_contra h_nz
          exact hi (Finsupp.mem_support_iff.mpr h_nz)
        rw [h_v_rest_i, add_zero]
        exact hc_zero
      have h2 := h_all i h1
      have h3 : (Finsupp.single i c + v_rest) i = c := by
        rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl]
        have h_v_rest_i : v_rest i = 0 := by
          by_contra h_nz
          exact hi (Finsupp.mem_support_iff.mpr h_nz)
        rw [h_v_rest_i, add_zero]
      rwa [h3] at h2
    have h_v_rest : ∀ j ∈ v_rest.support, v_rest j ∈ Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q := by
      intro j hj
      have h_neq : j ≠ i := by
        intro heq
        subst heq
        exact hi hj
      have h_in_supp : j ∈ (Finsupp.single i c + v_rest).support := by
        apply Finsupp.mem_support_iff.mpr
        rw [Finsupp.add_apply, Finsupp.single_apply, if_neg h_neq.symm, zero_add]
        exact Finsupp.mem_support_iff.mp hj
      have h2 := h_all j h_in_supp
      have h3 : (Finsupp.single i c + v_rest) j = v_rest j := by
        rw [Finsupp.add_apply, Finsupp.single_apply, if_neg h_neq.symm, zero_add]
      rwa [h3] at h2
    have h_ind_v_rest : tensor_basis.repr.symm v_rest ∈ Q := h_ind h_v_rest
    have h_single : tensor_basis.repr.symm (Finsupp.single i c) ∈ Q := by
      have h_smul : Finsupp.single i c = c • Finsupp.single i 1 := by
        ext j
        rw [Finsupp.smul_apply, smul_eq_mul]
        rw [Finsupp.single_apply, Finsupp.single_apply]
        by_cases h_eq : i = j
        · simp only [if_pos h_eq, mul_one]
        · simp only [if_neg h_eq, mul_zero]
      rw [h_smul, map_smul]
      have h_alg_smul : c • tensor_basis.repr.symm (Finsupp.single i 1) = (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) c * tensor_basis.repr.symm (Finsupp.single i 1) := by
        exact Algebra.smul_def c (tensor_basis.repr.symm (Finsupp.single i 1))
      rw [h_alg_smul]
      exact Ideal.mul_mem_right _ Q h_c
    have h_add : tensor_basis.repr.symm (Finsupp.single i c + v_rest) = tensor_basis.repr.symm (Finsupp.single i c) + tensor_basis.repr.symm v_rest := map_add _ _ _
    rw [h_add]
    exact Submodule.add_mem Q h_single h_ind_v_rest

lemma basis_repr_not_in_P {k R S : Type*} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (Q : Ideal (R ⊗[k] S)) (y : R ⊗[k] S) (hy : y ∉ Q) :
    ∃ i, (tensor_basis.repr y) i ∉ Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q := by
  by_contra h
  push_neg at h
  have h_in_Q : tensor_basis.repr.symm (tensor_basis.repr y) ∈ Q := sum_in_Q Q (tensor_basis.repr y) (fun i _ => h i)
  rw [LinearEquiv.symm_apply_apply] at h_in_Q
  exact hy h_in_Q

lemma exists_pow_mul_eq_zero_of_mem_minimalPrimes {A : Type*} [CommRing A] (Q : Ideal A) (hQ : Q ∈ minimalPrimes A) (x : A) (hx : x ∈ Q) :
    ∃ (n : ℕ) (y : A), y ∉ Q ∧ x^n * y = 0 := by
  let M : Submonoid A := {
    carrier := {z | ∃ (n : ℕ) (y : A), y ∉ Q ∧ z = x^n * y},
    mul_mem' := by
      rintro a b ⟨n1, y1, hy1, rfl⟩ ⟨n2, y2, hy2, rfl⟩
      use n1 + n2, y1 * y2
      refine ⟨?_, ?_⟩
      · intro h_in
        have h_prime := hQ.1.1
        cases Ideal.IsPrime.mem_or_mem h_prime h_in with
        | inl h1 => exact hy1 h1
        | inr h2 => exact hy2 h2
      · ring
    one_mem' := by
      use 0, 1
      refine ⟨?_, ?_⟩
      · intro h1
        have h_top : Q = ⊤ := by rwa [Ideal.eq_top_iff_one]
        exact hQ.1.1.1 h_top
      · ring
  }
  by_contra h_not
  push_neg at h_not
  have h_zero_not_mem : (0 : A) ∉ M := by
    intro h_in
    obtain ⟨n, y, hy, heq⟩ := h_in
    exact h_not n y hy heq.symm
  have h_exists_prime : ∃ (P : Ideal A), P.IsPrime ∧ Disjoint (M : Set A) (P : Set A) := by
    have h_nontriv : Nontrivial (Localization M) := by
      refine ⟨⟨algebraMap A (Localization M) 0, algebraMap A (Localization M) 1, ?_⟩⟩
      intro h_eq
      have h_eq_zero : algebraMap A (Localization M) 1 = algebraMap A (Localization M) 0 := by rw [← h_eq]
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M (Localization M)).mp h_eq_zero
      have hc2 : (c : A) = 0 := by
        have h_mul : (c : A) * 1 = c * 0 := hc
        rw [mul_one, mul_zero] at h_mul
        exact h_mul
      have hc_in_M : (c : A) ∈ M := c.2
      rw [hc2] at hc_in_M
      exact h_zero_not_mem hc_in_M
    obtain ⟨m, hm⟩ := @Ideal.exists_maximal (Localization M) _ h_nontriv
    use Ideal.comap (algebraMap A (Localization M)) m
    refine ⟨Ideal.comap_isPrime _ m, ?_⟩
    rw [Set.disjoint_left]
    intro a ha_in_M ha_in_P
    have h_unit : IsUnit (algebraMap A (Localization M) a) := IsLocalization.map_units (Localization M) ⟨a, ha_in_M⟩
    have h_in_m : algebraMap A (Localization M) a ∈ m := ha_in_P
    have h_m_top : m = ⊤ := by
      obtain ⟨u, hu⟩ := h_unit
      have h_one : (1 : Localization M) ∈ m := by
        have h2 : ↑u * (↑(u⁻¹) : Localization M) = 1 := Units.mul_inv u
        rw [← h2, hu]
        exact Ideal.mul_mem_right _ m ha_in_P
      rwa [Ideal.eq_top_iff_one]
    exact hm.out.1 h_m_top
  obtain ⟨P, hP, hP_disj⟩ := h_exists_prime
  have hP_le_Q : P ≤ Q := by
    intro a ha
    by_contra h_notin
    have h_in_M : a ∈ M := by
      use 0, a
      exact ⟨h_notin, by ring⟩
    exact Set.disjoint_left.mp hP_disj h_in_M ha
  have h_x_not_in_P : x ∉ P := by
    intro h_in
    have h_x_in_M : x ∈ M := by
      use 1, 1
      refine ⟨?_, by ring⟩
      intro h_one_in
      have h_top : Q = ⊤ := by rwa [Ideal.eq_top_iff_one]
      exact hQ.1.1.1 h_top
    exact Set.disjoint_left.mp hP_disj h_x_in_M h_in
  have h_P_eq_Q : P = Q := le_antisymm hP_le_Q (hQ.2 ⟨hP, bot_le⟩ hP_le_Q)
  rw [h_P_eq_Q] at h_x_not_in_P
  exact h_x_not_in_P hx

lemma isPrime_nilradical_of_irreducible (A : Type*) [CommRing A] [IrreducibleSpace (PrimeSpectrum A)] : (nilradical A).IsPrime := by
  refine Ideal.isPrime_iff.mpr (by_contradiction fun and=>? _)
  simp_all[nilradical_eq_sInf, mul_pow,irreducibleSpace_def]
  by_cases h :∃S:Ideal A,S.IsPrime∧¬S = ⊤
  · use(h.choose_spec.elim (and _)).elim fun and⟨A, B, ⟨a, C, _⟩,D,E, _⟩=>absurd (‹IsIrreducible ⊤›.2) ?_
    rw[IsPreirreducible]
    exact (. _ _ ( PrimeSpectrum.isOpen_basicOpen) ( PrimeSpectrum.isOpen_basicOpen) (by exists (by use a)) (by exists⟨D,E⟩) |>.some_mem.2.elim ((PrimeSpectrum.isPrime _).2 (B _ ( PrimeSpectrum.isPrime _) ) ).elim)
  · exact (subsingleton_or_nontrivial A).elim ( fun and=>by simp_all[isIrreducible_iff_singleton]) fun and=>h.comp (Ideal.exists_le_maximal ⊥ bot_ne_top).imp fun and(a)=> ⟨a.1.isPrime,a.1.1.1⟩

lemma minimal_prime_eq {B : Type*} [CommRing B] (p p' : Ideal B) (hp : p ∈ minimalPrimes B) (hp' : p'.IsPrime) (h_le : p' ≤ p) : p' = p := by
  exact (le_antisymm) (h_le) (hp.2 ⟨ hp',bot_le⟩ (h_le ) )

lemma unique_minimal_prime (A : Type*) [CommRing A] [IrreducibleSpace (PrimeSpectrum A)] :
    ∃! p, p ∈ minimalPrimes A := by
  have hp : (nilradical A).IsPrime := isPrime_nilradical_of_irreducible A
  simp_rw [minimalPrimes,irreducibleSpace_def,ExistsUnique] at*
  cases subsingleton_or_nontrivial A with| inl=>cases hp.1 (by subsingleton) | inr=>_
  simp_rw [Ideal.minimalPrimes,IsIrreducible,IsPreirreducible]at*
  norm_num[minimal_iff]
  exists _, ⟨hp, fun and R M=>le_antisymm (R.radical_le_iff.2 bot_le) M⟩
  exact fun and R L=>L hp (nilradical_le_prime _)

lemma unique_minimal_prime_of_geometricallyIrreducible
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    [GeometricallyIrreducibleAlgebra k S]
    (k' : Type (max u v)) [Field k'] [Algebra k k'] :
    ∃! p, p ∈ minimalPrimes (S ⊗[k] k') := by
  have h_irr : IrreducibleSpace (PrimeSpectrum (S ⊗[k] k')) := GeometricallyIrreducibleAlgebra.out k'
  exact unique_minimal_prime (S ⊗[k] k')



noncomputable def FiberRing (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] (P : Ideal R) : Type (max u v) :=
  ULift.{u, v} (FractionRing (R ⧸ P))

noncomputable instance FiberRing_field (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] (P : Ideal R) [P.IsPrime] : Field (FiberRing k R P) :=
  inferInstanceAs (Field (ULift _))

noncomputable instance FiberRing_algebra (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] (P : Ideal R) [P.IsPrime] : Algebra k (FiberRing k R P) :=
  inferInstanceAs (Algebra k (ULift _))


lemma mapsTo_minimalPrimes_comap
    {k R S : Type*} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] :
    MapsTo (Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S))
      (minimalPrimes (R ⊗[k] S)) (minimalPrimes R) := by
  intro Q hQ
  have hQp : Q.IsPrime := hQ.1.1
  have hp : (Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q).IsPrime := Ideal.comap_isPrime (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q
  refine ⟨⟨hp, bot_le⟩, ?_⟩
  intro P hP hP_le
  have h_eq : Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q ≤ P := by
    intro a ha
    by_contra h_not_in_P
    have h_fa_in_Q : (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) a ∈ Q := ha
    obtain ⟨n, y, hy_not_in_Q, hy_zero⟩ := exists_pow_mul_eq_zero_of_mem_minimalPrimes Q hQ _ h_fa_in_Q
    obtain ⟨i, hi⟩ := basis_repr_not_in_P Q y hy_not_in_Q
    have h_not_in_P_i : (tensor_basis.repr y) i ∉ P := by
      intro h_in
      exact hi (hP_le h_in)
    have h_fa_pow : (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) a ^ n = (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) (a ^ n) := (map_pow (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) a n).symm
    have h_smul : (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) (a ^ n) * y = a ^ n • y := (Algebra.smul_def (a ^ n) y).symm
    rw [h_fa_pow, h_smul] at hy_zero
    have h_repr_zero : tensor_basis.repr (a ^ n • y) = 0 := by rw [hy_zero, map_zero]
    have h_repr_smul : tensor_basis.repr (a ^ n • y) = a ^ n • tensor_basis.repr y := map_smul _ _ _
    rw [h_repr_smul] at h_repr_zero
    have h_eval_zero : (a ^ n • tensor_basis.repr y) i = 0 := by rw [h_repr_zero, Finsupp.coe_zero, Pi.zero_apply]
    have h_eval_smul : (a ^ n • tensor_basis.repr y) i = a ^ n * (tensor_basis.repr y) i := by rfl
    rw [h_eval_smul] at h_eval_zero
    have h_prod_in_P : a ^ n * (tensor_basis.repr y) i ∈ P := by rw [h_eval_zero]; exact Submodule.zero_mem P
    cases Ideal.IsPrime.mem_or_mem hP.1 h_prod_in_P with
    | inl h_pow =>
      exact h_not_in_P (hP.1.mem_of_pow_mem n h_pow)
    | inr h_y_i =>
      exact h_not_in_P_i h_y_i
  exact h_eq

noncomputable instance FiberRing_algebraR (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] (P : Ideal R) [P.IsPrime] : Algebra R (FiberRing k R P) :=
  inferInstanceAs (Algebra R (ULift _))

noncomputable instance FiberRing_isScalarTower (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] (P : Ideal R) [P.IsPrime] : IsScalarTower k R (FiberRing k R P) :=
  inferInstanceAs (IsScalarTower k R (ULift _))

noncomputable def fiberMap {k : Type u} {R S : Type v} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (P : Ideal R) [P.IsPrime] :
    (R ⊗[k] S) →ₐ[k] (S ⊗[k] FiberRing k R P) :=
  let f : R →ₐ[k] FiberRing k R P := IsScalarTower.toAlgHom k R (FiberRing k R P)
  let g : S →ₐ[k] S := AlgHom.id k S
  let map1 := Algebra.TensorProduct.map f g
  let comm := Algebra.TensorProduct.comm k (FiberRing k R P) S
  comm.toAlgHom.comp map1

lemma fiber_ker {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R] (P : Ideal R) [P.IsPrime] :
    Ideal.comap (algebraMap R (FiberRing k R P)) ⊥ = P := by
  norm_num[ FiberRing,Ideal.ext_iff,eq_comm]
  delta FiberRing
  use fun and=>Ideal.Quotient.eq_zero_iff_mem.symm.trans (IsFractionRing.to_map_eq_zero_iff.symm.trans (ULift.up_inj.trans (comm)).symm)

lemma fiberMap_comp_includeLeft {k : Type u} {R S : Type v} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (P : Ideal R) [P.IsPrime] :
    (fiberMap P).toRingHom.comp (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S).toRingHom =
    (Algebra.TensorProduct.includeRight : FiberRing k R P →ₐ[k] S ⊗[k] FiberRing k R P).toRingHom.comp (algebraMap R (FiberRing k R P)) := by
  norm_num[fiberMap, Algebra.algebraMap_eq_smul_one, false, RingHom.ext_iff]

lemma fiberMap_comp_includeLeft_apply {k : Type u} {R S : Type v} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (P : Ideal R) [P.IsPrime] (x : R) :
    fiberMap P ((Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) x) =
    (Algebra.TensorProduct.includeRight : FiberRing k R P →ₐ[k] S ⊗[k] FiberRing k R P) (algebraMap R (FiberRing k R P) x) := by
  have h := RingHom.ext_iff.1 (fiberMap_comp_includeLeft (k := k) (R := R) (S := S) P) x
  exact h

noncomputable def fiberMap_alt {k : Type u} {R S : Type v} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (P : Ideal R) [P.IsPrime] :
    (R ⊗[k] S) →ₐ[k] (FiberRing k R P ⊗[k] S) :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R (FiberRing k R P)) (AlgHom.id k S)

lemma fiberMap_alt_comp_includeLeft {k : Type u} {R S : Type v} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (P : Ideal R) [P.IsPrime] :
    (fiberMap_alt P).toRingHom.comp (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S).toRingHom =
    (Algebra.TensorProduct.includeLeft : FiberRing k R P →ₐ[k] FiberRing k R P ⊗[k] S).toRingHom.comp (algebraMap R (FiberRing k R P)) := by
  norm_num [fiberMap_alt, Algebra.algebraMap_eq_smul_one, RingHom.ext_iff]

noncomputable def tensor_basis_K {k : Type u} {R S : Type v} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (P : Ideal R) [P.IsPrime] :
    Module.Basis (Module.Free.ChooseBasisIndex k S) (FiberRing k R P) (FiberRing k R P ⊗[k] S) :=
  Algebra.TensorProduct.basis (FiberRing k R P) (Module.Free.chooseBasis k S)



lemma fiberMap_alt_apply_symm {k : Type u} {R S : Type v} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (P : Ideal R) [P.IsPrime] (f_v : Module.Free.ChooseBasisIndex k S →₀ R) :
    fiberMap_alt P (tensor_basis.repr.symm f_v) = (tensor_basis_K P).repr.symm (f_v.mapRange (algebraMap R (FiberRing k R P)) (map_zero _)) := by
  norm_num[fiberMap_alt, false,tensor_basis,tensor_basis_K,f_v.linearCombination_apply, Finsupp.sum]
  norm_num [TensorProduct.smul_tmul', Finsupp.mapRange, Finsupp.linearCombination_apply, Finsupp.sum]
  exact (congr_arg _ (by simp_all[Algebra.smul_def])).trans ( Finset.sum_subset (by simp_all) (by simp_all[Algebra.smul_def])).symm

lemma fiberMap_ker_le
    {k : Type u} {R S : Type v} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (P : Ideal R) [P.IsPrime] (Q : Ideal (R ⊗[k] S)) (hQ_prime : Q.IsPrime)
    (h_comap : Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q = P) :
    RingHom.ker (fiberMap P).toRingHom ≤ Q := by
  intro y hy
  have hy2 : (fiberMap P) y = 0 := hy
  have heq : fiberMap P = (Algebra.TensorProduct.comm k (FiberRing k R P) S).toAlgHom.comp (fiberMap_alt P) := rfl
  have hy3 : (Algebra.TensorProduct.comm k (FiberRing k R P) S).toAlgHom (fiberMap_alt P y) = 0 := by
    calc
      (Algebra.TensorProduct.comm k (FiberRing k R P) S).toAlgHom (fiberMap_alt P y) = ((Algebra.TensorProduct.comm k (FiberRing k R P) S).toAlgHom.comp (fiberMap_alt P)) y := rfl
      _ = (fiberMap P) y := by rw [← heq]
      _ = 0 := hy2
  have h_inj := (Algebra.TensorProduct.comm k (FiberRing k R P) S).injective
  have hy4 : fiberMap_alt P y = 0 := by
    apply h_inj
    rw [map_zero]
    exact hy3
  let f_v := tensor_basis.repr y
  have hy5 : y = tensor_basis.repr.symm f_v := (LinearEquiv.symm_apply_apply tensor_basis.repr y).symm
  have hy6 : fiberMap_alt P (tensor_basis.repr.symm f_v) = 0 := by
    rw [← hy5]
    exact hy4
  rw [fiberMap_alt_apply_symm P f_v] at hy6
  have hy7 : f_v.mapRange (algebraMap R (FiberRing k R P)) (map_zero _) = 0 := by
    exact (LinearEquiv.map_eq_zero_iff (tensor_basis_K P).repr.symm).mp hy6
  have h_supp : ∀ i ∈ f_v.support, f_v i ∈ Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q := by
    intro i hi
    have h_eval : (f_v.mapRange (algebraMap R (FiberRing k R P)) (map_zero _)) i = 0 := by rw [hy7, Finsupp.coe_zero, Pi.zero_apply]
    have h_eval2 : algebraMap R (FiberRing k R P) (f_v i) = 0 := by
      have h_eq : (f_v.mapRange (algebraMap R (FiberRing k R P)) (map_zero _)) i = algebraMap R (FiberRing k R P) (f_v i) := Finsupp.mapRange_apply
      rw [← h_eq]
      exact h_eval
    have h_in_P : f_v i ∈ P := by
      have h_ker := fiber_ker (k := k) (R := R) P
      have h_in_ker : f_v i ∈ Ideal.comap (algebraMap R (FiberRing k R P)) ⊥ := h_eval2
      rw [h_ker] at h_in_ker
      exact h_in_ker
    rw [h_comap.symm] at h_in_P
    exact h_in_P
  have hy_in_Q : tensor_basis.repr.symm f_v ∈ Q := sum_in_Q Q f_v h_supp
  rwa [hy5]

lemma fiber_unique_minimal_prime
    {k : Type u} {R S : Type v} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [GeometricallyIrreducibleAlgebra k S] (Q1 Q2 : Ideal (R ⊗[k] S))
    (hQ1 : Q1 ∈ minimalPrimes (R ⊗[k] S)) (hQ2 : Q2 ∈ minimalPrimes (R ⊗[k] S))
    (heq : Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q1 = Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q2) :
    Q1 = Q2 := by
  have hQ1_prime : Q1.IsPrime := hQ1.1.1
  have hQ2_prime : Q2.IsPrime := hQ2.1.1
  let P := Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q1
  have hP_prime : P.IsPrime := Ideal.comap_isPrime _ Q1
  let K := FiberRing k R P
  have h_uniq := unique_minimal_prime_of_geometricallyIrreducible (k := k) (S := S) (k' := K)
  rcases h_uniq with ⟨Q_tilde, hQ_tilde, h_uniq2⟩
  have hQ_tilde_prime : Q_tilde.IsPrime := hQ_tilde.1.1
  let Q0 := Q_tilde.comap (fiberMap P)
  have hQ0_prime : Q0.IsPrime := Ideal.comap_isPrime (fiberMap P) Q_tilde
  have h_nil : Q_tilde = nilradical (S ⊗[k] K) := by
    have h_irr : IrreducibleSpace (PrimeSpectrum (S ⊗[k] K)) := GeometricallyIrreducibleAlgebra.out K
    have h_nil_prime : (nilradical (S ⊗[k] K)).IsPrime := @isPrime_nilradical_of_irreducible (S ⊗[k] K) _ h_irr
    have h_nil_min : nilradical (S ⊗[k] K) ∈ minimalPrimes (S ⊗[k] K) := by
      refine ⟨⟨h_nil_prime, bot_le⟩, ?_⟩
      intro q hq _ x hx
      obtain ⟨n, hn⟩ := hx
      have hn_eq : x ^ n = 0 := hn
      have hn_in : x ^ n ∈ q := by rw [hn_eq]; exact Submodule.zero_mem q
      exact hq.1.mem_of_pow_mem n hn_in
    exact (h_uniq2 _ h_nil_min).symm
  have h_Q0_le_Q1 : Q0 ≤ Q1 := by
    intro x hx
    have hx_tilde : fiberMap P x ∈ Q_tilde := hx
    rw [h_nil] at hx_tilde
    obtain ⟨n, hn⟩ := hx_tilde
    have hn2 : (fiberMap P x) ^ n = 0 := hn
    have hn3 : fiberMap P (x ^ n) = 0 := by
      rw [map_pow]
      exact hn2
    have hn4 : x ^ n ∈ RingHom.ker (fiberMap P).toRingHom := hn3
    have hn5 : x ^ n ∈ Q1 := fiberMap_ker_le P Q1 hQ1_prime rfl hn4
    exact hQ1_prime.mem_of_pow_mem n hn5
  have h_Q0_le_Q2 : Q0 ≤ Q2 := by
    intro x hx
    have hx_tilde : fiberMap P x ∈ Q_tilde := hx
    rw [h_nil] at hx_tilde
    obtain ⟨n, hn⟩ := hx_tilde
    have hn2 : (fiberMap P x) ^ n = 0 := hn
    have hn3 : fiberMap P (x ^ n) = 0 := by
      rw [map_pow]
      exact hn2
    have hn4 : x ^ n ∈ RingHom.ker (fiberMap P).toRingHom := hn3
    have hn5 : x ^ n ∈ Q2 := fiberMap_ker_le P Q2 hQ2_prime heq.symm hn4
    exact hQ2_prime.mem_of_pow_mem n hn5
  have h_Q1_eq : Q0 = Q1 := minimal_prime_eq Q1 Q0 hQ1 hQ0_prime h_Q0_le_Q1
  have h_Q2_eq : Q0 = Q2 := minimal_prime_eq Q2 Q0 hQ2 hQ0_prime h_Q0_le_Q2
  rw [← h_Q1_eq, h_Q2_eq]

lemma fiber_exists_minimal_prime
    {k : Type u} {R S : Type v} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [GeometricallyIrreducibleAlgebra k S] (P : Ideal R) (hP : P ∈ minimalPrimes R) :
    ∃ Q ∈ minimalPrimes (R ⊗[k] S), Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q = P := by
  have hp_prime : P.IsPrime := hP.1.1
  let K := FiberRing k R P
  have h_uniq := unique_minimal_prime_of_geometricallyIrreducible (k := k) (S := S) (k' := K)
  rcases h_uniq with ⟨Q_tilde, hQ_tilde, h_uniq2⟩
  let Q := Q_tilde.comap (fiberMap P)
  have hQ_tilde_prime : Q_tilde.IsPrime := hQ_tilde.1.1
  have hQ_prime : Q.IsPrime := Ideal.comap_isPrime (fiberMap P) Q_tilde
  have h_comap : Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q = P := by
    ext x
    constructor
    · intro hx
      have hx2 : fiberMap P ((Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) x) ∈ Q_tilde := hx
      rw [fiberMap_comp_includeLeft_apply] at hx2
      have h_comap_bot : Ideal.comap (Algebra.TensorProduct.includeRight : K →ₐ[k] S ⊗[k] K).toRingHom Q_tilde = ⊥ := by
        have h_prime_comap : (Ideal.comap (Algebra.TensorProduct.includeRight : K →ₐ[k] S ⊗[k] K).toRingHom Q_tilde).IsPrime := Ideal.comap_isPrime _ Q_tilde
        exact Ideal.eq_bot_of_prime _
      have hx3 : algebraMap R K x ∈ Ideal.comap (Algebra.TensorProduct.includeRight : K →ₐ[k] S ⊗[k] K).toRingHom Q_tilde := hx2
      rw [h_comap_bot] at hx3
      have hx4 : algebraMap R K x ∈ (⊥ : Ideal K) := hx3
      have hx5 : x ∈ Ideal.comap (algebraMap R K) ⊥ := hx4
      rw [fiber_ker P] at hx5
      exact hx5
    · intro hx
      have hx2 : x ∈ Ideal.comap (algebraMap R K) ⊥ := by
        rw [fiber_ker P]
        exact hx
      have hx3 : algebraMap R K x ∈ (⊥ : Ideal K) := hx2
      have h_comap_bot : Ideal.comap (Algebra.TensorProduct.includeRight : K →ₐ[k] S ⊗[k] K).toRingHom Q_tilde = ⊥ := by
        have h_prime_comap : (Ideal.comap (Algebra.TensorProduct.includeRight : K →ₐ[k] S ⊗[k] K).toRingHom Q_tilde).IsPrime := Ideal.comap_isPrime _ Q_tilde
        exact Ideal.eq_bot_of_prime _
      have hx4 : algebraMap R K x ∈ Ideal.comap (Algebra.TensorProduct.includeRight : K →ₐ[k] S ⊗[k] K).toRingHom Q_tilde := by
        rw [h_comap_bot]
        exact hx3
      have hx5 : fiberMap P ((Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) x) ∈ Q_tilde := by
        rw [fiberMap_comp_includeLeft_apply]
        exact hx4
      exact hx5
  have h_min_le : ∃ Q_min ∈ minimalPrimes (R ⊗[k] S), Q_min ≤ Q := by
    have _inst_Q : Q.IsPrime := hQ_prime
    exact Ideal.exists_minimalPrimes_le bot_le
  rcases h_min_le with ⟨Q_min, hQ_min, h_le⟩
  use Q_min
  constructor
  · exact hQ_min
  · have h_comap_le : Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q_min ≤ P := by
      rw [← h_comap]
      exact Ideal.comap_mono h_le
    have hQ_min_prime : Q_min.IsPrime := hQ_min.1.1
    have h_comap_Q_min_prime : (Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) Q_min).IsPrime := Ideal.comap_isPrime _ Q_min
    exact minimal_prime_eq P _ hP h_comap_Q_min_prime h_comap_le

lemma injOn_minimalPrimes_comap
    {k : Type u} {R S : Type v} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [GeometricallyIrreducibleAlgebra k S] :
    InjOn (Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S))
      (minimalPrimes (R ⊗[k] S)) := by
  intro Q1 hQ1 Q2 hQ2 heq
  exact fiber_unique_minimal_prime Q1 Q2 hQ1 hQ2 heq

lemma surjOn_minimalPrimes_comap
    {k : Type u} {R S : Type v} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [GeometricallyIrreducibleAlgebra k S] :
    SurjOn (Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S))
      (minimalPrimes (R ⊗[k] S)) (minimalPrimes R) := by
  intro P hP
  exact fiber_exists_minimal_prime P hP
-- EVOLVE-BLOCK-END

theorem minimalPrimes_bijection_of_geometricallyIrreducibleAlgebra
    {k : Type u} {R S : Type v} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [GeometricallyIrreducibleAlgebra k S] :
    BijOn (Ideal.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S))
      (minimalPrimes (R ⊗[k] S)) (minimalPrimes R) := by
  -- EVOLVE-BLOCK-START
  exact ⟨mapsTo_minimalPrimes_comap, injOn_minimalPrimes_comap, surjOn_minimalPrimes_comap⟩
  -- EVOLVE-BLOCK-END
