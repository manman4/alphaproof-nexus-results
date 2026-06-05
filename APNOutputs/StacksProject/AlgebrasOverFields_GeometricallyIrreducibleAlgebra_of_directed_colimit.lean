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
lemma preirred_univ_of_nilradical_prime {A : Type _} [CommRing A] (h : (nilradical A).IsPrime) :
  IsPreirreducible (univ : Set (PrimeSpectrum A)) := by
  intro s t hs ht hs_ne ht_ne
  rw [PrimeSpectrum.isOpen_iff] at hs ht
  rcases hs with ⟨I, hI⟩
  rcases ht with ⟨J, hJ⟩
  have hs_eq : s = (zeroLocus I)ᶜ := by rw [←hI, compl_compl]
  have ht_eq : t = (zeroLocus J)ᶜ := by rw [←hJ, compl_compl]
  let I_ideal := Ideal.span I
  let J_ideal := Ideal.span J
  have hI_ne : zeroLocus (I_ideal : Set A) ≠ univ := by
    rw [PrimeSpectrum.zeroLocus_span]
    intro H
    rw [H] at hs_eq
    rw [hs_eq] at hs_ne
    have : (univ ∩ (univ : Set (PrimeSpectrum A))ᶜ).Nonempty := hs_ne
    rw [compl_univ, inter_empty] at this
    exact Set.not_nonempty_empty this
  have hI_sub : ¬ (I_ideal ≤ nilradical A) := by
    intro H
    apply hI_ne
    apply eq_univ_of_forall
    intro p
    intro x hx
    have h_nil : IsNilpotent x := H hx
    cases' h_nil with n hn
    have h_pow_zero : x ^ n ∈ p.asIdeal := by rw [hn]; exact Ideal.zero_mem p.asIdeal
    clear hn
    revert h_pow_zero
    induction' n with n ih
    · intro h_pow_zero
      rw [pow_zero] at h_pow_zero
      have h_top : p.asIdeal = ⊤ := Ideal.eq_top_of_isUnit_mem p.asIdeal h_pow_zero isUnit_one
      exact False.elim (p.2.ne_top h_top)
    · intro h_pow_zero
      rw [pow_succ] at h_pow_zero
      cases' p.2.mem_or_mem h_pow_zero with hx_mem hpow
      · exact ih hx_mem
      · exact hpow
  have hJ_ne : zeroLocus (J_ideal : Set A) ≠ univ := by
    rw [PrimeSpectrum.zeroLocus_span]
    intro H
    rw [H] at ht_eq
    rw [ht_eq] at ht_ne
    have : (univ ∩ (univ : Set (PrimeSpectrum A))ᶜ).Nonempty := ht_ne
    rw [compl_univ, inter_empty] at this
    exact Set.not_nonempty_empty this
  have hJ_sub : ¬ (J_ideal ≤ nilradical A) := by
    intro H
    apply hJ_ne
    apply eq_univ_of_forall
    intro p
    intro x hx
    have h_nil : IsNilpotent x := H hx
    cases' h_nil with n hn
    have h_pow_zero : x ^ n ∈ p.asIdeal := by rw [hn]; exact Ideal.zero_mem p.asIdeal
    clear hn
    revert h_pow_zero
    induction' n with n ih
    · intro h_pow_zero
      rw [pow_zero] at h_pow_zero
      have h_top : p.asIdeal = ⊤ := Ideal.eq_top_of_isUnit_mem p.asIdeal h_pow_zero isUnit_one
      exact False.elim (p.2.ne_top h_top)
    · intro h_pow_zero
      rw [pow_succ] at h_pow_zero
      cases' p.2.mem_or_mem h_pow_zero with hx_mem hpow
      · exact ih hx_mem
      · exact hpow
  have h_mul_sub : ¬ (I_ideal * J_ideal ≤ nilradical A) := by
    intro H
    have : I_ideal ≤ nilradical A ∨ J_ideal ≤ nilradical A := h.mul_le.mp H
    cases' this with hI_le hJ_le
    · exact hI_sub hI_le
    · exact hJ_sub hJ_le
  have h_mul_ne : zeroLocus ((I_ideal * J_ideal : Ideal A) : Set A) ≠ univ := by
    intro H
    apply h_mul_sub
    intro x hx
    have h_nil_mem : x ∈ nilradical A := by
      have H2 : (⟨nilradical A, h⟩ : PrimeSpectrum A) ∈ zeroLocus ((I_ideal * J_ideal : Ideal A) : Set A) := by
        rw [H]
        exact Set.mem_univ _
      exact H2 hx
    exact h_nil_mem
  have h_union : zeroLocus I ∪ zeroLocus J ≠ univ := by
    intro H
    apply h_mul_ne
    apply Set.ext
    intro p
    constructor
    · intro _
      exact Set.mem_univ p
    · intro hp
      have H2 : p ∈ zeroLocus I ∪ zeroLocus J := by rw [H]; exact Set.mem_univ p
      cases' H2 with hI_mem hJ_mem
      · intro x hx
        have hx_ideal : x ∈ I_ideal := Ideal.mul_le_right hx
        rw [← PrimeSpectrum.zeroLocus_span] at hI_mem
        exact hI_mem hx_ideal
      · intro x hx
        have hx_ideal : x ∈ J_ideal := Ideal.mul_le_left hx
        rw [← PrimeSpectrum.zeroLocus_span] at hJ_mem
        exact hJ_mem hx_ideal
  have hs_inter_t : (s ∩ t) = (zeroLocus I ∪ zeroLocus J)ᶜ := by
    rw [hs_eq, ht_eq, Set.compl_union]
  rw [hs_inter_t]
  have h_nonempty : (zeroLocus I ∪ zeroLocus J)ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    exact h_union
  have h_univ_inter : univ ∩ (zeroLocus I ∪ zeroLocus J)ᶜ = (zeroLocus I ∪ zeroLocus J)ᶜ := Set.univ_inter _
  rw [h_univ_inter]
  exact h_nonempty

lemma irred_of_nilradical_prime {A : Type _} [CommRing A] (h : (nilradical A).IsPrime) :
  IrreducibleSpace (PrimeSpectrum A) := by
  have h_bot : (0:A) ≠ 1 := by
    intro h_eq
    have h1 : (1:A) ∈ nilradical A := by rw [←h_eq]; exact Ideal.zero_mem (nilradical A)
    have h_top : nilradical A = ⊤ := Ideal.eq_top_of_isUnit_mem (nilradical A) h1 isUnit_one
    exact Ideal.IsPrime.ne_top h h_top
  haveI : Nontrivial A := nontrivial_of_ne 0 1 h_bot
  exact {
    toNonempty := inferInstance
    isPreirreducible_univ := preirred_univ_of_nilradical_prime h
  }

lemma nilradical_prime_iff {A : Type _} [CommRing A] :
  (nilradical A).IsPrime ↔ (¬ IsNilpotent (1 : A)) ∧
    (∀ x y : A, IsNilpotent (x * y) → IsNilpotent x ∨ IsNilpotent y) := by
  constructor
  · intro h
    constructor
    · intro h1
      have h1' : (1:A) ∈ nilradical A := h1
      have h_top : nilradical A = ⊤ := Ideal.eq_top_of_isUnit_mem (nilradical A) h1' isUnit_one
      have h_ne_top : nilradical A ≠ ⊤ := Ideal.IsPrime.ne_top h
      exact h_ne_top h_top
    · intro x y hxy
      exact Ideal.IsPrime.mem_or_mem h hxy
  · intro h
    apply Ideal.IsPrime.mk
    · intro h_top
      have h1 : (1:A) ∈ nilradical A := by rw [h_top]; trivial
      exact h.1 h1
    · intro x y hxy
      exact h.2 x y hxy

lemma nilradical_prime_of_equiv {A B : Type _} [CommRing A] [CommRing B]
  (e : A ≃+* B) (h : (nilradical B).IsPrime) : (nilradical A).IsPrime := by
  apply nilradical_prime_iff.mpr
  have h_B := nilradical_prime_iff.mp h
  constructor
  · intro h_nil
    have h_nil_e : IsNilpotent (e 1) := by
      cases' h_nil with n hn
      use n
      rw [← map_pow, hn, map_zero]
    rw [map_one] at h_nil_e
    exact h_B.1 h_nil_e
  · intro x y h_nil
    have h_nil_e : IsNilpotent (e x * e y) := by
      cases' h_nil with n hn
      use n
      rw [← map_mul, ← map_pow, hn, map_zero]
    have h_cases := h_B.2 (e x) (e y) h_nil_e
    cases' h_cases with hx hy
    · left
      cases' hx with n hn
      use n
      have he_inv := congr_arg e.symm hn
      rw [map_zero, ← map_pow, RingEquiv.symm_apply_apply] at he_inv
      exact he_inv
    · right
      cases' hy with n hn
      use n
      have he_inv := congr_arg e.symm hn
      rw [map_zero, ← map_pow, RingEquiv.symm_apply_apply] at he_inv
      exact he_inv

lemma nilradical_prime_of_irreducibleSpace {A : Type _} [CommRing A] [IrreducibleSpace (PrimeSpectrum A)] : (nilradical A).IsPrime := by
  apply nilradical_prime_iff.mpr
  constructor
  · intro h_nil
    have h_empty : (univ : Set (PrimeSpectrum A)) = ∅ := by
      ext p
      constructor
      · intro hp
        have h_one : IsNilpotent (1 : A) := h_nil
        cases' h_one with n hn
        have h_pow_zero : (1 : A) ^ n ∈ p.asIdeal := by rw [hn]; exact Ideal.zero_mem p.asIdeal
        clear hn
        revert h_pow_zero
        induction' n with n ih
        · intro h_pow_zero
          rw [pow_zero] at h_pow_zero
          have h_top : p.asIdeal = ⊤ := Ideal.eq_top_of_isUnit_mem p.asIdeal h_pow_zero isUnit_one
          exact False.elim (p.2.ne_top h_top)
        · intro h_pow_zero
          rw [pow_succ] at h_pow_zero
          cases' p.2.mem_or_mem h_pow_zero with hx_mem hpow
          · exact ih hx_mem
          · have h_top : p.asIdeal = ⊤ := Ideal.eq_top_of_isUnit_mem p.asIdeal hpow isUnit_one
            exact False.elim (p.2.ne_top h_top)
      · intro hp
        exact False.elim hp
    have h_univ_nonempty : (univ : Set (PrimeSpectrum A)).Nonempty := Set.univ_nonempty
    have h_contra : False := by
      rw [h_empty] at h_univ_nonempty
      exact Set.not_nonempty_empty h_univ_nonempty
    exact h_contra
  · intro x y h_nil
    have h_union : zeroLocus {x} ∪ zeroLocus {y} = univ := by
      ext p
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      have hxy_nil : IsNilpotent (x * y) := h_nil
      cases' hxy_nil with n hn
      have h_pow_zero : (x * y) ^ n ∈ p.asIdeal := by rw [hn]; exact p.asIdeal.zero_mem
      have hp_xy : x * y ∈ p.asIdeal := by
        clear hn
        revert h_pow_zero
        generalize hxy : x * y = z
        intro h_pow_zero
        induction' n with n ih
        · rw [pow_zero] at h_pow_zero
          have h_top : p.asIdeal = ⊤ := Ideal.eq_top_of_isUnit_mem p.asIdeal h_pow_zero isUnit_one
          exact False.elim (p.2.ne_top h_top)
        · rw [pow_succ] at h_pow_zero
          cases' p.2.mem_or_mem h_pow_zero with hx_mem hpow
          · exact ih hx_mem
          · exact hpow
      cases' p.2.mem_or_mem hp_xy with hx hy
      · left
        exact Set.singleton_subset_iff.mpr hx
      · right
        exact Set.singleton_subset_iff.mpr hy
    have h_open_x : IsOpen ((zeroLocus {x})ᶜ) := (PrimeSpectrum.isClosed_zeroLocus {x}).isOpen_compl
    have h_open_y : IsOpen ((zeroLocus {y})ᶜ) := (PrimeSpectrum.isClosed_zeroLocus {y}).isOpen_compl
    have h_inter_empty : (zeroLocus {x})ᶜ ∩ (zeroLocus {y})ᶜ = ∅ := by
      rw [← Set.compl_union, h_union, Set.compl_univ]
    have h_preirred : IsPreirreducible (univ : Set (PrimeSpectrum A)) := PreirreducibleSpace.isPreirreducible_univ
    have h_or : (zeroLocus {x})ᶜ = ∅ ∨ (zeroLocus {y})ᶜ = ∅ := by
      by_contra h_not_or
      push_neg at h_not_or
      have hx_ne : (univ ∩ (zeroLocus {x})ᶜ).Nonempty := by
        rw [Set.univ_inter]
        exact h_not_or.1
      have hy_ne : (univ ∩ (zeroLocus {y})ᶜ).Nonempty := by
        rw [Set.univ_inter]
        exact h_not_or.2
      have h_inter_ne := h_preirred ((zeroLocus {x})ᶜ) ((zeroLocus {y})ᶜ) h_open_x h_open_y hx_ne hy_ne
      rw [h_inter_empty, Set.inter_empty] at h_inter_ne
      exact Set.not_nonempty_empty h_inter_ne
    have h_cases : IsNilpotent x ∨ IsNilpotent y := by
      cases' h_or with hx hy
      · left
        have hz : zeroLocus ({x} : Set A) = univ := by
          rw [← Set.compl_empty_iff]
          exact hx
        have hz_span : zeroLocus ((Ideal.span ({x} : Set A)) : Set A) = univ := by
          rw [PrimeSpectrum.zeroLocus_span]
          exact hz
        have h_van : PrimeSpectrum.vanishingIdeal (zeroLocus ((Ideal.span ({x} : Set A)) : Set A)) = PrimeSpectrum.vanishingIdeal (univ : Set (PrimeSpectrum A)) := by rw [hz_span]
        have h_rad : PrimeSpectrum.vanishingIdeal (zeroLocus ((Ideal.span ({x} : Set A)) : Set A)) = (Ideal.span ({x} : Set A)).radical := PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical (Ideal.span ({x} : Set A))
        have h_van_univ : PrimeSpectrum.vanishingIdeal (univ : Set (PrimeSpectrum A)) = nilradical A := PrimeSpectrum.vanishingIdeal_univ
        have hx_mem : x ∈ (Ideal.span ({x} : Set A)).radical := by
          have h1 : x ∈ Ideal.span ({x} : Set A) := Ideal.mem_span_singleton_self x
          exact Ideal.le_radical h1
        have hx_nil : x ∈ nilradical A := by
          rw [← h_van_univ, ← h_van, h_rad]
          exact hx_mem
        exact hx_nil
      · right
        have hz : zeroLocus ({y} : Set A) = univ := by
          rw [← Set.compl_empty_iff]
          exact hy
        have hz_span : zeroLocus ((Ideal.span ({y} : Set A)) : Set A) = univ := by
          rw [PrimeSpectrum.zeroLocus_span]
          exact hz
        have h_van : PrimeSpectrum.vanishingIdeal (zeroLocus ((Ideal.span ({y} : Set A)) : Set A)) = PrimeSpectrum.vanishingIdeal (univ : Set (PrimeSpectrum A)) := by rw [hz_span]
        have h_rad : PrimeSpectrum.vanishingIdeal (zeroLocus ((Ideal.span ({y} : Set A)) : Set A)) = (Ideal.span ({y} : Set A)).radical := PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical (Ideal.span ({y} : Set A))
        have h_van_univ : PrimeSpectrum.vanishingIdeal (univ : Set (PrimeSpectrum A)) = nilradical A := PrimeSpectrum.vanishingIdeal_univ
        have hy_mem : y ∈ (Ideal.span ({y} : Set A)).radical := by
          have h1 : y ∈ Ideal.span ({y} : Set A) := Ideal.mem_span_singleton_self y
          exact Ideal.le_radical h1
        have hy_nil : y ∈ nilradical A := by
          rw [← h_van_univ, ← h_van, h_rad]
          exact hy_mem
        exact hy_nil
    exact h_cases

lemma isPrime_nilradical_of_colimit_like {ι : Type _} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (A : ι → Type _) [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h => f i j h)]
    (h_prime : ∀ i, (nilradical (A i)).IsPrime)
    (Alim : Type _) [CommRing Alim]
    (F : ∀ i, A i →+* Alim)
    (h_comp : ∀ i j h x, F j (f i j h x) = F i x)
    (h_surj : ∀ x : Alim, ∃ i, ∃ x_i : A i, F i x_i = x)
    (h_eq_zero : ∀ i, ∀ x_i : A i, F i x_i = 0 → ∃ j, ∃ h : i ≤ j, f i j h x_i = 0) :
    (nilradical Alim).IsPrime := by
  have h_ne_top : nilradical Alim ≠ ⊤ := by
    intro h_top
    have h_one : (1 : Alim) ∈ nilradical Alim := by rw [h_top]; exact Submodule.mem_top
    have h_one_nil : IsNilpotent (1 : Alim) := h_one
    cases' h_one_nil with n hn
    have hn_one : (1 : Alim) = 0 := by
      calc (1:Alim) = (1:Alim) ^ n := by rw [one_pow]
           _ = 0 := hn
    have h_one_surj : ∃ i, ∃ x_i : A i, F i x_i = 1 := h_surj 1
    rcases h_one_surj with ⟨i, x_i, h_xi⟩
    have F_i_one : F i 1 = 0 := by rw [map_one, hn_one]
    have h_eq : ∃ j, ∃ h : i ≤ j, f i j h 1 = 0 := h_eq_zero i 1 F_i_one
    rcases h_eq with ⟨j, hij, hj⟩
    have f_one : f i j hij 1 = 1 := map_one _
    rw [f_one] at hj
    have h_prime_j : (nilradical (A j)).IsPrime := h_prime j
    have h_top_j : nilradical (A j) = ⊤ := Ideal.eq_top_of_isUnit_mem _ (by rw [hj]; exact Ideal.zero_mem _) isUnit_one
    exact h_prime_j.ne_top h_top_j
  have h_mem : ∀ x y : Alim, x * y ∈ nilradical Alim → x ∈ nilradical Alim ∨ y ∈ nilradical Alim := by
    intro x y hxy
    have hx_surj := h_surj x
    have hy_surj := h_surj y
    rcases hx_surj with ⟨ix, x_i, hxi⟩
    rcases hy_surj with ⟨iy, y_i, hyi⟩
    rcases directed_of (· ≤ ·) ix iy with ⟨k, hkx, hky⟩
    let x_k := f ix k hkx x_i
    let y_k := f iy k hky y_i
    have hxk_map : F k x_k = x := by rw [h_comp, hxi]
    have hyk_map : F k y_k = y := by rw [h_comp, hyi]
    have hxy_map : F k (x_k * y_k) = x * y := by rw [map_mul, hxk_map, hyk_map]
    have hxy_nil : IsNilpotent (x * y) := hxy
    cases' hxy_nil with n hn
    have h_pow : F k ((x_k * y_k) ^ n) = 0 := by rw [map_pow, hxy_map, hn]
    have h_eq := h_eq_zero k ((x_k * y_k) ^ n) h_pow
    rcases h_eq with ⟨j, hkj, hj⟩
    have hj_pow : (f k j hkj (x_k * y_k)) ^ n = 0 := by rw [← map_pow, hj]
    have hj_nil : IsNilpotent (f k j hkj x_k * f k j hkj y_k) := by
      exact ⟨n, by rw [← map_mul]; exact hj_pow⟩
    have h_prime_j := h_prime j
    cases' h_prime_j.mem_or_mem hj_nil with hx_nil hy_nil
    · left
      have hx_is_nil : IsNilpotent (f k j hkj x_k) := hx_nil
      cases' hx_is_nil with m hm
      have hx_nil_Alim : IsNilpotent x := by
        use m
        have : x ^ m = F j ((f k j hkj x_k) ^ m) := by
          rw [map_pow]
          have : F j (f k j hkj x_k) = x := by rw [h_comp, hxk_map]
          rw [this]
        rw [this, hm, map_zero]
      exact hx_nil_Alim
    · right
      have hy_is_nil : IsNilpotent (f k j hkj y_k) := hy_nil
      cases' hy_is_nil with m hm
      have hy_nil_Alim : IsNilpotent y := by
        use m
        have : y ^ m = F j ((f k j hkj y_k) ^ m) := by
          rw [map_pow]
          have : F j (f k j hkj y_k) = y := by rw [h_comp, hyk_map]
          rw [this]
        rw [this, hm, map_zero]
      exact hy_nil_Alim
  exact ⟨h_ne_top, fun {x y} h => h_mem x y h⟩

universe u_1 u_2 u_3

noncomputable def tensor_finsupp_equiv {k ι M : Type _} [Field k] [AddCommGroup M] [Module k M] [DecidableEq ι] :
  M ⊗[k] (ι →₀ k) ≃ₗ[k] ι →₀ M :=
  (TensorProduct.finsuppRight k k M k ι).trans (Finsupp.mapRange.linearEquiv (TensorProduct.rid k M))

noncomputable def tensor_basis_equiv {k M k' : Type _} [Field k] [AddCommGroup M] [Module k M] [Field k'] [Algebra k k'] :
    M ⊗[k] k' ≃ₗ[k] (Module.Basis.ofVectorSpaceIndex k k') →₀ M :=
  let b := Module.Basis.ofVectorSpace k k'
  let ι := Module.Basis.ofVectorSpaceIndex k k'
  letI : DecidableEq ι := Classical.decEq ι
  (TensorProduct.congr (LinearEquiv.refl k M) b.repr).trans tensor_finsupp_equiv

lemma map_tensor_basis_equiv {k M M' k' : Type _} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] [Field k'] [Algebra k k']
    (f : M →ₗ[k] M') (x : M ⊗[k] k') :
    tensor_basis_equiv (TensorProduct.map f LinearMap.id x) = Finsupp.mapRange.linearMap f (tensor_basis_equiv x) := by
  ext
  induction x with| zero=>bound| tmul=>_| add=>simp_all
  norm_num[tensor_basis_equiv]
  norm_num[tensor_finsupp_equiv]

lemma tensor_mem_range_of_finset {k : Type u} [Field k] {G : Type (max u v)} [CommRing G] [Algebra k G]
    {k' : Type (max u v w)} [Field k'] [Algebra k k'] (x : G ⊗[k] k') :
    ∃ (s : Finset k'), ∀ (F : Type u) [Field F] [Algebra k F] (f : F →ₐ[k] k'),
      (∀ c ∈ s, c ∈ LinearMap.range f.toLinearMap) →
      x ∈ AlgHom.range (Algebra.TensorProduct.map (AlgHom.id k G) f) := by
  letI := Classical.decEq k'
  induction x using TensorProduct.induction_on with
  | zero =>
    use ∅
    intro F _ _ f h
    exact ⟨0, map_zero _⟩
  | tmul g c =>
    use {c}
    intro F _ _ f h
    have hc : c ∈ LinearMap.range f.toLinearMap := h c (Finset.mem_singleton_self c)
    rcases hc with ⟨c0, hc0⟩
    use g ⊗ₜ[k] c0
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    have h_f : f c0 = c := hc0
    rw [h_f]
  | add x y hx hy =>
    rcases hx with ⟨sx, hx⟩
    rcases hy with ⟨sy, hy⟩
    use sx ∪ sy
    intro F _ _ f h
    have hx_mem := hx F f (fun c hc => h c (Finset.mem_union_left sy hc))
    have hy_mem := hy F f (fun c hc => h c (Finset.mem_union_right sx hc))
    rcases hx_mem with ⟨x0, hx0⟩
    rcases hy_mem with ⟨y0, hy0⟩
    use x0 + y0
    rw [map_add, hx0, hy0]

lemma finset_subfield_equiv {k : Type u} [Field k] {k' : Type w} [Field k'] [Algebra k k'] (s : Finset k') :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra k F) (f : F →ₐ[k] k'),
      ∀ x ∈ s, x ∈ (LinearMap.range f.toLinearMap) := by
  let e := Fintype.equivFin s
  let P := MvPolynomial (Fin (Fintype.card s)) k
  let ev : P →ₐ[k] k' := MvPolynomial.aeval (fun i => (e.symm i).1)
  let p := RingHom.ker ev.toRingHom
  have hp : p.IsPrime := RingHom.ker_isPrime ev.toRingHom
  let A := P ⧸ p
  haveI : IsDomain A := Ideal.Quotient.isDomain p
  let F := FractionRing A
  let ev_quot : A →+* k' := RingHom.kerLift ev.toRingHom
  have h_inj : Function.Injective ev_quot := RingHom.kerLift_injective ev.toRingHom
  let f_ring : F →+* k' := IsFractionRing.lift h_inj
  have h_comm : ∀ r : k, f_ring (algebraMap k F r) = algebraMap k k' r := by
    intro r
    have h1 : algebraMap k F r = algebraMap A F (algebraMap k A r) := rfl
    rw [h1]
    have h2 : f_ring (algebraMap A F (algebraMap k A r)) = ev_quot (algebraMap k A r) := IsFractionRing.lift_algebraMap h_inj (algebraMap k A r)
    rw [h2]
    have h3 : ev_quot (algebraMap k A r) = ev.toRingHom (algebraMap k P r) := by rfl
    rw [h3]
    exact AlgHom.commutes ev r
  let f_alg : F →ₐ[k] k' := AlgHom.mk f_ring h_comm
  use F, inferInstance, inferInstance, f_alg
  intro x hx
  use algebraMap A F (Ideal.Quotient.mk p (MvPolynomial.X (e ⟨x, hx⟩)))
  change f_alg _ = x
  have h1 : f_alg (algebraMap A F (Ideal.Quotient.mk p (MvPolynomial.X (e ⟨x, hx⟩)))) = f_ring (algebraMap A F (Ideal.Quotient.mk p (MvPolynomial.X (e ⟨x, hx⟩)))) := rfl
  rw [h1]
  have h2 : f_ring (algebraMap A F (Ideal.Quotient.mk p (MvPolynomial.X (e ⟨x, hx⟩)))) = ev_quot (Ideal.Quotient.mk p (MvPolynomial.X (e ⟨x, hx⟩))) := IsFractionRing.lift_algebraMap h_inj _
  rw [h2]
  have h3 : ev_quot (Ideal.Quotient.mk p (MvPolynomial.X (e ⟨x, hx⟩))) = ev (MvPolynomial.X (e ⟨x, hx⟩)) := rfl
  rw [h3]
  have h4 : ev (MvPolynomial.X (e ⟨x, hx⟩)) = (e.symm (e ⟨x, hx⟩)).1 := MvPolynomial.aeval_X _ _
  rw [h4]
  have h5 : e.symm (e ⟨x, hx⟩) = ⟨x, hx⟩ := Equiv.symm_apply_apply e ⟨x, hx⟩
  rw [h5]

def uliftRingEquiv {R : Type u} [CommRing R] : R ≃+* ULift.{v, u} R :=
  { Equiv.ulift.symm with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

def SmallFieldLift (F : Type u_1) := ULift.{u_2, u_1} F

instance {F : Type u_1} [CommRing F] : CommRing (SmallFieldLift F) :=
  Equiv.ulift.commRing

instance {F : Type u_1} [Field F] : Field (SmallFieldLift F) :=
  Equiv.ulift.field

instance {k : Type u_1} [Field k] {F : Type u_1} [Field F] [Algebra k F] : Algebra k (SmallFieldLift F) :=
  RingHom.toAlgebra ((uliftRingEquiv.{u_1, u_2} (R := F)).toRingHom.comp (algebraMap k F))

lemma geom_irred_universe_lift_one {k : Type u_1} [Field k] {G : Type (max u_1 u_2)} [CommRing G] [Algebra k G]
    (h : GeometricallyIrreducibleAlgebra k G)
    (k' : Type (max u_1 u_2 u_3)) [Field k'] [Algebra k k'] :
    ¬ IsNilpotent (1 : G ⊗[k] k') := by
  intro h_nil
  obtain ⟨n, hn⟩ := h_nil
  have h_eq_zero : (1 : G ⊗[k] k') = 0 := by
    calc (1 : G ⊗[k] k') = 1 ^ n := by rw [one_pow]
      _ = 0 := hn
  have h_prime_k : IrreducibleSpace (PrimeSpectrum (G ⊗[k] SmallFieldLift k)) := h.out (SmallFieldLift k)
  haveI : Nonempty (PrimeSpectrum (G ⊗[k] SmallFieldLift k)) := h_prime_k.toNonempty
  have h2 : (1 : G ⊗[k] SmallFieldLift k) ≠ 0 := by
    intro h0
    have h_contra : False := by
      have h_nonempty : Nonempty (PrimeSpectrum (G ⊗[k] SmallFieldLift k)) := inferInstance
      rcases h_nonempty with ⟨p⟩
      have h_prime := p.2
      have h_ne_top := h_prime.ne_top
      have h1 : (1 : G ⊗[k] SmallFieldLift k) ∈ p.asIdeal := by
        rw [h0]
        exact Ideal.zero_mem _
      have h_top2 : p.asIdeal = ⊤ := Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one
      exact h_ne_top h_top2
    exact h_contra
  haveI : Nontrivial (G ⊗[k] SmallFieldLift k) := nontrivial_of_ne 0 1 h2.symm
  have h4 : (1 : G) ≠ 0 := by
    intro h0
    have h_one_tens : (1 : G ⊗[k] SmallFieldLift k) = 1 ⊗ₜ[k] 1 := rfl
    have h_one_tens_zero : (1 : G ⊗[k] SmallFieldLift k) = 0 := by
      rw [h_one_tens]
      have h0_tens : (1 : G) ⊗ₜ[k] (1 : SmallFieldLift k) = (0 : G) ⊗ₜ[k] 1 := by rw [h0]
      rw [h0_tens, TensorProduct.zero_tmul]
    exact h2 h_one_tens_zero
  haveI : Nontrivial G := nontrivial_of_ne 0 1 h4.symm
  have h_ne : (1 : G ⊗[k] k') ≠ 0 := by
    intro H
    have H2 : (1 : G) ⊗ₜ[k] (1 : k') = (0 : G ⊗[k] k') := by
      calc (1 : G) ⊗ₜ[k] (1 : k') = (1 : G ⊗[k] k') := rfl
        _ = 0 := H
    have h_bot_k' : (0 : k') ≠ 1 := zero_ne_one
    haveI : Nontrivial k' := nontrivial_of_ne 0 1 h_bot_k'
    haveI : Nontrivial (G ⊗[k] k') := inferInstance
    have h_bot_tens : (0 : G ⊗[k] k') ≠ 1 := zero_ne_one
    exact h_bot_tens H.symm
  exact h_ne h_eq_zero

lemma nilradical_prime_of_directed_colimit_tensor
    {k : Type u_1} [Field k]
    (ι : Type u_3) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type (max u_1 u_2)) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
    (f : ∀ i j, i ≤ j → G i →ₐ[k] G j)
    [DirectedSystem G (fun i j h => f i j h)]
    [Algebra k (Ring.DirectLimit G fun i j h => f i j h)]
    (k' : Type (max u_1 u_2 u_3)) [Field k'] [Algebra k k']
    (h_prime : ∀ j, (nilradical (G j ⊗[k] k')).IsPrime)
    (halg : algebraMap k (Ring.DirectLimit G fun i j h => f i j h) = RingHom.comp (Ring.DirectLimit.of G (fun i j h => f i j h) (Classical.arbitrary ι)) (algebraMap k (G (Classical.arbitrary ι)))) :
    (nilradical ((Ring.DirectLimit G fun i j h => f i j h) ⊗[k] k')).IsPrime := by
  let A (i : ι) := G i ⊗[k] k'
  let f_tens_alg (i j : ι) (h : i ≤ j) : A i →ₐ[k] A j :=
    Algebra.TensorProduct.map (f i j h) (AlgHom.id k k')
  let f_tens (i j : ι) (h : i ≤ j) : A i →+* A j :=
    (f_tens_alg i j h).toRingHom
  have instDir : DirectedSystem A (fun i j h => f_tens i j h) := by
    let instG := inferInstanceAs (DirectedSystem G (fun i j h => f i j h))
    constructor
    · intro i x
      have H_lin : (f_tens_alg i i (le_refl i)).toLinearMap = (AlgHom.id k (A i)).toLinearMap := by
        apply TensorProduct.ext'
        intro a b
        have h_self : (fun (i j : ι) (h : i ≤ j) => f i j h) i i (le_refl i) a = a := by apply DirectedSystem.map_self'
        change (f i i (le_refl i) a) ⊗ₜ[k] b = a ⊗ₜ[k] b
        rw [h_self]
      have H : f_tens_alg i i (le_refl i) = AlgHom.id k (A i) := AlgHom.ext (fun y => LinearMap.congr_fun H_lin y)
      exact AlgHom.congr_fun H x
    · intro i j k_idx hkj hji x
      have H_lin : (f_tens_alg j i hji).toLinearMap.comp (f_tens_alg k_idx j hkj).toLinearMap = (f_tens_alg k_idx i (le_trans hkj hji)).toLinearMap := by
        apply TensorProduct.ext'
        intro a b
        have h_map : (fun (i j : ι) (h : i ≤ j) => f i j h) j i hji ((fun (i j : ι) (h : i ≤ j) => f i j h) k_idx j hkj a) = (fun (i j : ι) (h : i ≤ j) => f i j h) k_idx i (le_trans hkj hji) a := by apply DirectedSystem.map_map'
        change (f j i hji (f k_idx j hkj a)) ⊗ₜ[k] b = (f k_idx i (le_trans hkj hji) a) ⊗ₜ[k] b
        rw [h_map]
      have H : (f_tens_alg j i hji).comp (f_tens_alg k_idx j hkj) = f_tens_alg k_idx i (le_trans hkj hji) := AlgHom.ext (fun y => LinearMap.congr_fun H_lin y)
      exact AlgHom.congr_fun H x
  let Alim := (Ring.DirectLimit G (fun i j h => f i j h)) ⊗[k] k'
  let of_alg (i : ι) : G i →ₐ[k] Ring.DirectLimit G (fun i j h => f i j h) :=
    { toRingHom := Ring.DirectLimit.of G (fun i j h => f i j h) i
      commutes' := fun r => by
        let i0 := Classical.arbitrary ι
        rcases directed_of (· ≤ ·) i i0 with ⟨l, hil, hi0l⟩
        have h1 : Ring.DirectLimit.of G (fun i j h => f i j h) i (algebraMap k (G i) r) = Ring.DirectLimit.of G (fun i j h => f i j h) l (f i l hil (algebraMap k (G i) r)) :=
          (Ring.DirectLimit.of_f hil (algebraMap k (G i) r)).symm
        have h2 : Ring.DirectLimit.of G (fun i j h => f i j h) i0 (algebraMap k (G i0) r) = Ring.DirectLimit.of G (fun i j h => f i j h) l (f i0 l hi0l (algebraMap k (G i0) r)) :=
          (Ring.DirectLimit.of_f hi0l (algebraMap k (G i0) r)).symm
        have f1 : f i l hil (algebraMap k (G i) r) = algebraMap k (G l) r := AlgHom.commutes _ _
        have f2 : f i0 l hi0l (algebraMap k (G i0) r) = algebraMap k (G l) r := AlgHom.commutes _ _
        rw [f1] at h1
        rw [f2] at h2
        have h_rhs : (algebraMap k (Ring.DirectLimit G fun i j h => f i j h)) r = Ring.DirectLimit.of G (fun i j h => f i j h) i0 (algebraMap k (G i0) r) := by
          rw [halg]
          rfl
        exact h1.trans (h2.symm.trans h_rhs.symm) }
  let F (i : ι) : A i →+* Alim :=
    (Algebra.TensorProduct.map (of_alg i) (AlgHom.id k k')).toRingHom
  have h_comp : ∀ i j h x, F j (f_tens i j h x) = F i x := by
    intro i j h x
    have H_lin : ((Algebra.TensorProduct.map (of_alg j) (AlgHom.id k k')).comp (f_tens_alg i j h)).toLinearMap = (Algebra.TensorProduct.map (of_alg i) (AlgHom.id k k')).toLinearMap := by
      apply TensorProduct.ext'
      intro a b
      change (of_alg j (f i j h a)) ⊗ₜ[k] b = (of_alg i a) ⊗ₜ[k] b
      have H_of : Ring.DirectLimit.of G (fun i j h => f i j h) j (f i j h a) = Ring.DirectLimit.of G (fun i j h => f i j h) i a := Ring.DirectLimit.of_f h a
      change (Ring.DirectLimit.of G (fun i j h => f i j h) j (f i j h a)) ⊗ₜ[k] b = (Ring.DirectLimit.of G (fun i j h => f i j h) i a) ⊗ₜ[k] b
      rw [H_of]
    have H : (Algebra.TensorProduct.map (of_alg j) (AlgHom.id k k')).comp (f_tens_alg i j h) = Algebra.TensorProduct.map (of_alg i) (AlgHom.id k k') := AlgHom.ext (fun y => LinearMap.congr_fun H_lin y)
    exact AlgHom.congr_fun H x
  have h_surj : ∀ x : Alim, ∃ i, ∃ x_i : A i, F i x_i = x := by
    intro x
    induction' x using TensorProduct.induction_on with a b x y hx hy
    · use Classical.arbitrary ι
      use 0
      simp only [map_zero]
    · have ha := Ring.DirectLimit.exists_of a
      rcases ha with ⟨i, a_i, hai⟩
      use i
      use a_i ⊗ₜ[k] b
      change (Ring.DirectLimit.of G (fun i j h => f i j h) i a_i) ⊗ₜ[k] b = a ⊗ₜ[k] b
      rw [hai]
    · rcases hx with ⟨ix, x_i, hxi⟩
      rcases hy with ⟨iy, y_i, hyi⟩
      rcases directed_of (· ≤ ·) ix iy with ⟨k_idx, hxk, hyk⟩
      use k_idx
      use f_tens ix k_idx hxk x_i + f_tens iy k_idx hyk y_i
      rw [map_add]
      have h1 : F k_idx (f_tens ix k_idx hxk x_i) = x := by rw [h_comp, hxi]
      have h2 : F k_idx (f_tens iy k_idx hyk y_i) = y := by rw [h_comp, hyi]
      rw [h1, h2]
  have h_eq_zero : ∀ i, ∀ x_i : A i, F i x_i = 0 → ∃ j, ∃ h : i ≤ j, f_tens i j h x_i = 0 := by
    intro i x_i hx
    let of_lin : G i →ₗ[k] Ring.DirectLimit G fun i j h => f i j h := (of_alg i).toLinearMap
    have h_lin : (TensorProduct.map of_lin LinearMap.id) x_i = 0 := by exact hx
    have h_eq := congr_arg (tensor_basis_equiv (k := k) (M := Ring.DirectLimit G fun i j h => f i j h) (k' := k')) h_lin
    rw [map_zero, map_tensor_basis_equiv] at h_eq
    let v := tensor_basis_equiv x_i
    have h_vanish : ∀ s ∈ v.support, of_lin (v s) = 0 := by
      intro s _
      have h_eval := DFunLike.congr_fun h_eq s
      change of_lin (v s) = (0 : _ →₀ _) s at h_eval
      rw [Finsupp.coe_zero, Pi.zero_apply] at h_eval
      exact h_eval
    have h_exact : ∀ s ∈ v.support, ∃ j, ∃ h : i ≤ j, f i j h (v s) = 0 := by
      intro s hs
      have h_zero : Ring.DirectLimit.of G (fun i j h => f i j h) i (v s) = 0 := h_vanish s hs
      exact Ring.DirectLimit.of.zero_exact h_zero
    have h_bound : ∃ j_max, ∃ h_max : i ≤ j_max, ∀ s ∈ v.support, f i j_max h_max (v s) = 0 := by
      revert h_exact
      letI := Classical.decEq (Module.Basis.ofVectorSpaceIndex k k')
      refine Finset.induction_on v.support ?_ ?_
      · intro _
        use i, le_refl i
        intro s hs
        exfalso
        revert hs
        simp
      · intro a S ha ih h_ex
        have h_ex_S : ∀ s ∈ S, ∃ j, ∃ h : i ≤ j, f i j h (v s) = 0 := fun s hs => h_ex s (Finset.mem_insert_of_mem hs)
        rcases ih h_ex_S with ⟨jS, hjS, hS⟩
        rcases h_ex a (Finset.mem_insert_self a S) with ⟨ja, hja, ha_zero⟩
        rcases directed_of (· ≤ ·) jS ja with ⟨j_max, hjS_max, hja_max⟩
        use j_max, le_trans hjS hjS_max
        intro s hs
        rw [Finset.mem_insert] at hs
        cases' hs with h_eq_s h_in
        · rw [h_eq_s]
          have h_map2 : f i j_max (le_trans hja hja_max) (v a) = f ja j_max hja_max (f i ja hja (v a)) := by exact (DirectedSystem.map_map' (fun i j h => f i j h) hja hja_max (v a)).symm
          rw [h_map2, ha_zero, map_zero]
        · have h_map : f i j_max (le_trans hjS hjS_max) (v s) = f jS j_max hjS_max (f i jS hjS (v s)) := by exact (DirectedSystem.map_map' (fun i j h => f i j h) hjS hjS_max (v s)).symm
          rw [h_map, hS s h_in, map_zero]
    rcases h_bound with ⟨j_max, h_max, hj_zero⟩
    use j_max, h_max
    have h_map_v : Finsupp.mapRange.linearMap (f i j_max h_max).toLinearMap v = 0 := by
      ext s
      have h_eval : (Finsupp.mapRange.linearMap (f i j_max h_max).toLinearMap v) s = (f i j_max h_max) (v s) := rfl
      rw [h_eval]
      have h_cases : s ∈ v.support ∨ s ∉ v.support := Classical.em _
      cases' h_cases with h_in h_out
      · rw [hj_zero s h_in]
        rfl
      · have h_out' : v s = 0 := by
          apply Classical.byContradiction
          intro h_neq
          have : s ∈ v.support := Finsupp.mem_support_iff.mpr h_neq
          exact h_out this
        rw [h_out', map_zero]
        rfl
    have h_map_tensor : tensor_basis_equiv (TensorProduct.map (f i j_max h_max).toLinearMap LinearMap.id x_i) = 0 := by
      rw [map_tensor_basis_equiv, h_map_v]
    have h_tensor_zero : TensorProduct.map (f i j_max h_max).toLinearMap LinearMap.id x_i = 0 := by
      have h_map_tensor2 : tensor_basis_equiv (TensorProduct.map (f i j_max h_max).toLinearMap LinearMap.id x_i) = tensor_basis_equiv 0 := by
        rw [h_map_tensor, map_zero]
      exact EquivLike.injective _ h_map_tensor2
    have h_lin_eq : ((f_tens_alg i j_max h_max).toLinearMap) x_i = (TensorProduct.map (f i j_max h_max).toLinearMap LinearMap.id) x_i := by
      have H_lin : ((f_tens_alg i j_max h_max).toLinearMap) = (TensorProduct.map (f i j_max h_max).toLinearMap LinearMap.id) := by
        apply TensorProduct.ext'
        intro g c
        rfl
      rw [H_lin]
    exact h_lin_eq.trans h_tensor_zero
  exact isPrime_nilradical_of_colimit_like A f_tens h_prime Alim F h_comp h_surj h_eq_zero

lemma geom_irred_universe_lift_prime {k : Type u_1} [Field k] {G : Type (max u_1 u_2)} [CommRing G] [Algebra k G]
    (h : GeometricallyIrreducibleAlgebra k G)
    (k' : Type (max u_1 u_2 u_3)) [Field k'] [Algebra k k']
    (x y : G ⊗[k] k') (h_nil : IsNilpotent (x * y)) :
    IsNilpotent x ∨ IsNilpotent y := by
  letI := Classical.decEq k'
  have hx := tensor_mem_range_of_finset x
  have hy := tensor_mem_range_of_finset y
  rcases hx with ⟨sx, hx⟩
  rcases hy with ⟨sy, hy⟩
  let s := sx ∪ sy
  have h_fin := finset_subfield_equiv (k := k) (k' := k') s
  rcases h_fin with ⟨K, hK_field, hK_alg, f, h_range⟩
  have hx_K := hx K f (fun c hc => h_range c (Finset.mem_union_left sy hc))
  have hy_K := hy K f (fun c hc => h_range c (Finset.mem_union_right sx hc))
  rcases hx_K with ⟨x0, hx0⟩
  rcases hy_K with ⟨y0, hy0⟩
  let f_tens : G ⊗[k] K →ₐ[k] G ⊗[k] k' := Algebra.TensorProduct.map (AlgHom.id k G) f
  have h_inj : Function.Injective f_tens := by
    have hf_inj : Function.Injective f.toRingHom := RingHom.injective f.toRingHom
    have hf_lin_inj : Function.Injective f.toLinearMap := hf_inj
    have hf_ker : f.toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.mpr hf_lin_inj
    rcases LinearMap.exists_leftInverse_of_injective f.toLinearMap hf_ker with ⟨g, hg⟩
    have h_comp : g.comp f.toLinearMap = LinearMap.id := hg
    have h_tens_comp : (TensorProduct.map (LinearMap.id : G →ₗ[k] G) g).comp (TensorProduct.map (LinearMap.id : G →ₗ[k] G) f.toLinearMap) = TensorProduct.map (LinearMap.id) (LinearMap.id) := by
      rw [← TensorProduct.map_comp, LinearMap.comp_id, h_comp]
    have h_tens_id : TensorProduct.map (LinearMap.id : G →ₗ[k] G) (LinearMap.id : K →ₗ[k] K) = LinearMap.id := TensorProduct.map_id
    rw [h_tens_id] at h_tens_comp
    intro a b hab
    have hab_lin : (TensorProduct.map (LinearMap.id : G →ₗ[k] G) f.toLinearMap) a = (TensorProduct.map (LinearMap.id : G →ₗ[k] G) f.toLinearMap) b := by exact hab
    have h_apply : (TensorProduct.map (LinearMap.id : G →ₗ[k] G) g) ((TensorProduct.map (LinearMap.id : G →ₗ[k] G) f.toLinearMap) a) =
                   (TensorProduct.map (LinearMap.id : G →ₗ[k] G) g) ((TensorProduct.map (LinearMap.id : G →ₗ[k] G) f.toLinearMap) b) := by rw [hab_lin]
    have h_comp_a : (TensorProduct.map (LinearMap.id : G →ₗ[k] G) g).comp (TensorProduct.map (LinearMap.id : G →ₗ[k] G) f.toLinearMap) a = a := by
      have H : (TensorProduct.map (LinearMap.id : G →ₗ[k] G) g).comp (TensorProduct.map (LinearMap.id : G →ₗ[k] G) f.toLinearMap) = LinearMap.id := h_tens_comp
      rw [H]
      rfl
    have h_comp_b : (TensorProduct.map (LinearMap.id : G →ₗ[k] G) g).comp (TensorProduct.map (LinearMap.id : G →ₗ[k] G) f.toLinearMap) b = b := by
      have H : (TensorProduct.map (LinearMap.id : G →ₗ[k] G) g).comp (TensorProduct.map (LinearMap.id : G →ₗ[k] G) f.toLinearMap) = LinearMap.id := h_tens_comp
      rw [H]
      rfl
    rw [← h_comp_a, ← h_comp_b]
    exact h_apply
  have h_nil_K : IsNilpotent (x0 * y0) := by
    cases' h_nil with n hn
    use n
    have h1 : f_tens ((x0 * y0) ^ n) = 0 := by
      rw [map_pow, map_mul]
      have h_x0 : f_tens x0 = x := hx0
      have h_y0 : f_tens y0 = y := hy0
      rw [h_x0, h_y0]
      exact hn
    have h2 : f_tens 0 = 0 := map_zero _
    have h3 : f_tens ((x0 * y0) ^ n) = f_tens 0 := by rw [h1, h2]
    exact h_inj h3
  let eK : K ≃ₐ[k] SmallFieldLift K :=
    { uliftRingEquiv.{u_1, u_2} (R := K) with
      commutes' := fun _ => rfl }
  let eTens : G ⊗[k] K ≃ₐ[k] G ⊗[k] SmallFieldLift K := Algebra.TensorProduct.congr (AlgEquiv.refl) eK
  have h_prime_lift : IrreducibleSpace (PrimeSpectrum (G ⊗[k] SmallFieldLift K)) := h.out (SmallFieldLift K)
  have h_prime_rad_lift : (nilradical (G ⊗[k] SmallFieldLift K)).IsPrime := nilradical_prime_of_irreducibleSpace
  have h_prime_rad_K : (nilradical (G ⊗[k] K)).IsPrime := nilradical_prime_of_equiv eTens.toRingEquiv h_prime_rad_lift
  have h_or_K : IsNilpotent x0 ∨ IsNilpotent y0 := (nilradical_prime_iff.mp h_prime_rad_K).2 x0 y0 h_nil_K
  cases' h_or_K with hx_nil hy_nil
  · left
    cases' hx_nil with n hn
    use n
    rw [← hx0, ← map_pow, hn, map_zero]
  · right
    cases' hy_nil with n hn
    use n
    rw [← hy0, ← map_pow, hn, map_zero]

lemma geom_irred_universe_lift {k : Type u_1} [Field k] {G : Type (max u_1 u_2)} [CommRing G] [Algebra k G]
    (h : GeometricallyIrreducibleAlgebra k G)
    (k' : Type (max u_1 u_2 u_3)) [Field k'] [Algebra k k'] :
    (nilradical (G ⊗[k] k')).IsPrime := by
  apply nilradical_prime_iff.mpr
  constructor
  · exact geom_irred_universe_lift_one h k'
  · intro x y h_nil
    exact geom_irred_universe_lift_prime h k' x y h_nil

-- EVOLVE-BLOCK-END

theorem GeometricallyIrreducibleAlgebra.of_directed_colimit
    {k : Type u} [Field k]
    (ι : Type w) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type (max u v)) [∀ i, CommRing (G i)] [∀ i, Algebra k (G i)]
    (f : ∀ i j, i ≤ j → G i →ₐ[k] G j)
    [DirectedSystem G (fun i j h => f i j h)]
    (h_irred : ∀ j, GeometricallyIrreducibleAlgebra k (G j)) :
    @GeometricallyIrreducibleAlgebra k (Ring.DirectLimit G fun i j h => f i j h)
      _ _ (alg_dir_lim k ι G f) := by
  -- EVOLVE-BLOCK-START
  letI := alg_dir_lim k ι G f
  exact ⟨fun k' hk' hk'_alg => by
    have h1 : ∀ j, (nilradical (G j ⊗[k] k')).IsPrime := fun j =>
      geom_irred_universe_lift (h_irred j) k'
    have h2 := nilradical_prime_of_directed_colimit_tensor ι G f k' h1 rfl
    exact irred_of_nilradical_prime h2⟩
  -- EVOLVE-BLOCK-END
