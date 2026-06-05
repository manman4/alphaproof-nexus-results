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

universe u v


class IsSeparablyGenerated (k K : Type*) [Field k] [Field K] [Algebra k K] : Prop where
  out : ∃ (s : Set K), IsTranscendenceBasis k (fun x : s ↦ (x : K)) ∧
    Algebra.IsSeparable (IntermediateField.adjoin k s) K

-- EVOLVE-BLOCK-START
lemma isAlgebraic_intermediateField_adjoin_of_isTranscendenceBasis {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (s : Set K) (hs : IsTranscendenceBasis k (fun x : s ↦ (x : K))) :
    Algebra.IsAlgebraic (IntermediateField.adjoin k s) K := by
  rcases ↑hs
  use fun and=>by_contra (. ( ((‹∀ (x _),_ →_› :) (_) ?_ (Set.subset_insert and _)▸Set.mem_insert _ _).elim fun and p=>?_))
  · convert AlgebraicIndepOn.insert ..
    · use‹AlgebraicIndependent _ _›.to_subtype_range
    · use (by valid ∘(·.tower_top_of_subalgebra_le (Algebra.adjoin_le (by use fun and⟨ _, ⟨a, rfl⟩,C⟩=>IntermediateField.subset_adjoin _ _ (C▸a.2)))))
  · convert←isAlgebraic_algebraMap (⟨ _,IntermediateField.subset_adjoin _ _ and.2⟩:IntermediateField.adjoin k s)

lemma isSeparable_intermediateField_adjoin_of_isAlgebraic_charZero {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] [CharZero k]
    (s : Set K) (h_alg : Algebra.IsAlgebraic (IntermediateField.adjoin k s) K) :
    Algebra.IsSeparable (IntermediateField.adjoin k s) K := by
  use fun and => (minpoly.irreducible (@h_alg.1 _).isIntegral).separable

lemma exists_separablyGenerated_charZero {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] [CharZero k] :
    IsSeparablyGenerated k K := by
  have h_trans := exists_isTranscendenceBasis k K
  obtain ⟨s, hs⟩ := h_trans
  have h_alg := isAlgebraic_intermediateField_adjoin_of_isTranscendenceBasis s hs
  have h_sep := isSeparable_intermediateField_adjoin_of_isAlgebraic_charZero s h_alg
  exact ⟨s, hs, h_sep⟩

lemma charZero_finDim_K {K : Type v} [Field K] :
    FiniteDimensional K (ULift.{u} K) := by
  infer_instance

lemma charZero_pureInsep_K {K : Type v} [Field K] :
    IsPurelyInseparable K (ULift.{u} K) := by
  simp_rw [isPurelyInseparable_iff_pow_mem K ↑(ringExpChar K)]
  exact fun and=>by repeat constructor

lemma charZero_finDim_k_bot {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] :
    FiniteDimensional k (⊥ : IntermediateField k (ULift.{u} K)) := by
  infer_instance

lemma charZero_pureInsep_k_bot {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] :
    IsPurelyInseparable k (⊥ : IntermediateField k (ULift.{u} K)) := by
  apply inferInstance

lemma charZero_bot_charZero {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] [CharZero k] :
    CharZero (⊥ : IntermediateField k (ULift.{u} K)) := by
  exact add_zero 10 |>.dvd.elim fun and x => ⟨fun _ _ h => Nat.cast_injective ((algebraMap k K).injective (by simp_all [Subtype.eq_iff]))⟩

lemma charZero_sepGen {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] [CharZero k]
    [Algebra.EssFiniteType k K] :
    IsSeparablyGenerated (⊥ : IntermediateField k (ULift.{u} K)) (ULift.{u} K) := by
  haveI : CharZero (⊥ : IntermediateField k (ULift.{u} K)) := charZero_bot_charZero
  have h_trans := exists_isTranscendenceBasis (⊥ : IntermediateField k (ULift.{u} K)) (ULift.{u} K)
  obtain ⟨s, hs⟩ := h_trans
  have h_alg := isAlgebraic_intermediateField_adjoin_of_isTranscendenceBasis s hs
  have h_sep := isSeparable_intermediateField_adjoin_of_isAlgebraic_charZero s h_alg
  exact ⟨s, hs, h_sep⟩

lemma charZero_case {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] [CharZero k] :
    ∃ (K' : Type (max u v)) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : IsScalarTower k K K') (k' : IntermediateField k K'),
      FiniteDimensional K K' ∧ IsPurelyInseparable K K' ∧
      FiniteDimensional k k' ∧ IsPurelyInseparable k k' ∧
      IsSeparablyGenerated k' K' := by
  refine ⟨ULift.{u} K, inferInstance, inferInstance, inferInstance, inferInstance, (⊥ : IntermediateField k (ULift.{u} K)), ?_⟩
  exact ⟨charZero_finDim_K, charZero_pureInsep_K, charZero_finDim_k_bot, charZero_pureInsep_k_bot, charZero_sepGen⟩

lemma essFiniteType_implies_fg (k K : Type*) [Field k] [Field K] [Algebra k K] [h : Algebra.EssFiniteType k K] :
    ∃ s : Finset K, IntermediateField.adjoin k (s : Set K) = ⊤ := by
  refine h.1.imp fun and=>top_unique ∘ fun and a s=>?_
  rcases@ and
  cases‹_›
  exact (‹∀y, ∃_, _› a).elim (by exact fun and x =>eq_div_of_mul_eq and.2.2.ne_zero x▸div_mem (IntermediateField.algebra_adjoin_le_adjoin _ _ and.1.2) (IntermediateField.algebra_adjoin_le_adjoin _ _ and.2.1.2))

lemma algebraic_and_fg_implies_finite {E K : Type*} [Field E] [Field K] [Algebra E K]
    (h_alg : Algebra.IsAlgebraic E K) (h_fg : ∃ s : Finset K, IntermediateField.adjoin E (s : Set K) = ⊤) :
    FiniteDimensional E K := by
  convert Module.finite_of_isArtinianRing E K with a
  refine h_fg.elim fun and x =>by_contra fun and' => absurd (x▸IntermediateField.adjoin_algebraic_toSubalgebra fun and h=>h_alg.1 and) ?_
  use (and' ⟨ _,·.symm⟩)

lemma fg_over_k_implies_fg_over_E {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (E : IntermediateField k K) (s : Finset K) (h_fg : IntermediateField.adjoin k (s : Set K) = ⊤) :
    IntermediateField.adjoin E (s : Set K) = ⊤ := by
  norm_num [IntermediateField.adjoin,IntermediateField.ext_iff] at*
  simp_rw [ Subfield.mem_closure]at *
  exact fun and A B=>h_fg _ _ fun and=>B.comp (.imp_left (.rec (by use⟨_, E.algebraMap_mem ·⟩,.)))

lemma exists_trans_basis_and_finite {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    ∃ (S : Finset K),
      IsTranscendenceBasis k (fun x : (S : Set K) ↦ (x : K)) ∧
      FiniteDimensional (IntermediateField.adjoin k (S : Set K)) K := by
  have h_trans := exists_isTranscendenceBasis k K
  obtain ⟨S, hS⟩ := h_trans
  have h_alg := isAlgebraic_intermediateField_adjoin_of_isTranscendenceBasis S hS
  have h_fg_k := essFiniteType_implies_fg k K
  obtain ⟨s0, hs0⟩ := h_fg_k
  have h_fg_E := fg_over_k_implies_fg_over_E (IntermediateField.adjoin k S) s0 hs0
  have h_fin := algebraic_and_fg_implies_finite h_alg ⟨s0, h_fg_E⟩
  have h1 : Algebra.IsAlgebraic (IntermediateField.adjoin k (s0 : Set K)) K := by
    rw [hs0]
    constructor
    intro x
    use Polynomial.X - Polynomial.C (⟨x, trivial⟩ : (⊤ : IntermediateField k K))
    constructor
    · exact Polynomial.X_sub_C_ne_zero (⟨x, trivial⟩ : (⊤ : IntermediateField k K))
    · simp
  have h2 : Algebra.IsAlgebraic (Algebra.adjoin k (s0 : Set K)) K :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp h1
  have h3 : Algebra.trdeg k K ≤ Cardinal.mk (s0 : Set K) := by
    haveI := h2
    exact Algebra.IsAlgebraic.trdeg_le_cardinalMk k (s0 : Set K)
  have h4 : Cardinal.mk S = Algebra.trdeg k K :=
    IsTranscendenceBasis.cardinalMk_eq_trdeg hS
  have h5 : Cardinal.mk S < Cardinal.aleph0 := by
    apply lt_of_le_of_lt (b := Cardinal.mk (s0 : Set K))
    · rw [h4]; exact h3
    · exact Cardinal.mk_lt_aleph0
  have h6 : S.Finite := Cardinal.lt_aleph0_iff_set_finite.mp h5
  use h6.toFinset
  have h7 : (h6.toFinset : Set K) = S := Set.Finite.coe_toFinset h6
  rw [h7]
  exact ⟨hS, h_fin⟩



lemma purely_insep_exponent_algebra_adjoin {L K : Type*} [Field L] [Field K] [Algebra L K]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP L p] (S : Set K) (e : ℕ)
    (hS : ∀ x ∈ S, x ^ (p ^ e) ∈ (⊥ : IntermediateField L K)) (x : K)
    (hx : x ∈ IntermediateField.adjoin L S) :
    x ^ (p ^ e) ∈ (⊥ : IntermediateField L K) := by
  revert hS
  rcases↑(CharP.exists (K ) )
  rcases (by valid:).eq K ( charP_of_injective_algebraMap (algebraMap L K).injective _)
  use fun and=>by_contra fun and' =>absurd (IntermediateField.adjoin_algebraic_toSubalgebra (?_ : ∀ a ∈ S,IsAlgebraic L a)) ?_
  · exact (.of_pow (p.pow_pos (p.pos_of_neZero)) <|and · · |>.choose_spec▸isAlgebraic_algebraMap _)
  use and' ∘(Algebra.adjoin_induction and ?_ (?_) ?_<|·.le hx)
  · refine fun and =>⟨ _, RingHom.map_pow _ _ _⟩
  · simp_all[add_pow_char_pow, add_mem]
  · refine fun and _ _ _' =>mul_pow and _ _▸mul_mem

lemma purely_insep_exponent_finset {L K : Type*} [Field L] [Field K] [Algebra L K]
    [IsPurelyInseparable L K] (p : ℕ) [Fact (Nat.Prime p)] [CharP L p] (S : Finset K) :
    ∃ e : ℕ, ∀ x ∈ S, x ^ (p ^ e) ∈ (⊥ : IntermediateField L K) := by
  inhabit ↑K
  replace : ∀ a ∈ S,∃x,a^p^x ∈(⊥:IntermediateField L K) :=fun R M=>?_
  · choose! _ _ using this
    exists S.sup (by assumption)
    use fun and x =>(Nat.add_sub_of_le (S.le_sup x)▸pow_add p _ _)▸pow_mul and _ _▸pow_mem (by tauto) ( _)
  · apply IsPurelyInseparable.pow_mem

lemma finiteDimensional_implies_adjoin_finset_eq_top {L K : Type*} [Field L] [Field K] [Algebra L K]
    [FiniteDimensional L K] : ∃ S : Finset K, IntermediateField.adjoin L (S : Set K) = ⊤ := by
  apply (by assumption :).1.elim (by_contradiction _)
  exact (. ( (by use.,top_unique fun and n=>Submodule.span_induction (by apply IntermediateField.subset_adjoin) (zero_mem _) (by bound) (by bound)<|·.ge n)))

lemma purely_insep_exponent {L K : Type*} [Field L] [Field K] [Algebra L K]
    [FiniteDimensional L K] [IsPurelyInseparable L K] (p : ℕ) [Fact (Nat.Prime p)] [CharP L p] :
    ∃ e : ℕ, ∀ x : K, x ^ (p ^ e) ∈ (⊥ : IntermediateField L K) := by
  obtain ⟨S, hS⟩ := finiteDimensional_implies_adjoin_finset_eq_top (L := L) (K := K)
  obtain ⟨e, he⟩ := purely_insep_exponent_finset (L := L) (K := K) p S
  use e
  intro x
  have hx : x ∈ IntermediateField.adjoin L (S : Set K) := by
    rw [hS]
    exact trivial
  exact purely_insep_exponent_algebra_adjoin p (S : Set K) e he x hx

lemma exists_exponent_of_purelyInseparable {L : Type u} {K : Type v} [Field L] [Field K] [Algebra L K]
    [FiniteDimensional L K] [IsPurelyInseparable L K] (p : ℕ) [Fact (Nat.Prime p)] [CharP L p] :
    ∃ e : ℕ, ∀ x : K, ∃ (y : L), x ^ (p ^ e) = algebraMap L K y := by
  obtain ⟨e, he⟩ := purely_insep_exponent (L := L) (K := K) p
  use e
  intro x
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp (he x)
  exact ⟨y, hy.symm⟩

lemma purely_inseparable_separableClosure {E : Type u} {K : Type v} [Field E] [Field K] [Algebra E K]
    [FiniteDimensional E K] : IsPurelyInseparable (separableClosure E K) K := by
  repeat infer_instance

lemma finiteDimensional_separableClosure {E : Type u} {K : Type v} [Field E] [Field K] [Algebra E K]
    [FiniteDimensional E K] : FiniteDimensional (separableClosure E K) K := by
  refine inferInstance

lemma exists_exponent_of_finite {E : Type u} {K : Type v} [Field E] [Field K] [Algebra E K]
    [FiniteDimensional E K] (p : ℕ) [Fact (Nat.Prime p)] [CharP E p] :
    ∃ e : ℕ, ∀ x : K, x ^ (p ^ e) ∈ separableClosure E K := by
  haveI : IsPurelyInseparable (separableClosure E K) K := purely_inseparable_separableClosure
  haveI : FiniteDimensional (separableClosure E K) K := finiteDimensional_separableClosure
  haveI : CharP (separableClosure E K) p := RingHom.charP_iff_charP (algebraMap E (separableClosure E K)) p |>.mp inferInstance
  have h := exists_exponent_of_purelyInseparable (L := separableClosure E K) (K := K) p
  obtain ⟨e, he⟩ := h
  use e
  intro x
  obtain ⟨y, hy⟩ := he x
  rw [hy]
  exact Subtype.mem y

lemma mem_separableClosure_iff_isSeparable {E : Type u} {K : Type v} [Field E] [Field K] [Algebra E K] (x : K) :
    x ∈ separableClosure E K ↔ IsSeparable E x := by
  rfl

lemma exists_sep_power_of_finite {E : Type u} {K : Type v} [Field E] [Field K] [Algebra E K]
    [FiniteDimensional E K] (p : ℕ) [Fact (Nat.Prime p)] [CharP E p] :
    ∃ e : ℕ, ∀ x : K, IsSeparable E (x ^ (p ^ e)) := by
  obtain ⟨e, he⟩ := exists_exponent_of_finite p (E := E) (K := K)
  use e
  intro x
  have hx := he x
  exact (mem_separableClosure_iff_isSeparable (x ^ (p ^ e))).mp hx

lemma helper_charP_K {k K : Type*} [Field k] [Field K] [Algebra k K] (p : ℕ) [CharP k p] : CharP K p := by
  exact RingHom.charP_iff_charP (algebraMap k K) p |>.mp inferInstance

lemma finite_dim_sup_K {K A : Type*} [Field K] [Field A] [Algebra K A]
    (K1 K2 : IntermediateField K A) [FiniteDimensional K K1] [FiniteDimensional K K2] :
    FiniteDimensional K (K1 ⊔ K2 : IntermediateField K A) := by
  infer_instance

lemma purely_insep_sup_K {K A : Type*} [Field K] [Field A] [Algebra K A] (p : ℕ) [Fact (Nat.Prime p)] [CharP K p]
    (K1 K2 : IntermediateField K A) [IsPurelyInseparable K K1] [IsPurelyInseparable K K2] :
    IsPurelyInseparable K (K1 ⊔ K2 : IntermediateField K A) := by
  infer_instance

lemma exists_finset_k_of_mem_adjoin_S {k K : Type*} [Field k] [Field K] [Algebra k K]
    (S : Set K) (x : K) (hx : x ∈ IntermediateField.adjoin k S) :
    ∃ C : Finset k, x ∈ Subfield.closure ((algebraMap k K) '' (C : Set k) ∪ S) := by
  letI : DecidableEq k := Classical.decEq k
  let P : Subfield K := {
    carrier := {x : K | ∃ C : Finset k, x ∈ Subfield.closure ((algebraMap k K) '' (C : Set k) ∪ S)}
    mul_mem' := by
      rintro a b ⟨Ca, ha⟩ ⟨Cb, hb⟩
      use Ca ∪ Cb
      have h1 : Subfield.closure ((algebraMap k K) '' (Ca : Set k) ∪ S) ≤ Subfield.closure ((algebraMap k K) '' ((Ca ∪ Cb : Finset k) : Set k) ∪ S) := by
        apply Subfield.closure_mono
        apply Set.union_subset_union_left
        apply Set.image_mono
        exact Finset.coe_subset.mpr Finset.subset_union_left
      have h2 : Subfield.closure ((algebraMap k K) '' (Cb : Set k) ∪ S) ≤ Subfield.closure ((algebraMap k K) '' ((Ca ∪ Cb : Finset k) : Set k) ∪ S) := by
        apply Subfield.closure_mono
        apply Set.union_subset_union_left
        apply Set.image_mono
        exact Finset.coe_subset.mpr Finset.subset_union_right
      exact mul_mem (h1 ha) (h2 hb)
    one_mem' := ⟨∅, by apply Subfield.one_mem⟩
    add_mem' := by
      rintro a b ⟨Ca, ha⟩ ⟨Cb, hb⟩
      use Ca ∪ Cb
      have h1 : Subfield.closure ((algebraMap k K) '' (Ca : Set k) ∪ S) ≤ Subfield.closure ((algebraMap k K) '' ((Ca ∪ Cb : Finset k) : Set k) ∪ S) := by
        apply Subfield.closure_mono
        apply Set.union_subset_union_left
        apply Set.image_mono
        exact Finset.coe_subset.mpr Finset.subset_union_left
      have h2 : Subfield.closure ((algebraMap k K) '' (Cb : Set k) ∪ S) ≤ Subfield.closure ((algebraMap k K) '' ((Ca ∪ Cb : Finset k) : Set k) ∪ S) := by
        apply Subfield.closure_mono
        apply Set.union_subset_union_left
        apply Set.image_mono
        exact Finset.coe_subset.mpr Finset.subset_union_right
      exact add_mem (h1 ha) (h2 hb)
    zero_mem' := ⟨∅, by apply Subfield.zero_mem⟩
    neg_mem' := by
      rintro a ⟨Ca, ha⟩
      use Ca
      exact neg_mem ha
    inv_mem' := by
      rintro a ⟨Ca, ha⟩
      use Ca
      exact inv_mem ha
  }
  have h_k : ∀ c : k, algebraMap k K c ∈ P := by
    intro c
    use {c}
    apply Subfield.subset_closure
    apply Or.inl
    exact ⟨c, Finset.mem_singleton_self c, rfl⟩
  have h_S : S ⊆ P := by
    intro s hs
    use ∅
    apply Subfield.subset_closure
    exact Or.inr hs
  let P_int : IntermediateField k K := {
    carrier := P.carrier
    mul_mem' := P.mul_mem'
    add_mem' := P.add_mem'
    inv_mem' := P.inv_mem'
    algebraMap_mem' := h_k
  }
  have h_sub : IntermediateField.adjoin k S ≤ P_int := IntermediateField.adjoin_le_iff.mpr h_S
  exact h_sub hx

lemma separable_of_p_pow_eq_aux {L : Type*} [Field L] (p : ℕ) [Fact (Nat.Prime p)] [CharP L p]
    (e : ℕ) (Q : Polynomial L) :
    Q ^ (p ^ e) = (Q.map (frobenius L p ^ e)).comp (Polynomial.X ^ (p ^ e)) := by
  rewrite [(Q).as_sum_range_C_mul_X_pow]
  norm_num[ ←map_pow, mul_pow, Polynomial.map_sum,pow_right_comm,sum_pow_char_pow,frobenius_def]
  exact (congr_arg _)<|funext fun and=>congr_arg (Polynomial.C ·*_) (e.rec (pow_one _) fun and x=>Function.iterate_succ_apply' _ _ _▸x▸pow_mul _ _ _)

lemma separable_of_p_pow_eq_aux2 {L : Type*} [Field L] (p : ℕ) [Fact (Nat.Prime p)] [CharP L p]
    (e : ℕ) (P Q : Polynomial L) (h : (Q.map (frobenius L p ^ e)).comp (Polynomial.X ^ (p ^ e)) = P.comp (Polynomial.X ^ (p ^ e))) :
    Q.map (frobenius L p ^ e) = P := by
  replace h :(Q.map ( frobenius L p^e)-P).comp (@.X^p^e)=0:=by simp_all
  rw[Polynomial.comp_eq_zero_iff,] at h
  convert sub_eq_zero.mp (h.resolve_right (Polynomial.X_pow_sub_C_ne_zero (p.pow_pos (p.pos_of_neZero)) ( _) ∘(sub_eq_zero.2 ·.2)))

lemma separable_of_p_pow_eq_aux3 {L : Type*} [Field L] (p : ℕ) [Fact (Nat.Prime p)] [CharP L p]
    (e : ℕ) (P Q : Polynomial L) (h : Q.map (frobenius L p ^ e) = P) (hP_sep : P.Separable) :
    Q.Separable := by
  norm_num[<-h, Polynomial.separable_def,Q.derivative_map]at*
  convert isCoprime_of_irreducible_dvd _ _
  · apply inferInstance
  · refine EuclideanDomain.to_principal_ideal_domain
  · use fun and=>by simp_all[not_isCoprime_zero_zero]
  use fun and p R M=>p.1 ((hP_sep.isUnit_of_dvd' (and.map_dvd _ R) (and.map_dvd _ M)).exists_left_inv.elim fun and c=>? _)
  refine(Polynomial.isUnit_iff_degree_eq_zero.mpr (Polynomial.degree_eq_zero_of_isUnit ↑(isUnit_of_mul_eq_one_right and c)▸Polynomial.degree_map_eq_of_injective (frobenius_inj _ _|>.iterate _) _).symm)

lemma separable_of_p_pow_eq {L : Type*} [Field L] (p : ℕ) [Fact (Nat.Prime p)] [CharP L p]
    (e : ℕ) (P Q : Polynomial L)
    (h_eq : Q ^ (p ^ e) = P.comp (Polynomial.X ^ (p ^ e)))
    (hP_sep : P.Separable) : Q.Separable := by
  have h1 := separable_of_p_pow_eq_aux p e Q
  have h2 : (Q.map (frobenius L p ^ e)).comp (Polynomial.X ^ (p ^ e)) = P.comp (Polynomial.X ^ (p ^ e)) := by
    rw [← h1, h_eq]
  have h3 := separable_of_p_pow_eq_aux2 p e P Q h2
  exact separable_of_p_pow_eq_aux3 p e P Q h3 hP_sep

lemma exists_finite_generators_of_finDim {E K : Type*} [Field E] [Field K] [Algebra E K]
    [FiniteDimensional E K] : ∃ B : Finset K, IntermediateField.adjoin E (B : Set K) = ⊤ := by
  refine (by valid :).1.imp fun and x =>top_unique fun and n=>?_
  use Submodule.span_induction (by apply IntermediateField.subset_adjoin) (zero_mem _) (by bound) (by bound) (x.ge n)

lemma exists_minpoly_coeffs_finset {E K : Type*} [Field E] [Field K] [Algebra E K]
    (B : Finset K) (e : ℕ) :
    ∃ D : Finset E, ∀ x ∈ B, ∀ i, (minpoly E (x ^ e)).coeff i ∈ D := by
  letI : DecidableEq E := Classical.decEq E
  let f (x : K) : Finset E := insert 0 ((minpoly E (x ^ e)).support.image (fun i => (minpoly E (x ^ e)).coeff i))
  use B.biUnion f
  intro x hx i
  apply Finset.mem_biUnion.mpr
  use x, hx
  by_cases h : (minpoly E (x ^ e)).coeff i = 0
  · rw [h]
    exact Finset.mem_insert_self 0 _
  · apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    use i
    exact ⟨Polynomial.mem_support_iff.mpr h, rfl⟩

lemma helper_coefficients_field {k K : Type*} [Field k] [Field K] [Algebra k K]
    (S : Set K) (h_trans : IsTranscendenceBasis k (fun x : S ↦ (x : K)))
    (D : Finset (IntermediateField.adjoin k S)) :
    ∃ C : Finset k, (Subtype.val '' (D : Set (IntermediateField.adjoin k S))) ⊆
      Subfield.closure ((algebraMap k K) '' (C : Set k) ∪ S) := by
  letI : DecidableEq k := Classical.decEq k
  letI : DecidableEq (IntermediateField.adjoin k S) := Classical.decEq _
  induction' D using Finset.induction_on with d D' hd ih
  · use ∅
    intro x hx
    rcases hx with ⟨y, hy, _⟩
    simp at hy
  · obtain ⟨C', hC'⟩ := ih
    have hd_mem : (d : K) ∈ IntermediateField.adjoin k S := d.property
    obtain ⟨Cd, hCd⟩ := exists_finset_k_of_mem_adjoin_S S (d : K) hd_mem
    use C' ∪ Cd
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [Finset.mem_coe, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · have h_sub : Subfield.closure ((algebraMap k K) '' (Cd : Set k) ∪ S) ≤ Subfield.closure ((algebraMap k K) '' ((C' ∪ Cd : Finset k) : Set k) ∪ S) := by
        apply Subfield.closure_mono
        apply Set.union_subset_union_left
        apply Set.image_mono
        exact Finset.coe_subset.mpr Finset.subset_union_right
      exact h_sub hCd
    · have hy_C' : (y : K) ∈ Subfield.closure ((algebraMap k K) '' (C' : Set k) ∪ S) := hC' ⟨y, hy, rfl⟩
      have h_sub : Subfield.closure ((algebraMap k K) '' (C' : Set k) ∪ S) ≤ Subfield.closure ((algebraMap k K) '' ((C' ∪ Cd : Finset k) : Set k) ∪ S) := by
        apply Subfield.closure_mono
        apply Set.union_subset_union_left
        apply Set.image_mono
        exact Finset.coe_subset.mpr Finset.subset_union_left
      exact h_sub hy_C'

def root_set (K A : Type*) [Field K] [Field A] [Algebra K A] (S : Set K) (q : ℕ) : Set A :=
  { y : A | ∃ s ∈ S, y ^ q = algebraMap K A s }

lemma finiteDimensional_sup {k A : Type*} [Field k] [Field A] [Algebra k A]
    (k1 k2 : IntermediateField k A) [FiniteDimensional k k1] [FiniteDimensional k k2] :
    FiniteDimensional k (k1 ⊔ k2 : IntermediateField k A) := by
  infer_instance

lemma isPurelyInseparable_sup {k A : Type*} [Field k] [Field A] [Algebra k A] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (k1 k2 : IntermediateField k A) [IsPurelyInseparable k k1] [IsPurelyInseparable k k2] :
    IsPurelyInseparable k (k1 ⊔ k2 : IntermediateField k A) := by
  infer_instance

lemma exists_root_in_algClosed {A : Type*} [Field A] [IsAlgClosed A] (x : A) (n : ℕ) (hn : 0 < n) :
    ∃ y : A, y ^ n = x := by
  have hp : (Polynomial.X ^ n - Polynomial.C x).degree ≠ 0 := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt]
    · rw [Polynomial.degree_X_pow]
      exact ne_of_gt (by exact_mod_cast hn)
    · rw [Polynomial.degree_X_pow]
      have hc := Polynomial.degree_C_le (a := x)
      exact lt_of_le_of_lt hc (by exact_mod_cast hn)
  have h := IsAlgClosed.exists_root (Polynomial.X ^ n - Polynomial.C x) hp
  obtain ⟨y, hy⟩ := h
  use y
  have h_eval : (Polynomial.X ^ n - Polynomial.C x).eval y = 0 := hy
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at h_eval
  exact sub_eq_zero.mp h_eval

lemma exists_roots_finset {k A : Type*} [Field k] [Field A] [Algebra k A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (C : Finset k) :
    ∃ C' : Finset A, (∀ c ∈ C, ∃ y ∈ C', y ^ (p ^ e) = algebraMap k A c) ∧
      (∀ y ∈ C', ∃ c ∈ C, y ^ (p ^ e) = algebraMap k A c) := by
  letI : DecidableEq k := Classical.decEq k
  letI : DecidableEq A := Classical.decEq A
  induction' C using Finset.induction_on with c C' hc ih
  · use ∅
    refine ⟨?_, ?_⟩
    · intro c hc
      simp at hc
    · intro y hy
      simp at hy
  · obtain ⟨C'', hC''_1, hC''_2⟩ := ih
    have hp : 0 < p ^ e := Nat.pos_of_ne_zero (pow_ne_zero e (Nat.Prime.ne_zero Fact.out))
    have h_root := exists_root_in_algClosed (algebraMap k A c) (p ^ e) hp
    obtain ⟨y, hy⟩ := h_root
    use insert y C''
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · use y
        refine ⟨Finset.mem_insert_self y C'', hy⟩
      · obtain ⟨y', hy'_mem, hy'_eq⟩ := hC''_1 x hx
        use y'
        refine ⟨Finset.mem_insert_of_mem hy'_mem, hy'_eq⟩
    · intro y' hy'
      rw [Finset.mem_insert] at hy'
      rcases hy' with rfl | hy'
      · use c
        refine ⟨Finset.mem_insert_self c C', hy⟩
      · obtain ⟨x, hx_mem, hx_eq⟩ := hC''_2 y' hy'
        use x
        refine ⟨Finset.mem_insert_of_mem hx_mem, hx_eq⟩

lemma finiteDimensional_adjoin_root {k A : Type*} [Field k] [Field A] [Algebra k A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (y : A) (e : ℕ) (c : k) (hy : y ^ (p ^ e) = algebraMap k A c) :
    FiniteDimensional k (IntermediateField.adjoin k {y} : IntermediateField k A) := by
  exact (IntermediateField.adjoin.finiteDimensional) (.of_pow (p.pow_pos (p.pos_of_neZero)) (hy.symm.subst (isIntegral_algebraMap)))

lemma purely_inseparable_adjoin_root {k A : Type*} [Field k] [Field A] [Algebra k A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (y : A) (e : ℕ) (c : k) (hy : y ^ (p ^ e) = algebraMap k A c) :
    IsPurelyInseparable k (IntermediateField.adjoin k {y} : IntermediateField k A) := by
  have' :=IntermediateField.adjoin.finiteDimensional (.of_pow (p.pow_pos (p.pos_of_neZero)) (hy▸isIntegral_algebraMap):IsIntegral k y)
  replace hy:IsPurelyInseparable k ↑(IntermediateField.adjoin k {y})
  · apply isPurelyInseparable_iff_pow_mem k p|>.2
    norm_num[IntermediateField.mem_adjoin_simple_iff,Subtype.eq_iff]at*
    simp_all(config := {singlePass:=1})[@forall_comm A,div_pow, Polynomial.aeval_eq_sum_range]
    rcases CharP.exists A
    cases (by valid:).eq A ↑( charP_of_injective_algebraMap ↑(algebraMap k A).injective _)
    conv_rhs=>norm_num[*, Algebra.smul_def,pow_right_comm _ _ (p^ _),sum_pow_char_pow]
    use fun and x =>⟨e,(∑ a ∈.range (and.natDegree+1), and.coeff a^p^e*c^a)/∑ a ∈.range (x.natDegree+1),x.coeff a^p^e*c^a,by simp_all[pow_right_comm _ _ (p^e), mul_pow]⟩
  · valid

lemma add_pow_pe {A : Type*} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)] [CharP A p] (x y : A) (e : ℕ) :
    (x + y) ^ (p ^ e) = x ^ (p ^ e) + y ^ (p ^ e) := by
  apply add_pow_char_pow _ _ _

lemma helper_mem_adjoin_of_mem_base {k A : Type*} [Field k] [Field A] [Algebra k A]
    (k' : IntermediateField k A) (S : Set A) (y : A) (hy : y ∈ k') :
    y ∈ IntermediateField.adjoin k' S := by
  refine Subalgebra.algebraMap_mem _ (⟨y,hy⟩ :k')

lemma helper_adjoin_mono_left {k A : Type*} [Field k] [Field A] [Algebra k A]
    (k1 k2 : IntermediateField k A) (h : k1 ≤ k2) (S : Set A) (x : A) (hx : x ∈ IntermediateField.adjoin k1 S) :
    x ∈ IntermediateField.adjoin k2 S := by
  induction hx using IntermediateField.adjoin_induction
  · bound
  · exact Subalgebra.algebraMap_mem _ (⟨ _,h (by valid:).2⟩:k2)
  · bound
  · simp_all
  · bound

lemma exists_k_prime_for_adjoin_element {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (S : Set K) (e : ℕ) (x : K) (hx : x ∈ IntermediateField.adjoin k S) :
    ∃ (k' : IntermediateField k A), FiniteDimensional k k' ∧ IsPurelyInseparable k k' ∧
      ∃ y : IntermediateField.adjoin k' (root_set K A S (p ^ e)),
        y ^ (p ^ e) = algebraMap K A x := by
  haveI : CharP A p := RingHom.charP_iff_charP (algebraMap k A) p |>.mp inferInstance
  revert hx
  let q := p ^ e
  refine IntermediateField.adjoin_induction (F:=k) (E:=K) (s:=S) (p := fun x _ ↦ ∃ (k' : IntermediateField k A), FiniteDimensional k k' ∧ IsPurelyInseparable k k' ∧ ∃ y : IntermediateField.adjoin k' (root_set K A S (p ^ e)), y ^ (p ^ e) = algebraMap K A x) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    use ⊥
    have h_fin : FiniteDimensional k (⊥ : IntermediateField k A) := inferInstance
    have h_ins : IsPurelyInseparable k (⊥ : IntermediateField k A) := inferInstance
    have h_pos : 0 < p ^ e := pos_iff_ne_zero.mpr (pow_ne_zero e (Nat.Prime.ne_zero Fact.out))
    have h_ex := exists_root_in_algClosed (algebraMap K A x) (p ^ e) h_pos
    obtain ⟨y, hy⟩ := h_ex
    have hy_in_root_set : y ∈ root_set K A S (p ^ e) := ⟨x, hx, hy⟩
    have hy_in_adjoin : y ∈ IntermediateField.adjoin (⊥ : IntermediateField k A) (root_set K A S (p ^ e)) := by
      apply IntermediateField.subset_adjoin
      exact hy_in_root_set
    exact ⟨h_fin, h_ins, ⟨⟨y, hy_in_adjoin⟩, hy⟩⟩
  · intro c
    have h_pos : 0 < p ^ e := pos_iff_ne_zero.mpr (pow_ne_zero e (Nat.Prime.ne_zero Fact.out))
    have h_ex := exists_root_in_algClosed (algebraMap k A c) (p ^ e) h_pos
    obtain ⟨y, hy⟩ := h_ex
    use IntermediateField.adjoin k {y}
    have h_fin := finiteDimensional_adjoin_root p y e c hy
    have h_ins := purely_inseparable_adjoin_root p y e c hy
    have hy_in_adjoin : y ∈ IntermediateField.adjoin (IntermediateField.adjoin k {y}) (root_set K A S (p ^ e)) := helper_mem_adjoin_of_mem_base _ _ _ (IntermediateField.mem_adjoin_simple_self k y)
    have hy_eq : y ^ (p ^ e) = algebraMap K A (algebraMap k K c) := by
      rw [hy]
      exact IsScalarTower.algebraMap_apply k K A c
    exact ⟨h_fin, h_ins, ⟨⟨y, hy_in_adjoin⟩, hy_eq⟩⟩
  · intro x y hx hy px py
    rcases px with ⟨k1, hk1_fin, hk1_ins, y1, hy1⟩
    rcases py with ⟨k2, hk2_fin, hk2_ins, y2, hy2⟩
    let k' : IntermediateField k A := k1 ⊔ k2
    have h_fin := finiteDimensional_sup k1 k2
    have h_ins := isPurelyInseparable_sup p k1 k2
    have hy1_in : (y1 : A) ∈ IntermediateField.adjoin k' (root_set K A S (p ^ e)) := helper_adjoin_mono_left k1 k' le_sup_left _ _ y1.property
    have hy2_in : (y2 : A) ∈ IntermediateField.adjoin k' (root_set K A S (p ^ e)) := helper_adjoin_mono_left k2 k' le_sup_right _ _ y2.property
    have h_add_in : (y1 : A) + (y2 : A) ∈ IntermediateField.adjoin k' (root_set K A S (p ^ e)) := add_mem hy1_in hy2_in
    have h_eq : ((y1 : A) + (y2 : A)) ^ (p ^ e) = algebraMap K A (x + y) := by
      rw [add_pow_pe p (y1 : A) (y2 : A) e, hy1, hy2, map_add]
    exact ⟨k', h_fin, h_ins, ⟨⟨(y1 : A) + (y2 : A), h_add_in⟩, h_eq⟩⟩
  · intro x hx px
    rcases px with ⟨k1, hk1_fin, hk1_ins, y1, hy1⟩
    let k' : IntermediateField k A := k1
    have hy1_inv_in : (y1 : A)⁻¹ ∈ IntermediateField.adjoin k' (root_set K A S (p ^ e)) := inv_mem y1.property
    have h_eq : ((y1 : A)⁻¹) ^ (p ^ e) = algebraMap K A x⁻¹ := by
      rw [inv_pow, hy1, map_inv₀]
    exact ⟨k', hk1_fin, hk1_ins, ⟨⟨(y1 : A)⁻¹, hy1_inv_in⟩, h_eq⟩⟩
  · intro x y hx hy px py
    rcases px with ⟨k1, hk1_fin, hk1_ins, y1, hy1⟩
    rcases py with ⟨k2, hk2_fin, hk2_ins, y2, hy2⟩
    let k' : IntermediateField k A := k1 ⊔ k2
    have h_fin := finiteDimensional_sup k1 k2
    have h_ins := isPurelyInseparable_sup p k1 k2
    have hy1_in : (y1 : A) ∈ IntermediateField.adjoin k' (root_set K A S (p ^ e)) := helper_adjoin_mono_left k1 k' le_sup_left _ _ y1.property
    have hy2_in : (y2 : A) ∈ IntermediateField.adjoin k' (root_set K A S (p ^ e)) := helper_adjoin_mono_left k2 k' le_sup_right _ _ y2.property
    have h_mul_in : (y1 : A) * (y2 : A) ∈ IntermediateField.adjoin k' (root_set K A S (p ^ e)) := mul_mem hy1_in hy2_in
    have h_eq : ((y1 : A) * (y2 : A)) ^ (p ^ e) = algebraMap K A (x * y) := by
      rw [mul_pow, hy1, hy2, map_mul]
    exact ⟨k', h_fin, h_ins, ⟨⟨(y1 : A) * (y2 : A), h_mul_in⟩, h_eq⟩⟩

lemma exists_k_prime_for_finset {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (S : Set K) (e : ℕ) (D : Finset K) (hD : ∀ x ∈ D, x ∈ IntermediateField.adjoin k S) :
    ∃ (k' : IntermediateField k A), FiniteDimensional k k' ∧ IsPurelyInseparable k k' ∧
      ∀ x ∈ D, ∃ y : IntermediateField.adjoin k' (root_set K A S (p ^ e)),
        y ^ (p ^ e) = algebraMap K A x := by
  haveI : DecidableEq K := Classical.decEq K
  induction D using Finset.induction_on with
  | empty =>
    use ⊥
    refine ⟨inferInstance, inferInstance, by
      intro x hx
      simp at hx⟩
  | insert x D' hx ih =>
    have hD' : ∀ x ∈ D', x ∈ IntermediateField.adjoin k S := fun z hz ↦ hD z (Finset.mem_insert_of_mem hz)
    rcases ih hD' with ⟨k1, hk1_fin, hk1_ins, h_k1⟩
    have hx_adjoin : x ∈ IntermediateField.adjoin k S := hD x (Finset.mem_insert_self x D')
    have hx_ex := exists_k_prime_for_adjoin_element (A:=A) p S e x hx_adjoin
    rcases hx_ex with ⟨k2, hk2_fin, hk2_ins, y, hy⟩
    let k' : IntermediateField k A := k1 ⊔ k2
    use k'
    have h_fin := finiteDimensional_sup k1 k2
    have h_ins := isPurelyInseparable_sup p k1 k2
    refine ⟨h_fin, h_ins, ?_⟩
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · have hy_in : (y : A) ∈ IntermediateField.adjoin k' (root_set K A S (p ^ e)) := helper_adjoin_mono_left k2 k' le_sup_right _ _ y.property
      exact ⟨⟨y, hy_in⟩, hy⟩
    · rcases h_k1 z hz with ⟨yz, hyz⟩
      have hyz_in : (yz : A) ∈ IntermediateField.adjoin k' (root_set K A S (p ^ e)) := helper_adjoin_mono_left k1 k' le_sup_left _ _ yz.property
      exact ⟨⟨yz, hyz_in⟩, hyz⟩

lemma finiteDimensional_adjoin_roots_finset {k A : Type*} [Field k] [Field A] [Algebra k A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (C' : Finset A)
    (hC' : ∀ y ∈ C', ∃ c : k, y ^ (p ^ e) = algebraMap k A c) :
    FiniteDimensional k (IntermediateField.adjoin k (C' : Set A)) := by
  exact (IntermediateField.finiteDimensional_adjoin) (hC' · ·|>.elim (⟨_, Polynomial.monic_X_pow_sub_C · (NeZero.ne (p^e)),by·norm_num[ ·]⟩))

lemma isPurelyInseparable_adjoin_roots_finset {k A : Type*} [Field k] [Field A] [Algebra k A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (C' : Finset A)
    (hC' : ∀ y ∈ C', ∃ c : k, y ^ (p ^ e) = algebraMap k A c) :
    IsPurelyInseparable k (IntermediateField.adjoin k (C' : Set A)) := by
  haveI : ExpChar k p := inferInstance
  apply (isPurelyInseparable_iff_pow_mem (F := k) (E := IntermediateField.adjoin k (C' : Set A)) (q := p)).mpr
  intro x
  use e
  have hS : ∀ y ∈ (C' : Set A), y ^ (p ^ e) ∈ (⊥ : IntermediateField k A) := by
    intro y hy
    obtain ⟨c, hc⟩ := hC' y hy
    rw [IntermediateField.mem_bot]
    use c
    exact hc.symm
  have hx_prop := purely_insep_exponent_algebra_adjoin p (C' : Set A) e hS (x : A) x.property
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hx_prop
  use c
  apply Subtype.ext
  have h_alg : (algebraMap k (IntermediateField.adjoin k (C' : Set A)) c : A) = algebraMap k A c := rfl
  rw [h_alg]
  exact hc

lemma helper_finset_subset_adjoin {k K : Type*} [Field k] [Field K] [Algebra k K]
    (S : Set K) (D : Finset K) (hD : ∀ x ∈ D, x ∈ IntermediateField.adjoin k S) :
    ∃ S_fin : Finset K, (S_fin : Set K) ⊆ S ∧ ∀ x ∈ D, x ∈ IntermediateField.adjoin k (S_fin : Set K) := by
  choose! I A Bsimpa using (IntermediateField.exists_finset_of_mem_adjoin ∘ hD ·)
  classical·exact ⟨ _,D.coe_biUnion.trans_subset @(iSup₂_le A),fun R L=>IntermediateField.adjoin_le_iff.mpr (@ fun and=>IntermediateField.subset_adjoin _ _|>.comp (D.subset_biUnion_of_mem I L ·)) (Bsimpa R L)⟩

lemma adjoin_union_eq_sup {K A : Type*} [Field K] [Field A] [Algebra K A] (S1 S2 : Set A) :
    IntermediateField.adjoin K (S1 ∪ S2) = IntermediateField.adjoin K S1 ⊔ IntermediateField.adjoin K S2 := by
  apply@IntermediateField.adjoin_union

lemma K_prime_finite {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]
    (k' : IntermediateField k A) [FiniteDimensional k k'] :
    FiniteDimensional K (IntermediateField.adjoin K (k' : Set A)) := by
  let:=Module.finBasis k k'
  rw [show IntermediateField.adjoin _ _ =IntermediateField.adjoin K (.range (this · |>.1)) from _,]
  · convert IntermediateField.finiteDimensional_adjoin (Set.forall_mem_range.2 fun and=> _)
    · infer_instance
    · exact (IsIntegral.of_mem_of_fg ↑_ ↑(Module.Finite.iff_fg.1 (by assumption)) ( _) ↑(this _).2).tower_top
  · refine le_antisymm (IntermediateField.adjoin_le_iff.2 fun and x =>Subtype.coe_mk and x▸this.sum_repr ⟨ _,x⟩▸?_) (IntermediateField.adjoin_le_iff.2 fun and p=>p.choose_spec▸IntermediateField.subset_adjoin _ _ (this _).2)
    norm_num
    refine Subtype.coe_mk and x▸this.sum_repr ⟨ _,x⟩▸?_
    zify [IntermediateField.sum_mem _ fun a s=>mul_mem (Subalgebra.algebraMap_mem _ _) (IntermediateField.subset_adjoin _ _ (Set.mem_range_self a)), Algebra.smul_def,←IsScalarTower.algebraMap_apply]
    exact (Subalgebra.sum_mem _) fun a s=>mul_mem ((IsScalarTower.algebraMap_apply _ _ _ _).symm.subst (Subalgebra.algebraMap_mem _ _)) (IntermediateField.subset_adjoin _ _ ⟨a, rfl⟩)

lemma purely_inseparable_adjoin_root_K {K A : Type*} [Field K] [Field A] [Algebra K A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (s : K) (e : ℕ) (y : A) (hy : y ^ (p ^ e) = algebraMap K A s) :
    IsPurelyInseparable K (IntermediateField.adjoin K ({y} : Set A)) := by
  borelize@ ℂ
  by_cases h:FiniteDimensional K ↑(IntermediateField.adjoin K {(y)})
  · replace hy :IsPurelyInseparable K (IntermediateField.adjoin K {y})
    · apply isPurelyInseparable_iff_pow_mem K p |>.2
      have:=IntermediateField.adjoin_simple_toSubalgebra_of_integral (.of_mem_of_fg @_ ↑(Module.Finite.iff_fg.mp h) y <|IntermediateField.subset_adjoin _ _ (by constructor))
      use fun and=>(Algebra.adjoin_singleton_eq_range_aeval _ _).le (this.le and.2) |>.elim fun and c=>?_
      norm_num[c.symm, and.aeval_eq_sum_range,Subtype.eq_iff]at hy⊢
      cases CharP.exists A
      cases (by valid :).eq A ( charP_of_injective_algebraMap (algebraMap K A).injective _)
      norm_num[pow_right_comm _ _ (p^ _),hy, Algebra.smul_def,sum_pow_char_pow]
      simp_all[pow_right_comm _ _ (p^e),<-map_pow, mul_pow]
      simp_all[funext_iff,and.aeval_eq_sum_range]
      norm_num[Algebra.smul_def,funext_iff]at*
      simp_all[pow_right_comm y _ (p^ _),funext_iff]
      simp_all[algebraMap]
      revert‹IntermediateField.adjoin _ _›e(s)
      use fun x a s R L=>⟨a,∑M ∈.range (and.natDegree+1), and.coeff M^p^a*x^ M,by simp_all⟩
    · congr
  · cases h (IntermediateField.adjoin.finiteDimensional (.of_pow (p.pow_pos (NeZero.pos p)) (hy.symm.subst (isIntegral_algebraMap))))

lemma adjoin_insert_eq_sup (K A : Type*) [Field K] [Field A] [Algebra K A] [DecidableEq A] (x : A) (s : Finset A) :
    IntermediateField.adjoin K (↑(insert x s : Finset A) : Set A) = IntermediateField.adjoin K (s : Set A) ⊔ IntermediateField.adjoin K ({x} : Set A) := by
  zify[IntermediateField.adjoin_union,Set.insert_eq,Set.union_comm]

lemma adjoin_empty_eq_bot (K A : Type*) [Field K] [Field A] [Algebra K A] :
    IntermediateField.adjoin K (↑(∅ : Finset A) : Set A) = ⊥ := by
  simp_all

lemma K_prime_insep_finset {K A : Type*} [Field K] [Field A] [Algebra K A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP K p]
    (s : Finset A) (hs : ∀ x ∈ s, ∃ e : ℕ, x ^ (p ^ e) ∈ (algebraMap K A).range) :
    IsPurelyInseparable K (IntermediateField.adjoin K (s : Set A)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [adjoin_empty_eq_bot K A]
    exact inferInstance
  | insert x s hx ih =>
    have hs_x : ∀ y ∈ s, ∃ e : ℕ, y ^ (p ^ e) ∈ (algebraMap K A).range := fun y hy => hs y (Finset.mem_insert_of_mem hy)
    have ih' := ih hs_x
    have hx_root := hs x (Finset.mem_insert_self x s)
    obtain ⟨e, he⟩ := hx_root
    obtain ⟨c, hc⟩ := he
    have h_adjoin_x : IsPurelyInseparable K (IntermediateField.adjoin K ({x} : Set A)) := purely_inseparable_adjoin_root_K p c e x hc.symm
    have h_sup : IsPurelyInseparable K (IntermediateField.adjoin K (s : Set A) ⊔ IntermediateField.adjoin K ({x} : Set A) : IntermediateField K A) :=
      purely_insep_sup_K p (IntermediateField.adjoin K (s : Set A)) (IntermediateField.adjoin K ({x} : Set A))
    have h_eq := adjoin_insert_eq_sup K A x s
    rw [h_eq]
    exact h_sup

lemma K_prime_adjoin_eq_finset {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [DecidableEq A]
    (k' : IntermediateField k A) (C' : Finset k') (hC' : IntermediateField.adjoin k (C' : Set k') = ⊤) :
    IntermediateField.adjoin K (k' : Set A) = IntermediateField.adjoin K ((Finset.image (fun x => (x.val : A)) C' : Finset A) : Set A) := by
  push_cast [IntermediateField.adjoin]at *
  norm_num[Subfield.ext_iff,Subfield.mem_closure]at*
  norm_num[Subfield.mem_closure,SetLike.ext_iff] at *
  use fun and=>⟨ fun and R L=>and R L ∘ fun and a s=>by_contra fun and' =>? _, fun and R L h=>and R L fun and m=>h and.2⟩
  refine and' (hC' a s (R.comap k'.subtype) (Set.range_subset_iff.mpr (L ⟨algebraMap k K ·,by·norm_num[← IsScalarTower.algebraMap_apply]⟩)) and)

lemma K_prime_insep {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (k' : IntermediateField k A) [FiniteDimensional k k'] [IsPurelyInseparable k k'] :
    IsPurelyInseparable K (IntermediateField.adjoin K (k' : Set A)) := by
  have ⟨C', hC'⟩ := exists_finite_generators_of_finDim (E := k) (K := k')
  have ⟨e, he⟩ := purely_insep_exponent_finset (L := k) (K := k') p C'
  letI := Classical.decEq A
  have h_eq : IntermediateField.adjoin K (k' : Set A) = IntermediateField.adjoin K ((Finset.image (fun x => (x.val : A)) C' : Finset A) : Set A) := K_prime_adjoin_eq_finset k' C' hC'
  rw [h_eq]
  haveI : CharP K p := helper_charP_K (k := k) (K := K) p
  apply K_prime_insep_finset p (Finset.image (fun x => (x.val : A)) C')
  intro y hy
  rw [Finset.mem_image] at hy
  rcases hy with ⟨x, hx, rfl⟩
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp (he x hx)
  use e
  use algebraMap k K c
  have h_alg : algebraMap K A (algebraMap k K c) = algebraMap k A c := by
    exact (IsScalarTower.algebraMap_apply k K A c).symm
  have hc_val : (algebraMap k A) c = (x : A) ^ (p ^ e) := by
    have h1 : ((algebraMap k k' c) : A) = (x ^ (p ^ e) : A) := congr_arg Subtype.val hc
    have h2 : ((algebraMap k k' c) : A) = algebraMap k A c := rfl
    rw [h2] at h1
    exact h1
  rw [h_alg, hc_val]

lemma K_prime_finite_root_set {K A : Type*} [Field K] [Field A]
    [Algebra K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (e : ℕ) (S : Finset K) :
    FiniteDimensional K (IntermediateField.adjoin K (root_set K A (S : Set K) (p ^ e))) := by
  delta root_set
  let T: Polynomial A:=.X ^p ^e-.C 0
  convert IntermediateField.finiteDimensional_adjoin fun and x =>_
  · exact (S.finite_toSet.biUnion fun and h=>(T-.C (algebraMap _ _ and)).roots.finite_toSet).subset ( fun and=>by simp_all[mt (congr_arg Polynomial.natDegree),Nat.Prime.ne_zero Fact.out, T, sub_eq_zero])
  · exact (.of_pow (p.pow_pos (p.pos_of_neZero)) (x.choose_spec.2.symm.subst isIntegral_algebraMap))

lemma root_set_eq_finset {K A : Type*} [Field K] [Field A] [Algebra K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (e : ℕ) (S : Finset K) :
    ∃ C' : Finset A, root_set K A (S : Set K) (p ^ e) = (C' : Set A) := by
  norm_num(config := {singlePass :=1})[root_set,Set.ext_iff]
  classical use S.biUnion fun and=>(Polynomial.roots (@.X^p ^e-.C (algebraMap K A (and)))).toFinset,by simp_all [mt ↑(congr_arg Polynomial.natDegree), ←map_pow, sub_eq_zero,funext_iff, NeZero.ne p]

lemma K_prime_insep_root_set {K A : Type*} [Field K] [Field A]
    [Algebra K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (e : ℕ) (S : Finset K) :
    IsPurelyInseparable K (IntermediateField.adjoin K (root_set K A (S : Set K) (p ^ e))) := by
  obtain ⟨C', hC'⟩ := root_set_eq_finset (A := A) p e S
  rw [hC']
  apply isPurelyInseparable_adjoin_roots_finset p e C'
  intro y hy
  have hy2 : y ∈ root_set K A (S : Set K) (p ^ e) := by
    rw [hC']
    exact hy
  rcases hy2 with ⟨s, hs, hs_eq⟩
  exact ⟨s, hs_eq⟩

lemma helper_K_int_finite {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K) (k' : IntermediateField k A)
    [FiniteDimensional k k'] (h_fin : FiniteDimensional (IntermediateField.adjoin k (S : Set K)) K)
    (h_trans : IsTranscendenceBasis k (fun x : (S : Set K) ↦ (x : K))) :
    FiniteDimensional K (IntermediateField.adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e))) := by
  haveI : CharP K p := helper_charP_K (k := k) (K := K) p
  rw [adjoin_union_eq_sup]
  haveI : FiniteDimensional K (IntermediateField.adjoin K (k' : Set A)) := K_prime_finite k'
  haveI : FiniteDimensional K (IntermediateField.adjoin K (root_set K A (S : Set K) (p ^ e))) := K_prime_finite_root_set p e S
  exact finite_dim_sup_K _ _

lemma helper_K_int_purely_inseparable {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K) (k' : IntermediateField k A)
    [FiniteDimensional k k'] [IsPurelyInseparable k k'] :
    IsPurelyInseparable K (IntermediateField.adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e))) := by
  haveI : CharP K p := helper_charP_K (k := k) (K := K) p
  rw [adjoin_union_eq_sup]
  haveI : IsPurelyInseparable K (IntermediateField.adjoin K (k' : Set A)) := K_prime_insep p k'
  haveI : IsPurelyInseparable K (IntermediateField.adjoin K (root_set K A (S : Set K) (p ^ e))) := K_prime_insep_root_set p e S
  exact purely_insep_sup_K p _ _

lemma helper_K_int_sep_gen_E_prime_contains_B_step1 {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K) (k' : IntermediateField k A)
    (K'_int : IntermediateField K A) (h_eq : K'_int = IntermediateField.adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e)))
    (k'_in_K' : IntermediateField k K'_int)
    (hk_eq : k'_in_K'.toSubalgebra = Subalgebra.comap (K'_int.val.restrictScalars k) k'.toSubalgebra)
    (S_prime : Set K'_int)
    (h_S_prime : S_prime = Subtype.val ⁻¹' root_set K A (S : Set K) (p ^ e))
    (L : IntermediateField k K'_int)
    (h_S_prime_in_L : S_prime ⊆ (L : Set K'_int)) :
    ∀ s ∈ S, algebraMap K K'_int s ∈ L := by
  intro s hs
  have h_pos : 0 < p ^ e := pos_iff_ne_zero.mpr (pow_ne_zero e (Nat.Prime.ne_zero Fact.out))
  have h_ex := exists_root_in_algClosed (algebraMap K A s) (p ^ e) h_pos
  obtain ⟨y, hy⟩ := h_ex
  have hy_root : y ∈ root_set K A (S : Set K) (p ^ e) := ⟨s, hs, hy⟩
  have hy_in_K' : y ∈ K'_int := by
    rw [h_eq]
    exact IntermediateField.subset_adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e)) (Or.inr hy_root)
  let y_K' : K'_int := ⟨y, hy_in_K'⟩
  have hy_in_S_prime : y_K' ∈ S_prime := by
    rw [h_S_prime]
    exact hy_root
  have hy_in_L : y_K' ∈ L := h_S_prime_in_L hy_in_S_prime
  have h_pow_in_L : y_K' ^ (p ^ e) ∈ L := pow_mem hy_in_L _
  have h_eq2 : y_K' ^ (p ^ e) = algebraMap K K'_int s := Subtype.ext hy
  rw [← h_eq2]
  exact h_pow_in_L

lemma helper_K_int_sep_gen_E_prime_contains_B_step2 {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (S : Finset K)
    (K'_int : IntermediateField K A)
    (L : IntermediateField k K'_int)
    (h_S : ∀ s ∈ S, algebraMap K K'_int s ∈ L) :
    ∀ x : IntermediateField.adjoin k (S : Set K), algebraMap K K'_int (x : K) ∈ L := by
  intro x
  have h_le : IntermediateField.adjoin k (S : Set K) ≤ L.comap (IsScalarTower.toAlgHom k K K'_int) := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro s hs
    exact h_S s hs
  exact h_le x.property

lemma helper_K_int_sep_gen_E_prime_contains_B_step3 {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (S B : Finset K)
    (hB : IntermediateField.adjoin (IntermediateField.adjoin k (S : Set K)) (B : Set K) = ⊤)
    (K'_int : IntermediateField K A)
    (L : IntermediateField k K'_int)
    (h_kS : ∀ x : IntermediateField.adjoin k (S : Set K), algebraMap K K'_int (x : K) ∈ L)
    (h_B : ∀ b ∈ B, algebraMap K K'_int b ∈ L) :
    ∀ x : K, algebraMap K K'_int x ∈ L := by
  norm_num[IntermediateField.ext_iff,IntermediateField.mem_adjoin_simple_iff,funext_iff]at hB h_kS h_B⊢
  use (by induction hB · using@@IntermediateField.adjoin_induction with | mem K V =>apply h_B K V | _=>simp_all -contextual [mul_mem _,add_mem])

lemma helper_K_int_sep_gen_E_prime_contains_B_step4 {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S B : Finset K) (k' : IntermediateField k A)
    (K'_int : IntermediateField K A) (h_eq : K'_int = IntermediateField.adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e)))
    (k'_in_K' : IntermediateField k K'_int)
    (hk_eq : k'_in_K'.toSubalgebra = Subalgebra.comap (K'_int.val.restrictScalars k) k'.toSubalgebra)
    (S_prime : Set K'_int)
    (h_S_prime : S_prime = Subtype.val ⁻¹' root_set K A (S : Set K) (p ^ e))
    (L : IntermediateField k K'_int)
    (h_K : ∀ x : K, algebraMap K K'_int x ∈ L)
    (h_k' : ∀ x : k', x.val ∈ Subtype.val '' (L : Set K'_int))
    (h_root : ∀ x ∈ root_set K A (S : Set K) (p ^ e), x ∈ Subtype.val '' (L : Set K'_int)) :
    L = ⊤ := by
  norm_num [ L.ext_iff] at h_root h_k'⊢
  subst_vars
  intro _ _
  induction‹_› using@@IntermediateField.adjoin_induction
  · use (by assumption:).elim (h_k' _ · |>.snd) (h_root _ · |>.snd)
  · apply h_K
  · exact add_mem (by gcongr) (by assumption :)
  · apply inv_mem (by valid:)
  · exact (mul_mem (by gcongr) (by valid:) )

lemma helper_K_int_sep_gen_E_prime_contains_B {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K) (k' : IntermediateField k A)
    (K'_int : IntermediateField K A) (h_eq : K'_int = IntermediateField.adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e)))
    (k'_in_K' : IntermediateField k K'_int)
    (hk_eq : k'_in_K'.toSubalgebra = Subalgebra.comap (K'_int.val.restrictScalars k) k'.toSubalgebra)
    (B : Finset K) (hB : IntermediateField.adjoin (IntermediateField.adjoin k (S : Set K)) (B : Set K) = ⊤)
    (S_prime : Set K'_int)
    (h_S_prime : S_prime = Subtype.val ⁻¹' root_set K A (S : Set K) (p ^ e))
    (E_prime : IntermediateField k'_in_K' K'_int)
    (h_E_prime : E_prime = IntermediateField.adjoin k'_in_K' S_prime) :
    (⊤ : IntermediateField E_prime K'_int) = IntermediateField.adjoin E_prime ((algebraMap K K'_int) '' (B : Set K)) := by
  let L := IntermediateField.adjoin E_prime ((algebraMap K K'_int) '' (B : Set K))
  have hk_in_L : ∀ c : k, algebraMap k K'_int c ∈ L := by
    intro c
    have h1 : algebraMap k K'_int c = algebraMap k'_in_K' K'_int (algebraMap k k'_in_K' c) := rfl
    rw [h1]
    have h2 : algebraMap k'_in_K' K'_int (algebraMap k k'_in_K' c) = algebraMap E_prime K'_int (algebraMap k'_in_K' E_prime (algebraMap k k'_in_K' c)) := rfl
    rw [h2]
    exact L.algebraMap_mem _
  let L_k : IntermediateField k K'_int := {
    carrier := L
    mul_mem' := fun h1 h2 => mul_mem h1 h2
    add_mem' := fun h1 h2 => add_mem h1 h2
    inv_mem' := fun x hx => inv_mem hx
    algebraMap_mem' := hk_in_L
  }
  have hL1 : S_prime ⊆ (L_k : Set K'_int) := by
    intro x hx
    have hE : x ∈ E_prime := by
      rw [h_E_prime]
      exact IntermediateField.subset_adjoin k'_in_K' S_prime hx
    have hE_in_L : x ∈ L := IntermediateField.algebraMap_mem L (⟨x, hE⟩ : E_prime)
    exact hE_in_L
  have h_S : ∀ s ∈ S, algebraMap K K'_int s ∈ L_k := helper_K_int_sep_gen_E_prime_contains_B_step1 p e S k' K'_int h_eq k'_in_K' hk_eq S_prime h_S_prime L_k hL1
  have h_kS : ∀ x : IntermediateField.adjoin k (S : Set K), algebraMap K K'_int (x : K) ∈ L_k := helper_K_int_sep_gen_E_prime_contains_B_step2 S K'_int L_k h_S
  have h_B : ∀ b ∈ B, algebraMap K K'_int b ∈ L_k := by
    intro b hb
    exact IntermediateField.subset_adjoin E_prime ((algebraMap K K'_int) '' (B : Set K)) (Set.mem_image_of_mem (algebraMap K K'_int) hb)
  have h_K : ∀ x : K, algebraMap K K'_int x ∈ L_k := helper_K_int_sep_gen_E_prime_contains_B_step3 S B hB K'_int L_k h_kS h_B
  have h_k' : ∀ x : k', x.val ∈ Subtype.val '' (L_k : Set K'_int) := by
    intro x
    have hx_K' : x.val ∈ K'_int := by
      rw [h_eq]
      exact IntermediateField.subset_adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e)) (Or.inl x.property)
    let y : K'_int := ⟨x.val, hx_K'⟩
    have hy : y ∈ k'_in_K' := by
      have h1 : y ∈ k'_in_K'.toSubalgebra := by
        rw [hk_eq]
        exact x.property
      exact h1
    have h_in_E : y ∈ E_prime := IntermediateField.algebraMap_mem E_prime ⟨y, hy⟩
    use y
    refine ⟨IntermediateField.algebraMap_mem L (⟨y, h_in_E⟩ : E_prime), rfl⟩
  have h_root : ∀ x ∈ root_set K A (S : Set K) (p ^ e), x ∈ Subtype.val '' (L_k : Set K'_int) := by
    intro x hx
    have h_in_K : x ∈ K'_int := by
      rw [h_eq]
      exact IntermediateField.subset_adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e)) (Or.inr hx)
    let y : K'_int := ⟨x, h_in_K⟩
    have hy : y ∈ S_prime := by
      rw [h_S_prime]
      exact hx
    use y
    refine ⟨hL1 hy, rfl⟩
  have h_top := helper_K_int_sep_gen_E_prime_contains_B_step4 p e S B k' K'_int h_eq k'_in_K' hk_eq S_prime h_S_prime L_k h_K h_k' h_root
  apply IntermediateField.ext
  intro x
  have h_top_x := IntermediateField.ext_iff.mp h_top x
  exact ⟨fun _ => h_top_x.mpr trivial, fun _ => trivial⟩

lemma helper_translate_roots {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K) (k' : IntermediateField k A)
    (K'_int : IntermediateField K A) (h_eq : K'_int = IntermediateField.adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e)))
    (k'_in_K' : IntermediateField k K'_int)
    (hk_eq : k'_in_K'.toSubalgebra = Subalgebra.comap (K'_int.val.restrictScalars k) k'.toSubalgebra)
    (S_prime : Set K'_int)
    (h_S_prime : S_prime = Subtype.val ⁻¹' root_set K A (S : Set K) (p ^ e))
    (E_prime : IntermediateField k'_in_K' K'_int)
    (h_E_prime : E_prime = IntermediateField.adjoin k'_in_K' S_prime)
    (D : Finset (IntermediateField.adjoin k (S : Set K)))
    (hk'_roots : ∀ x ∈ D, ∃ y : IntermediateField.adjoin k' (root_set K A (S : Set K) (p ^ e)), y ^ (p ^ e) = algebraMap (IntermediateField.adjoin k (S : Set K)) A x) :
    ∀ x ∈ D, ∃ y : E_prime, y ^ (p ^ e) = algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int x := by
  refine (@hk'_roots · ·|>.elim (h_E_prime▸h_S_prime▸fun ⟨a, _⟩R=>?_))
  norm_num[funext_iff,Subtype.eq_iff]at R⊢
  exists a
  exists ?_
  · clear‹_ ∈D›h_S_prime‹Subtype _›h_E_prime (hk'_roots)R
    induction‹_› using IntermediateField.adjoin_induction
    · use h_eq▸IntermediateField.subset_adjoin _ _ (.inr (by valid)),IntermediateField.subset_adjoin _ _ (by valid)
    · use h_eq▸IntermediateField.subset_adjoin _ _ (.inl (by valid:).2),IntermediateField.algebraMap_mem _ (⟨ _,hk_eq.ge (by valid:).2⟩:k'_in_K')
    · cases‹_› with|intro R M=>cases‹∃_, _› with|intro a s=>use add_mem a R,add_mem s M
    · exact (by valid:).elim (by use inv_mem ·,inv_mem ·)
    · cases‹_› with|intro R M=>cases‹∃_, _› with|intro a s=>exact ⟨mul_mem a R,mul_mem s M⟩
  · repeat assumption

lemma is_separable_of_generators_finset {E K : Type*} [Field E] [Field K] [Algebra E K]
    (B : Finset K) (h_gen : (⊤ : IntermediateField E K) = IntermediateField.adjoin E (B : Set K))
    (h_sep : ∀ b ∈ B, IsSeparable E b) : Algebra.IsSeparable E K := by
  use fun and=>by_contra (absurd (IntermediateField.adjoin_algebraic_toSubalgebra (@h_sep · · |>.isIntegral.isAlgebraic) ) fun and=>. (?_))
  exact Algebra.adjoin_induction h_sep isSeparable_algebraMap (by simp_all[Field.isSeparable_add]) (by simp_all[Field.isSeparable_mul]) (and.le (h_gen.le (Set.mem_univ (‹K›:))))

noncomputable def construct_Q {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K)
    (K'_int : IntermediateField K A)
    (k'_in_K' : IntermediateField k K'_int)
    (b : K)
    (D : Finset (IntermediateField.adjoin k (S : Set K)))
    (hD : ∀ i, (minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))).coeff i ∈ D)
    (E_prime : IntermediateField k'_in_K' K'_int)
    (hk'_roots : ∀ x ∈ D, ∃ y : E_prime, y ^ (p ^ e) = algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int x) :
    Polynomial E_prime :=
  let P := minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))
  P.support.sum (fun i => Polynomial.monomial i (Classical.choose (hk'_roots (P.coeff i) (hD i))))

lemma construct_Q_coeff {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K)
    (K'_int : IntermediateField K A)
    (k'_in_K' : IntermediateField k K'_int)
    (b : K)
    (D : Finset (IntermediateField.adjoin k (S : Set K)))
    (hD : ∀ i, (minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))).coeff i ∈ D)
    (E_prime : IntermediateField k'_in_K' K'_int)
    (hk'_roots : ∀ x ∈ D, ∃ y : E_prime, y ^ (p ^ e) = algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int x)
    (i : ℕ) :
    (construct_Q p e S K'_int k'_in_K' b D hD E_prime hk'_roots).coeff i =
    if h : i ∈ (minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))).support
    then Classical.choose (hk'_roots ((minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))).coeff i) (hD i))
    else 0 := by
  delta Classical.choose construct_Q
  norm_num[Polynomial.coeff_monomial]

lemma construct_Q_pow_pe_eq {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K)
    (K'_int : IntermediateField K A)
    (k'_in_K' : IntermediateField k K'_int)
    (b : K)
    (D : Finset (IntermediateField.adjoin k (S : Set K)))
    (hD : ∀ i, (minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))).coeff i ∈ D)
    (E_prime : IntermediateField k'_in_K' K'_int)
    (hk'_roots : ∀ x ∈ D, ∃ y : E_prime, y ^ (p ^ e) = algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int x) :
    let P := minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))
    let P_K := P.map (algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int)
    let Q := construct_Q p e S K'_int k'_in_K' b D hD E_prime hk'_roots
    let Q_K := Q.map (algebraMap E_prime K'_int)
    Q_K ^ (p ^ e) = P_K.comp (Polynomial.X ^ (p ^ e)) := by
  norm_num[construct_Q]
  norm_num[*, mul_pow, Polynomial.map_sum,←Polynomial.C_mul_X_pow_eq_monomial,pow_right_comm,((hk'_roots _ _).choose_spec), (minpoly (IntermediateField.adjoin k S.toSet) (b^_)).as_sum_support▸Polynomial.map_sum _ _ _]
  cases CharP.exists K'_int
  cases (by valid:).eq _ ( charP_of_injective_algebraMap (algebraMap k _).injective _) with zify[*, mul_pow,←map_pow,sum_pow_char_pow,((hk'_roots _ _)).choose_spec]

lemma construct_Q_aeval_eq_zero {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K)
    (K'_int : IntermediateField K A)
    (k'_in_K' : IntermediateField k K'_int)
    (b : K)
    (D : Finset (IntermediateField.adjoin k (S : Set K)))
    (hD : ∀ i, (minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))).coeff i ∈ D)
    (E_prime : IntermediateField k'_in_K' K'_int)
    (hk'_roots : ∀ x ∈ D, ∃ y : E_prime, y ^ (p ^ e) = algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int x) :
    let Q := construct_Q p e S K'_int k'_in_K' b D hD E_prime hk'_roots
    Polynomial.aeval (algebraMap K K'_int b) Q = 0 := by
  intro Q
  have h_pow_eq := construct_Q_pow_pe_eq p e S K'_int k'_in_K' b D hD E_prime hk'_roots
  change (Q.map (algebraMap E_prime K'_int)) ^ (p ^ e) = ((minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))).map (algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int)).comp (Polynomial.X ^ (p ^ e)) at h_pow_eq
  have h_eval := congr_arg (Polynomial.eval (algebraMap K K'_int b)) h_pow_eq
  rw [Polynomial.eval_pow] at h_eval
  have h1 : Polynomial.eval (algebraMap K K'_int b) (((minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))).map (algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int)).comp (Polynomial.X ^ (p ^ e))) = 0 := by
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
    have h_pow_b : (algebraMap K K'_int b) ^ (p ^ e) = algebraMap K K'_int (b ^ (p ^ e)) := (map_pow (algebraMap K K'_int) b (p ^ e)).symm
    rw [h_pow_b]
    rw [Polynomial.eval_map]
    have h_eval2 : Polynomial.eval₂ (algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int) (algebraMap K K'_int (b ^ (p ^ e))) (minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))) = 0 := by
      have h_alg_comp : (algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int) = (algebraMap K K'_int).comp (algebraMap (IntermediateField.adjoin k (S : Set K)) K) := rfl
      rw [h_alg_comp]
      rw [← Polynomial.hom_eval₂]
      have h_minpoly : Polynomial.eval₂ (algebraMap (IntermediateField.adjoin k (S : Set K)) K) (b ^ (p ^ e)) (minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))) = 0 := by
        exact minpoly.aeval (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))
      rw [h_minpoly]
      exact map_zero (algebraMap K K'_int)
    exact h_eval2
  rw [h1] at h_eval
  haveI : CharP K'_int p := helper_charP_K (k := k) (K := K'_int) p
  have h_eval_zero : Polynomial.eval (algebraMap K K'_int b) (Q.map (algebraMap E_prime K'_int)) = 0 := by
    have h_pow_zero : (Polynomial.eval (algebraMap K K'_int b) (Q.map (algebraMap E_prime K'_int))) ^ (p ^ e) = 0 := h_eval
    exact (pow_eq_zero_iff (pow_ne_zero e (Nat.Prime.ne_zero Fact.out))).mp h_pow_zero
  have h2 : Polynomial.aeval (algebraMap K K'_int b) Q = Polynomial.eval (algebraMap K K'_int b) (Q.map (algebraMap E_prime K'_int)) := by
    rw [Polynomial.aeval_def, Polynomial.eval_map]
  rw [h2]
  exact h_eval_zero

lemma helper_separable_of_map {E K : Type*} [Field E] [Field K] (f : E →+* K) (Q : Polynomial E) (h : (Q.map f).Separable) : Q.Separable := by
  simp_all only [Polynomial.separable_map]

lemma helper_isSeparable_of_root {E K : Type*} [Field E] [Field K] [Algebra E K] (b : K) (Q : Polynomial E) (hQ_sep : Q.Separable) (hQ_root : Polynomial.aeval b Q = 0) (hQ_ne : Q ≠ 0) : IsSeparable E b := by
  simp_all[Q.aeval_eq_sum_range,IsSeparable,funext_iff]
  exact (.of_dvd (by valid) ( (minpoly.dvd _ _) <|by simp_all only[Q.aeval_eq_sum_range]))

lemma helper_single_generator_separable {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K)
    (K'_int : IntermediateField K A)
    (k'_in_K' : IntermediateField k K'_int)
    (b : K)
    (D : Finset (IntermediateField.adjoin k (S : Set K)))
    (hD : ∀ i, (minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))).coeff i ∈ D)
    (h_sep : IsSeparable (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e)))
    (E_prime : IntermediateField k'_in_K' K'_int)
    (hk'_roots : ∀ x ∈ D, ∃ y : E_prime, y ^ (p ^ e) = algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int x) :
    IsSeparable E_prime (algebraMap K K'_int b) := by
  let Q := construct_Q p e S K'_int k'_in_K' b D hD E_prime hk'_roots
  have h1 : Polynomial.aeval (algebraMap K K'_int b) Q = 0 := construct_Q_aeval_eq_zero p e S K'_int k'_in_K' b D hD E_prime hk'_roots
  have h2_eq : (Q.map (algebraMap E_prime K'_int)) ^ (p ^ e) = ((minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))).map (algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int)).comp (Polynomial.X ^ (p ^ e)) := construct_Q_pow_pe_eq p e S K'_int k'_in_K' b D hD E_prime hk'_roots
  have hP_sep_base : (minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))).Separable := h_sep
  have hP_sep : ((minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))).map (algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int)).Separable := Polynomial.Separable.map hP_sep_base
  haveI : CharP K'_int p := helper_charP_K (k := k) (K := K'_int) p
  have hQ_K_sep : (Q.map (algebraMap E_prime K'_int)).Separable := separable_of_p_pow_eq p e ((minpoly (IntermediateField.adjoin k (S : Set K)) (b ^ (p ^ e))).map (algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int)) (Q.map (algebraMap E_prime K'_int)) h2_eq hP_sep
  have hQ_sep : Q.Separable := helper_separable_of_map (algebraMap E_prime K'_int) Q hQ_K_sep
  have hQ_ne : Q ≠ 0 := by use (by valid:).ne_zero
  exact helper_isSeparable_of_root (algebraMap K K'_int b) Q hQ_sep h1 hQ_ne

lemma helper_K_int_sep_gen_is_separable {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K)
    (K'_int : IntermediateField K A)
    (k'_in_K' : IntermediateField k K'_int)
    (B : Finset K)
    (D : Finset (IntermediateField.adjoin k (S : Set K)))
    (hD : ∀ x ∈ B, ∀ i, (minpoly (IntermediateField.adjoin k (S : Set K)) (x ^ (p ^ e))).coeff i ∈ D)
    (h_sep : ∀ x : K, IsSeparable (IntermediateField.adjoin k (S : Set K)) (x ^ (p ^ e)))
    (E_prime : IntermediateField k'_in_K' K'_int)
    (h_gen : (⊤ : IntermediateField E_prime K'_int) = IntermediateField.adjoin E_prime ((algebraMap K K'_int) '' (B : Set K)))
    (hk'_roots : ∀ x ∈ D, ∃ y : E_prime, y ^ (p ^ e) = algebraMap (IntermediateField.adjoin k (S : Set K)) K'_int x) :
    Algebra.IsSeparable E_prime K'_int := by
  let B_img := (algebraMap K K'_int) '' (B : Set K)
  have h_gen2 : (⊤ : IntermediateField E_prime K'_int) = IntermediateField.adjoin E_prime B_img := h_gen
  letI := Classical.decEq K'_int
  apply is_separable_of_generators_finset (B.image (algebraMap K K'_int))
  · have h_img_eq : ((B.image (algebraMap K K'_int) : Finset K'_int) : Set K'_int) = B_img := by exact Finset.coe_image
    rw [h_img_eq]
    exact h_gen2
  · intro b' hb'
    rw [Finset.mem_image] at hb'
    rcases hb' with ⟨b, hb, rfl⟩
    exact helper_single_generator_separable p e S K'_int k'_in_K' b D (hD b hb) (h_sep b) E_prime hk'_roots

lemma helper_algebraic_independent_of_purely_inseparable {k L E : Type*} [Field k] [Field L] [Field E]
    [Algebra k L] [Algebra k E] [Algebra L E] [IsScalarTower k L E]
    [IsPurelyInseparable k L] (S : Set E) (h_indep : AlgebraicIndependent k (fun x : S ↦ (x : E))) :
    AlgebraicIndependent L (fun x : S ↦ (x : E)) := by
  apply h_indep.extendScalars L

lemma alg_indep_of_power {k K : Type*} [Field k] [Field K] [Algebra k K]
    (p e : ℕ) [Fact p.Prime] [CharP k p] [CharP K p]
    (S_prime : Set K) (f : S_prime → K) (hf : ∀ x, f x = (x : K) ^ (p ^ e))
    (h_indep : AlgebraicIndependent k f) :
    AlgebraicIndependent k (fun x : S_prime ↦ (x : K)) := by
  have H : ∀ P : MvPolynomial S_prime k, MvPolynomial.aeval (fun x : S_prime ↦ (x : K)) P = 0 → P = 0 := by
    intro P hP
    have hp_ne : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    have hPp : (MvPolynomial.aeval (fun x : S_prime ↦ (x : K)) P) ^ (p ^ e) = 0 := by
      rw [hP, zero_pow (pow_pos (Nat.pos_of_ne_zero hp_ne) e).ne.symm]
    have eq1 : (MvPolynomial.aeval (fun x : S_prime ↦ (x : K)) P) ^ (p ^ e) =
      MvPolynomial.aeval (fun x : S_prime ↦ (x : K) ^ (p ^ e)) (MvPolynomial.map (iterateFrobenius k p e) P) := by
      clear(hP)hf h_indep hPp hp_ne
      norm_num[iterateFrobenius, P.aeval_def, P.eval₂_eq,<-map_pow,sum_pow_char_pow,funext_iff]
      norm_num [pow_right_comm, mul_pow, P.aeval_def, P.eval₂_eq, false,← Finset.prod_pow]
      norm_num[MvPolynomial.aeval_def, P.eval₂_eq]
    rw [eq1] at hPp
    have eq2 : MvPolynomial.aeval (fun x : S_prime ↦ (x : K) ^ (p ^ e)) (MvPolynomial.map (iterateFrobenius k p e) P) =
      MvPolynomial.aeval f (MvPolynomial.map (iterateFrobenius k p e) P) := by
      apply congr_fun
      apply congr_arg
      ext x
      simp
      exact (hf x).symm
    rw [eq2] at hPp
    have h_inj : Function.Injective (MvPolynomial.aeval f : MvPolynomial S_prime k → K) := h_indep
    have h_map_zero : MvPolynomial.map (iterateFrobenius k p e) P = 0 := h_inj hPp
    have h_inj_map : Function.Injective (MvPolynomial.map (iterateFrobenius k p e) : MvPolynomial S_prime k → MvPolynomial S_prime k) := by
      apply MvPolynomial.map_injective
      exact RingHom.injective _
    have h_map_zero2 : MvPolynomial.map (iterateFrobenius k p e) P = MvPolynomial.map (iterateFrobenius k p e) 0 := by
      rw [h_map_zero, map_zero]
    exact h_inj_map h_map_zero2
  have H2 : Function.Injective (MvPolynomial.aeval (fun x : S_prime ↦ (x : K)) : MvPolynomial S_prime k →ₐ[k] K) := by
    apply (injective_iff_map_eq_zero (MvPolynomial.aeval (fun x : S_prime ↦ (x : K)) : MvPolynomial S_prime k →ₐ[k] K).toRingHom.toAddMonoidHom).mpr
    exact H
  exact H2

lemma helper_algebraic_independent_roots {L E : Type*} [Field L] [Field E] [Algebra L E]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP L p] (e : ℕ) (S_prime : Set E) (S_img : Set E)
    (h_pow : ∀ y ∈ S_prime, y ^ (p ^ e) ∈ S_img)
    (h_inj : Set.InjOn (fun y => y ^ (p ^ e)) S_prime)
    (h_surj : Set.SurjOn (fun y => y ^ (p ^ e)) S_prime S_img)
    (h_indep : AlgebraicIndependent L (fun x : S_img ↦ (x : E))) :
    AlgebraicIndependent L (fun x : S_prime ↦ (x : E)) := by
  let f : S_prime → S_img := fun x => ⟨(x : E) ^ (p ^ e), h_pow (x : E) x.property⟩
  have hf_inj : Function.Injective f := by
    intro x1 x2 h_eq
    have h_eq2 : (f x1 : E) = (f x2 : E) := congr_arg Subtype.val h_eq
    exact Subtype.ext (h_inj x1.property x2.property h_eq2)
  have h_indep_comp : AlgebraicIndependent L (fun x : S_prime ↦ (x : E) ^ (p ^ e)) := h_indep.comp f hf_inj
  haveI : CharP E p := RingHom.charP_iff_charP (algebraMap L E) p |>.mp inferInstance
  exact alg_indep_of_power p e S_prime (fun x : S_prime ↦ (x : E) ^ (p ^ e)) (fun x => rfl) h_indep_comp

lemma helper_algebraic_independent_map {k K K'_int : Type*} [Field k] [Field K] [Field K'_int]
    [Algebra k K] [Algebra k K'_int] [Algebra K K'_int] [IsScalarTower k K K'_int]
    (S : Finset K) (h_indep : AlgebraicIndependent k (fun x : (S : Set K) ↦ (x : K))) :
    AlgebraicIndependent k (fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) := by
  let f_alg := IsScalarTower.toAlgHom k K K'_int
  have h1 : AlgebraicIndependent k (fun x : (S : Set K) ↦ f_alg (x : K)) := by
    have h_aeval : (MvPolynomial.aeval (fun x : (S : Set K) ↦ f_alg (x : K)) : MvPolynomial (S : Set K) k →ₐ[k] K'_int) = f_alg.comp (MvPolynomial.aeval (fun x : (S : Set K) ↦ (x : K))) := by
      ext i
      simp
    apply (injective_iff_map_eq_zero (MvPolynomial.aeval (fun x : (S : Set K) ↦ f_alg (x : K)) : MvPolynomial (S : Set K) k →ₐ[k] K'_int).toRingHom.toAddMonoidHom).mpr
    intro P hP
    have hP2 : f_alg.comp (MvPolynomial.aeval (fun x : (S : Set K) ↦ (x : K))) P = 0 := by
      have hP3 : (MvPolynomial.aeval (fun x : (S : Set K) ↦ f_alg (x : K))) P = 0 := hP
      rw [h_aeval] at hP3
      exact hP3
    have h_inj : Function.Injective f_alg := RingHom.injective (algebraMap K K'_int)
    have h_aeval_zero : MvPolynomial.aeval (fun x : (S : Set K) ↦ (x : K)) P = 0 := by
      have h0 : f_alg 0 = 0 := map_zero f_alg
      have hP4 : f_alg (MvPolynomial.aeval (fun x : (S : Set K) ↦ (x : K)) P) = f_alg 0 := by
        have hP2_val : f_alg (MvPolynomial.aeval (fun x : (S : Set K) ↦ (x : K)) P) = 0 := hP2
        rw [hP2_val]
        exact h0.symm
      exact h_inj hP4
    have h_indep_inj : Function.Injective (MvPolynomial.aeval (fun x : (S : Set K) ↦ (x : K)) : MvPolynomial (S : Set K) k →ₐ[k] K) := h_indep
    have h_zero : MvPolynomial.aeval (fun x : (S : Set K) ↦ (x : K)) (0 : MvPolynomial (S : Set K) k) = 0 := map_zero _
    have h_aeval_zero2 : MvPolynomial.aeval (fun x : (S : Set K) ↦ (x : K)) P = MvPolynomial.aeval (fun x : (S : Set K) ↦ (x : K)) (0 : MvPolynomial (S : Set K) k) := by
      rw [h_aeval_zero, h_zero]
    exact h_indep_inj h_aeval_zero2
  let f : (S : Set K) ≃ ((algebraMap K K'_int) '' (S : Set K)) := Equiv.Set.imageOfInjOn (algebraMap K K'_int) (S : Set K) ((RingHom.injective (algebraMap K K'_int)).injOn)
  have h_comp : (fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) ∘ f = (fun x : (S : Set K) ↦ f_alg (x : K)) := by
    ext x
    rfl
  have h2 : AlgebraicIndependent k ((fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) ∘ f) := by
    have h_eq : ((fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) ∘ f) = (fun x : (S : Set K) ↦ f_alg (x : K)) := h_comp
    rw [h_eq]
    exact h1
  have h_aeval_equiv : ∀ P : MvPolynomial ((algebraMap K K'_int) '' (S : Set K)) k, MvPolynomial.aeval (fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) P = MvPolynomial.aeval ((fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) ∘ f) (MvPolynomial.rename f.symm P) := by
    intro P
    rw [MvPolynomial.aeval_rename]
    have h_comp2 : ((fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) ∘ f) ∘ f.symm = (fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) := by
      ext x
      simp
    rw [h_comp2]
  apply (injective_iff_map_eq_zero (MvPolynomial.aeval (fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) : MvPolynomial ((algebraMap K K'_int) '' (S : Set K)) k →ₐ[k] K'_int).toRingHom.toAddMonoidHom).mpr
  intro P hP
  have hP3 : MvPolynomial.aeval (fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) P = 0 := hP
  rw [h_aeval_equiv P] at hP3
  have h_inj2 : Function.Injective (MvPolynomial.aeval ((fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) ∘ f) : MvPolynomial (S : Set K) k →ₐ[k] K'_int) := h2
  have h_zero2 : MvPolynomial.aeval ((fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) ∘ f) (0 : MvPolynomial (S : Set K) k) = 0 := map_zero _
  have hP2 : MvPolynomial.aeval ((fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) ∘ f) (MvPolynomial.rename f.symm P) = MvPolynomial.aeval ((fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) ∘ f) (0 : MvPolynomial (S : Set K) k) := by
    have h_eval_P : MvPolynomial.aeval ((fun x : ((algebraMap K K'_int) '' (S : Set K)) ↦ (x : K'_int)) ∘ f) (MvPolynomial.rename f.symm P) = 0 := hP3
    rw [h_eval_P]
    exact h_zero2.symm
  have h_renamed_zero : MvPolynomial.rename f.symm P = 0 := h_inj2 hP2
  have h_renamed_zero2 : MvPolynomial.rename f (MvPolynomial.rename f.symm P) = MvPolynomial.rename f 0 := by
    rw [h_renamed_zero]
  rw [MvPolynomial.rename_rename, map_zero] at h_renamed_zero2
  have h_comp3 : ⇑f ∘ ⇑f.symm = id := funext f.apply_symm_apply
  rw [h_comp3, MvPolynomial.rename_id] at h_renamed_zero2
  exact h_renamed_zero2

lemma helper_K_int_sep_gen_S_prime_is_trans_basis_step_pow {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K)
    (K'_int : IntermediateField K A)
    (S_prime : Set K'_int)
    (h_S_prime : S_prime = Subtype.val ⁻¹' root_set K A (S : Set K) (p ^ e)) :
    ∀ y ∈ S_prime, y ^ (p ^ e) ∈ (algebraMap K K'_int) '' (S : Set K) := by
  simp_all?-contextual[root_set,funext_iff,Subtype.eq_iff]
  tauto

lemma helper_K_int_sep_gen_S_prime_is_trans_basis_step_inj {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K)
    (K'_int : IntermediateField K A)
    (S_prime : Set K'_int) :
    Set.InjOn (fun y : K'_int => y ^ (p ^ e)) S_prime := by
  use fun and _ _ _ R=>and.eq (by_contra fun and' =>absurd (congr_arg (·.1) (R) ) (e.rec (by simp_all) fun and=>mt fun and=>?_))
  cases CharP.exists A
  cases (by valid:).eq A ( charP_of_injective_algebraMap (algebraMap k A).injective _) with use frobenius_inj _ _ ((pow_mul _ _ _).symm.trans (and.trans (pow_mul _ _ _)))

lemma helper_K_int_sep_gen_S_prime_is_trans_basis_step_surj {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K) (k' : IntermediateField k A)
    (K'_int : IntermediateField K A) (h_eq : K'_int = IntermediateField.adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e)))
    (S_prime : Set K'_int)
    (h_S_prime : S_prime = Subtype.val ⁻¹' root_set K A (S : Set K) (p ^ e)) :
    Set.SurjOn (fun y : K'_int => y ^ (p ^ e)) S_prime ((algebraMap K K'_int) '' (S : Set K)) := by
  norm_num[root_set, false,by assumption']
  rintro-⟨s, and, rfl⟩
  by_cases h:∃y,y^p^e=algebraMap K A s
  · cases h with use⟨by assumption,h_eq▸IntermediateField.subset_adjoin _ _ (by tauto)⟩, (by exists s),by bound
  · cases h ((IsAlgClosed.exists_root _ (Polynomial.degree_X_pow_sub_C (pow_pos (NeZero.pos p) e) (algebraMap K A s)▸Nat.cast_ne_zero.2 (p.pow_pos (NeZero.pos p)).ne')).imp (by simp_all[sub_eq_zero]))

lemma helper_K_int_sep_gen_S_prime_is_trans_basis_indep {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K) (h_trans : IsTranscendenceBasis k (fun x : (S : Set K) ↦ (x : K))) (k' : IntermediateField k A)
    (K'_int : IntermediateField K A) (h_eq : K'_int = IntermediateField.adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e)))
    (k'_in_K' : IntermediateField k K'_int) [IsPurelyInseparable k k'_in_K']
    (S_prime : Set K'_int)
    (h_S_prime : S_prime = Subtype.val ⁻¹' root_set K A (S : Set K) (p ^ e)) :
    AlgebraicIndependent k'_in_K' (fun x : S_prime ↦ (x : K'_int)) := by
  let S_img := (algebraMap K K'_int) '' (S : Set K)
  have h_indep1 : AlgebraicIndependent k (fun x : (S : Set K) ↦ (x : K)) := h_trans.1
  have h_indep2 : AlgebraicIndependent k (fun x : S_img ↦ (x : K'_int)) := helper_algebraic_independent_map S h_indep1
  have h_indep3 : AlgebraicIndependent k'_in_K' (fun x : S_img ↦ (x : K'_int)) := helper_algebraic_independent_of_purely_inseparable S_img h_indep2
  haveI : CharP k'_in_K' p := helper_charP_K (k := k) (K := k'_in_K') p
  apply @helper_algebraic_independent_roots k'_in_K' K'_int _ _ _ p _ _ e S_prime S_img
  · exact helper_K_int_sep_gen_S_prime_is_trans_basis_step_pow (k:=k) (K:=K) (A:=A) p e S K'_int S_prime h_S_prime
  · exact helper_K_int_sep_gen_S_prime_is_trans_basis_step_inj (k:=k) (K:=K) (A:=A) p e S K'_int S_prime
  · exact helper_K_int_sep_gen_S_prime_is_trans_basis_step_surj (k:=k) (K:=K) (A:=A) p e S k' K'_int h_eq S_prime h_S_prime
  · exact h_indep3

lemma helper_K_int_sep_gen_S_prime_is_algebraic {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (K'_int : IntermediateField K A)
    (k'_in_K' : IntermediateField k K'_int)
    (B : Finset K)
    (S_prime : Set K'_int)
    (E_prime : IntermediateField k'_in_K' K'_int)
    (h_E_prime : E_prime = IntermediateField.adjoin k'_in_K' S_prime)
    (h_gen : (⊤ : IntermediateField E_prime K'_int) = IntermediateField.adjoin E_prime ((algebraMap K K'_int) '' (B : Set K)))
    (h_sep_ext : Algebra.IsSeparable E_prime K'_int) :
    Algebra.IsAlgebraic E_prime K'_int := by
  exact (h_sep_ext.isAlgebraic)

lemma isTranscendenceBasis_of_algebraicIndependent_isAlgebraic {k K : Type*} [Field k] [Field K] [Algebra k K]
    (s : Set K) (h_indep : AlgebraicIndependent k (fun x : s ↦ (x : K)))
    (h_alg : Algebra.IsAlgebraic (IntermediateField.adjoin k s) K) :
    IsTranscendenceBasis k (fun x : s ↦ (x : K)) := by
  constructor
  · exact h_indep
  · intro t ht_indep ht_sub
    have hs_range : Set.range (fun x : s ↦ (x : K)) = s := Subtype.range_coe
    rw [hs_range] at ht_sub ⊢
    apply Set.eq_of_subset_of_subset ht_sub
    intro x hx_t
    by_contra hx_not_s
    have h_not_alg : ¬ IsAlgebraic (IntermediateField.adjoin k s) x := by
      intro h_alg_x
      have h1 : IsAlgebraic (IntermediateField.adjoin k s) x := h_alg_x
      -- we can use the fact that t is algebraically independent.
      simp_rw [Set.range, Subtype.exists] at hs_range
      apply hx_not_s
      convert ht_indep.transcendental_adjoin ..
      grind
      use(s).preimage (↑)
      use(? _)
      · valid
      erw[id,Subtype.image_preimage_coe,Set.inter_eq_right.mpr (by assumption)]
      convert h1.restrictScalars _
      exact (algebraMap _ _).comp (Subsemiring.inclusion (IntermediateField.algebra_adjoin_le_adjoin _ _)) |>.toAlgebra
      · use@fun _ _ _=>mul_assoc _ _ _
      use @fun ⟨a, _⟩=>?_
      replace h_indep : IsAlgebraic (Algebra.adjoin k s) a
      · induction‹_› using IntermediateField.adjoin_induction
        · exact (isAlgebraic_algebraMap) (⟨_, Algebra.subset_adjoin (by assumption)⟩: Algebra.adjoin k s)
        · apply isAlgebraic_algebraMap (⟨ _,Subalgebra.algebraMap_mem _ _⟩: Algebra.adjoin _ _)
        · simp_all[IsAlgebraic.add]
        · exact (.inv (by valid ) )
        · simp_all[IsAlgebraic.mul]
      · simp_all only [IsAlgebraic, Polynomial.aeval_eq_sum_range, true, Subtype.eq_iff]
        push_cast [ *]
        congr
    let ⟨h⟩ := h_alg
    exact h_not_alg (h x)

lemma helper_K_int_sep_gen_S_prime_is_trans_basis {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K) (h_trans : IsTranscendenceBasis k (fun x : (S : Set K) ↦ (x : K))) (k' : IntermediateField k A)
    (K'_int : IntermediateField K A) (h_eq : K'_int = IntermediateField.adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e)))
    (k'_in_K' : IntermediateField k K'_int) [IsPurelyInseparable k k'_in_K']
    (B : Finset K)
    (S_prime : Set K'_int)
    (h_S_prime : S_prime = Subtype.val ⁻¹' root_set K A (S : Set K) (p ^ e))
    (E_prime : IntermediateField k'_in_K' K'_int)
    (h_E_prime : E_prime = IntermediateField.adjoin k'_in_K' S_prime)
    (h_gen : (⊤ : IntermediateField E_prime K'_int) = IntermediateField.adjoin E_prime ((algebraMap K K'_int) '' (B : Set K)))
    (h_sep_ext : Algebra.IsSeparable E_prime K'_int) :
    IsTranscendenceBasis k'_in_K' (fun x : S_prime ↦ (x : K'_int)) := by
  have h_indep := helper_K_int_sep_gen_S_prime_is_trans_basis_indep p e S h_trans k' K'_int h_eq k'_in_K' S_prime h_S_prime
  have h_alg := helper_K_int_sep_gen_S_prime_is_algebraic K'_int k'_in_K' B S_prime E_prime h_E_prime h_gen h_sep_ext
  rw [h_E_prime] at h_alg
  exact isTranscendenceBasis_of_algebraicIndependent_isAlgebraic S_prime h_indep h_alg

lemma helper_K_int_separably_generated {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K) (h_trans : IsTranscendenceBasis k (fun x : (S : Set K) ↦ (x : K))) (k' : IntermediateField k A)
    (K'_int : IntermediateField K A) (h_eq : K'_int = IntermediateField.adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e)))
    (k'_in_K' : IntermediateField k K'_int) [IsPurelyInseparable k k'_in_K']
    (hk_eq : k'_in_K'.toSubalgebra = Subalgebra.comap (K'_int.val.restrictScalars k) k'.toSubalgebra)
    (B : Finset K) (hB : IntermediateField.adjoin (IntermediateField.adjoin k (S : Set K)) (B : Set K) = ⊤)
    (D : Finset (IntermediateField.adjoin k (S : Set K)))
    (hD : ∀ x ∈ B, ∀ i, (minpoly (IntermediateField.adjoin k (S : Set K)) (x ^ (p ^ e))).coeff i ∈ D)
    (h_sep : ∀ x : K, IsSeparable (IntermediateField.adjoin k (S : Set K)) (x ^ (p ^ e)))
    (hk'_roots : ∀ x ∈ D, ∃ y : IntermediateField.adjoin k' (root_set K A (S : Set K) (p ^ e)), y ^ (p ^ e) = algebraMap (IntermediateField.adjoin k (S : Set K)) A x) :
    IsSeparablyGenerated k'_in_K' K'_int := by
  let S_prime : Set K'_int := Subtype.val ⁻¹' root_set K A (S : Set K) (p ^ e)
  have h_S_prime : S_prime = Subtype.val ⁻¹' root_set K A (S : Set K) (p ^ e) := rfl
  let E_prime : IntermediateField k'_in_K' K'_int := IntermediateField.adjoin k'_in_K' S_prime
  have h_E_prime : E_prime = IntermediateField.adjoin k'_in_K' S_prime := rfl
  have h_gen := helper_K_int_sep_gen_E_prime_contains_B p e S k' K'_int h_eq k'_in_K' hk_eq B hB S_prime h_S_prime E_prime h_E_prime
  have hk'_roots_E := helper_translate_roots p e S k' K'_int h_eq k'_in_K' hk_eq S_prime h_S_prime E_prime h_E_prime D hk'_roots
  have h_sep_ext := helper_K_int_sep_gen_is_separable p e S K'_int k'_in_K' B D hD h_sep E_prime h_gen hk'_roots_E
  have h_trans_basis := helper_K_int_sep_gen_S_prime_is_trans_basis p e S h_trans k' K'_int h_eq k'_in_K' B S_prime h_S_prime E_prime h_E_prime h_gen h_sep_ext
  exact ⟨S_prime, h_trans_basis, h_sep_ext⟩

lemma helper_k'_in_K'_purely_inseparable {k K A : Type*} [Field k] [Field K] [Field A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A] [IsAlgClosed A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (e : ℕ) (S : Finset K) (k' : IntermediateField k A)
    [IsPurelyInseparable k k']
    (K'_int : IntermediateField K A) (h_eq : K'_int = IntermediateField.adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e)))
    (k'_in_K' : IntermediateField k K'_int)
    (hk_eq : k'_in_K'.toSubalgebra = Subalgebra.comap (K'_int.val.restrictScalars k) k'.toSubalgebra) :
    IsPurelyInseparable k k'_in_K' := by
  haveI : ExpChar k p := inferInstance
  apply (isPurelyInseparable_iff_pow_mem (F := k) (E := k'_in_K') p).mpr
  intro x
  have h_insep := inferInstanceAs (IsPurelyInseparable k k')
  have hx_A : (x.val : A) ∈ k' := by
    have h1 : x.val ∈ k'_in_K'.toSubalgebra := x.property
    have h2 : x.val ∈ Subalgebra.comap (K'_int.val.restrictScalars k) k'.toSubalgebra := by
      rw [← hk_eq]
      exact h1
    exact h2
  obtain ⟨n, hn⟩ := (isPurelyInseparable_iff_pow_mem (F := k) (E := k') p).mp h_insep ⟨(x.val : A), hx_A⟩
  use n
  obtain ⟨c, hc⟩ := hn
  use c
  apply Subtype.ext
  apply Subtype.ext
  have h1 : (((x ^ (p ^ n) : k'_in_K') : K'_int) : A) = (x.val : A) ^ (p ^ n) := rfl
  have h2 : ((algebraMap k k'_in_K' c : K'_int) : A) = algebraMap k A c := rfl
  rw [h1, h2]
  have h3 : ((⟨(x.val : A), hx_A⟩ ^ (p ^ n) : k') : A) = (x.val : A) ^ (p ^ n) := rfl
  have h4 : ((algebraMap k k' c : k') : A) = algebraMap k A c := rfl
  have h5 : ((algebraMap k k' c : k') : A) = ((⟨(x.val : A), hx_A⟩ ^ (p ^ n) : k') : A) := congr_arg Subtype.val hc
  rw [h3, h4] at h5
  exact h5

lemma exists_K'_k'_in_A
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (A : Type (max u v)) [Field A] [Algebra k A] [Algebra K A] [IsScalarTower k K A] [IsAlgClosed A]
    (S : Finset K) (h_trans : IsTranscendenceBasis k (fun x : (S : Set K) ↦ (x : K)))
    (h_fin : FiniteDimensional (IntermediateField.adjoin k (S : Set K)) K)
    (e : ℕ) (h_sep : ∀ x : K, IsSeparable (IntermediateField.adjoin k (S : Set K)) (x ^ (p ^ e))) :
    ∃ (K' : IntermediateField K A) (k_in_K' : IntermediateField k K'),
      FiniteDimensional K K' ∧ IsPurelyInseparable K K' ∧
      FiniteDimensional k k_in_K' ∧ IsPurelyInseparable k k_in_K' ∧
      IsSeparablyGenerated k_in_K' K' := by
  have ⟨B, hB⟩ := exists_finite_generators_of_finDim (E := IntermediateField.adjoin k (S : Set K)) (K := K)
  have ⟨D, hD⟩ := exists_minpoly_coeffs_finset (E := IntermediateField.adjoin k (S : Set K)) B (p ^ e)
  letI := Classical.decEq K
  let D_K : Finset K := Finset.image (algebraMap (IntermediateField.adjoin k (S : Set K)) K) D
  have hD_prop : ∀ x ∈ D_K, x ∈ IntermediateField.adjoin k (S : Set K) := by
    intro x hx
    dsimp only [D_K] at hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨y, _, rfl⟩
    exact y.property
  have ⟨k', hk'_fin, hk'_insep, hk'_roots⟩ := exists_k_prime_for_finset (A := A) p (S : Set K) e D_K hD_prop
  let K'_int := IntermediateField.adjoin K ((k' : Set A) ∪ root_set K A (S : Set K) (p ^ e))
  use K'_int
  let k'_in_K' : IntermediateField k K'_int := {
    toSubalgebra := Subalgebra.comap (K'_int.val.restrictScalars k) k'.toSubalgebra
    inv_mem' := by
      intro x hx
      show (x⁻¹ : A) ∈ k'
      exact k'.inv_mem hx
  }
  use k'_in_K'
  haveI hk'_fin_inst : FiniteDimensional k k' := hk'_fin
  haveI hk'_insep_inst : IsPurelyInseparable k k' := hk'_insep
  have h_K_fin : FiniteDimensional K K'_int := helper_K_int_finite p e S k' h_fin h_trans
  have h_K_insep : IsPurelyInseparable K K'_int := helper_K_int_purely_inseparable p e S k'
  let equiv : k'_in_K' ≃ₐ[k] k' := {
    toFun := fun x => ⟨(x.val : A), x.property⟩
    invFun := fun x => ⟨⟨(x : A), by
      apply IntermediateField.subset_adjoin
      exact Or.inl x.property⟩, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
    commutes' := fun _ => rfl
  }
  have h_k_fin : FiniteDimensional k k'_in_K' := LinearEquiv.finiteDimensional equiv.symm.toLinearEquiv
  haveI h_k_insep : IsPurelyInseparable k k'_in_K' := helper_k'_in_K'_purely_inseparable p e S k' K'_int rfl k'_in_K' rfl
  have h_sep_gen : IsSeparablyGenerated k'_in_K' K'_int := by
    apply helper_K_int_separably_generated p e S h_trans k' K'_int rfl k'_in_K' rfl B hB D
    · intro x hx i
      exact hD x hx i
    · exact h_sep
    · intro x hx
      let x_K : K := algebraMap (IntermediateField.adjoin k (S : Set K)) K x
      have hx_K : x_K ∈ D_K := by
        dsimp only [x_K, D_K]
        rw [Finset.mem_image]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy⟩ := hk'_roots x_K hx_K
      use y
      have h_eq : algebraMap K A x_K = algebraMap (IntermediateField.adjoin k (S : Set K)) A x := rfl
      rw [← h_eq]
      exact hy
  exact ⟨h_K_fin, h_K_insep, h_k_fin, h_k_insep, h_sep_gen⟩

lemma charP_case_from_algClosed
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (A : Type (max u v)) [Field A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (K' : IntermediateField K A)
    (k_in_K' : IntermediateField k K')
    (h_K_fin : FiniteDimensional K K') (h_K_insep : IsPurelyInseparable K K')
    (h_k_fin : FiniteDimensional k k_in_K') (h_k_insep : IsPurelyInseparable k k_in_K')
    (h_sep : IsSeparablyGenerated k_in_K' K') :
    ∃ (K_res : Type (max u v)) (_ : Field K_res) (_ : Algebra k K_res) (_ : Algebra K K_res)
      (_ : IsScalarTower k K K_res) (k_res : IntermediateField k K_res),
      FiniteDimensional K K_res ∧ IsPurelyInseparable K K_res ∧
      FiniteDimensional k k_res ∧ IsPurelyInseparable k k_res ∧
      IsSeparablyGenerated k_res K_res := by
  exact ⟨K', inferInstance, inferInstance, inferInstance, inferInstance, k_in_K', h_K_fin, h_K_insep, h_k_fin, h_k_insep, h_sep⟩

lemma exists_algClosed_extension {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] :
    ∃ (A : Type (max u v)) (_ : Field A) (_ : Algebra k A) (_ : Algebra K A) (_ : IsScalarTower k K A), IsAlgClosed A := by
  exact ⟨AlgebraicClosure (ULift.{max u v, v} K), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

lemma charP_case_construction {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (S : Finset K) (h_trans : IsTranscendenceBasis k (fun x : (S : Set K) ↦ (x : K)))
    (h_fin : FiniteDimensional (IntermediateField.adjoin k (S : Set K)) K)
    (e : ℕ) (h_sep : ∀ x : K, IsSeparable (IntermediateField.adjoin k (S : Set K)) (x ^ (p ^ e))) :
    ∃ (K' : Type (max u v)) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : IsScalarTower k K K') (k' : IntermediateField k K'),
      FiniteDimensional K K' ∧ IsPurelyInseparable K K' ∧
      FiniteDimensional k k' ∧ IsPurelyInseparable k k' ∧
      IsSeparablyGenerated k' K' := by
  obtain ⟨A, inst_A_field, inst_A_algk, inst_A_algK, inst_tower, inst_closed⟩ := exists_algClosed_extension (k := k) (K := K)
  obtain ⟨K', k_in_K', h_K_fin, h_K_insep, h_k_fin, h_k_insep, h_sep_gen⟩ := exists_K'_k'_in_A p A S h_trans h_fin e h_sep
  exact charP_case_from_algClosed A K' k_in_K' h_K_fin h_K_insep h_k_fin h_k_insep h_sep_gen

lemma charP_case {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] :
    ∃ (K' : Type (max u v)) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : IsScalarTower k K K') (k' : IntermediateField k K'),
      FiniteDimensional K K' ∧ IsPurelyInseparable K K' ∧
      FiniteDimensional k k' ∧ IsPurelyInseparable k k' ∧
      IsSeparablyGenerated k' K' := by
  have h1 := exists_trans_basis_and_finite (k := k) (K := K)
  obtain ⟨S, h_trans, h_fin⟩ := h1
  haveI : CharP (IntermediateField.adjoin k (S : Set K)) p := RingHom.charP_iff_charP (algebraMap k (IntermediateField.adjoin k (S : Set K))) p |>.mp inferInstance
  have h2 := exists_sep_power_of_finite (E := IntermediateField.adjoin k (S : Set K)) (K := K) p
  obtain ⟨e, he⟩ := h2
  exact charP_case_construction p S h_trans h_fin e he

lemma main_theorem_combine {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    ∃ (K' : Type (max u v)) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : IsScalarTower k K K') (k' : IntermediateField k K'),
      FiniteDimensional K K' ∧ IsPurelyInseparable K K' ∧
      FiniteDimensional k k' ∧ IsPurelyInseparable k k' ∧
      IsSeparablyGenerated k' K' := by
  rcases CharP.exists k with ⟨p, _⟩
  rcases eq_or_ne p 0 with rfl | hp
  · haveI : CharZero k := CharP.charP_to_charZero k
    exact charZero_case
  · have hp_prime : p.Prime := by
      have h_or := CharP.char_is_prime_or_zero k p
      cases h_or with
      | inl h_prime => exact h_prime
      | inr h_zero => exact (hp h_zero).elim
    haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
    exact charP_case p

-- EVOLVE-BLOCK-END

theorem exists_isPurelyInseparable_isSeparablyGenerated_of_essFiniteType
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    ∃ (K' : Type (max u v)) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : IsScalarTower k K K') (k' : IntermediateField k K'),
      FiniteDimensional K K' ∧ IsPurelyInseparable K K' ∧
      FiniteDimensional k k' ∧ IsPurelyInseparable k k' ∧
      IsSeparablyGenerated k' K' := by
  -- EVOLVE-BLOCK-START
  have h := main_theorem_combine (k := k) (K := K)
  exact h
  -- EVOLVE-BLOCK-END
