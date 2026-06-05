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

class NormalDomain (R : Type*) [CommRing R] : Prop extends IsDomain R, IsIntegrallyClosed R

class NormalRing (R : Type*) [CommRing R] : Prop where
  localization_atPrime_normalDomain (p : Ideal R) [p.IsPrime] :
    NormalDomain (Localization.AtPrime p)


open Polynomial PowerSeries

-- EVOLVE-BLOCK-START
lemma normalDomain_of_normalRing {A : Type*} [CommRing A] [IsDomain A] [NormalRing A] :
    NormalDomain A := by
  haveI : IsIntegrallyClosed A := by
    apply IsIntegrallyClosed.of_isLocalization_maximal (fun (P : Ideal A) _ => Localization.AtPrime P)
    intro P hP
    have hPrime : P.IsPrime := Ideal.IsMaximal.isPrime hP
    haveI := NormalRing.localization_atPrime_normalDomain P
    infer_instance
  exact { }

lemma NormalDomain.toNormalRing {A : Type*} [CommRing A] [NormalDomain A] :
    NormalRing A := by
  constructor
  intro P hP
  haveI : IsDomain (Localization.AtPrime P) := inferInstance
  have hM : P.primeCompl ≤ nonZeroDivisors A := by
    intro x hx
    rw [mem_nonZeroDivisors_iff_ne_zero]
    rintro rfl
    exact hx P.zero_mem
  haveI : IsIntegrallyClosed (Localization.AtPrime P) := isIntegrallyClosed_of_isLocalization (Localization.AtPrime P) P.primeCompl hM
  exact { }

lemma map_injective {A : Type*} [CommRing A] [IsDomain A] :
    Function.Injective (algebraMap A⟦X⟧ (FractionRing A)⟦X⟧) := by
  intro f g hfg
  ext n
  have h1 : PowerSeries.coeff n (algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ f) = algebraMap A (FractionRing A) (PowerSeries.coeff n f) := by norm_num[RingHom.algebraMap_toAlgebra]
  have h2 : PowerSeries.coeff n (algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ g) = algebraMap A (FractionRing A) (PowerSeries.coeff n g) := by norm_num[ RingHom.algebraMap_toAlgebra]
  have h3 : algebraMap A (FractionRing A) (PowerSeries.coeff n f) = algebraMap A (FractionRing A) (PowerSeries.coeff n g) := by
    rw [← h1, ← h2, hfg]
  exact IsFractionRing.injective A (FractionRing A) h3

noncomputable def map_frac {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Injective f) :
    FractionRing R →+* FractionRing S :=
  IsLocalization.map (T := nonZeroDivisors S) (Q := FractionRing S) f (by
    rintro x hx
    change f x ∈ nonZeroDivisors S
    rw [mem_nonZeroDivisors_iff_ne_zero]
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    intro h
    have h2 : f x = f 0 := by simp [h]
    exact hx (hf h2)
  )

noncomputable def map_powerSeries_frac {A : Type*} [CommRing A] [IsDomain A] :
    FractionRing A⟦X⟧ →+* FractionRing (FractionRing A)⟦X⟧ :=
  map_frac (algebraMap A⟦X⟧ (FractionRing A)⟦X⟧) map_injective

lemma isIntegral_map {R S L M : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing M]
    [Algebra R L] [Algebra S M] (f : R →+* S) (g : L →+* M)
    (h_comm : ∀ x, g (algebraMap R L x) = algebraMap S M (f x))
    (x : L) (hx : IsIntegral R x) : IsIntegral S (g x) := by
  rcases hx with ⟨P, hP_monic, hP_root⟩
  use P.map f
  constructor
  · exact Polynomial.Monic.map f hP_monic
  · have h1 : (P.map f).eval₂ (algebraMap S M) (g x) = g (P.eval₂ (algebraMap R L) x) := by
      norm_num[eval₂_map, P.eval₂_eq_sum_range,show g (f _) = _ from(h_comm _).symm]
      simp_all only
    rw [h1, hP_root, map_zero]

lemma pow_mul_in_range_aux {A : Type*} [CommRing A] [IsDomain A]
    (f : (FractionRing A)⟦X⟧) (b a : A⟦X⟧)
    (h_bf : algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ b * f = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ a)
    (n : ℕ) :
    algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (b ^ n) * f^n = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (a ^ n) := by
  simp_all only [ ←mul_pow, RingHom.map_pow]

lemma pow_mul_in_range_lt {A : Type*} [CommRing A] [IsDomain A]
    (f : (FractionRing A)⟦X⟧) (b a : A⟦X⟧)
    (h_bf : algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ b * f = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ a)
    (m n : ℕ) (h_lt : n < m) (hm : 0 < m) :
    ∃ (g : A⟦X⟧), algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (b ^ (m - 1)) * f^n = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ g := by
  refine ⟨b ^ (m-1-n) *a^ (n : ℕ),by zify[←h_bf,Nat.sub_add_cancel (n.le_sub_one_of_lt h_lt)▸pow_add _ _ _,mul_assoc, mul_pow]⟩

lemma pow_mul_in_range {A : Type*} [CommRing A] [IsDomain A]
    (f : (FractionRing A)⟦X⟧) (b a : A⟦X⟧)
    (h_bf : algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ b * f = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ a)
    (m : ℕ) (hm : 0 < m) (c : ℕ → A⟦X⟧)
    (hf_eq : f^m = ∑ i ∈ Finset.range m, algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (c i) * f^i)
    (n : ℕ) :
    ∃ (g : A⟦X⟧), algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (b ^ (m - 1)) * f^n = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ g := by
  refine n.strongRec ?_
  use fun and x => if I:m≤ and then(? _)else(? _)
  · refine(m.exists_eq_add_of_le' I).elim fun and k=>(Classical.axiomOfChoice fun and2 : Fin m=>x (and+and2) (by valid)).elim fun a s=>⟨∑B,c B.1*a B,?_⟩
    zify[k,←s,hf_eq,mul_left_comm (algebraMap (A⟦X⟧) _ _),pow_add, Finset.mul_sum, Finset.sum_range]
  · use b^(m-1-and) *a^and,by zify[←h_bf,mul_assoc,Nat.sub_add_cancel (and.le_sub_one_of_lt (not_le.1 I))▸pow_add _ _ _, mul_pow]

lemma fg_of_denom_pow_mul {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (c : FractionRing A) (d_r : A) (hd_r : d_r ≠ 0)
    (h_int : ∀ n : ℕ, ∃ (a : A), algebraMap A (FractionRing A) a = algebraMap A (FractionRing A) d_r * c^n) :
    IsIntegral A c := by
  let S := Algebra.adjoin A ({c} : Set (FractionRing A))
  have h_sub : ∀ z : S, (algebraMap A (FractionRing A) d_r) * z.val ∈ LinearMap.range (Algebra.linearMap A (FractionRing A)) := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx⟩ := Algebra.adjoin_singleton_eq_range_aeval _ _ |>.le hz
    simp_all -contextual [aeval_eq_sum_range, mul_left_comm, ← hx, Finset.mul_sum, Submodule.sum_mem, Submodule.smul_mem _,funext_iff]
  have h_add : ∀ a b : S, Classical.choose (h_sub (a + b)) = Classical.choose (h_sub a) + Classical.choose (h_sub b) := by
    use fun and i=>IsFractionRing.injective _ _ ((h_sub _).choose_spec.trans (symm (( RingHom.map_add _ _ _).trans ((congr_arg₂ _ (h_sub and).choose_spec (h_sub i).choose_spec).trans (mul_add _ _ _).symm))))
  have h_smul : ∀ (r : A) (a : S), Classical.choose (h_sub (r • a)) = r * Classical.choose (h_sub a) := by
    delta Classical.choose
    use fun and i=>match Classical.indefiniteDescription _ _ with| ⟨a, e⟩=>match Classical.indefiniteDescription _ _ with|⟨b,k⟩=>IsFractionRing.injective _ _ (e.trans ( ((congr_arg _) ↑(Algebra.smul_def _ _)).trans ((mul_left_comm _ _ _).trans ?_)))
    norm_num[←k,funext_iff]
  let f : S →ₗ[A] A := {
    toFun := fun z => Classical.choose (h_sub z)
    map_add' := h_add
    map_smul' := h_smul
  }
  have hf_inj : Function.Injective f := by
    intro a b hab
    exact (a.eq (mul_left_cancel₀ (IsFractionRing.to_map_eq_zero_iff.not.mpr (by assumption)) ( (h_sub a).choose_spec.symm.trans ( ((congr_arg _) hab).trans ( h_sub b).choose_spec))))
  haveI h_noeth : IsNoetherian A S := isNoetherian_of_injective f hf_inj
  exact isIntegral_of_submodule_noetherian S h_noeth c (Algebra.subset_adjoin (Set.mem_singleton c))


lemma int_of_denom_pow_mul {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (c : FractionRing A) (d_r : A) (hd_r : d_r ≠ 0)
    (h_int : ∀ n : ℕ, ∃ (a : A), algebraMap A (FractionRing A) a = algebraMap A (FractionRing A) d_r * c^n) :
    ∃ (a : A), algebraMap A (FractionRing A) a = c := by
  have h1 : IsIntegral A c := fg_of_denom_pow_mul c d_r hd_r h_int
  exact (isIntegrallyClosed_iff (FractionRing A)).1 (by infer_instance) h1

lemma exists_lowest_coeff {A : Type*} [CommRing A] (d : A⟦X⟧) (hd : d ≠ 0) :
    ∃ (r : ℕ), PowerSeries.coeff r d ≠ 0 ∧ ∀ i < r, PowerSeries.coeff i d = 0 := by
  haveI := Classical.decEq A
  exact ⟨ _,Nat.find_spec (not_forall.1 (hd ∘d.ext)), (by_contra ∘·.find_min _)⟩

lemma coeff_integral_of_denom {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (f : (FractionRing A)⟦X⟧) (d : A⟦X⟧) (hd : d ≠ 0)
    (h_df : ∀ n : ℕ, ∃ (g : A⟦X⟧), algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ g = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ d * f^n) :
    ∀ k : ℕ, ∃ (a : A), algebraMap A (FractionRing A) a = PowerSeries.coeff k f := by
  intro k
  induction' k using Nat.strong_induction_on with k ih
  obtain ⟨r, hd_r, hd_lt⟩ := exists_lowest_coeff d hd
  have h_p_exists : ∃ (p : A⟦X⟧), (∀ i < k, PowerSeries.coeff i (algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ p) = PowerSeries.coeff i f) ∧ (∀ i ≥ k, PowerSeries.coeff i p = 0) := by
    choose! _ _ using ih
    simp_all[RingHom.algebraMap_toAlgebra]
    exact ⟨∑ a ∈.range k,.monomial a (‹∀_, _› a),by simp_all[PowerSeries.coeff_monomial, if_neg]⟩
  obtain ⟨p, hp, hp_k⟩ := h_p_exists
  let h := f - algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ p
  have hh_lt : ∀ i < k, PowerSeries.coeff i h = 0 := by
    apply(sub_eq_zero.mpr ∘.symm ∘hp ·)
  have hh_k : PowerSeries.coeff k h = PowerSeries.coeff k f := by
    norm_num[*,h,RingHom.algebraMap_toAlgebra]
  have h_dh_n : ∀ n : ℕ, ∃ (g : A⟦X⟧), algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ g = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ d * h^n := by
    simp_rw [h, sub_eq_add_neg, add_pow]
    use fun and=>⟨∑ a ∈.range (and+1), ( h_df a).choose*(-p)^ (and-a) *and.choose a,by zify[←mul_assoc,(h_df _).choose_spec, Finset.mul_sum]⟩
  have h_coeff_dhn : ∀ n : ℕ, PowerSeries.coeff (r + k * n) (algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ d * h^n) = algebraMap A (FractionRing A) (PowerSeries.coeff r d) * (PowerSeries.coeff k f)^n := by
    norm_num[PowerSeries.coeff_mul,funext_iff,RingHom.algebraMap_toAlgebra]
    use fun and=>hh_k▸.trans ( Finset.sum_eq_single_of_mem (r,k*and) (by norm_num[ Finset.HasAntidiagonal.antidiagonal]) fun and R M=>? _) ((congr_arg _) (and.rec (by norm_num) ?_))
    · use(mul_eq_zero.2 ((lt_or_gt_of_ne (M ∘ (and.ext · (add_left_cancel (‹_›▸ Finset.mem_antidiagonal.1 R))))).imp (by norm_num[hd_lt,.]) fun and=>?_))
      use(‹ℕ›:).rec (nofun) ?_ (‹_ ×_›:).2 (by linarith[ Finset.mem_antidiagonal.1 R]:(‹_ ×_›:).2<k*(‹ℕ›:))
      simp_rw [k.mul_succ,pow_succ,PowerSeries.coeff_mul]
      exact fun and a s C=> Finset.sum_eq_zero fun and=>mul_eq_zero.2 ∘.imp (a _) (@hh_lt _) ∘by valid ∘ Finset.mem_antidiagonal.1
    norm_num[PowerSeries.coeff_mul,pow_add,mul_add]
    use fun and true => true▸ Finset.sum_eq_single_of_mem (_, _) (by norm_num[ Finset.HasAntidiagonal.antidiagonal]) fun and R M=> if a:_ then(mul_eq_zero_of_right _) ↑(hh_lt _ a)else(mul_eq_zero_of_left) ? _ _
    use(‹ℕ›:).strongRec ?_ and.1 (by_contra (by bound[ Finset.mem_antidiagonal.1 R]):and.1<k*(‹ℕ›:))
    rintro@c _ _ _
    · omega
    simp_rw [pow_succ, mul_add_one,PowerSeries.coeff_mul]at*
    exact Finset.sum_eq_zero fun and=>mul_eq_zero.2 ∘.imp (by apply_rules[Nat.lt_succ_self]) (hh_lt _) ∘by valid ∘ Finset.mem_antidiagonal.1
  have h_int_c : ∀ n : ℕ, ∃ (a : A), algebraMap A (FractionRing A) a = algebraMap A (FractionRing A) (PowerSeries.coeff r d) * (PowerSeries.coeff k f)^n := by
    use fun and=>by_contra fun and' =>?_
    cases h_dh_n and
    norm_num[<-h_coeff_dhn,←by assumption]at and'
    norm_num[RingHom.algebraMap_toAlgebra,funext_iff]at and'
  exact int_of_denom_pow_mul (PowerSeries.coeff k f) (PowerSeries.coeff r d) hd_r h_int_c

lemma mem_A_of_denom_pow_mul {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (f : (FractionRing A)⟦X⟧) (d : A⟦X⟧) (hd : d ≠ 0)
    (h_df : ∀ n : ℕ, ∃ (g : A⟦X⟧), algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ d * f^n = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ g) :
    ∃ (g : A⟦X⟧), algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ g = f := by
  have h_coeff : ∀ k, ∃ (a : A), algebraMap A (FractionRing A) a = PowerSeries.coeff k f := by
    intro k
    have h_df2 : ∀ n : ℕ, ∃ (g : A⟦X⟧), algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ g = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ d * f^n := by
      intro n
      rcases h_df n with ⟨g, hg⟩
      exact ⟨g, hg.symm⟩
    exact coeff_integral_of_denom f d hd h_df2 k
  use PowerSeries.mk (fun k => Classical.choose (h_coeff k))
  ext n
  have h1 : PowerSeries.coeff n (algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (PowerSeries.mk fun k ↦ Classical.choose (h_coeff k))) = algebraMap A (FractionRing A) (PowerSeries.coeff n (PowerSeries.mk fun k ↦ Classical.choose (h_coeff k))) := by norm_num[RingHom.algebraMap_toAlgebra]
  rw [h1]
  have h2 : PowerSeries.coeff n (PowerSeries.mk fun k ↦ Classical.choose (h_coeff k)) = Classical.choose (h_coeff n) := by bound
  rw [h2]
  exact Classical.choose_spec (h_coeff n)

lemma eq_of_integral_K {A : Type*} [CommRing A] [IsDomain A]
    (f : (FractionRing A)⟦X⟧) (hf_int : IsIntegral A⟦X⟧ f) :
    ∃ (m : ℕ) (hm : 0 < m) (c : ℕ → A⟦X⟧), f^m = ∑ i ∈ Finset.range m, algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (c i) * f^i := by
  apply@hf_int.elim
  use fun R L=>⟨natDegree R,pos_of_ne_zero fun and=>by simp_all,-R.coeff,by simp_all[eval₂_eq_sum_range, L.1, add_eq_zero_iff_eq_neg, Finset.sum]⟩

lemma mem_A_of_integral_K {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (a b : A⟦X⟧) (hb : b ≠ 0)
    (f : (FractionRing A)⟦X⟧)
    (h_bf : algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ b * f = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ a)
    (hf_int : IsIntegral A⟦X⟧ f) :
    ∃ (g : A⟦X⟧), algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ g = f := by
  obtain ⟨m, hm, c, hf_eq⟩ := eq_of_integral_K f hf_int
  have hd_ne : b ^ (m - 1) ≠ 0 := pow_ne_zero _ hb
  have h_df : ∀ n : ℕ, ∃ (g : A⟦X⟧), algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (b ^ (m - 1)) * f^n = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ g := pow_mul_in_range f b a h_bf m hm c hf_eq
  exact mem_A_of_denom_pow_mul f (b ^ (m - 1)) hd_ne h_df

lemma coeff_mul_lowest {R : Type*} [CommRing R] (p q : R⟦X⟧) (r s : ℕ)
    (hp : ∀ i < r, PowerSeries.coeff i p = 0)
    (hq : ∀ i < s, PowerSeries.coeff i q = 0) :
    PowerSeries.coeff (r + s) (p * q) = PowerSeries.coeff r p * PowerSeries.coeff s q := by
  ((nontriviality ) )
  rw[p.coeff_mul]
  exact Finset.sum_eq_single_of_mem (r,s) (by bound) fun and R M=>by cases not_and_or.mp (M ∘Prod.ext_iff.2) with match Finset.mem_antidiagonal.mp R with | S=>grind

lemma coeff_pow_lowest {R : Type*} [CommRing R] (p : R⟦X⟧) (k n : ℕ)
    (hp : ∀ i < k, PowerSeries.coeff i p = 0) :
    (∀ i < k * n, PowerSeries.coeff i (p ^ n) = 0) ∧
    PowerSeries.coeff (k * n) (p ^ n) = (PowerSeries.coeff k p) ^ n := by
  refine n.rec (by norm_num) fun and x =>pow_succ p and▸⟨fun a s=>.trans (PowerSeries.coeff_mul _ _ _) ( Finset.sum_eq_zero fun and h=>? _),.trans (PowerSeries.coeff_mul _ _ _) ?_⟩
  · exact (em _).elim (by rw [(x.1 _) ·, zero_mul]) fun and' =>by rw [hp _ (by cases Finset.mem_antidiagonal.1 h with linarith),mul_zero]
  rw[k.mul_succ, Finset.sum_eq_single_of_mem (k*and,k) (by norm_num[ Finset.HasAntidiagonal.antidiagonal]) fun and R M=>? _,pow_succ,x.2]
  exact (em _).elim (by rw [(x.1 _) ·, zero_mul]) fun and' =>by rw [hp _ (not_le.1 (M ∘and.ext_iff.2 ∘ (by valid ∘ Finset.mem_antidiagonal.1) R)),mul_zero]

lemma eq_of_integral_frac {A : Type*} [CommRing A] [IsDomain A]
    (a b : A⟦X⟧) (hb : b ≠ 0)
    (h_int : IsIntegral A⟦X⟧ (algebraMap A⟦X⟧ (FractionRing A⟦X⟧) a / algebraMap A⟦X⟧ (FractionRing A⟦X⟧) b)) :
    ∃ (n : ℕ) (hn : 0 < n) (c : ℕ → A⟦X⟧), a ^ n = - ∑ i ∈ Finset.range n, c i * a ^ i * b ^ (n - i) := by
  choose _ _ _simpa using(id) h_int
  norm_num[*,eval₂_eq_sum_range,mul_assoc,div_pow, Finset.sum_range_succ]at*
  refine ⟨natDegree (by valid),pos_of_ne_zero fun and=>by simp_all,coeff (by valid),IsFractionRing.injective _ (FractionRing (A⟦X⟧)) (? _)⟩
  simp_all only[mul_assoc, map_sum, map_mul, map_pow, map_neg, add_eq_zero_iff_neg_eq, Finset.sum_mul,div_eq_mul_inv,pow_sub₀,le_of_lt ∘ Finset.mem_range.1]
  simp_all[←div_eq_of_eq_mul ↑_ _simpa, Finset.sum_mul,div_eq_mul_inv,mul_comm (_^natDegree _:FractionRing (A⟦X⟧)),mul_assoc,pow_sub₀,le_of_lt ∘ Finset.mem_range.1]

lemma map_eq_of_eq {A : Type*} [CommRing A] [IsDomain A]
    (a b : A⟦X⟧) (n : ℕ) (c : ℕ → A⟦X⟧)
    (heq : a ^ n = - ∑ i ∈ Finset.range n, c i * a ^ i * b ^ (n - i)) :
    (algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ a) ^ n = - ∑ i ∈ Finset.range n, (algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (c i)) * (algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ a) ^ i * (algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ b) ^ (n - i) := by
  have h_map := congrArg (algebraMap A⟦X⟧ (FractionRing A)⟦X⟧) heq
  linear_combination2(norm:=zify)h_map

lemma isIntegral_K_of_eq {A : Type*} [CommRing A] [IsDomain A]
    (a b : (FractionRing A)⟦X⟧) (f : (FractionRing A)⟦X⟧) (hb : b ≠ 0)
    (n : ℕ) (hn : 0 < n) (c : ℕ → A⟦X⟧)
    (hf_eq : a = b * f)
    (heq : a ^ n = - ∑ i ∈ Finset.range n, algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (c i) * a ^ i * b ^ (n - i)) :
    IsIntegral A⟦X⟧ f := by
  have heq1 : (b * f) ^ n = - ∑ i ∈ Finset.range n, algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (c i) * (b * f) ^ i * b ^ (n - i) := by
    simp_all only
  have heq2 : b ^ n * f ^ n = - ∑ i ∈ Finset.range n, b ^ n * (algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (c i) * f ^ i) := by
    exact (mul_pow b _ _)▸heq1.trans (congr_arg _ (Finset.sum_congr rfl fun and β=> (and.add_sub_of_le (List.mem_range.1 β).le▸pow_add b _ _)▸by ring))
  have heq3 : b ^ n * f ^ n = b ^ n * (- ∑ i ∈ Finset.range n, algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (c i) * f ^ i) := by
    rwa[mul_neg,@@ Finset.mul_sum]
  have h_bn_ne : b ^ n ≠ 0 := pow_ne_zero n hb
  have heq4 : f ^ n = - ∑ i ∈ Finset.range n, algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (c i) * f ^ i := by
    exact mul_left_cancel₀ h_bn_ne heq3
  use .X^n+∑ a ∈.range n,.monomial a (c a),Polynomial.monic_X_pow_add ((Polynomial.degree_sum_le _ _).trans_lt (( Finset.sup_lt_iff<|WithBot.bot_lt_coe _).2 fun and=>?_))
  · norm_num[*,eval₂_finset_sum]
  · exact (degree_monomial_le _ _).trans_lt ∘WithBot.coe_lt_coe.mpr ∘ Finset.mem_range.mp

lemma isIntegral_K_of_integral_frac {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (a b : A⟦X⟧) (hb : b ≠ 0)
    (h_int : IsIntegral A⟦X⟧ (algebraMap A⟦X⟧ (FractionRing A⟦X⟧) a / algebraMap A⟦X⟧ (FractionRing A⟦X⟧) b))
    (f : (FractionRing A)⟦X⟧)
    (hf_eq : algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ a = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ b * f) :
    IsIntegral A⟦X⟧ f := by
  obtain ⟨n, hn, c, heq⟩ := eq_of_integral_frac a b hb h_int
  have heq2 := map_eq_of_eq a b n c heq
  have hb_K : algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ b ≠ 0 := by
    intro h
    have h2 : algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ b = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ 0 := by rw [h, map_zero]
    exact hb (map_injective h2)
  exact isIntegral_K_of_eq _ _ f hb_K n hn c hf_eq heq2

lemma dvd_of_integral_K {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (a b : A⟦X⟧) (hb : b ≠ 0)
    (h_int : IsIntegral A⟦X⟧ (algebraMap A⟦X⟧ (FractionRing A⟦X⟧) a / algebraMap A⟦X⟧ (FractionRing A⟦X⟧) b)) :
    ∃ (f : (FractionRing A)⟦X⟧), algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ a = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ b * f := by
  let f_map := algebraMap A⟦X⟧ (FractionRing A)⟦X⟧
  let g_map := map_powerSeries_frac (A := A)
  have h_comm : ∀ x, g_map (algebraMap A⟦X⟧ (FractionRing A⟦X⟧) x) = algebraMap (FractionRing A)⟦X⟧ (FractionRing (FractionRing A)⟦X⟧) (f_map x) := by
    norm_num[g_map,f_map,map_powerSeries_frac]
    norm_num[map_frac,funext_iff]
  have h_int_g : IsIntegral (FractionRing A)⟦X⟧ (g_map (algebraMap A⟦X⟧ (FractionRing A⟦X⟧) a / algebraMap A⟦X⟧ (FractionRing A⟦X⟧) b)) := by
    exact isIntegral_map f_map g_map h_comm _ h_int
  have h_map_div : g_map (algebraMap A⟦X⟧ (FractionRing A⟦X⟧) a / algebraMap A⟦X⟧ (FractionRing A⟦X⟧) b) = g_map (algebraMap A⟦X⟧ (FractionRing A⟦X⟧) a) / g_map (algebraMap A⟦X⟧ (FractionRing A⟦X⟧) b) := map_div₀ g_map _ _
  rw [h_map_div, h_comm a, h_comm b] at h_int_g
  haveI : IsIntegrallyClosed (FractionRing A)⟦X⟧ := inferInstance
  have h_exists := (isIntegrallyClosed_iff (FractionRing (FractionRing A)⟦X⟧)).1 (by infer_instance) h_int_g
  rcases h_exists with ⟨f, hf_eq⟩
  use f
  have h_inj_f : Function.Injective f_map := map_injective
  have hb1 : f_map b ≠ 0 := by
    intro h
    have h2 : f_map b = f_map 0 := by simp [h]
    exact hb (h_inj_f h2)
  have h_inj_L : Function.Injective (algebraMap (FractionRing A)⟦X⟧ (FractionRing (FractionRing A)⟦X⟧)) := IsFractionRing.injective _ _
  have hb_ne_zero_L : algebraMap (FractionRing A)⟦X⟧ (FractionRing (FractionRing A)⟦X⟧) (f_map b) ≠ 0 := by
    intro h
    have h2 : algebraMap (FractionRing A)⟦X⟧ (FractionRing (FractionRing A)⟦X⟧) (f_map b) = algebraMap (FractionRing A)⟦X⟧ (FractionRing (FractionRing A)⟦X⟧) 0 := by simp [h]
    exact hb1 (h_inj_L h2)
  have h2 : algebraMap (FractionRing A)⟦X⟧ (FractionRing (FractionRing A)⟦X⟧) (f_map a) = algebraMap (FractionRing A)⟦X⟧ (FractionRing (FractionRing A)⟦X⟧) (f_map b * f) := by
    rw [map_mul, hf_eq, mul_comm, div_mul_cancel₀ _ hb_ne_zero_L]
  exact IsFractionRing.injective (FractionRing A)⟦X⟧ (FractionRing (FractionRing A)⟦X⟧) h2

lemma powerSeries_isIntegrallyClosed {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] :
    IsIntegrallyClosed A⟦X⟧ := by
  haveI h_int_closed_KX : IsIntegrallyClosed (FractionRing A)⟦X⟧ := inferInstance
  apply (isIntegrallyClosed_iff (FractionRing A⟦X⟧)).mpr
  intro x hx
  obtain ⟨a, b, hb, hx_eq⟩ := IsFractionRing.div_surjective (A := A⟦X⟧) x
  have hb_ne_zero : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have h_int_ab : IsIntegral A⟦X⟧ (algebraMap A⟦X⟧ (FractionRing A⟦X⟧) a / algebraMap A⟦X⟧ (FractionRing A⟦X⟧) b) := hx_eq ▸ hx
  obtain ⟨f, hf_eq⟩ := dvd_of_integral_K a b hb_ne_zero h_int_ab
  have hf_int : IsIntegral A⟦X⟧ f := isIntegral_K_of_integral_frac a b hb_ne_zero h_int_ab f hf_eq
  obtain ⟨g, hg_eq⟩ := mem_A_of_integral_K a b hb_ne_zero f (by rw [hf_eq, mul_comm]) hf_int
  use g
  have h_eq_a : algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ a = algebraMap A⟦X⟧ (FractionRing A)⟦X⟧ (b * g) := by
    rw [map_mul, hg_eq, hf_eq]
  have h_eq_a2 : a = b * g := map_injective h_eq_a
  rw [← hx_eq, h_eq_a2, map_mul]
  have hb_ne_zero_frac : algebraMap A⟦X⟧ (FractionRing A⟦X⟧) b ≠ 0 := by
    intro h
    have h2 : algebraMap A⟦X⟧ (FractionRing A⟦X⟧) b = algebraMap A⟦X⟧ (FractionRing A⟦X⟧) 0 := by rw [h, map_zero]
    exact hb_ne_zero (IsFractionRing.injective A⟦X⟧ (FractionRing A⟦X⟧) h2)
  exact (mul_div_cancel_left₀ (algebraMap A⟦X⟧ (FractionRing A⟦X⟧) g) hb_ne_zero_frac).symm

lemma NormalRing.powerSeries {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [NormalRing A] :
    NormalRing A⟦X⟧ := by
  have h_nd : NormalDomain A := normalDomain_of_normalRing
  haveI : IsIntegrallyClosed A := h_nd.2
  haveI : IsIntegrallyClosed A⟦X⟧ := powerSeries_isIntegrallyClosed
  have h_nd_X : NormalDomain A⟦X⟧ := { }
  exact NormalDomain.toNormalRing
-- EVOLVE-BLOCK-END

/-- The power series ring over a Noetherian normal domain is a normal domain. -/
theorem NormalDomain.powerSeries {R : Type*} [CommRing R] [IsNoetherianRing R] [NormalDomain R] :
    NormalDomain R⟦X⟧ := by
  -- EVOLVE-BLOCK-START
  have h1 : NormalRing R := NormalDomain.toNormalRing
  have h2 : NormalRing R⟦X⟧ := NormalRing.powerSeries
  haveI h3 : IsDomain R⟦X⟧ := inferInstance
  exact normalDomain_of_normalRing
  -- EVOLVE-BLOCK-END
