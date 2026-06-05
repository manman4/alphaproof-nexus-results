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
universe u1 u2 u3

noncomputable def tensorFinsuppEquiv {k K S : Type*} [Field k] [CommRing K] [Algebra k K] [CommRing S] [Algebra k S] :
  K ⊗[k] S ≃ₗ[k] (Module.Free.ChooseBasisIndex k K →₀ S) :=
  let ι := Module.Free.ChooseBasisIndex k K
  let b := Module.Free.chooseBasis k K
  let e1 : K ⊗[k] S ≃ₗ[k] (ι →₀ k) ⊗[k] S := TensorProduct.congr b.repr (LinearEquiv.refl k S)
  let e2 : (ι →₀ k) ⊗[k] S ≃ₗ[k] (ι →₀ k ⊗[k] S) := TensorProduct.finsuppLeft k k k S ι
  let e3 : (ι →₀ k ⊗[k] S) ≃ₗ[k] (ι →₀ S) := Finsupp.mapRange.linearEquiv (TensorProduct.lid k S)
  e1 ≪≫ₗ e2 ≪≫ₗ e3

abbrev ProdResidueFields (S : Type*) [CommRing S] :=
  ∀ P : PrimeSpectrum S, S ⧸ P.asIdeal

noncomputable def evalMap (k S : Type*) [CommRing k] [CommRing S] [Algebra k S] :
    S →ₗ[k] ProdResidueFields S :=
  LinearMap.pi (fun P => (IsScalarTower.toAlgHom k S (S ⧸ P.asIdeal)).toLinearMap)

lemma evalMap_injective {k S : Type*} [Field k] [CommRing S] [Algebra k S] [IsReduced S] :
    Function.Injective (evalMap k S) := by
  show (Function.Injective fun and=> fun and' =>id _)
  use fun and R M=>sub_eq_zero.1 (IsReduced.eq_zero _ ((nilpotent_iff_mem_prime.2 fun and n=>Ideal.Quotient.eq.1 (congrFun M ⟨ _,n⟩))))

lemma tensor_map_injective
  {k K S A : Type*} [Field k] [CommRing K] [Algebra k K] [AddCommGroup S] [Module k S]
  [AddCommGroup A] [Module k A] (f : S →ₗ[k] A) (hf : Function.Injective f) :
  Function.Injective (TensorProduct.map (LinearMap.id : K →ₗ[k] K) f) := by
  exact (Module.Flat.lTensor_preserves_injective_linearMap _) @hf

def mapToS {k K S : Type*} [Field k] [CommRing K] [Algebra k K] [CommRing S] [Algebra k S]
  (g : K →ₗ[k] k) : K ⊗[k] S →ₗ[k] S :=
  (TensorProduct.lid k S) ∘ₗ (TensorProduct.map g (LinearMap.id : S →ₗ[k] S))

lemma mapToS_eval {k K S : Type*} [Field k] [CommRing K] [Algebra k K] [CommRing S] [Algebra k S]
  (g : K →ₗ[k] k) (x : K ⊗[k] S) (P : PrimeSpectrum S) :
  Ideal.Quotient.mk P.asIdeal (mapToS g x) =
    mapToS g (TensorProduct.map (LinearMap.id : K →ₗ[k] K) (IsScalarTower.toAlgHom k S (S ⧸ P.asIdeal)).toLinearMap x) := by
  induction x with| zero=>rfl| tmul A B=>rfl| add=>simp_all

lemma tensorFinsuppEquiv_apply_eq_mapToS {k K S : Type*} [Field k] [CommRing K] [Algebra k K] [CommRing S] [Algebra k S]
  (x : K ⊗[k] S) (i : Module.Free.ChooseBasisIndex k K) :
  tensorFinsuppEquiv x i = mapToS ((Module.Free.chooseBasis k K).coord i) x := by
  induction ↑x with| zero=>bound| tmul=>_| add=>simp_all
  norm_num[tensorFinsuppEquiv]
  bound

lemma tensor_eq_zero_of_mapToS_eq_zero {k K S : Type*} [Field k] [CommRing K] [Algebra k K] [CommRing S] [Algebra k S]
  (x : K ⊗[k] S) (h : ∀ g : K →ₗ[k] k, mapToS g x = 0) : x = 0 := by
  have h1 : tensorFinsuppEquiv x = 0 := by
    ext i
    rw [Finsupp.zero_apply]
    rw [tensorFinsuppEquiv_apply_eq_mapToS x i]
    exact h _
  exact (LinearEquiv.map_eq_zero_iff tensorFinsuppEquiv).mp h1

lemma tensor_eq_zero_of_eval_eq_zero
  {k K S : Type*} [Field k] [CommRing K] [Algebra k K] [CommRing S] [Algebra k S] [IsReduced S]
  (x : K ⊗[k] S)
  (h_eval : ∀ P : PrimeSpectrum S,
    TensorProduct.map (LinearMap.id : K →ₗ[k] K) (IsScalarTower.toAlgHom k S (S ⧸ P.asIdeal)).toLinearMap x = 0) :
  x = 0 := by
  apply tensor_eq_zero_of_mapToS_eq_zero
  intro g
  have h1 : ∀ P : PrimeSpectrum S, Ideal.Quotient.mk P.asIdeal (mapToS g x) = 0 := by
    intro P
    rw [mapToS_eval]
    rw [h_eval P]
    exact map_zero (mapToS g)
  -- now since S is reduced, mapToS g x = 0
  exact (IsReduced.eq_zero _).comp (nilpotent_iff_mem_prime.mpr) (Ideal.Quotient.eq_zero_iff_mem.1 <| h1 ⟨., ·⟩)

lemma map_injective_of_fractionRing
  {k K D : Type*} [Field k] [CommRing K] [Algebra k K] [CommRing D] [IsDomain D] [Algebra k D] :
  Function.Injective (TensorProduct.map (LinearMap.id : K →ₗ[k] K) (IsScalarTower.toAlgHom k D (FractionRing D)).toLinearMap) := by
  use(Module.Flat.lTensor_preserves_injective_linearMap (IsScalarTower.toAlgHom _ _ _).toLinearMap fun and=>by simp_all)

lemma isReduced_quotient_of_coprime (F : Type*) [Field F] (P : F[X])
  (h : IsCoprime P (Polynomial.derivative P)) : IsReduced (F[X] ⧸ Ideal.span {P}) := by
  simp_all only [isReduced_iff,Function.comp]
  use Ideal.Quotient.mk_surjective.forall.2 fun and β=>Ideal.Quotient.eq_zero_iff_mem.2.comp (Ideal.mem_span_singleton.2) (by_contra fun and' =>absurd ↑(Ideal.Quotient.eq_zero_iff_mem.1 β.choose_spec) ? _)
  use and' ∘β.choose.rec ?_ fun and x=>?_ ∘Ideal.mem_span_singleton.1
  · exact (Ideal.mem_span_singleton.1 ·|>.trans ( (one_dvd and)))
  refine match and with|0=>by ·norm_num | (n + 1) => x ∘Ideal.mem_span_singleton.mpr ∘ fun and=>((exists_dvd_and_dvd_of_dvd_mul (and.trans (pow_succ _ _).dvd) ).elim) ?_
  use fun and ⟨a, M, R, E⟩=>E▸((exists_dvd_and_dvd_of_dvd_mul (M.trans (by rw [ R.choose_spec, mul_pow]))).elim) ?_
  rintro S⟨y,@c, C, rfl⟩
  norm_num[E,congrArg (.^ (n + 1)) R.choose_spec, mul_pow,mul_assoc,‹_ = S*c›] at h⊢
  apply(mul_dvd_mul_left S ((mul_comm _ _).dvd.trans (mul_dvd_mul ((IsCoprime.dvd_of_dvd_mul_left _) ⟨ _,.trans (.symm (by assumption)) (mul_comm _ _)⟩) C)))
  exact h.elim fun and⟨A, B⟩=>⟨derivative S* A*y+and* S*y,(a*derivative y+derivative a*y)*A,B▸by ring⟩

lemma isReduced_quotient_of_separable {F : Type*} [Field F] (P : F[X]) (hP : P.Separable) :
    IsReduced (F[X] ⧸ Ideal.span {P}) := by
  have h_coprime : IsCoprime P (Polynomial.derivative P) := hP
  exact isReduced_quotient_of_coprime F P h_coprime

lemma quotient_map_injective_cond {A B : Type*} [CommRing A] [CommRing B]
  (f : A →+* B) (P : Polynomial A) (x : A[X]) (hx : x ∈ Ideal.span {P}) :
  (RingHom.comp (Ideal.Quotient.mk (Ideal.span {Polynomial.map f P})) (Polynomial.mapRingHom f)) x = 0 := by
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hx
  rw [hq, map_mul]
  have H : Polynomial.map f P ∈ Ideal.span {Polynomial.map f P} := Ideal.mem_span_singleton_self (Polynomial.map f P)
  have H2 : Ideal.Quotient.mk (Ideal.span {Polynomial.map f P}) (Polynomial.map f P) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr H
  simp [H2]

lemma modByMonic_sub_mem_ideal {R : Type*} [CommRing R]
    (P y : R[X]) (hP : P.Monic) : y - (y %ₘ P) ∈ Ideal.span {P} := by
  have H := Polynomial.modByMonic_add_div y hP
  have H2 : y - (y %ₘ P) = P * (y /ₘ P) := by
    calc y - (y %ₘ P) = (y %ₘ P + P * (y /ₘ P)) - (y %ₘ P) := by rw [H]
      _ = P * (y /ₘ P) := by rw [add_sub_cancel_left]
  rw [H2]
  exact Ideal.mem_span_singleton.mpr ⟨y /ₘ P, rfl⟩

lemma zero_of_mem_span_of_degree_lt {R : Type*} [CommRing R] (P r : R[X]) (hP : P.Monic)
    (h1 : r ∈ Ideal.span {P}) (h2 : r = 0 ∨ r.degree < P.degree) : r = 0 := by
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp h1
  cases h2 with
  | inl h => exact h
  | inr h =>
    have H_cases : q = 0 ∨ q ≠ 0 := Classical.em (q = 0)
    cases H_cases with
    | inl hq_zero =>
      rw [hq_zero, mul_zero] at hq
      exact hq
    | inr hq_not_zero =>
      have hq_deg : (q * P).degree = q.degree + P.degree := hP.degree_mul
      have H4 : (q * P).degree < P.degree := by
        have h_comm : q * P = P * q := mul_comm q P
        rw [h_comm]
        rw [← hq]
        exact h
      cases H4.not_ge (hq_deg▸le_add_of_nonneg_left (zero_le_degree_iff.mpr (by valid)))

lemma polynomial_quotient_map_prod_injective_cond {A : Type*} [CommRing A]
  {ι : Type*} (F : ι → Type*) [∀ i, CommRing (F i)]
  (f : ∀ i, A →+* F i)
  (hf : ∀ (c : A), (∀ i, f i c = 0) → c = 0)
  (P : Polynomial A) (hP : P.Monic) (x : A[X])
  (hx : ∀ i, Polynomial.map (f i) x ∈ Ideal.span {Polynomial.map (f i) P}) :
  x ∈ Ideal.span {P} := by
  let r := x %ₘ P
  have h1 : x - r ∈ Ideal.span {P} := modByMonic_sub_mem_ideal P x hP
  have h_r_eq_zero : r = 0 := by
    ext
    apply (hf)
    use fun and=>by_contra fun and' =>absurd ((Ideal.mem_span_singleton.1 (hx and)).sub (P.map_dvd (f and) (Ideal.mem_span_singleton.1 h1) )) ?_
    norm_num[r,dvd_def]at and'⊢
    use fun and h=>absurd (h▸natDegree_map_le) ?_
    rw[natDegree_mul',natDegree_map_of_leadingCoeff_ne_zero]
    · exact (subsingleton_or_nontrivial A).elim (and'.elim ∘ fun and=>by convert(f _).map_zero) fun and=> (by valid ∘natDegree_modByMonic_lt x hP) (by norm_num[.]at and')
    · use and'.comp (by rw [←mul_one (f _ _ ),←(f _).map_one,←hP,.,mul_zero])
    · use and' ∘by norm_num+contextual[←coeff_map,hP.map,h]
  have h4 : x = (x - r) := by rw [h_r_eq_zero, sub_zero]
  rw [h4]
  exact h1

lemma polynomial_quotient_map_prod_injective {A : Type*} [CommRing A]
  {ι : Type*} (F : ι → Type*) [∀ i, CommRing (F i)]
  (f : ∀ i, A →+* F i)
  (hf : ∀ (c : A), (∀ i, f i c = 0) → c = 0)
  (P : Polynomial A) (hP : P.Monic) :
  Function.Injective (fun (x : A[X] ⧸ Ideal.span {P}) i =>
    Ideal.Quotient.lift (Ideal.span {P})
      (RingHom.comp (Ideal.Quotient.mk (Ideal.span {Polynomial.map (f i) P})) (Polynomial.mapRingHom (f i)))
      (quotient_map_injective_cond (f i) P) x) := by
  intro x y hxy
  revert hxy
  refine Quotient.inductionOn₂' x y ?_
  intro x y hxy
  have h1 : ∀ i, Polynomial.map (f i) (x - y) ∈ Ideal.span {Polynomial.map (f i) P} := by
    intro i
    have hxy_i := congr_fun hxy i
    have hx_i : Ideal.Quotient.mk (Ideal.span {Polynomial.map (f i) P}) (Polynomial.map (f i) x) =
      Ideal.Quotient.mk (Ideal.span {Polynomial.map (f i) P}) (Polynomial.map (f i) y) := hxy_i
    have hd : Ideal.Quotient.mk (Ideal.span {Polynomial.map (f i) P}) (Polynomial.map (f i) (x - y)) = 0 := by
      rw [Polynomial.map_sub, map_sub]
      exact sub_eq_zero.mpr hx_i
    exact Ideal.Quotient.eq_zero_iff_mem.mp hd
  have h2 : x - y ∈ Ideal.span {P} := polynomial_quotient_map_prod_injective_cond F f hf P hP (x - y) h1
  exact Ideal.Quotient.eq.mpr h2

lemma isReduced_quotient_of_monic_separable_prod {A : Type*} [CommRing A]
  {ι : Type*} (F : ι → Type*) [∀ i, Field (F i)]
  (f : ∀ i, A →+* F i)
  (hf : ∀ (c : A), (∀ i, f i c = 0) → c = 0)
  (P : Polynomial A) (hP : P.Monic)
  (hsep : ∀ i, (Polynomial.map (f i) P).Separable) :
  IsReduced (A[X] ⧸ Ideal.span {P}) := by
  have H := polynomial_quotient_map_prod_injective F f hf P hP
  constructor
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have H2 : ∀ i, (Ideal.Quotient.lift (Ideal.span {P})
      (RingHom.comp (Ideal.Quotient.mk (Ideal.span {Polynomial.map (f i) P})) (Polynomial.mapRingHom (f i)))
      (quotient_map_injective_cond (f i) P) x) ^ n = 0 := by
    intro i
    have H3 : (Ideal.Quotient.lift (Ideal.span {P})
      (RingHom.comp (Ideal.Quotient.mk (Ideal.span {Polynomial.map (f i) P})) (Polynomial.mapRingHom (f i)))
      (quotient_map_injective_cond (f i) P)) (x ^ n) = 0 := by
      rw [hn, map_zero]
    rw [← map_pow]
    exact H3
  have H3 : ∀ i, IsNilpotent (Ideal.Quotient.lift (Ideal.span {P})
      (RingHom.comp (Ideal.Quotient.mk (Ideal.span {Polynomial.map (f i) P})) (Polynomial.mapRingHom (f i)))
      (quotient_map_injective_cond (f i) P) x) := fun i => ⟨n, H2 i⟩
  have H4 : ∀ i, Ideal.Quotient.lift (Ideal.span {P})
      (RingHom.comp (Ideal.Quotient.mk (Ideal.span {Polynomial.map (f i) P})) (Polynomial.mapRingHom (f i)))
      (quotient_map_injective_cond (f i) P) x = 0 := by
    intro i
    haveI Hred := isReduced_quotient_of_separable (Polynomial.map (f i) P) (hsep i)
    exact IsReduced.eq_zero _ (H3 i)
  have H5 : (fun (x : A[X] ⧸ Ideal.span {P}) i =>
    Ideal.Quotient.lift (Ideal.span {P})
      (RingHom.comp (Ideal.Quotient.mk (Ideal.span {Polynomial.map (f i) P})) (Polynomial.mapRingHom (f i)))
      (quotient_map_injective_cond (f i) P) x) x =
    (fun (x : A[X] ⧸ Ideal.span {P}) i =>
    Ideal.Quotient.lift (Ideal.span {P})
      (RingHom.comp (Ideal.Quotient.mk (Ideal.span {Polynomial.map (f i) P})) (Polynomial.mapRingHom (f i)))
      (quotient_map_injective_cond (f i) P) x) 0 := by
    funext i
    have hzero : Ideal.Quotient.lift (Ideal.span {P})
      (RingHom.comp (Ideal.Quotient.mk (Ideal.span {Polynomial.map (f i) P})) (Polynomial.mapRingHom (f i)))
      (quotient_map_injective_cond (f i) P) 0 = 0 := map_zero _
    change Ideal.Quotient.lift (Ideal.span {P}) _ _ x = Ideal.Quotient.lift (Ideal.span {P}) _ _ 0
    rw [H4 i, hzero]
  exact H H5

lemma isReduced_polynomial_quotient_of_monic_separable {F A : Type*} [Field F] [CommRing A] [Algebra F A] [IsReduced A]
    (P : F[X]) (hP : P.Monic) (hP_sep : P.Separable) : IsReduced (A[X] ⧸ Ideal.span {Polynomial.map (algebraMap F A) P}) := by
  let ι := PrimeSpectrum A
  let F' := fun (p : PrimeSpectrum A) => FractionRing (A ⧸ p.asIdeal)
  let f' := fun (p : PrimeSpectrum A) => RingHom.comp (algebraMap (A ⧸ p.asIdeal) (F' p)) (Ideal.Quotient.mk p.asIdeal)
  have hf' : ∀ (c : A), (∀ i : PrimeSpectrum A, f' i c = 0) → c = 0 := by
    intro c hc
    have h1 : ∀ i : PrimeSpectrum A, Ideal.Quotient.mk i.asIdeal c = 0 := by
      intro i
      have h2 := hc i
      have h3 : Function.Injective (algebraMap (A ⧸ i.asIdeal) (F' i)) := IsFractionRing.injective (A ⧸ i.asIdeal) (F' i)
      have h4 : algebraMap (A ⧸ i.asIdeal) (F' i) (Ideal.Quotient.mk i.asIdeal c) = algebraMap (A ⧸ i.asIdeal) (F' i) 0 := by
        rw [map_zero]
        exact h2
      exact h3 h4
    have h2 : ∀ i : PrimeSpectrum A, c ∈ i.asIdeal := by
      intro i
      exact Ideal.Quotient.eq_zero_iff_mem.mp (h1 i)
    have h3 : IsNilpotent c := by
      rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
      intro I hI
      exact h2 ⟨I, hI⟩
    exact IsReduced.eq_zero c h3
  have h_monic : (Polynomial.map (algebraMap F A) P).Monic := Polynomial.Monic.map (algebraMap F A) hP
  have h_sep : ∀ i : PrimeSpectrum A, (Polynomial.map (f' i) (Polynomial.map (algebraMap F A) P)).Separable := by
    intro i
    have h_comp : Polynomial.map (f' i) (Polynomial.map (algebraMap F A) P) = Polynomial.map (RingHom.comp (f' i) (algebraMap F A)) P := by
      rw [Polynomial.map_map]
    rw [h_comp]
    exact Polynomial.Separable.map hP_sep
  exact isReduced_quotient_of_monic_separable_prod F' f' hf' (Polynomial.map (algebraMap F A) P) h_monic h_sep

lemma isReduced_localization {R_ S_ : Type*} [CommRing R_] [CommRing S_] [Algebra R_ S_]
  (M : Submonoid R_) [IsLocalization M S_] [IsReduced R_] : IsReduced S_ := by
  constructor
  intro x ⟨n, hn⟩
  cases n with
  | zero =>
    have h_zero : x ^ 0 = 0 := hn
    rw [pow_zero] at h_zero
    have h_one_eq_zero : (1 : S_) = 0 := h_zero
    exact eq_zero_of_zero_eq_one h_one_eq_zero.symm x
  | succ n' =>
    obtain ⟨⟨a, b⟩, hb⟩ := IsLocalization.surj M x
    have h1 : x ^ (n' + 1) * (algebraMap R_ S_ b) ^ (n' + 1) = (algebraMap R_ S_ a) ^ (n' + 1) := by
      rw [← mul_pow]
      rw [hb]
    rw [hn, zero_mul] at h1
    have h2 : algebraMap R_ S_ (a ^ (n' + 1)) = algebraMap R_ S_ 0 := by
      rw [map_pow, map_zero]
      exact h1.symm
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S_).mp h2
    rw [mul_zero] at hc
    have hc_pow : (c * a) ^ (n' + 1) = 0 := by
      calc (c * a) ^ (n' + 1) = (c : R_) ^ (n' + 1) * a ^ (n' + 1) := by rw [mul_pow]
        _ = ((c : R_) ^ n' * (c : R_)) * a ^ (n' + 1) := by rw [pow_succ (c : R_) n']
        _ = (c : R_) ^ n' * ((c : R_) * a ^ (n' + 1)) := by rw [mul_assoc]
        _ = (c : R_) ^ n' * 0 := by rw [hc]
        _ = 0 := mul_zero _
    have hca_nilp : IsNilpotent ((c : R_) * a) := ⟨n' + 1, hc_pow⟩
    have hca_zero : (c : R_) * a = 0 := hca_nilp.eq_zero
    have ha_map : algebraMap R_ S_ a = 0 := by
      have h3 : algebraMap R_ S_ c * algebraMap R_ S_ a = 0 := by
        rw [← map_mul, hca_zero, map_zero]
      have h4 : IsUnit (algebraMap R_ S_ c) := IsLocalization.map_units S_ c
      calc algebraMap R_ S_ a = 1 * algebraMap R_ S_ a := by rw [one_mul]
        _ = (↑(h4.unit⁻¹) * ↑h4.unit) * algebraMap R_ S_ a := by rw [Units.inv_mul]
        _ = ↑(h4.unit⁻¹) * (↑h4.unit * algebraMap R_ S_ a) := by rw [mul_assoc]
        _ = ↑(h4.unit⁻¹) * (algebraMap R_ S_ c * algebraMap R_ S_ a) := rfl
        _ = ↑(h4.unit⁻¹) * 0 := by rw [h3]
        _ = 0 := mul_zero _
    have hx_zero : x = 0 := by
      have h5 : x * algebraMap R_ S_ b = 0 := by rw [hb, ha_map]
      have h6 : IsUnit (algebraMap R_ S_ b) := IsLocalization.map_units S_ b
      calc x = x * 1 := by rw [mul_one]
        _ = x * (↑h6.unit * ↑(h6.unit⁻¹)) := by rw [Units.mul_inv]
        _ = (x * ↑h6.unit) * ↑(h6.unit⁻¹) := by rw [← mul_assoc]
        _ = (x * algebraMap R_ S_ b) * ↑(h6.unit⁻¹) := rfl
        _ = 0 * ↑(h6.unit⁻¹) := by rw [h5]
        _ = 0 := zero_mul _
    exact hx_zero

lemma alg_equiv_reduced {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (e : A ≃ₐ[R] B) (h : IsReduced B) : IsReduced A := by
  refine isReduced_of_injective @e.toAlgHom e.injective

noncomputable def TensorProduct_isReduced_of_primitive_element_aux_equiv_to {E K R : Type*} [Field E] [Field K] [CommRing R] [Algebra E K] [Algebra E R] (x : K) :
    R[X] →ₐ[E] K ⊗[E] R :=
  letI : Algebra R (K ⊗[E] R) := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower E R (K ⊗[E] R) := inferInstance
  let f : R[X] →ₐ[R] K ⊗[E] R := Polynomial.aeval (x ⊗ₜ[E] (1 : R))
  f.restrictScalars E

lemma TensorProduct_isReduced_of_primitive_element_aux_equiv_to_ker {E K R : Type*} [Field E] [Field K] [CommRing R] [Algebra E K] [Algebra E R] (x : K) :
    Polynomial.map (algebraMap E R) (minpoly E x) ∈ RingHom.ker (TensorProduct_isReduced_of_primitive_element_aux_equiv_to (E := E) (K := K) (R := R) x).toRingHom := by
  letI : Algebra R (K ⊗[E] R) := Algebra.TensorProduct.rightAlgebra
  have h1 : (TensorProduct_isReduced_of_primitive_element_aux_equiv_to (E := E) (K := K) (R := R) x) (Polynomial.map (algebraMap E R) (minpoly E x)) = 0 := by
    -- wait, TensorProduct_isReduced_of_primitive_element_aux_equiv_to is Polynomial.aeval (x ⊗ 1)
    norm_num[TensorProduct_isReduced_of_primitive_element_aux_equiv_to]
    linear_combination2(norm:=norm_num[aeval_eq_sum_range,TensorProduct.sum_tmul,TensorProduct.smul_tmul'])congrArg (. ⊗ₜ[E] (1:R)) (minpoly.aeval E x)
  exact h1

lemma K_equiv_polynomial_dummy : True := trivial

lemma tensorProduct_isReduced_of_finite_separable_map_ker {E K R : Type*} [Field E] [Field K] [CommRing R] [Algebra E K] [Algebra E R] [IsReduced R] (x : K)
    [Algebra R (K ⊗[E] R)] [IsScalarTower E R (K ⊗[E] R)]
    (f : R[X] →ₐ[R] K ⊗[E] R) (hf : f = Polynomial.aeval (x ⊗ₜ[E] (1 : R))) :
    Ideal.span {Polynomial.map (algebraMap E R) (minpoly E x)} ≤ RingHom.ker f := by
  use (hf▸Ideal.span_le.2 fun and true => true▸.trans (aeval_map_algebraMap _ _ _) ? _)
  linear_combination2(norm:=norm_num[aeval_eq_sum_range,TensorProduct.sum_tmul,TensorProduct.smul_tmul'])congr_arg (. ⊗ₜ[E] (1:R)) (minpoly.aeval E x)

noncomputable def tensorProduct_isReduced_of_finite_separable_map {E K R : Type*} [Field E] [Field K] [CommRing R] [Algebra E K] [Algebra E R] [IsReduced R] (x : K) :
    R[X] ⧸ Ideal.span {Polynomial.map (algebraMap E R) (minpoly E x)} →ₐ[E] K ⊗[E] R :=
  letI : Algebra R (K ⊗[E] R) := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower E R (K ⊗[E] R) := inferInstance
  let f : R[X] →ₐ[R] K ⊗[E] R := Polynomial.aeval (x ⊗ₜ[E] (1 : R))
  let f_quot : R[X] ⧸ Ideal.span {Polynomial.map (algebraMap E R) (minpoly E x)} →ₐ[R] K ⊗[E] R :=
    Ideal.Quotient.liftₐ _ f (tensorProduct_isReduced_of_finite_separable_map_ker x f rfl)
  f_quot.restrictScalars E

noncomputable def K_equiv_polynomial {E K : Type*} [Field E] [Field K] [Algebra E K] [FiniteDimensional E K] (x : K) (hx : IntermediateField.adjoin E ({x} : Set K) = ⊤) :
    (E[X] ⧸ Ideal.span {minpoly E x}) ≃ₐ[E] K := by
  have h_alg : IsIntegral E x := Algebra.IsIntegral.isIntegral x
  let e1 : (E[X] ⧸ Ideal.span {minpoly E x}) ≃ₐ[E] IntermediateField.adjoin E ({x} : Set K) :=
    IntermediateField.adjoinRootEquivAdjoin E h_alg
  let e2 : IntermediateField.adjoin E ({x} : Set K) ≃ₐ[E] K :=
    (IntermediateField.equivOfEq hx).trans IntermediateField.topEquiv
  exact e1.trans e2

lemma K_equiv_polynomial_apply_X {E K : Type*} [Field E] [Field K] [Algebra E K] [FiniteDimensional E K] (x : K) (hx : IntermediateField.adjoin E ({x} : Set K) = ⊤) :
    K_equiv_polynomial x hx (Ideal.Quotient.mk (Ideal.span {minpoly E x}) Polynomial.X) = x := by
  norm_num[ K_equiv_polynomial ·]
  norm_num[IntermediateField.adjoinRootEquivAdjoin]
  exact (congr_arg _) ↑(aeval_X _)

noncomputable def tensorProduct_isReduced_of_finite_separable_inv_K {E K R : Type*} [Field E] [Field K] [CommRing R] [Algebra E K] [Algebra E R] [IsReduced R] [FiniteDimensional E K] (x : K) (hx : IntermediateField.adjoin E ({x} : Set K) = ⊤) :
    K →ₐ[E] R[X] ⧸ Ideal.span {Polynomial.map (algebraMap E R) (minpoly E x)} :=
  let e_K := K_equiv_polynomial x hx
  let f_X : E[X] →ₐ[E] R[X] ⧸ Ideal.span {Polynomial.map (algebraMap E R) (minpoly E x)} :=
    (Ideal.Quotient.mkₐ E (Ideal.span {Polynomial.map (algebraMap E R) (minpoly E x)})).comp (Polynomial.mapAlgHom (Algebra.ofId E R))
  have h_ker : Ideal.span {minpoly E x} ≤ RingHom.ker f_X := by
    rw [Ideal.span_le]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    rw [hy]
    have H1 : Polynomial.map (algebraMap E R) (minpoly E x) ∈ Ideal.span {Polynomial.map (algebraMap E R) (minpoly E x)} := Ideal.mem_span_singleton.mpr ⟨1, by rw [mul_one]⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr H1
  let f_quot : E[X] ⧸ Ideal.span {minpoly E x} →ₐ[E] R[X] ⧸ Ideal.span {Polynomial.map (algebraMap E R) (minpoly E x)} :=
    Ideal.Quotient.liftₐ (Ideal.span {minpoly E x}) f_X h_ker
  f_quot.comp e_K.symm.toAlgHom

noncomputable def tensorProduct_isReduced_of_finite_separable_inv {E K R : Type*} [Field E] [Field K] [CommRing R] [Algebra E K] [Algebra E R] [IsReduced R] [FiniteDimensional E K] (x : K) (hx : IntermediateField.adjoin E ({x} : Set K) = ⊤) :
    K ⊗[E] R →ₐ[E] R[X] ⧸ Ideal.span {Polynomial.map (algebraMap E R) (minpoly E x)} :=
  let f_K := tensorProduct_isReduced_of_finite_separable_inv_K x hx
  let f_R' := Algebra.ofId R (R[X] ⧸ Ideal.span {Polynomial.map (algebraMap E R) (minpoly E x)})
  let f_R'' : R →ₐ[E] R[X] ⧸ Ideal.span {Polynomial.map (algebraMap E R) (minpoly E x)} := f_R'.restrictScalars E
  have h_comm : ∀ k r, Commute (f_K k) (f_R'' r) := by
    intro k r
    exact mul_comm _ _
  Algebra.TensorProduct.lift f_K f_R'' h_comm

lemma tensorProduct_isReduced_of_finite_separable_inv_inj_left {E K R : Type*} [Field E] [Field K] [CommRing R] [Algebra E K] [Algebra E R] [IsReduced R] [FiniteDimensional E K] (x : K) (hx : IntermediateField.adjoin E ({x} : Set K) = ⊤) :
    (tensorProduct_isReduced_of_finite_separable_map x).comp ((tensorProduct_isReduced_of_finite_separable_inv x hx).comp (Algebra.TensorProduct.includeLeft : K →ₐ[E] K ⊗[E] R)) = (Algebra.TensorProduct.includeLeft : K →ₐ[E] K ⊗[E] R) := by
  delta tensorProduct_isReduced_of_finite_separable_inv
  norm_num[tensorProduct_isReduced_of_finite_separable_map,tensorProduct_isReduced_of_finite_separable_inv_K]
  norm_num[aeval_eq_sum_range,AlgHom.ext_iff]
  use fun and=>(Ideal.Quotient.mk_surjective ((K_equiv_polynomial _ _).symm and)).elim fun and true => true▸?_
  norm_num[aeval_eq_sum_range, K_equiv_polynomial,funext_iff]at*
  cases subsingleton_or_nontrivial R with| inl=>subsingleton| inr=>_
  simp_all[TensorProduct.sum_tmul, Algebra.smul_def]
  simp_all[Ideal.Quotient.eq, Algebra.algebraMap_eq_smul_one,Ideal.mem_span_singleton',Subtype.eq_iff]
  symm at true
  symm
  simp_all[TensorProduct.sum_tmul, Algebra.smul_def,IntermediateField.adjoinRootEquivAdjoin,Ideal.Quotient.eq,Ideal.mem_span_singleton, (minpoly.dvd_iff)]
  erw[AlgEquiv.symm_apply_eq]at*
  norm_num[Subtype.mk.inj true]
  norm_num[eval₂_eq_sum_range,TensorProduct.sum_tmul]

lemma tensorProduct_isReduced_of_finite_separable_inv_inj_right {E K R : Type*} [Field E] [Field K] [CommRing R] [Algebra E K] [Algebra E R] [IsReduced R] [FiniteDimensional E K] (x : K) (hx : IntermediateField.adjoin E ({x} : Set K) = ⊤) :
    (tensorProduct_isReduced_of_finite_separable_map x).comp ((tensorProduct_isReduced_of_finite_separable_inv x hx).comp (Algebra.TensorProduct.includeRight : R →ₐ[E] K ⊗[E] R)) = (Algebra.TensorProduct.includeRight : R →ₐ[E] K ⊗[E] R) := by
  norm_num[tensorProduct_isReduced_of_finite_separable_inv,tensorProduct_isReduced_of_finite_separable_map,DFunLike.ext_iff]
  bound

lemma tensorProduct_isReduced_of_finite_separable_inv_inj_comp {E K R : Type*} [Field E] [Field K] [CommRing R] [Algebra E K] [Algebra E R] [IsReduced R] [FiniteDimensional E K] (x : K) (hx : IntermediateField.adjoin E ({x} : Set K) = ⊤) :
    (tensorProduct_isReduced_of_finite_separable_map x).comp (tensorProduct_isReduced_of_finite_separable_inv x hx) = AlgHom.id E (K ⊗[E] R) := by
  apply Algebra.TensorProduct.ext
  · exact tensorProduct_isReduced_of_finite_separable_inv_inj_left x hx
  · exact tensorProduct_isReduced_of_finite_separable_inv_inj_right x hx

lemma tensorProduct_isReduced_of_finite_separable_inv_inj {E K R : Type*} [Field E] [Field K] [CommRing R] [Algebra E K] [Algebra E R] [IsReduced R] [FiniteDimensional E K] (x : K) (hx : IntermediateField.adjoin E ({x} : Set K) = ⊤) :
    Function.Injective (tensorProduct_isReduced_of_finite_separable_inv (E := E) (K := K) (R := R) x hx) := by
  intro y z hyz
  have h1 : (tensorProduct_isReduced_of_finite_separable_map x) ((tensorProduct_isReduced_of_finite_separable_inv x hx) y) = (tensorProduct_isReduced_of_finite_separable_map x) ((tensorProduct_isReduced_of_finite_separable_inv x hx) z) := by
    rw [hyz]
  have h2 : ((tensorProduct_isReduced_of_finite_separable_map x).comp (tensorProduct_isReduced_of_finite_separable_inv x hx)) y = y := by
    have H := tensorProduct_isReduced_of_finite_separable_inv_inj_comp (R := R) x hx
    rw [H]
    rfl
  have h3 : ((tensorProduct_isReduced_of_finite_separable_map x).comp (tensorProduct_isReduced_of_finite_separable_inv x hx)) z = z := by
    have H := tensorProduct_isReduced_of_finite_separable_inv_inj_comp (R := R) x hx
    rw [H]
    rfl
  rw [← h2, ← h3]
  exact h1

lemma TensorProduct_isReduced_of_finite_separable {E K R : Type*} [Field E] [Field K] [CommRing R]
    [Algebra E K] [Algebra E R] [IsReduced R] [FiniteDimensional E K] [Algebra.IsSeparable E K] :
    IsReduced (K ⊗[E] R) := by
  obtain ⟨x, hx_adjoin⟩ := Field.exists_primitive_element E K
  have h_inj : Function.Injective (tensorProduct_isReduced_of_finite_separable_inv (E := E) (K := K) (R := R) x hx_adjoin) :=
    tensorProduct_isReduced_of_finite_separable_inv_inj x hx_adjoin
  have h_monic : (minpoly E x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have h_sep : (minpoly E x).Separable := Algebra.IsSeparable.isSeparable E x
  have h_red_quot : IsReduced (R[X] ⧸ Ideal.span {Polynomial.map (algebraMap E R) (minpoly E x)}) :=
    isReduced_polynomial_quotient_of_monic_separable (minpoly E x) h_monic h_sep
  exact isReduced_of_injective (tensorProduct_isReduced_of_finite_separable_inv (E := E) (K := K) (R := R) x hx_adjoin) h_inj

lemma IsReduced.of_subalgebra_field_aux_fin {E K : Type*} [Field E] [Field K] [Algebra E K] [Algebra.IsAlgebraic E K] (B : Subalgebra E K) (hB : B.FG) : FiniteDimensional E B := by induction (hB)
                                                                                                                                                                                     replace:FiniteDimensional E ↑(Subalgebra.toSubmodule B) :=by valid▸.iff_fg.2 (fg_adjoin_of_finite (Finset.finite_toSet _) fun and x =>(Algebra.IsIntegral.isIntegral and))
                                                                                                                                                                                     repeat assumption

lemma IsReduced.of_subalgebra_field_aux_sep {E K : Type*} [Field E] [Field K] [Algebra E K] [Algebra.IsSeparable E K] (B : Subalgebra E K) : Algebra.IsSeparable E B := by use fun and=>(((‹ Algebra.IsSeparable _ _›.1) and.1)).imp fun and x =>?_
                                                                                                                                                                           rwa [ (minpoly.algebraMap_eq Subtype.coe_injective _).symm]

lemma IsReduced.of_subalgebra_field_aux_alg {E K : Type*} [Field E] [Field K] [Algebra E K] [Algebra.IsAlgebraic E K] (B : Subalgebra E K) : Algebra.IsAlgebraic E B := by use fun and=>(‹ Algebra.IsAlgebraic E K›.1 (and)).imp (by simp_all [Subtype.eq_iff,Polynomial.aeval_eq_sum_range])

lemma IsReduced.of_subalgebra_field {E K R : Type*} [Field E] [Field K] [CommRing R]
    [Algebra E K] [Algebra E R] [IsReduced R] [Algebra.IsSeparable E K] [Algebra.IsAlgebraic E K]
    (B : Subalgebra E K) (hB : B.FG) : IsReduced (R ⊗[E] B) := by
  have h_alg : Algebra.IsAlgebraic E B := IsReduced.of_subalgebra_field_aux_alg B
  letI : Algebra.IsAlgebraic E B := h_alg
  have h_field : IsField B := Subalgebra.isField_of_algebraic B
  let B_field : Field B := h_field.toField
  letI : Field B := B_field
  have h_fin : FiniteDimensional E B := IsReduced.of_subalgebra_field_aux_fin B hB
  have h_sep : Algebra.IsSeparable E B := IsReduced.of_subalgebra_field_aux_sep B
  have e : R ⊗[E] B ≃ₐ[E] B ⊗[E] R := Algebra.TensorProduct.comm E R B
  have h_red : IsReduced (B ⊗[E] R) := TensorProduct_isReduced_of_finite_separable
  exact alg_equiv_reduced e h_red

lemma isReduced_tensorProduct_of_isSeparable {F_ K_ A_ : Type*} [Field F_] [Field K_] [CommRing A_]
    [Algebra F_ K_] [Algebra F_ A_] [Algebra.IsSeparable F_ K_] [Algebra.IsAlgebraic F_ K_] [IsReduced A_] : IsReduced (K_ ⊗[F_] A_) := by
  have e : K_ ⊗[F_] A_ ≃ₐ[F_] A_ ⊗[F_] K_ := Algebra.TensorProduct.comm F_ K_ A_
  have h_red : IsReduced (A_ ⊗[F_] K_) := by
    apply IsReduced.tensorProduct_of_flat_of_forall_fg
    intro B hB
    exact IsReduced.of_subalgebra_field B hB
  exact alg_equiv_reduced e h_red

lemma mvPolynomial_tensor_equiv_comm {k S : Type*} [CommRing k] [CommRing S] [Algebra k S] (s : Type*) (x : MvPolynomial s k) (y : S) :
  Commute (MvPolynomial.aeval (fun i => MvPolynomial.X i) x) (IsScalarTower.toAlgHom k S (MvPolynomial s S) y) := by
  apply @mul_comm

noncomputable def mvPolynomial_tensor_equiv_lift {k S : Type*} [CommRing k] [CommRing S] [Algebra k S] (s : Type*) : (MvPolynomial s k ⊗[k] S) →ₐ[k] MvPolynomial s S :=
  Algebra.TensorProduct.lift (MvPolynomial.aeval (fun i => MvPolynomial.X i)) (IsScalarTower.toAlgHom k S (MvPolynomial s S)) (mvPolynomial_tensor_equiv_comm s)

noncomputable def mvPolynomial_tensor_equiv_inv {k S : Type*} [CommRing k] [CommRing S] [Algebra k S] (s : Type*) : MvPolynomial s S →ₐ[k] (MvPolynomial s k ⊗[k] S) :=
  letI : Algebra S (MvPolynomial s k ⊗[k] S) := Algebra.TensorProduct.rightAlgebra
  (MvPolynomial.aeval (fun i => (MvPolynomial.X i : MvPolynomial s k) ⊗ₜ[k] (1 : S))).restrictScalars k

lemma mvPolynomial_tensor_equiv_comp1 {k S : Type*} [CommRing k] [CommRing S] [Algebra k S] (s : Type*) :
  (mvPolynomial_tensor_equiv_lift s).comp (mvPolynomial_tensor_equiv_inv s) = AlgHom.id k (MvPolynomial s S) := by
  apply AlgHom.ext fun and=>?_
  norm_num[mvPolynomial_tensor_equiv_inv,mvPolynomial_tensor_equiv_lift]
  norm_num[and.aeval_def,and.eval₂_eq]
  exact (congr_arg _ (funext fun and' =>.trans (congr_arg₂ _ (Algebra.TensorProduct.lift_tmul ..) rfl) (by simp_all[Algebra.algebraMap_eq_smul_one, MvPolynomial.monomial_eq]))).trans and.as_sum.symm

lemma mvPolynomial_tensor_equiv_comp2 {k S : Type*} [CommRing k] [CommRing S] [Algebra k S] (s : Type*) :
  (mvPolynomial_tensor_equiv_inv s).comp (mvPolynomial_tensor_equiv_lift s) = AlgHom.id k (MvPolynomial s k ⊗[k] S) := by
  ext
  · simp_all [mvPolynomial_tensor_equiv_inv,mvPolynomial_tensor_equiv_lift]
  simp_all [mvPolynomial_tensor_equiv_inv,mvPolynomial_tensor_equiv_lift]
  aesop

lemma mvPolynomial_tensor_equiv {k S : Type*} [CommRing k] [CommRing S] [Algebra k S] (s : Type*) :
    Nonempty (MvPolynomial s k ⊗[k] S ≃ₐ[k] MvPolynomial s S) := by
  exact ⟨AlgEquiv.ofAlgHom (mvPolynomial_tensor_equiv_lift s) (mvPolynomial_tensor_equiv_inv s) (mvPolynomial_tensor_equiv_comp1 s) (mvPolynomial_tensor_equiv_comp2 s)⟩

lemma isReduced_tensorProduct_adjoin_transcendenceBasis_aux1 {k_ K_ : Type*} [Field k_] [Field K_] [Algebra k_ K_] (s : Set K_) (hs : IsTranscendenceBasis k_ (fun x : s ↦ (x : K_))) :
    Nonempty (MvPolynomial s k_ ≃ₐ[k_] Algebra.adjoin k_ (s : Set K_)) := by
  refine Algebra.adjoin_eq_range k_ s▸⟨?_⟩
  apply AlgEquiv.ofInjective _ hs.1

lemma isReduced_tensorProduct_adjoin_transcendenceBasis_aux2 {k_ K_ F_ : Type*} [Field k_] [Field K_] [Field F_]
    [Algebra k_ K_] [Algebra k_ F_] (s : Set K_) (hs : IsTranscendenceBasis k_ (fun x : s ↦ (x : K_))) :
    IsReduced (Algebra.adjoin k_ (s : Set K_) ⊗[k_] F_) := by
  have H := isReduced_tensorProduct_adjoin_transcendenceBasis_aux1 s hs
  obtain ⟨e⟩ := H
  have e2 : (Algebra.adjoin k_ (s : Set K_) ⊗[k_] F_) ≃ₐ[k_] (MvPolynomial s k_ ⊗[k_] F_) := by
    apply Algebra.TensorProduct.congr e.symm (AlgEquiv.refl)
  have e3 : (MvPolynomial s k_ ⊗[k_] F_) ≃ₐ[k_] MvPolynomial s F_ := by
    exact Classical.choice (mvPolynomial_tensor_equiv (s : Type _))
  have h_red : IsReduced (MvPolynomial s F_) := by
    haveI : IsDomain (MvPolynomial s F_) := inferInstance
    constructor
    intro x hx
    obtain ⟨n, hn⟩ := hx
    exact IsNilpotent.eq_zero ⟨n, hn⟩
  have h_red2 : IsReduced (MvPolynomial s k_ ⊗[k_] F_) := alg_equiv_reduced e3 h_red
  exact alg_equiv_reduced e2 h_red2

lemma tensor_localization_isReduced_aux1 {R S F : Type*} [Field R] [CommRing S] [Field F]
    [Algebra R S] [Algebra R F] [IsDomain S] (L : Type*) [CommRing L] [Algebra S L]
    [Algebra R L] [IsScalarTower R S L] [IsFractionRing S L] :
    Function.Injective (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S L) (AlgHom.id R F)) := by
  refine(Module.Flat.rTensor_preserves_injective_linearMap (IsScalarTower.toAlgHom R S L).toLinearMap (IsFractionRing.injective _ _))

lemma tensor_localization_isReduced_aux2 {R S F : Type*} [Field R] [CommRing S] [Field F]
    [Algebra R S] [Algebra R F] [IsDomain S] (L : Type*) [CommRing L] [Algebra S L]
    [Algebra R L] [IsScalarTower R S L] [IsFractionRing S L] (b : S) (hb : b ≠ 0) :
    IsUnit (algebraMap S L b ⊗ₜ[R] (1 : F)) := by
  delta Ne at *
  cases‹IsFractionRing _ _›
  cases‹_›
  cases‹∀S:nonZeroDivisors S,_› ⟨b,by norm_num[*]⟩
  norm_num[←‹_›]
  norm_num[isUnit_iff_exists_inv]
  use Units.inv (by valid) ⊗ₜ[R]1
  norm_num
  rfl

lemma exists_mul_mem_tensor_of_fractionRing_aux {R S F : Type*} [Field R] [CommRing S] [Field F]
    [Algebra R S] [Algebra R F] [IsDomain S] (L : Type*) [CommRing L] [Algebra S L]
    [Algebra R L] [IsScalarTower R S L] [IsFractionRing S L] (x : L ⊗[R] F) :
    ∃ (b : S) (hb : b ≠ 0) (y : S ⊗[R] F),
      x * (algebraMap S L b ⊗ₜ[R] (1 : F)) =
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S L) (AlgHom.id R F) y := by
  cases‹IsFractionRing S L›
  cases‹_›
  induction x with| zero=>use(1),one_ne_zero,0,zero_mul _| tmul A B=>_| add=>_
  · obtain ⟨⟨x, y⟩, h⟩ :=‹∀ z, ∃_, _› A
    use y,nonZeroDivisors.ne_zero y.2,x ⊗ₜ[R]B,?_
    norm_num[h]
  · revert‹ L ⊗[R] F› R
    use fun and i ⟨a, M, R, _⟩⟨b,A, B, _⟩=>⟨ _,mul_ne_zero M A,R*algebraMap _ _ b ⊗ₜ[_]1+B*algebraMap _ _ a ⊗ₜ[_]1,?_⟩
    norm_num[mul_assoc, add_mul,←‹and*_ = _›,←by valid,TensorProduct.smul_tmul',mul_comm, mul_add,mul_left_comm]

lemma tensor_localization_isReduced {R S F : Type*} [Field R] [CommRing S] [Field F]
    [Algebra R S] [Algebra R F] [IsDomain S] (L : Type*) [CommRing L] [Algebra S L]
    [Algebra R L] [IsScalarTower R S L] [IsFractionRing S L] (h : IsReduced (S ⊗[R] F)) :
    IsReduced (L ⊗[R] F) := by
  constructor
  intro x ⟨n, hn⟩
  obtain ⟨b, hb, y, hy⟩ := exists_mul_mem_tensor_of_fractionRing_aux (R := R) (S := S) (F := F) L x
  have h1 : (x * (algebraMap S L b ⊗ₜ[R] (1 : F))) ^ n = 0 := by
    rw [mul_pow, hn, zero_mul]
  have h2 : (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S L) (AlgHom.id R F)) (y ^ n) = 0 := by
    rw [map_pow, ← hy, h1]
  have h3 : Function.Injective (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S L) (AlgHom.id R F)) := tensor_localization_isReduced_aux1 L
  have h4 : y ^ n = 0 := h3 (by rw [h2, map_zero])
  have h5 : IsNilpotent y := ⟨n, h4⟩
  have h6 : y = 0 := by
    letI := h
    exact IsReduced.eq_zero y h5
  have h7 : x * (algebraMap S L b ⊗ₜ[R] (1 : F)) = 0 := by
    rw [hy, h6, map_zero]
  have h8 : IsUnit (algebraMap S L b ⊗ₜ[R] (1 : F)) := tensor_localization_isReduced_aux2 L b hb
  have h9 : x * (algebraMap S L b ⊗ₜ[R] (1 : F)) = 0 * (algebraMap S L b ⊗ₜ[R] (1 : F)) := by
    rw [h7, zero_mul]
  exact IsUnit.mul_left_inj h8 |>.mp h9

noncomputable instance adjoin_algebra_adjoin {k_ K_ : Type*} [Field k_] [Field K_] [Algebra k_ K_] (s : Set K_) :
  Algebra (Algebra.adjoin k_ s) (IntermediateField.adjoin k_ s) :=
  RingHom.toAlgebra (Subalgebra.inclusion (Algebra.adjoin_le (IntermediateField.subset_adjoin k_ s)))

lemma isScalarTower_adjoin {k_ K_ : Type*} [Field k_] [Field K_] [Algebra k_ K_] (s : Set K_) :
  IsScalarTower k_ (Algebra.adjoin k_ s) (IntermediateField.adjoin k_ s) := by
  use fun and R L=> Subtype.eq (Algebra.smul_mul_assoc and _ _)

lemma isFractionRing_adjoin_map_units {k_ K_ : Type*} [Field k_] [Field K_] [Algebra k_ K_] (s : Set K_)
  (y : nonZeroDivisors (Algebra.adjoin k_ s)) : IsUnit (algebraMap (Algebra.adjoin k_ s) (IntermediateField.adjoin k_ s) y) := by
  exact (Ne.isUnit (nonZeroDivisors.ne_zero y.2 ∘ Subtype.eq ∘congr_arg Subtype.val))

lemma isFractionRing_adjoin_surj {k_ K_ : Type*} [Field k_] [Field K_] [Algebra k_ K_] (s : Set K_)
  (z : IntermediateField.adjoin k_ s) : ∃ (x : Algebra.adjoin k_ s × nonZeroDivisors (Algebra.adjoin k_ s)),
  z * algebraMap (Algebra.adjoin k_ s) (IntermediateField.adjoin k_ s) x.2 = algebraMap (Algebra.adjoin k_ s) (IntermediateField.adjoin k_ s) x.1 := by
  norm_num[.*.]
  replace:z.1 ∈IntermediateField.adjoin k_ (s) := z.2
  rewrite [IntermediateField.mem_adjoin_iff] at this
  choose _ _ _simpa using(id) this
  norm_num [Subtype.eq_iff, Mul.mul, MvPolynomial.aeval_def, *]
  norm_num[MvPolynomial.eval₂_eq',RingHom.algebraMap_toAlgebra]
  norm_num[Subalgebra.inclusion,MvPolynomial.eval₂_eq']
  by_cases h : MvPolynomial.eval₂ (algebraMap k_ _) Subtype.val (by assumption) = (0:K_)
  · exact ⟨0,by bound, 1,by simp_all[MvPolynomial.aeval_def]⟩
  · exact ⟨ _,( (by bound : MvPolynomial _ _):).eval₂_mem (by bound) (by bound), _,h, MvPolynomial.eval₂_mem (by bound) (by bound), (div_mul_cancel₀ _) h⟩

lemma isFractionRing_adjoin_eq_iff_exists {k_ K_ : Type*} [Field k_] [Field K_] [Algebra k_ K_] (s : Set K_)
  {x y : Algebra.adjoin k_ s} (h : algebraMap (Algebra.adjoin k_ s) (IntermediateField.adjoin k_ s) x = algebraMap (Algebra.adjoin k_ s) (IntermediateField.adjoin k_ s) y) :
  ∃ (c : nonZeroDivisors (Algebra.adjoin k_ s)), c * x = c * y := by
  use⟨ _,one_mem _,⟩,congr_arg ↑_<|Subtype.eq (and_self_iff.mp @? _)
  simp_all [algebraMap,funext_iff]
  use x.eq<|Subtype.mk.inj h

lemma isFractionRing_adjoin {k_ K_ : Type*} [Field k_] [Field K_] [Algebra k_ K_] (s : Set K_) :
    IsFractionRing (Algebra.adjoin k_ (s : Set K_)) (IntermediateField.adjoin k_ s) :=
  { map_units := isFractionRing_adjoin_map_units s
    surj := isFractionRing_adjoin_surj s
    exists_of_eq := isFractionRing_adjoin_eq_iff_exists s }

lemma isReduced_tensorProduct_adjoin_transcendenceBasis {k_ K_ F_ : Type*} [Field k_] [Field K_] [Field F_]
    [Algebra k_ K_] [Algebra k_ F_] (s : Set K_) (hs : IsTranscendenceBasis k_ (fun x : s ↦ (x : K_))) :
    IsReduced (IntermediateField.adjoin k_ s ⊗[k_] F_) := by
  have h_red : IsReduced (Algebra.adjoin k_ (s : Set K_) ⊗[k_] F_) := isReduced_tensorProduct_adjoin_transcendenceBasis_aux2 s hs
  haveI : IsDomain (Algebra.adjoin k_ (s : Set K_)) := inferInstance
  haveI : IsFractionRing (Algebra.adjoin k_ (s : Set K_)) (IntermediateField.adjoin k_ s) := isFractionRing_adjoin s
  haveI : IsScalarTower k_ (Algebra.adjoin k_ s) (IntermediateField.adjoin k_ s) := isScalarTower_adjoin s
  exact tensor_localization_isReduced (IntermediateField.adjoin k_ s) h_red

noncomputable def tensor_equiv_base_change_f
  (k_ E_ K_ S_ : Type*) [Field k_] [Field E_] [Field K_] [CommRing S_]
  [Algebra k_ E_] [Algebra k_ K_] [Algebra k_ S_] [Algebra E_ K_] [IsScalarTower k_ E_ K_] :
  K_ ⊗[k_] S_ →ₐ[k_] K_ ⊗[E_] (E_ ⊗[k_] S_) :=
  letI : Module E_ (E_ ⊗[k_] S_) := TensorProduct.leftModule
  letI : Algebra E_ (E_ ⊗[k_] S_) := Algebra.TensorProduct.leftAlgebra
  let f_K : K_ →ₐ[k_] K_ ⊗[E_] (E_ ⊗[k_] S_) := (Algebra.TensorProduct.includeLeft : K_ →ₐ[E_] K_ ⊗[E_] (E_ ⊗[k_] S_)).restrictScalars k_
  let f_S : S_ →ₐ[k_] K_ ⊗[E_] (E_ ⊗[k_] S_) := (Algebra.TensorProduct.includeRight : (E_ ⊗[k_] S_) →ₐ[E_] K_ ⊗[E_] (E_ ⊗[k_] S_)).restrictScalars k_ |>.comp (Algebra.TensorProduct.includeRight : S_ →ₐ[k_] E_ ⊗[k_] S_)
  have h_comm_f : ∀ x y, Commute (f_K x) (f_S y) := by
    intro x y
    exact mul_comm (f_K x) (f_S y)
  Algebra.TensorProduct.lift f_K f_S h_comm_f

noncomputable def tensor_equiv_base_change_g
  (k_ E_ K_ S_ : Type*) [Field k_] [Field E_] [Field K_] [CommRing S_]
  [Algebra k_ E_] [Algebra k_ K_] [Algebra k_ S_] [Algebra E_ K_] [IsScalarTower k_ E_ K_] :
  K_ ⊗[E_] (E_ ⊗[k_] S_) →ₐ[E_] K_ ⊗[k_] S_ :=
  letI : Module E_ (E_ ⊗[k_] S_) := TensorProduct.leftModule
  letI : Algebra E_ (E_ ⊗[k_] S_) := Algebra.TensorProduct.leftAlgebra
  letI : Module E_ (K_ ⊗[k_] S_) := TensorProduct.leftModule
  letI : Algebra E_ (K_ ⊗[k_] S_) := Algebra.TensorProduct.leftAlgebra
  letI : IsScalarTower k_ E_ (K_ ⊗[k_] S_) := inferInstance
  let g_K_k : K_ →ₐ[k_] K_ ⊗[k_] S_ := Algebra.TensorProduct.includeLeft
  let g_K : K_ →ₐ[E_] K_ ⊗[k_] S_ := { g_K_k with commutes' := fun _ => rfl }
  let g_ES_k : E_ ⊗[k_] S_ →ₐ[k_] K_ ⊗[k_] S_ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k_ E_ K_) (AlgHom.id k_ S_)
  let g_ES : E_ ⊗[k_] S_ →ₐ[E_] K_ ⊗[k_] S_ := { g_ES_k with commutes' := fun _ => rfl }
  have h_comm_g : ∀ x y, Commute (g_K x) (g_ES y) := fun x y => mul_comm (g_K x) (g_ES y)
  Algebra.TensorProduct.lift g_K g_ES h_comm_g

lemma tensor_equiv_base_change_gf
  (k_ E_ K_ S_ : Type*) [Field k_] [Field E_] [Field K_] [CommRing S_]
  [Algebra k_ E_] [Algebra k_ K_] [Algebra k_ S_] [Algebra E_ K_] [IsScalarTower k_ E_ K_] (x : K_ ⊗[k_] S_) :
  tensor_equiv_base_change_g k_ E_ K_ S_ (tensor_equiv_base_change_f k_ E_ K_ S_ x) = x := by
  push_cast[tensor_equiv_base_change_g,tensor_equiv_base_change_f]
  induction x with| zero=>apply RingHom.map_zero| tmul=>_| add=>simp_all
  aesop

lemma tensor_equiv_base_change
  (k_ E_ K_ S_ : Type*) [Field k_] [Field E_] [Field K_] [CommRing S_]
  [Algebra k_ E_] [Algebra k_ K_] [Algebra k_ S_] [Algebra E_ K_] [IsScalarTower k_ E_ K_] :
  IsReduced (K_ ⊗[E_] (E_ ⊗[k_] S_)) → IsReduced (K_ ⊗[k_] S_) := by
  intro h_red
  have h_inj : Function.Injective (tensor_equiv_base_change_f k_ E_ K_ S_) := by
    apply Function.LeftInverse.injective
    intro x
    apply tensor_equiv_base_change_gf
  exact isReduced_of_injective (tensor_equiv_base_change_f k_ E_ K_ S_) h_inj

lemma isReduced_tensorProduct_field_of_separablyGenerated
  (k_ K_ F_ : Type*) [Field k_] [Field K_] [Algebra k_ K_] [IsSeparablyGenerated k_ K_]
  [Field F_] [Algebra k_ F_] : IsReduced (K_ ⊗[k_] F_) := by
  obtain ⟨s, hs, hsep⟩ := IsSeparablyGenerated.out (k := k_) (K := K_)
  let E_ := IntermediateField.adjoin k_ s
  have hE_red : IsReduced (E_ ⊗[k_] F_) := isReduced_tensorProduct_adjoin_transcendenceBasis s hs
  letI : Module E_ E_ := Semiring.toModule
  letI : Module E_ (E_ ⊗[k_] F_) := TensorProduct.leftModule
  letI : Algebra E_ (E_ ⊗[k_] F_) := Algebra.TensorProduct.leftAlgebra
  apply tensor_equiv_base_change k_ E_ K_ F_
  haveI : Algebra.IsSeparable E_ K_ := hsep
  haveI : Algebra.IsAlgebraic E_ K_ := inferInstance
  apply isReduced_tensorProduct_of_isSeparable

-- EVOLVE-BLOCK-END

theorem isReduced_tensorProduct_of_separablyGenerated
    (K : Type u) [Field K] [Algebra k K] [IsSeparablyGenerated k K]
    [IsReduced S] : IsReduced (K ⊗[k] S) := by
  -- EVOLVE-BLOCK-START
  constructor
  rintro x ⟨n, hn⟩
  apply tensor_eq_zero_of_eval_eq_zero
  intro P
  let D := S ⧸ P.asIdeal
  let F_P := FractionRing D
  have h_red_F_P : IsReduced (K ⊗[k] F_P) := isReduced_tensorProduct_field_of_separablyGenerated k K F_P
  have h_map_inj : Function.Injective (TensorProduct.map (LinearMap.id : K →ₗ[k] K) (IsScalarTower.toAlgHom k D F_P).toLinearMap) :=
    map_injective_of_fractionRing
  have h_eval_nilp : IsNilpotent (Algebra.TensorProduct.map (AlgHom.id k K) (IsScalarTower.toAlgHom k S F_P) x) := by
    use n
    rw [← map_pow, hn, map_zero]
  have h_eval_zero : Algebra.TensorProduct.map (AlgHom.id k K) (IsScalarTower.toAlgHom k S F_P) x = 0 :=
    IsReduced.eq_zero _ h_eval_nilp
  have h_map_D_zero : TensorProduct.map (LinearMap.id : K →ₗ[k] K) (IsScalarTower.toAlgHom k S D).toLinearMap x = 0 := by
    apply h_map_inj
    rw [map_zero]
    have h1 : TensorProduct.map (LinearMap.id : K →ₗ[k] K) (IsScalarTower.toAlgHom k D F_P).toLinearMap (TensorProduct.map (LinearMap.id : K →ₗ[k] K) (IsScalarTower.toAlgHom k S D).toLinearMap x) = Algebra.TensorProduct.map (AlgHom.id k K) (IsScalarTower.toAlgHom k S F_P) x := by
      use x.induction_on (by bound) (by bound) (by norm_num+contextual)
    rw [h1, h_eval_zero]
  exact h_map_D_zero
  -- EVOLVE-BLOCK-END
