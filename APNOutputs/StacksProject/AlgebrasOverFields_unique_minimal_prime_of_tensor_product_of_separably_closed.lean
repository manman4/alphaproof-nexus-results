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
lemma irreducibleSpace_iff_nilradical_isPrime {R : Type*} [CommRing R] :
    IrreducibleSpace (PrimeSpectrum R) ↔ (nilradical R).IsPrime := by
  use fun and=>Ideal.isPrime_iff.2 ? _, fun and=>?_
  · simp_rw [nilradical_eq_sInf,Ne,irreducibleSpace_def]at*
    simp_rw [Ideal.mem_sInf,IsIrreducible,IsPreirreducible]at *
    use and.1.elim fun and R L=>and.2.1 (eq_top_mono (sInf_le and.2) L),or_iff_not_imp_left.2 ∘fun R L A B=>by_contra (L ∘fun H K V=>by_contra fun and' =>? _)
    use (and.2 _ _ ( PrimeSpectrum.isOpen_basicOpen) ( PrimeSpectrum.isOpen_basicOpen) ⟨⟨K, V⟩,trivial, and'⟩ ⟨⟨A, B⟩,trivial, H⟩).some_mem.2.elim (( PrimeSpectrum.isPrime _).2 (R ( PrimeSpectrum.isPrime _) ) ).elim
  rw [irreducibleSpace_def]
  cases subsingleton_or_nontrivial R with| inl=>cases and.1 (by subsingleton) | inr=>_
  delta IsIrreducible IsPreirreducible
  simp_rw [ PrimeSpectrum.isOpen_iff]
  use (by exists⟨_, and⟩),fun K V⟨A, B⟩C ⟨a, E, M⟩⟨b,F,α⟩=>⟨⟨_, and⟩,E,by_contra (B.ge.comp (fun H R L=>by_contra fun and' =>? _) · M),by_contra fun and' =>?_⟩
  · use and' (a.2.mem_of_pow_mem _ ((B.le H L).choose_spec▸zero_mem _))
  use C.elim fun and p=>p.ge (fun a s=>by_contra fun and=>? _) α
  use and (b.2.radical_le_iff.2 bot_le (p.le and' s))

lemma nilradical_prime_of_injective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f)
    (hB : (nilradical B).IsPrime) : (nilradical A).IsPrime := by
  have H : nilradical A = Ideal.comap f (nilradical B) := by
    ext x
    rw [Ideal.mem_comap, mem_nilradical, mem_nilradical]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← map_pow, hn, map_zero]⟩
    · rintro ⟨n, hn⟩
      use n
      apply hf
      rw [map_zero, map_pow, hn]
  rw [H]
  exact Ideal.comap_isPrime f (nilradical B)

lemma nilradical_prime_of_rad_surj {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f)
    (h_pow : ∀ y : B, ∃ n : ℕ, 0 < n ∧ ∃ x : A, y ^ n = f x) :
    (nilradical A).IsPrime ↔ (nilradical B).IsPrime := by
  constructor
  · intro hA
    constructor
    · intro h_top
      have h1 : (1 : B) ∈ nilradical B := by rw [h_top]; trivial
      rcases h1 with ⟨m, hm⟩
      have h_one_B : (1 : B) = 0 := by
        have h_pow_one : (1 : B) ^ m = 1 := one_pow m
        rw [h_pow_one] at hm
        exact hm
      have h_false : (1 : A) = 0 := by
        apply hf
        rw [map_one, map_zero, h_one_B]
      have h_not_top : nilradical A ≠ ⊤ := hA.ne_top
      apply h_not_top
      rw [Ideal.eq_top_iff_one]
      rw [h_false]
      exact Ideal.zero_mem (nilradical A)
    · rintro x y ⟨m, hm⟩
      rcases h_pow x with ⟨nx, hnx, x', hx'⟩
      rcases h_pow y with ⟨ny, hny, y', hy'⟩
      have hxy_pow : (x * y) ^ (nx * ny) = f (x' ^ ny * y' ^ nx) := by
        calc (x * y) ^ (nx * ny) = x ^ (nx * ny) * y ^ (nx * ny) := mul_pow x y (nx * ny)
        _ = (x ^ nx) ^ ny * (y ^ ny) ^ nx := by rw [pow_mul, mul_comm nx ny, ← pow_mul y ny nx]
        _ = (f x') ^ ny * (f y') ^ nx := by rw [hx', hy']
        _ = f (x' ^ ny) * f (y' ^ nx) := by rw [map_pow, map_pow]
        _ = f (x' ^ ny * y' ^ nx) := by rw [map_mul]
      have hm2 : (f (x' ^ ny * y' ^ nx)) ^ m = 0 := by
        rw [← hxy_pow, ← pow_mul, mul_comm (nx * ny) m, pow_mul, hm, zero_pow]
        intro h_zero
        have h_pos : 0 < nx * ny := mul_pos hnx hny
        linarith
      rw [← map_pow, map_eq_zero_iff f hf] at hm2
      have h_nil_A : x' ^ ny * y' ^ nx ∈ nilradical A := ⟨m, hm2⟩
      cases Ideal.IsPrime.mem_or_mem hA h_nil_A with
      | inl hx_nil =>
        left
        rcases hx_nil with ⟨k, hk⟩
        use nx * ny * k
        calc x ^ (nx * ny * k) = x ^ (nx * (ny * k)) := by rw [mul_assoc]
        _ = (x ^ nx) ^ (ny * k) := by rw [pow_mul]
        _ = (f x') ^ (ny * k) := by rw [hx']
        _ = f (x' ^ (ny * k)) := by rw [map_pow]
        _ = f ((x' ^ ny) ^ k) := by rw [pow_mul]
        _ = f 0 := by rw [hk]
        _ = 0 := map_zero f
      | inr hy_nil =>
        right
        rcases hy_nil with ⟨k, hk⟩
        use ny * nx * k
        calc y ^ (ny * nx * k) = y ^ (ny * (nx * k)) := by rw [mul_assoc]
        _ = (y ^ ny) ^ (nx * k) := by rw [pow_mul]
        _ = (f y') ^ (nx * k) := by rw [hy']
        _ = f (y' ^ (nx * k)) := by rw [map_pow]
        _ = f ((y' ^ nx) ^ k) := by rw [pow_mul]
        _ = f 0 := by rw [hk]
        _ = 0 := map_zero f
  · intro hB
    exact nilradical_prime_of_injective f hf hB

lemma purely_inseparable_extension_injective
    {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K]
    {R : Type*} [CommRing R] [Algebra k R] :
    Function.Injective (algebraMap R (R ⊗[k] K)) := by
  norm_num[Function.Injective,funext_iff]
  let:=Module.Free.chooseBasis k R
  norm_num[this.tensorProduct (Module.Free.chooseBasis _ _)|>.ext_elem_iff,this.ext_elem_iff]
  exact fun and A B x =>(B _ _).resolve_right (DFunLike.exists_ne ((Module.Free.chooseBasis _ _).repr.map_ne_zero_iff.mpr one_ne_zero)).choose_spec

lemma rad_surj_zero {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K]
    [IsPurelyInseparable k K] {R : Type*} [CommRing R] [Algebra k R] :
    ∃ n : ℕ, ∃ x : R, (0 : R ⊗[k] K) ^ ((ringExpChar k) ^ n) = x ⊗ₜ[k] 1 := by
  use 0, 0
  simp

lemma rad_surj_tmul {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K]
    [IsPurelyInseparable k K] {R : Type*} [CommRing R] [Algebra k R] (a : R) (b : K) :
    let q := ringExpChar k
    ∃ n : ℕ, ∃ x : R, (a ⊗ₜ[k] b) ^ (q ^ n) = x ⊗ₜ[k] 1 := by
  apply (IsPurelyInseparable.pow_mem k ↑(ringExpChar k) b).imp
  simp_all[TensorProduct.smul_tmul',comm, Algebra.algebraMap_eq_smul_one]

lemma rad_surj_add {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K]
    [IsPurelyInseparable k K] {R : Type*} [CommRing R] [Algebra k R] (x y : R ⊗[k] K) :
    let q := ringExpChar k
    (∃ n : ℕ, ∃ a : R, x ^ (q ^ n) = a ⊗ₜ[k] 1) →
    (∃ n : ℕ, ∃ a : R, y ^ (q ^ n) = a ⊗ₜ[k] 1) →
    ∃ n : ℕ, ∃ a : R, (x + y) ^ (q ^ n) = a ⊗ₜ[k] 1 := by
  rcases ↑(CharP.exists @k)
  obtain ⟨rfl⟩ :=eq_or_ne (by valid) 0
  · norm_num[ringExpChar.eq,CharP.charP_to_charZero]
    use fun and A B true => true▸A▸⟨ _,by rw [TensorProduct.add_tmul]⟩
  simp_all (config := {singlePass := 1})[ringExpChar.eq,Fact.mk,CharP.char_prime_of_ne_zero k]
  use fun and A B R L h=>by_contra (absurd (Fact.mk (CharP.char_prime_of_ne_zero k (by valid))) fun and' =>. ⟨and⊔ R,?_⟩)
  norm_num[ringExpChar.eq,Commute.add_pow<|.all x y] at h B⊢
  norm_num[ringExpChar.eq k (by bound), Finset.sum_range_succ] at h B⊢
  rw[ Finset.sum_eq_single_of_mem 0 (by norm_num[ (and').out.pos])]
  · norm_num[*,Nat.add_sub_of_le (le_max_right and R)▸pow_add _ _ _,and.add_sub_of_le (le_max_left and R)▸pow_add _ _ _,pow_mul]
    norm_num[B,←pow_mul,←pow_add]
    norm_num[B,and.add_sub_of_le (le_max_left _ _)▸pow_add _ _ _,pow_mul,TensorProduct.add_tmul]
    exact ⟨ _,by rw [TensorProduct.add_tmul]⟩
  · use fun and R M=>mul_eq_zero_of_right _ ?_
    rcases (and').out.dvd_choose_pow M ↑(List.mem_range.1 R).ne
    norm_num[*,←map_natCast ↑(algebraMap k (by assumption))]
    exact (mul_eq_zero_of_left ((map_natCast (algebraMap k _) _).symm.trans (by norm_num)) _)

lemma rad_surj_helper {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K]
    [IsPurelyInseparable k K] {R : Type*} [CommRing R] [Algebra k R] :
    ∀ y : R ⊗[k] K, ∃ n : ℕ, ∃ x : R, y ^ ((ringExpChar k) ^ n) = x ⊗ₜ[k] 1 := by
  intro y
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · exact rad_surj_zero K
  · exact rad_surj_tmul K
  · exact rad_surj_add K

lemma purely_inseparable_extension_rad_surj
    {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K]
    [IsPurelyInseparable k K]
    {R : Type*} [CommRing R] [Algebra k R] :
    let f : R →+* R ⊗[k] K := algebraMap R (R ⊗[k] K)
    ∀ y : R ⊗[k] K, ∃ n : ℕ, 0 < n ∧ ∃ x : R, y ^ n = f x := by
  intro f y
  have h := rad_surj_helper K (R := R) y
  exact ⟨ _,pow_pos (expChar_pos k _) _,h.choose_spec⟩




lemma purely_inseparable_extension_spectrum_homeo
    {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K]
    [IsPurelyInseparable k K]
    {R : Type*} [CommRing R] [Algebra k R] :
    IrreducibleSpace (PrimeSpectrum R) ↔ IrreducibleSpace (PrimeSpectrum (R ⊗[k] K)) := by
  rw [irreducibleSpace_iff_nilradical_isPrime, irreducibleSpace_iff_nilradical_isPrime]
  exact nilradical_prime_of_rad_surj
    (algebraMap R (R ⊗[k] K))
    (purely_inseparable_extension_injective K)
    (purely_inseparable_extension_rad_surj K)

lemma algebraic_closure_is_purely_inseparable
    {k : Type*} [Field k] [IsSepClosed k] :
    IsPurelyInseparable k (AlgebraicClosure k) := by
  infer_instance

lemma nilradical_comap_isPrime {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (h_surj : Function.Surjective f) (h_ker : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    (nilradical A).IsPrime ↔ (nilradical B).IsPrime := by
  simp_rw [Ideal.isPrime_iff,mem_nilradical, RingHom.mem_ker] at *
  push_cast[nilradical,Ne,Submodule.eq_top_iff',Submodule.mem_span_singleton]
  push_cast only[Ideal.mem_radical_iff,Pi.mul_apply,Pi.zero_apply,Function.Surjective]at*
  use .imp (mt fun and x =>(and (f x)).elim ? _) fun and R M ⟨a, _⟩=>(h_surj R).elim ((h_surj M).elim fun A B K V=>? _),.imp (mt fun and x =>(and (h_surj x).choose).imp ?_) ?_
  · exact (IsNilpotent.of_pow ∘h_ker _<|f.map_pow x ·|>.trans ·)
  · use V▸B▸ (@and K A ((h_ker _ ((f.map_pow _ _).trans (f.map_mul _ _▸by bound))).elim (⟨a*.,pow_mul (K*A) _ _▸.⟩))).imp (.imp fun and=>(f.map_pow _ _▸by simp_all)) ?_
    exact (.imp (f.map_pow A ·▸·▸f.map_zero))
  · use fun and=>((congr_arg₂ _) (@h_surj x).choose_spec.symm rfl).trans ∘(f.map_pow _ _▸.▸f.map_zero)
  · use fun and K V p=> (and (p.imp fun and=>(f.map_mul K V▸f.map_pow _ _▸.▸f.map_zero))).imp (.rec fun and x =>⟨ _,.trans (pow_mul _ _ _) (h_ker _ ((f.map_pow _ _).trans x)).choose_spec⟩) ?_
    exact (.rec fun and x =>⟨ _,by rw [pow_mul,((h_ker _).comp (f.map_pow _ _).trans x).choose_spec]⟩)

lemma TensorProduct_map_surjective {k R S R' S' : Type*} [CommRing k] [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra k R] [Algebra k S] [Algebra k R'] [Algebra k S'] (f : R →ₐ[k] R') (g : S →ₐ[k] S') (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (Algebra.TensorProduct.map f g) := by
  use TensorProduct.map_surjective hf hg

lemma isNilpotent_of_mem_ideal_map_of_isNilpotent
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (I : Ideal R)
    (hI : ∀ x ∈ I, IsNilpotent x) (y : S) (hy : y ∈ Ideal.map f I) : IsNilpotent y := by
  rewrite[Ideal.map]at hy
  obtain ⟨x, hx⟩ := Submodule.mem_span_image_iff_exists_fun _ |>.mp hy
  exact hx.2.choose_spec▸isNilpotent_sum fun and k=>Commute.isNilpotent_mul_left (.all _ _) ((hI and (hx.1 and.2)).imp fun and=>(f.map_pow _ _).symm.trans ∘f.map_zero.subst ∘congr_arg _)

lemma ker_tensorProduct_map_id_eq_ideal_map
    {k A B C : Type*} [Field k]
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (f : A →ₐ[k] C)
    (hf_surj : Function.Surjective f) :
    RingHom.ker (Algebra.TensorProduct.map f (AlgHom.id k B)).toRingHom =
    Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom (RingHom.ker f.toRingHom) := by
  apply Algebra.TensorProduct.rTensor_ker
  valid

lemma ker_tensorProduct_map_id_isNilpotent
    {k A B C : Type*} [Field k]
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (f : A →ₐ[k] C)
    (hf : ∀ x ∈ RingHom.ker f.toRingHom, IsNilpotent x)
    (hf_surj : Function.Surjective f) :
    ∀ x ∈ RingHom.ker (Algebra.TensorProduct.map f (AlgHom.id k B)).toRingHom, IsNilpotent x := by
  intro x hx
  rw [ker_tensorProduct_map_id_eq_ideal_map f hf_surj] at hx
  exact isNilpotent_of_mem_ideal_map_of_isNilpotent _ _ hf x hx

lemma ker_comp_isNilpotent {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (hg : ∀ y ∈ RingHom.ker g, IsNilpotent y) :
    ∀ x ∈ RingHom.ker (g.comp f), IsNilpotent x := by
  intro x hx
  have h1 : g (f x) = 0 := hx
  have h2 : IsNilpotent (f x) := hg (f x) h1
  rcases h2 with ⟨n, hn⟩
  have h3 : f (x ^ n) = 0 := by rw [map_pow, hn]
  have h4 : IsNilpotent (x ^ n) := hf (x ^ n) h3
  rcases h4 with ⟨m, hm⟩
  use n * m
  rw [pow_mul]
  exact hm

lemma ker_tensorProduct_map_id_right_eq_ideal_map
    {k A B C : Type*} [Field k]
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (g : B →ₐ[k] C)
    (hg_surj : Function.Surjective g) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k A) g).toRingHom =
    Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom (RingHom.ker g.toRingHom) := by
  apply Algebra.TensorProduct.lTensor_ker
  valid

lemma ker_tensorProduct_map_id_right_isNilpotent
    {k A B C : Type*} [Field k]
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (g : B →ₐ[k] C)
    (hg : ∀ x ∈ RingHom.ker g.toRingHom, IsNilpotent x)
    (hg_surj : Function.Surjective g) :
    ∀ x ∈ RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k A) g).toRingHom, IsNilpotent x := by
  intro x hx
  rw [ker_tensorProduct_map_id_right_eq_ideal_map g hg_surj] at hx
  exact isNilpotent_of_mem_ideal_map_of_isNilpotent _ _ hg x hx

lemma TensorProduct_map_ker_isNilpotent {k R S R' S' : Type*} [Field k] [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra k R] [Algebra k S] [Algebra k R'] [Algebra k S'] (f : R →ₐ[k] R') (g : S →ₐ[k] S') (hf_surj : Function.Surjective f) (hg_surj : Function.Surjective g) (hf : ∀ x ∈ RingHom.ker f.toRingHom, IsNilpotent x) (hg : ∀ x ∈ RingHom.ker g.toRingHom, IsNilpotent x) :
    ∀ x ∈ RingHom.ker (Algebra.TensorProduct.map f g).toRingHom, IsNilpotent x := by
  have h1 : (Algebra.TensorProduct.map f g) = ((Algebra.TensorProduct.map (AlgHom.id k R') g)).comp ((Algebra.TensorProduct.map f (AlgHom.id k S))) := by
    apply Algebra.TensorProduct.ext
    · ext a; simp
    · ext b; simp
  have h2 : (Algebra.TensorProduct.map f g).toRingHom = ((Algebra.TensorProduct.map (AlgHom.id k R') g).toRingHom).comp ((Algebra.TensorProduct.map f (AlgHom.id k S)).toRingHom) := by
    ext x
    exact AlgHom.congr_fun h1 x
  rw [h2]
  apply ker_comp_isNilpotent
  · exact ker_tensorProduct_map_id_isNilpotent f hf hf_surj
  · exact ker_tensorProduct_map_id_right_isNilpotent g hg hg_surj

lemma isPrime_nilradical_of_injective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) (hB : (nilradical B).IsPrime) :
    (nilradical A).IsPrime := by
  replace hf:nilradical A=(nilradical B).comap f
  · exact (Ideal.ext fun and=>exists_congr fun and=>hf.eq_iff.symm.trans (Eq.congr (f.map_pow _ _) f.map_zero))
  · convert(hB.comap (f))

lemma tensor_map_injective {k R S R' S' : Type*} [Field k] [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra k R] [Algebra k S] [Algebra k R'] [Algebra k S']
    (f : R →ₐ[k] R') (g : S →ₐ[k] S') (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (Algebra.TensorProduct.map f g) := by
  exact (TensorProduct.map_injective_of_flat_flat _ _ (hf ) ) hg

lemma reduction_to_domains
    {k : Type u} [Field k]
    {R : Type v} {S : Type w} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [IrreducibleSpace (PrimeSpectrum R)] [IrreducibleSpace (PrimeSpectrum S)]
    (h_dom : ∀ (R' : Type v) (S' : Type w) [CommRing R'] [CommRing S'] [Algebra k R'] [Algebra k S'] [IsDomain R'] [IsDomain S'],
      IrreducibleSpace (PrimeSpectrum R') → IrreducibleSpace (PrimeSpectrum S') →
      IrreducibleSpace (PrimeSpectrum (R' ⊗[k] S'))) :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) := by
  have hR : (nilradical R).IsPrime := (irreducibleSpace_iff_nilradical_isPrime).mp ‹_›
  have hS : (nilradical S).IsPrime := (irreducibleSpace_iff_nilradical_isPrime).mp ‹_›
  let R' := R ⧸ nilradical R
  let S' := S ⧸ nilradical S
  haveI : IsDomain R' := Ideal.Quotient.isDomain (nilradical R)
  haveI : IsDomain S' := Ideal.Quotient.isDomain (nilradical S)
  let f := Ideal.Quotient.mkₐ k (nilradical R)
  let g := Ideal.Quotient.mkₐ k (nilradical S)
  have hf_surj : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hg_surj : Function.Surjective g := Ideal.Quotient.mk_surjective
  have hf_nil : ∀ x ∈ RingHom.ker f.toRingHom, IsNilpotent x := fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp hx
  have hg_nil : ∀ x ∈ RingHom.ker g.toRingHom, IsNilpotent x := fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp hx
  have hR'_nil_prime : (nilradical R').IsPrime := (nilradical_comap_isPrime f.toRingHom hf_surj hf_nil).mp hR
  have hS'_nil_prime : (nilradical S').IsPrime := (nilradical_comap_isPrime g.toRingHom hg_surj hg_nil).mp hS
  have hR'_irred : IrreducibleSpace (PrimeSpectrum R') := (irreducibleSpace_iff_nilradical_isPrime).mpr hR'_nil_prime
  have hS'_irred : IrreducibleSpace (PrimeSpectrum S') := (irreducibleSpace_iff_nilradical_isPrime).mpr hS'_nil_prime
  have h_RS_irred : IrreducibleSpace (PrimeSpectrum (R' ⊗[k] S')) := h_dom R' S' hR'_irred hS'_irred
  have h_RS'_nil_prime : (nilradical (R' ⊗[k] S')).IsPrime := (irreducibleSpace_iff_nilradical_isPrime).mp h_RS_irred
  have h_ker_nil : ∀ x ∈ RingHom.ker (Algebra.TensorProduct.map f g).toRingHom, IsNilpotent x := TensorProduct_map_ker_isNilpotent f g hf_surj hg_surj hf_nil hg_nil

  have h_map_surj : Function.Surjective (Algebra.TensorProduct.map f g) := TensorProduct_map_surjective f g hf_surj hg_surj
  have h_comap : (nilradical (R ⊗[k] S)).IsPrime ↔ (nilradical (R' ⊗[k] S')).IsPrime := nilradical_comap_isPrime (Algebra.TensorProduct.map f g).toRingHom h_map_surj h_ker_nil
  have h_final : (nilradical (R ⊗[k] S)).IsPrime := h_comap.mpr h_RS'_nil_prime
  exact (irreducibleSpace_iff_nilradical_isPrime).mpr h_final

lemma reduction_to_fields
    {k : Type u} [Field k]
    {R : Type v} {S : Type w} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] [IsDomain R] [IsDomain S]
    (h_fields : ∀ (K : Type v) (L : Type w) [Field K] [Field L] [Algebra k K] [Algebra k L],
      IrreducibleSpace (PrimeSpectrum (K ⊗[k] L))) :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) := by
  let K := FractionRing R
  let L := FractionRing S
  have hKL := h_fields K L
  let f : R →ₐ[k] K := IsScalarTower.toAlgHom k R K
  let g : S →ₐ[k] L := IsScalarTower.toAlgHom k S L
  have hf : Function.Injective f := IsFractionRing.injective R K
  have hg : Function.Injective g := IsFractionRing.injective S L
  have h_inj : Function.Injective (Algebra.TensorProduct.map f g) := tensor_map_injective f g hf hg
  have h_prime := (irreducibleSpace_iff_nilradical_isPrime).mp hKL
  have h_comap := isPrime_nilradical_of_injective (Algebra.TensorProduct.map f g).toRingHom h_inj h_prime
  exact (irreducibleSpace_iff_nilradical_isPrime).mpr h_comap

lemma irreducibleSpace_of_isDomain {A : Type*} [CommRing A] [IsDomain A] : IrreducibleSpace (PrimeSpectrum A) := by
  rw [irreducibleSpace_iff_nilradical_isPrime]
  have : nilradical A = ⊥ := nilradical_eq_zero A
  rw [this]
  exact Ideal.isPrime_bot

lemma tensorProduct_nontrivial {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] : Nontrivial (K ⊗[k] L) := by
  infer_instance

lemma test_nullstellensatz_eval
    {k A : Type*} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [IsDomain A] (h_fg : Algebra.FiniteType k A) (m : Ideal A) [hm : m.IsMaximal] :
    Nonempty ((A ⧸ m) ≃ₐ[k] k) := by
  let' :=Ideal.Quotient.maximal_ideal_iff_isField_quotient m
  let' :=(this.1 @hm).toField
  replace h_fg: (FiniteDimensional k (A⧸ (m)))
  · convert←Module.finite_of_isArtinianRing k (A⧸m)
  · exact ⟨.symm<|AlgEquiv.ofBijective (Algebra.ofId _ _) ⟨ RingHom.injective _, fun and=> (minpoly.degree_eq_one_iff.1 (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible (.of_finite _ _))))⟩⟩

lemma exists_finite_set_subalgebra_single
    {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    (x : K ⊗[k] L) :
    ∃ (S : Set K), S.Finite ∧ ∃ x' : (Algebra.adjoin k S) ⊗[k] L,
      Algebra.TensorProduct.map (Algebra.adjoin k S).val (AlgHom.id k L) x' = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · use ∅
    refine ⟨Set.finite_empty, 0, map_zero _⟩
  · intro a b
    use {a}
    refine ⟨Set.finite_singleton a, ⟨a, Algebra.subset_adjoin (Set.mem_singleton a)⟩ ⊗ₜ b, ?_⟩
    simp
  · rintro u v ⟨Su, hSu, u', hu'⟩ ⟨Sv, hSv, v', hv'⟩
    use Su ∪ Sv
    refine ⟨hSu.union hSv, ?_⟩
    let Au := Algebra.adjoin k (Su ∪ Sv)
    let fu : Algebra.adjoin k Su →ₐ[k] Au := Subalgebra.inclusion (Algebra.adjoin_mono Set.subset_union_left)
    let fv : Algebra.adjoin k Sv →ₐ[k] Au := Subalgebra.inclusion (Algebra.adjoin_mono Set.subset_union_right)
    use (Algebra.TensorProduct.map fu (AlgHom.id k L)) u' + (Algebra.TensorProduct.map fv (AlgHom.id k L)) v'
    rw [map_add]
    have h1 : Algebra.TensorProduct.map Au.val (AlgHom.id k L) ((Algebra.TensorProduct.map fu (AlgHom.id k L)) u') = u := by
      have hF_eq_G : (Algebra.TensorProduct.map Au.val (AlgHom.id k L)).comp (Algebra.TensorProduct.map fu (AlgHom.id k L)) = Algebra.TensorProduct.map (Algebra.adjoin k Su).val (AlgHom.id k L) := by
        apply Algebra.TensorProduct.ext
        · ext a; simp; rfl
        · ext b; simp
      have h_eval : (Algebra.TensorProduct.map Au.val (AlgHom.id k L)) ((Algebra.TensorProduct.map fu (AlgHom.id k L)) u') = ((Algebra.TensorProduct.map Au.val (AlgHom.id k L)).comp (Algebra.TensorProduct.map fu (AlgHom.id k L))) u' := rfl
      rw [h_eval, hF_eq_G, hu']
    have h2 : Algebra.TensorProduct.map Au.val (AlgHom.id k L) ((Algebra.TensorProduct.map fv (AlgHom.id k L)) v') = v := by
      have hF_eq_G : (Algebra.TensorProduct.map Au.val (AlgHom.id k L)).comp (Algebra.TensorProduct.map fv (AlgHom.id k L)) = Algebra.TensorProduct.map (Algebra.adjoin k Sv).val (AlgHom.id k L) := by
        apply Algebra.TensorProduct.ext
        · ext a; simp; rfl
        · ext b; simp
      have h_eval : (Algebra.TensorProduct.map Au.val (AlgHom.id k L)) ((Algebra.TensorProduct.map fv (AlgHom.id k L)) v') = ((Algebra.TensorProduct.map Au.val (AlgHom.id k L)).comp (Algebra.TensorProduct.map fv (AlgHom.id k L))) v' := rfl
      rw [h_eval, hF_eq_G, hv']
    rw [h1, h2]

lemma exists_finite_set_subalgebra_double
    {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    (x y : K ⊗[k] L) :
    ∃ (S : Set K), S.Finite ∧
      (∃ x' : (Algebra.adjoin k S) ⊗[k] L, Algebra.TensorProduct.map (Algebra.adjoin k S).val (AlgHom.id k L) x' = x) ∧
      (∃ y' : (Algebra.adjoin k S) ⊗[k] L, Algebra.TensorProduct.map (Algebra.adjoin k S).val (AlgHom.id k L) y' = y) := by
  rcases exists_finite_set_subalgebra_single x with ⟨Sx, hSx, x', hx⟩
  rcases exists_finite_set_subalgebra_single y with ⟨Sy, hSy, y', hy⟩
  use Sx ∪ Sy
  refine ⟨hSx.union hSy, ?_, ?_⟩
  · let Axy := Algebra.adjoin k (Sx ∪ Sy)
    let fx : Algebra.adjoin k Sx →ₐ[k] Axy := Subalgebra.inclusion (Algebra.adjoin_mono Set.subset_union_left)
    use Algebra.TensorProduct.map fx (AlgHom.id k L) x'
    have hF_eq_G : (Algebra.TensorProduct.map Axy.val (AlgHom.id k L)).comp (Algebra.TensorProduct.map fx (AlgHom.id k L)) = Algebra.TensorProduct.map (Algebra.adjoin k Sx).val (AlgHom.id k L) := by
      apply Algebra.TensorProduct.ext
      · ext a; simp; rfl
      · ext b; simp
    have h_eval : (Algebra.TensorProduct.map Axy.val (AlgHom.id k L)) ((Algebra.TensorProduct.map fx (AlgHom.id k L)) x') = ((Algebra.TensorProduct.map Axy.val (AlgHom.id k L)).comp (Algebra.TensorProduct.map fx (AlgHom.id k L))) x' := rfl
    rw [h_eval, hF_eq_G, hx]
  · let Axy := Algebra.adjoin k (Sx ∪ Sy)
    let fy : Algebra.adjoin k Sy →ₐ[k] Axy := Subalgebra.inclusion (Algebra.adjoin_mono Set.subset_union_right)
    use Algebra.TensorProduct.map fy (AlgHom.id k L) y'
    have hF_eq_G : (Algebra.TensorProduct.map Axy.val (AlgHom.id k L)).comp (Algebra.TensorProduct.map fy (AlgHom.id k L)) = Algebra.TensorProduct.map (Algebra.adjoin k Sy).val (AlgHom.id k L) := by
      apply Algebra.TensorProduct.ext
      · ext a; simp; rfl
      · ext b; simp
    have h_eval : (Algebra.TensorProduct.map Axy.val (AlgHom.id k L)) ((Algebra.TensorProduct.map fy (AlgHom.id k L)) y') = ((Algebra.TensorProduct.map Axy.val (AlgHom.id k L)).comp (Algebra.TensorProduct.map fy (AlgHom.id k L))) y' := rfl
    rw [h_eval, hF_eq_G, hy]

lemma finiteType_adjoin_set {k K : Type*} [Field k] [CommRing K] [Algebra k K] {S : Set K} (hS : S.Finite) :
    Algebra.FiniteType k (Algebra.adjoin k S) := by
  use hS.toFinset.preimage _ Subtype.coe_injective.injOn, by aesop

noncomputable def tensor_eval {k A L : Type*} [Field k] [CommRing A] [Field L] [Algebra k A] [Algebra k L]
    (f : L →ₗ[k] k) : A ⊗[k] L →ₗ[k] A :=
  (TensorProduct.rid k A).toLinearMap.comp (TensorProduct.map LinearMap.id f)

lemma exists_tensor_eval_ne_zero_helper
    {k A L : Type*} [Field k] [CommRing A] [Field L] [Algebra k A] [Algebra k L]
    (x : A ⊗[k] L) (h : ∀ f : L →ₗ[k] k, tensor_eval f x = 0) : x = 0 := by
  let:=Module.Free.chooseBasis k L
  norm_num [tensor_eval] at h
  simp_all[TensorProduct.map]
  let α :=Module.Free.chooseBasis k A
  obtain ⟨l, rfl⟩:=α.tensorProduct this|>.repr.symm.surjective x
  norm_num[l.linearCombination_apply, Finsupp.sum] at h⊢
  norm_num[α.tensorProduct this|>.ext_elem_iff]at*
  use fun R M=>by_contra<|absurd (congrArg (α.repr · R)<|congrArg (TensorProduct.rid _ _)<|h<|this.coord M) ∘?_
  norm_num[Finsupp.single_apply,id]
  rw[Finset.sum_eq_single (R,M)]
  · norm_num[Module.Basis.tensorProduct]
  · exact (fun(a, b) A B=>by cases em (b=M) with simp_all-contextual[ne_comm])
  · exact (mul_eq_zero_of_left.comp l.notMem_support_iff.1 · _)

lemma exists_tensor_eval_ne_zero
    {k A L : Type*} [Field k] [CommRing A] [Field L] [Algebra k A] [Algebra k L]
    (x : A ⊗[k] L) (hx : x ≠ 0) :
    ∃ (f : L →ₗ[k] k), tensor_eval f x ≠ 0 := by
  by_contra h
  push_neg at h
  exact hx (exists_tensor_eval_ne_zero_helper x h)

lemma isJacobsonRing_of_finiteType_field {k A : Type*} [Field k] [CommRing A] [Algebra k A] (h_fg : Algebra.FiniteType k A) : IsJacobsonRing A := by
  have α :=Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h_fg
  convert isJacobsonRing_of_surjective ⟨ _,α.choose_spec.choose_spec⟩

lemma jacobson_bot_helper_h1
    {A : Type*} [CommRing A]
    (a : A) (h : ∀ m : Ideal A, m.IsMaximal → a ∈ m) :
    a ∈ Ideal.jacobson ⊥ := by
  exact (Ideal.mem_sInf.2) (h · ·.2)

lemma jacobson_bot_helper_h2
    {A : Type*} [CommRing A]
    [IsJacobsonRing A] :
    Ideal.jacobson ⊥ = nilradical A := by
  rcases (by assumption')
  exact (le_antisymm ((Ideal.jacobson_mono bot_le).trans_eq (by apply_rules[Ideal.radical_isRadical]))) (Ideal.radical_le_jacobson)

lemma jacobson_bot_of_domain_helper
    {k A : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (h_fg : Algebra.FiniteType k A) (a : A) (h : ∀ m : Ideal A, m.IsMaximal → a ∈ m) :
    IsNilpotent a := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType_field h_fg
  have h1 : a ∈ Ideal.jacobson ⊥ := jacobson_bot_helper_h1 a h
  have h2 : Ideal.jacobson ⊥ = nilradical A := jacobson_bot_helper_h2
  rw [← mem_nilradical]
  rw [← h2]
  exact h1

lemma nilpotent_eq_zero_of_domain {A : Type*} [CommRing A] [IsDomain A] (a : A) (h : IsNilpotent a) : a = 0 := by
  simp_all?

lemma jacobson_bot_of_domain
    {k A : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (h_fg : Algebra.FiniteType k A) (a : A) (ha : a ≠ 0) :
    ∃ (m : Ideal A), m.IsMaximal ∧ a ∉ m := by
  by_contra h
  push_neg at h
  have h_nil : IsNilpotent a := jacobson_bot_of_domain_helper h_fg a h
  have h_zero : a = 0 := nilpotent_eq_zero_of_domain a h_nil
  exact ha h_zero

noncomputable def eval_hom {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (m : Ideal A) [m.IsMaximal] (psi : (A ⧸ m) ≃ₐ[k] k) : A →ₐ[k] k :=
  psi.toAlgHom.comp (Ideal.Quotient.mkₐ k m)

lemma eval_hom_not_mem {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (m : Ideal A) [hm : m.IsMaximal] (psi : (A ⧸ m) ≃ₐ[k] k) (a : A) (ha : a ∉ m) :
    eval_hom m psi a ≠ 0 := by
  apply psi.map_ne_zero_iff.2.comp ha.comp Ideal.Quotient.eq_zero_iff_mem.mp

noncomputable def eval_tensor_hom {k A L : Type*} [Field k] [CommRing A] [Field L] [Algebra k A] [Algebra k L]
    (pi : A →ₐ[k] k) : A ⊗[k] L →ₐ[k] L :=
  AlgEquiv.toAlgHom (Algebra.TensorProduct.lid k L) |>.comp (Algebra.TensorProduct.map pi (AlgHom.id k L))

lemma pi_tensor_eval
    {k A L : Type*} [Field k] [CommRing A] [Field L] [Algebra k A] [Algebra k L]
    (f : L →ₗ[k] k) (pi : A →ₐ[k] k) (x : A ⊗[k] L) :
    pi (tensor_eval f x) = f (eval_tensor_hom pi x) := by
  simp_rw [tensor_eval, eval_tensor_hom]
  induction x with| zero=>apply pi.map_zero.trans f.map_zero.symm| tmul=>_| add=>simp_all
  norm_num[mul_comm]

lemma tensor_map_injective_helper {k A K L : Type*} [Field k] [CommRing A] [Field K] [Field L]
    [Algebra k A] [Algebra k K] [Algebra k L]
    (f : A →ₐ[k] K) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map f (AlgHom.id k L)) := by
  apply Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf

lemma isDomain_of_alg_closed
    {k K L : Type*} [Field k] [IsAlgClosed k]
    [Field K] [Field L] [Algebra k K] [Algebra k L] :
    IsDomain (K ⊗[k] L) := by
  haveI : Nontrivial (K ⊗[k] L) := tensorProduct_nontrivial
  haveI : NoZeroDivisors (K ⊗[k] L) := ⟨by
    intro x y hxy
    by_contra h_contra
    push_neg at h_contra
    rcases h_contra with ⟨hx, hy⟩
    rcases exists_finite_set_subalgebra_double x y with ⟨S, hS, ⟨x', hx'⟩, ⟨y', hy'⟩⟩
    let A := Algebra.adjoin k S
    haveI : IsDomain A := inferInstance
    have h_fg : Algebra.FiniteType k A := finiteType_adjoin_set hS
    have h_inj : Function.Injective (Algebra.TensorProduct.map A.val (AlgHom.id k L)) :=
      tensor_map_injective_helper A.val (fun u v h => Subtype.ext h)
    have hxy' : x' * y' = 0 := by
      apply h_inj
      rw [map_mul, hx', hy', hxy, map_zero]
    have hx'_ne : x' ≠ 0 := by
      intro h
      apply hx
      rw [← hx', h, map_zero]
    have hy'_ne : y' ≠ 0 := by
      intro h
      apply hy
      rw [← hy', h, map_zero]
    rcases exists_tensor_eval_ne_zero x' hx'_ne with ⟨fx, hfx⟩
    rcases exists_tensor_eval_ne_zero y' hy'_ne with ⟨fy, hfy⟩
    let a := tensor_eval fx x'
    let c := tensor_eval fy y'
    have hac : a * c ≠ 0 := mul_ne_zero hfx hfy
    rcases jacobson_bot_of_domain h_fg (a * c) hac with ⟨m, hm_max, hm_not⟩
    have ha_not : a ∉ m := by
      intro h
      apply hm_not
      exact Ideal.mul_mem_right c m h
    have hc_not : c ∉ m := by
      intro h
      apply hm_not
      exact Ideal.mul_mem_left m a h
    haveI : m.IsMaximal := hm_max
    have ⟨psi⟩ := test_nullstellensatz_eval h_fg m
    let pi := eval_hom m psi
    have h_pi_a : pi a ≠ 0 := eval_hom_not_mem m psi a ha_not
    have h_pi_c : pi c ≠ 0 := eval_hom_not_mem m psi c hc_not
    let Phi := eval_tensor_hom (L := L) pi
    have hPhi_x : Phi x' ≠ 0 := by
      intro h
      have : fx (Phi x') = 0 := by rw [h, map_zero]
      rw [← pi_tensor_eval fx pi x'] at this
      exact h_pi_a this
    have hPhi_y : Phi y' ≠ 0 := by
      intro h
      have : fy (Phi y') = 0 := by rw [h, map_zero]
      rw [← pi_tensor_eval fy pi y'] at this
      exact h_pi_c this
    have hPhi_xy : Phi (x' * y') = Phi x' * Phi y' := map_mul Phi x' y'
    rw [hxy', map_zero] at hPhi_xy
    have h_prod : Phi x' * Phi y' ≠ 0 := mul_ne_zero hPhi_x hPhi_y
    rw [← hPhi_xy] at h_prod
    exact h_prod rfl
  ⟩
  exact ⟨⟩

lemma fields_over_alg_closed
    {k : Type*} [Field k] [IsAlgClosed k]
    (K L : Type*) [Field K] [Field L] [Algebra k K] [Algebra k L] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[k] L)) := by
  haveI := isDomain_of_alg_closed (k := k) (K := K) (L := L)
  exact irreducibleSpace_of_isDomain

lemma tensor_product_over_alg_closed
    {k : Type*} [Field k] [IsAlgClosed k]
    {R S : Type*} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [IrreducibleSpace (PrimeSpectrum R)] [IrreducibleSpace (PrimeSpectrum S)] :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) := by
  let h_dom : ∀ (R' S' : Type _) [CommRing R'] [CommRing S'] [Algebra k R'] [Algebra k S'] [IsDomain R'] [IsDomain S'],
      IrreducibleSpace (PrimeSpectrum R') → IrreducibleSpace (PrimeSpectrum S') → IrreducibleSpace (PrimeSpectrum (R' ⊗[k] S')) := by
    intros R' S' _ _ _ _ _ _ _ _
    apply reduction_to_fields
    intros K L _ _ _ _
    apply fields_over_alg_closed
  apply reduction_to_domains h_dom

def comm_K_alg
    {k K S : Type*} [Field k] [Field K] [CommRing S]
    [Algebra k K] [Algebra k S] :
    letI : Algebra K (S ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra K (K ⊗[k] S) := Algebra.TensorProduct.leftAlgebra
    (S ⊗[k] K) ≃ₐ[K] (K ⊗[k] S) := by
  letI : Algebra K (S ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra K (K ⊗[k] S) := Algebra.TensorProduct.leftAlgebra
  exact {
    (Algebra.TensorProduct.comm k S K) with
    commutes' := by
      intro r
      change Algebra.TensorProduct.comm k S K (1 ⊗ₜ r) = r ⊗ₜ 1
      simp
  }

lemma tensor_base_change_iso_h1
    {k K R S : Type*} [Field k] [Field K] [CommRing R] [CommRing S]
    [Algebra k K] [Algebra k R] [Algebra k S] :
    letI : Algebra K (R ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra K (S ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    Nonempty ((R ⊗[k] K) ⊗[K] (S ⊗[k] K) ≃+* R ⊗[k] (S ⊗[k] K)) := by
  letI : Algebra K (R ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra K (S ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  have e1 : ((R ⊗[k] K) ⊗[K] (S ⊗[k] K)) ≃ₐ[K] ((R ⊗[k] K) ⊗[K] (K ⊗[k] S)) :=
    Algebra.TensorProduct.congr AlgEquiv.refl (comm_K_alg (k:=k) (K:=K) (S:=S))
  have e2 : ((R ⊗[k] K) ⊗[K] (K ⊗[k] S)) ≃ₐ[K] ((R ⊗[k] K) ⊗[k] S) :=
    Algebra.TensorProduct.cancelBaseChange k K K (R ⊗[k] K) S
  have e3 : ((R ⊗[k] K) ⊗[k] S) ≃ₐ[k] (R ⊗[k] (K ⊗[k] S)) :=
    Algebra.TensorProduct.assoc k k R K S
  have e4 : (R ⊗[k] (K ⊗[k] S)) ≃ₐ[k] (R ⊗[k] (S ⊗[k] K)) :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.TensorProduct.comm k K S)
  let F1 := e1.toRingEquiv
  let F2 := e2.toRingEquiv
  let F3 := e3.toRingEquiv
  let F4 := e4.toRingEquiv
  exact ⟨F1.trans (F2.trans (F3.trans F4))⟩

lemma tensor_base_change_iso
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {R S : Type*} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] :
    letI : Algebra K (R ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra K (S ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra K ((R ⊗[k] S) ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    Nonempty ((R ⊗[k] K) ⊗[K] (S ⊗[k] K) ≃+* ((R ⊗[k] S) ⊗[k] K)) := by
  letI : Algebra K (R ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra K (S ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra K ((R ⊗[k] S) ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  have h1 : Nonempty ((R ⊗[k] K) ⊗[K] (S ⊗[k] K) ≃+* R ⊗[k] (S ⊗[k] K)) := tensor_base_change_iso_h1
  have h2 : Nonempty ((R ⊗[k] (S ⊗[k] K)) ≃+* ((R ⊗[k] S) ⊗[k] K)) :=
    ⟨(Algebra.TensorProduct.assoc k k R S K).symm.toRingEquiv⟩
  exact ⟨h1.some.trans h2.some⟩



lemma irreducibleSpace_equiv {A B : Type*} [CommSemiring A] [CommSemiring B] (e : A ≃+* B) :
    IrreducibleSpace (PrimeSpectrum A) ↔ IrreducibleSpace (PrimeSpectrum B) := by
  let:=e.toRingHom.toAlgebra
  simp_rw [irreducibleSpace_def,IsIrreducible,isPreirreducible_iff_isClosed_union_isClosed]
  push_cast[ PrimeSpectrum.isClosed_iff_zeroLocus,Set.nonempty_def,Set.subset_def,Set.mem_union]
  use .imp (.rec ?_) ? _,.imp (.rec ?_) ?_
  · use fun and K V ⟨a, C⟩⟨A, B⟩=>C▸B▸.imp ( fun and R L=>?_) ( fun and R L=>? _) ∘and _ _ ⟨a.preimage e, rfl⟩ ⟨ A.preimage e, rfl⟩ ∘ fun and R L=>?_
    · exact (e.surjective).forall.mpr (and ⟨_, R.isPrime.comap _,⟩ (L ) )
    · exact (e.surjective).forall.2 (@and ⟨_, R.2.comap _,⟩ L )
    · use (and ⟨ _,R.2.comap e.symm.toRingHom⟩ L).imp ( fun and A B=>e.symm_apply_apply A▸ and B) fun and A B=>e.symm_apply_apply A▸ and B
  · (aesop)
    exact ⟨⟨ _,w.2.comap e.symm.toRingHom⟩⟩
  · use fun and K V ⟨a, _⟩⟨x, _⟩=>?_ ∘and _ _ ⟨a.image e, rfl⟩ ⟨x.image e, rfl⟩ ∘?_
    · use‹K = _›▸by valid▸.imp ( fun and A B R L=>by_contra (absurd (and ⟨_, A.2.comap e.symm.toRingHom⟩ B (by use R)) ∘by norm_num)) fun and A B R L=>?_
      exact (e.symm_apply_apply R).subst (and ⟨_, A.2.comap _,⟩ B (by exists R))
    · use‹K = _›▸by valid▸ fun and R L=> (and ⟨_, R.2.comap _,⟩ L).imp (a.image_subset_iff.2) (x.image_subset_iff.2)
  · norm_num
    use fun and=>⟨ _,and.2.comap<|algebraMap A B⟩




-- EVOLVE-BLOCK-END

theorem unique_minimal_prime_of_tensor_product_of_separably_closed
    {k : Type*} [Field k] [IsSepClosed k]
    {R S : Type*} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [IrreducibleSpace (PrimeSpectrum R)]
    [IrreducibleSpace (PrimeSpectrum S)] :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) := by
  -- EVOLVE-BLOCK-START
  let K := AlgebraicClosure k
  have hpure : IsPurelyInseparable k K := algebraic_closure_is_purely_inseparable
  have h1 : IrreducibleSpace (PrimeSpectrum (R ⊗[k] K)) := by
    rw [← purely_inseparable_extension_spectrum_homeo K]
    exact inferInstance
  have h2 : IrreducibleSpace (PrimeSpectrum (S ⊗[k] K)) := by
    rw [← purely_inseparable_extension_spectrum_homeo K]
    exact inferInstance
  letI : Algebra K (R ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra K (S ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  have h3 : IrreducibleSpace (PrimeSpectrum ((R ⊗[k] K) ⊗[K] (S ⊗[k] K))) := by
    haveI := h1
    haveI := h2
    exact tensor_product_over_alg_closed
  have h4 : IrreducibleSpace (PrimeSpectrum ((R ⊗[k] S) ⊗[k] K)) := by
    have iso := tensor_base_change_iso (k := k) (K := K) (R := R) (S := S)
    obtain ⟨e⟩ := iso
    exact (irreducibleSpace_equiv e).mp h3
  exact (purely_inseparable_extension_spectrum_homeo K (R := R ⊗[k] S)).mpr h4
  -- EVOLVE-BLOCK-END
