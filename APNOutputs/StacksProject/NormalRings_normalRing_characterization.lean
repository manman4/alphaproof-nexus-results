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


universe u


class NormalDomain (R : Type*) [CommRing R] : Prop extends IsDomain R, IsIntegrallyClosed R

class NormalRing (R : Type*) [CommRing R] : Prop where
  localization_atPrime_normalDomain (p : Ideal R) [p.IsPrime] :
    NormalDomain (Localization.AtPrime p)


open Polynomial

-- EVOLVE-BLOCK-START

lemma imp13_comaximal.{v} {R : Type v} [CommRing R] [IsReduced R]
    (h : NormalRing R) (p q : Ideal R) (hp : p ∈ (⊥ : Ideal R).minimalPrimes)
    (hq : q ∈ (⊥ : Ideal R).minimalPrimes) (hne : p ≠ q) : p + q = ⊤ := by
  by_contra h_not_top
  obtain ⟨m, hm_max, hm_le⟩ := Ideal.exists_le_maximal (p + q) h_not_top
  haveI hm_prime : m.IsPrime := hm_max.isPrime
  have hp_le_m : p ≤ m := le_trans le_sup_left hm_le
  have hq_le_m : q ≤ m := le_trans le_sup_right hm_le
  let Rm := Localization.AtPrime m
  have h_norm : NormalDomain Rm := h.localization_atPrime_normalDomain m
  haveI h_dom : IsDomain Rm := h_norm.toIsDomain
  have h_min_Rm : minimalPrimes Rm = {⊥} := IsDomain.minimalPrimes_eq_singleton_bot Rm
  let iso := IsLocalization.orderIsoOfPrime m.primeCompl Rm
  have hp_prime : p.IsPrime := hp.1.1
  have hq_prime : q.IsPrime := hq.1.1
  have hp_disj : Disjoint (m.primeCompl : Set R) (p : Set R) := by
    rw [Set.disjoint_iff]
    intro x hx
    have h1 : x ∉ m := hx.1
    have h2 : x ∈ m := hp_le_m hx.2
    exact h1 h2
  have hq_disj : Disjoint (m.primeCompl : Set R) (q : Set R) := by
    rw [Set.disjoint_iff]
    intro x hx
    have h1 : x ∉ m := hx.1
    have h2 : x ∈ m := hq_le_m hx.2
    exact h1 h2
  let p_R : { P : Ideal R // P.IsPrime ∧ Disjoint (m.primeCompl : Set R) (P : Set R) } := ⟨p, hp_prime, hp_disj⟩
  let q_R : { P : Ideal R // P.IsPrime ∧ Disjoint (m.primeCompl : Set R) (P : Set R) } := ⟨q, hq_prime, hq_disj⟩
  let p_Rm := iso.symm p_R
  let q_Rm := iso.symm q_R
  have hp_min : p_Rm.1 ∈ minimalPrimes Rm := by
    constructor
    · exact ⟨p_Rm.2, bot_le⟩
    · intro J hJ hJ_le
      let J_Rm : { P : Ideal Rm // P.IsPrime } := ⟨J, hJ.1⟩
      have h1 : J_Rm ≤ p_Rm := hJ_le
      have h2 : iso J_Rm ≤ iso p_Rm := OrderIso.monotone iso h1
      have h3 : (iso J_Rm).1 ≤ (iso p_Rm).1 := h2
      have h4 : iso p_Rm = p_R := OrderIso.apply_symm_apply iso p_R
      have h4_1 : (iso p_Rm).1 = p := congr_arg Subtype.val h4
      have h5 : (iso J_Rm).1 ≤ p := h4_1 ▸ h3
      have h6 : p ≤ (iso J_Rm).1 := hp.2 ⟨(iso J_Rm).2.1, bot_le⟩ h5
      have h7_le : p_R ≤ iso J_Rm := h6
      have h7 : iso p_Rm ≤ iso J_Rm := h4.symm ▸ h7_le
      have h8 : p_Rm ≤ J_Rm := (OrderIso.le_iff_le iso).mp h7
      exact h8
  have hq_min : q_Rm.1 ∈ minimalPrimes Rm := by
    constructor
    · exact ⟨q_Rm.2, bot_le⟩
    · intro J hJ hJ_le
      let J_Rm : { P : Ideal Rm // P.IsPrime } := ⟨J, hJ.1⟩
      have h1 : J_Rm ≤ q_Rm := hJ_le
      have h2 : iso J_Rm ≤ iso q_Rm := OrderIso.monotone iso h1
      have h3 : (iso J_Rm).1 ≤ (iso q_Rm).1 := h2
      have h4 : iso q_Rm = q_R := OrderIso.apply_symm_apply iso q_R
      have h4_1 : (iso q_Rm).1 = q := congr_arg Subtype.val h4
      have h5 : (iso J_Rm).1 ≤ q := h4_1 ▸ h3
      have h6 : q ≤ (iso J_Rm).1 := hq.2 ⟨(iso J_Rm).2.1, bot_le⟩ h5
      have h7_le : q_R ≤ iso J_Rm := h6
      have h7 : iso q_Rm ≤ iso J_Rm := h4.symm ▸ h7_le
      have h8 : q_Rm ≤ J_Rm := (OrderIso.le_iff_le iso).mp h7
      exact h8
  have hp_bot : p_Rm.1 = ⊥ := by
    have h1 : p_Rm.1 ∈ {⊥} := h_min_Rm ▸ hp_min
    exact Set.mem_singleton_iff.mp h1
  have hq_bot : q_Rm.1 = ⊥ := by
    have h1 : q_Rm.1 ∈ {⊥} := h_min_Rm ▸ hq_min
    exact Set.mem_singleton_iff.mp h1
  have heq : p_Rm.1 = q_Rm.1 := hp_bot.trans hq_bot.symm
  have heq2 : p_Rm = q_Rm := Subtype.ext heq
  have heq3 : p_R = q_R := EquivLike.injective iso.symm heq2
  have heq4 : p = q := Subtype.ext_iff.mp heq3
  exact hne heq4

lemma imp13_iso.{v} {R : Type v} [CommRing R] [IsReduced R]
    (h_min_primes : (⊥ : Ideal R).minimalPrimes.Finite)
    (h : NormalRing R) :
    Nonempty (R ≃+* ∀ i : { p : Ideal R // p ∈ (⊥ : Ideal R).minimalPrimes }, R ⧸ i.val) := by
  let S := { p : Ideal R // p ∈ (⊥ : Ideal R).minimalPrimes }
  have hS : Finite S := h_min_primes
  haveI : Fintype S := Fintype.ofFinite S
  have h_coprime : Pairwise (fun i j : S => IsCoprime i.val j.val) := by
    intro i j hij
    have h_ne : i.val ≠ j.val := by
      intro h_eq
      exact hij (Subtype.ext h_eq)
    have h_top : i.val + j.val = ⊤ := imp13_comaximal h i.val j.val i.prop j.prop h_ne
    exact Ideal.isCoprime_iff_sup_eq.mpr h_top
  have h_inf : ⨅ i : S, i.val = ⊥ := by
    have h1 : ⨅ i : S, i.val = sInf (⊥ : Ideal R).minimalPrimes := (sInf_eq_iInf' _).symm
    have h2 : sInf (⊥ : Ideal R).minimalPrimes = (⊥ : Ideal R).radical := Ideal.sInf_minimalPrimes
    have h3 : (⊥ : Ideal R).radical = nilradical R := rfl
    have h4 : nilradical R = ⊥ := nilradical_eq_bot_iff.mpr inferInstance
    rw [h1, h2, h3, h4]
  have e1 : R ≃+* R ⧸ (⊥ : Ideal R) := (RingEquiv.quotientBot R).symm
  have e2 : R ⧸ (⊥ : Ideal R) ≃+* R ⧸ ⨅ i : S, i.val := Ideal.quotEquivOfEq h_inf.symm
  have e3 : R ⧸ ⨅ i : S, i.val ≃+* ∀ i : S, R ⧸ i.val := Ideal.quotientInfRingEquivPiQuotient _ h_coprime
  exact ⟨e1.trans (e2.trans e3)⟩

lemma isIntegrallyClosed_of_localization.{v} {R : Type v} [CommRing R] [IsDomain R]
    (h : ∀ (m : Ideal R) [m.IsMaximal], IsIntegrallyClosed (Localization.AtPrime m)) :
    IsIntegrallyClosed R := by
  refine .of_localization_maximal fun and j=>?_
  apply h

lemma NormalDomain_of_NormalRing_and_IsDomain.{v} {A : Type v} [CommRing A] [IsDomain A] (h : NormalRing A) : NormalDomain A := by
  have h2 : ∀ (m : Ideal A) [m.IsMaximal], IsIntegrallyClosed (Localization.AtPrime m) := by
    intro m hm
    haveI h_nd : NormalDomain (Localization.AtPrime m) := h.localization_atPrime_normalDomain m
    exact inferInstance
  haveI h3 : IsIntegrallyClosed A := isIntegrallyClosed_of_localization h2
  exact { }

lemma isDomain_of_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) [IsDomain S] : IsDomain R := by
  rwa [e.isDomain_iff]

lemma isIntegrallyClosed_of_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) [IsIntegrallyClosed S] : IsIntegrallyClosed R := by
  have:=Classical.decEq R
  refine IsIntegrallyClosed.of_equiv e.symm

lemma normalDomain_of_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) [hS : NormalDomain S] : NormalDomain R := by
  haveI : IsDomain R := isDomain_of_equiv e
  haveI : IsIntegrallyClosed R := isIntegrallyClosed_of_equiv e
  constructor

lemma normalDomain_of_equiv_nonempty {R S : Type*} [CommRing R] [CommRing S]
    (e : Nonempty (R ≃+* S)) [hS : NormalDomain S] : NormalDomain R := by
  rcases e with ⟨e_eq⟩
  exact @normalDomain_of_equiv _ _ _ _ e_eq hS

lemma localRingEquiv_cond {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (p : Ideal R) [p.IsPrime] :
    Submonoid.map (e : R →* S) p.primeCompl = (p.map e : Ideal S).primeCompl := by
  norm_num[p.mem_map_iff_of_surjective,Submonoid.ext_iff,Ideal.primeCompl,←e.eq_symm_apply]

lemma Localization.localRingEquiv_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (p : Ideal R) [p.IsPrime] :
    Nonempty (Localization.AtPrime p ≃+* Localization.AtPrime (p.map e : Ideal S)) :=
  ⟨IsLocalization.ringEquivOfRingEquiv (M := p.primeCompl) (T := (p.map e : Ideal S).primeCompl)
    (Localization.AtPrime p) (Localization.AtPrime (p.map e : Ideal S)) e (localRingEquiv_cond e p)⟩

lemma NormalRing_of_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (h : NormalRing S) : NormalRing R := by
  constructor
  intro p hp
  have h_prime_map : (p.map e : Ideal S).IsPrime := Ideal.map_isPrime_of_equiv e
  have h1 : NormalDomain (Localization.AtPrime (p.map e : Ideal S)) :=
    @NormalRing.localization_atPrime_normalDomain S _ h _ h_prime_map
  have e_loc : Nonempty (Localization.AtPrime p ≃+* Localization.AtPrime (p.map e : Ideal S)) :=
    Localization.localRingEquiv_of_ringEquiv e p
  exact @normalDomain_of_equiv_nonempty _ _ _ _ e_loc h1

lemma prime_prod_equiv {ι : Type*} [Fintype ι] [DecidableEq ι] (R_i : ι → Type _)
    [∀ i, CommRing (R_i i)] (j : ι) (p : Ideal (R_i j)) [p.IsPrime] :
    Nonempty (Localization.AtPrime (p.comap (Pi.evalRingHom R_i j)) ≃+* Localization.AtPrime p) := by
  let P := p.comap (Pi.evalRingHom R_i j)
  let S := Localization.AtPrime p
  letI : Algebra (∀ i, R_i i) S := RingHom.toAlgebra ((algebraMap (R_i j) S).comp (Pi.evalRingHom R_i j))
  haveI : IsLocalization P.primeCompl S := {
    map_units := fun ⟨x, hx⟩ => by
      have h1 : x j ∈ p.primeCompl := hx
      change IsUnit ((algebraMap (R_i j) S) (x j))
      exact IsLocalization.map_units S (⟨x j, h1⟩ : p.primeCompl)
    surj := fun z => by
      obtain ⟨⟨a, s⟩, heq⟩ := IsLocalization.surj p.primeCompl z
      let a' : ∀ i, R_i i := fun i => if h : j = i then h ▸ a else 0
      let s' : ∀ i, R_i i := fun i => if h : j = i then h ▸ s.1 else 1
      have hs' : s' ∈ P.primeCompl := by
        have hj : s' j = s.1 := dif_pos rfl
        change s' j ∉ p
        rw [hj]
        exact s.2
      use ⟨a', ⟨s', hs'⟩⟩
      change z * algebraMap (R_i j) S (s' j) = algebraMap (R_i j) S (a' j)
      have hj_a : a' j = a := dif_pos rfl
      have hj_s : s' j = s.1 := dif_pos rfl
      rw [hj_a, hj_s]
      exact heq
    exists_of_eq := fun {x y} hxy => by
      change algebraMap (R_i j) S (x j) = algebraMap (R_i j) S (y j) at hxy
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists p.primeCompl S).mp hxy
      let c' : ∀ i, R_i i := fun i => if h : j = i then h ▸ c.1 else 0
      have hc' : c' ∈ P.primeCompl := by
        have hj : c' j = c.1 := dif_pos rfl
        change c' j ∉ p
        rw [hj]
        exact c.2
      use ⟨c', hc'⟩
      ext i
      by_cases h : j = i
      · subst h
        have hj_x : (c' * x) j = c.1 * x j := by
          have hj : c' j = c.1 := dif_pos rfl
          change c' j * x j = c.1 * x j
          rw [hj]
        have hj_y : (c' * y) j = c.1 * y j := by
          have hj : c' j = c.1 := dif_pos rfl
          change c' j * y j = c.1 * y j
          rw [hj]
        rw [hj_x, hj_y]
        exact hc
      · have hc'_i : c' i = 0 := dif_neg h
        have hx_i : (c' * x) i = 0 := by
          change c' i * x i = 0
          rw [hc'_i, zero_mul]
        have hy_i : (c' * y) i = 0 := by
          change c' i * y i = 0
          rw [hc'_i, zero_mul]
        rw [hx_i, hy_i]
  }
  exact ⟨IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) S |>.toRingEquiv⟩

lemma normalRing_factor {ι : Type*} [Fintype ι] [DecidableEq ι] (R_i : ι → Type _)
    [∀ i, CommRing (R_i i)] (h : NormalRing (∀ i, R_i i)) (j : ι) : NormalRing (R_i j) := by
  constructor
  intro p hp
  let M := p.comap (Pi.evalRingHom R_i j)
  haveI hM : M.IsPrime := Ideal.comap_isPrime _ p
  have h_nd : NormalDomain (Localization.AtPrime M) := @NormalRing.localization_atPrime_normalDomain _ _ h M hM
  have e : Nonempty (Localization.AtPrime p ≃+* Localization.AtPrime M) := by
    have h_symm := prime_prod_equiv R_i j p
    rcases h_symm with ⟨e_symm⟩
    exact ⟨e_symm.symm⟩
  exact @normalDomain_of_equiv_nonempty _ _ _ _ e h_nd

lemma imp13.{v} {R : Type v} [CommRing R] [IsReduced R]
    (h_min_primes : (⊥ : Ideal R).minimalPrimes.Finite)
    (h : NormalRing R) :
    ∃ (ι : Type) (_ : Finite ι) (R_i : ι → Type v)
        (_ : ∀ i, CommRing (R_i i)) (_ : ∀ i, NormalDomain (R_i i)),
        Nonempty (R ≃+* ∀ i, R_i i) := by
  let S := { p : Ideal R // p ∈ (⊥ : Ideal R).minimalPrimes }
  have hS : Finite S := h_min_primes
  haveI : Fintype S := Fintype.ofFinite S
  haveI : DecidableEq S := Classical.decEq S
  obtain ⟨n, ⟨e_fin⟩⟩ := Finite.exists_equiv_fin S
  have e1_ne := imp13_iso h_min_primes h
  obtain ⟨e1⟩ := e1_ne
  let e2 := RingEquiv.piCongrLeft' (fun (p : S) => R ⧸ p.val) e_fin
  have e_total : R ≃+* ∀ j : Fin n, R ⧸ (e_fin.symm j).val := e1.trans e2
  have h_norm : ∀ j : Fin n, NormalDomain (R ⧸ (e_fin.symm j).val) := by
    intro j
    let i := e_fin.symm j
    have hp : i.val.IsPrime := i.property.1.1
    have h_ri : NormalRing (R ⧸ i.val) := normalRing_factor (fun k => R ⧸ k.val) (@NormalRing_of_equiv _ _ _ _ e1.symm h) i
    haveI : IsDomain (R ⧸ i.val) := Ideal.Quotient.isDomain i.val
    exact NormalDomain_of_NormalRing_and_IsDomain h_ri
  exact ⟨Fin n, inferInstance, fun j => R ⧸ (e_fin.symm j).val, fun j => inferInstance, h_norm, ⟨e_total⟩⟩

lemma local_idempotent.{v} {A : Type v} [CommRing A] [IsLocalRing A] (w : A) (hw : w * w = w) : w = 0 ∨ w = 1 := by
  have h_mul : w * (1 - w) = 0 := by
    calc w * (1 - w) = w * 1 - w * w := mul_sub w 1 w
         _ = w - w := by rw [mul_one, hw]
         _ = 0 := sub_self w
  have h_add : w + (1 - w) = 1 := by ring
  have h_unit : IsUnit (w + (1 - w)) := by
    rw [h_add]
    exact isUnit_one
  cases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h_unit with
  | inl h_u =>
    right
    have h1 : 1 - w = 0 := (IsUnit.mul_right_eq_zero h_u).mp h_mul
    exact eq_of_sub_eq_zero (by rw [h1]) |>.symm
  | inr h_u =>
    left
    have h_mul2 : (1 - w) * w = 0 := by rw [mul_comm, h_mul]
    exact (IsUnit.mul_right_eq_zero h_u).mp h_mul2

lemma idempotent_of_zero_divisor.{v} {A : Type v} [CommRing A] [IsReduced A] [IsLocalRing A]
    (h_int : IsIntegrallyClosed A) (x y : A) (hxy : x * y = 0) (hx_add_y : x + y ∈ nonZeroDivisors A) :
    x = 0 ∨ y = 0 := by
  let K := FractionRing A
  let f := algebraMap A K
  let sum_K := f (x + y)
  have h_sum_unit : IsUnit sum_K := IsLocalization.map_units K (⟨x + y, hx_add_y⟩ : nonZeroDivisors A)
  let z := f x * h_sum_unit.unit⁻¹
  have hz_idemp : z * z = z := by
    have eq1 : f x * f x = f x * sum_K := by
      calc f x * f x = f (x * x) := by rw [←map_mul]
           _ = f (x * x + x * y) := by rw [hxy, add_zero]
           _ = f (x * (x + y)) := by rw [←mul_add]
           _ = f x * sum_K := by rw [map_mul]
    have eq2 : (f x * h_sum_unit.unit⁻¹) * (f x * h_sum_unit.unit⁻¹) = f x * h_sum_unit.unit⁻¹ := by
      calc (f x * h_sum_unit.unit⁻¹) * (f x * h_sum_unit.unit⁻¹)
        = (f x * f x) * (h_sum_unit.unit⁻¹ * h_sum_unit.unit⁻¹) := by ring
        _ = (f x * sum_K) * (h_sum_unit.unit⁻¹ * h_sum_unit.unit⁻¹) := by rw [eq1]
        _ = f x * (sum_K * h_sum_unit.unit⁻¹) * h_sum_unit.unit⁻¹ := by ring
        _ = f x * (h_sum_unit.unit * h_sum_unit.unit⁻¹) * h_sum_unit.unit⁻¹ := rfl
        _ = f x * 1 * h_sum_unit.unit⁻¹ := by rw [h_sum_unit.unit.mul_inv]
        _ = f x * h_sum_unit.unit⁻¹ := by rw [mul_one]
    exact eq2
  have hz_int : IsIntegral A z := by
    use Polynomial.X ^ 2 - Polynomial.X
    constructor
    · exact (monic_X_pow_sub (by(((norm_num)))))
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
      exact sub_eq_zero.mpr (by rw [sq, hz_idemp])
  have hz_in := (isIntegrallyClosed_iff K).mp h_int hz_int
  rcases hz_in with ⟨w, hw⟩
  have hw_idemp_K : f (w * w) = f w := by
    rw [map_mul, hw, hz_idemp]
  have hw_idemp : w * w = w := IsFractionRing.injective A K hw_idemp_K
  rcases local_idempotent w hw_idemp with hw0 | hw1
  · left
    have eq_z_sum : z * sum_K = f x := by
      calc z * sum_K = f x * h_sum_unit.unit⁻¹ * sum_K := rfl
           _ = f x * (h_sum_unit.unit⁻¹ * sum_K) := mul_assoc _ _ _
           _ = f x * (h_sum_unit.unit⁻¹ * h_sum_unit.unit) := rfl
           _ = f x * 1 := by rw [h_sum_unit.unit.inv_mul]
           _ = f x := mul_one (f x)
    have hx0 : f x = f 0 := by
      calc f x = z * sum_K := eq_z_sum.symm
           _ = f w * sum_K := by rw [←hw]
           _ = f 0 * sum_K := by rw [hw0]
           _ = 0 * sum_K := by rw [map_zero]
           _ = 0 := zero_mul _
           _ = f 0 := (map_zero f).symm
    exact IsFractionRing.injective A K hx0
  · right
    have eq_z_sum : z * sum_K = f x := by
      calc z * sum_K = f x * h_sum_unit.unit⁻¹ * sum_K := rfl
           _ = f x * (h_sum_unit.unit⁻¹ * sum_K) := mul_assoc _ _ _
           _ = f x * (h_sum_unit.unit⁻¹ * h_sum_unit.unit) := rfl
           _ = f x * 1 := by rw [h_sum_unit.unit.inv_mul]
           _ = f x := mul_one (f x)
    have eq_z : z = 1 := by rw [←hw, hw1, map_one]
    have eq_x : f x = sum_K := by
      calc f x = z * sum_K := eq_z_sum.symm
           _ = 1 * sum_K := by rw [eq_z]
           _ = sum_K := one_mul _
    have eq2 : f y = sum_K - f x := by
      calc f y = f y + f x - f x := (add_sub_cancel_right (f y) (f x)).symm
           _ = f x + f y - f x := by rw [add_comm (f x) (f y)]
           _ = f (x + y) - f x := by rw [←map_add]
    have hy0 : f y = f 0 := by
      calc f y = sum_K - f x := eq2
           _ = sum_K - sum_K := by rw [eq_x]
           _ = 0 := sub_self _
           _ = f 0 := (map_zero f).symm
    exact IsFractionRing.injective A K hy0

lemma exists_x_y_of_min_primes_aux2.{v} {R : Type v} [CommRing R] [IsReduced R]
    (S_fin : Finset (Ideal R)) (p : Ideal R)
    (h_prime_all : ∀ q ∈ S_fin, Ideal.IsPrime q)
    (h_not_le : ∀ q ∈ S_fin, ¬ (p ≤ q)) :
    ∃ x ∈ p, ∀ q ∈ S_fin, x ∉ q := by
  have h_not_subset : ¬ ((p : Set R) ⊆ ⋃ q ∈ (S_fin : Set (Ideal R)), (q : Set R)) := by
    intro h_sub
    have h_le_q : ∃ q ∈ S_fin, p ≤ q := (Ideal.subset_union_prime p p (fun q hq _ _ => h_prime_all q hq)).mp h_sub
    rcases h_le_q with ⟨q, hq_S, hq_le⟩
    exact h_not_le q hq_S hq_le
  have h_exists : ∃ x ∈ p, x ∉ ⋃ q ∈ (S_fin : Set (Ideal R)), (q : Set R) := Set.not_subset.mp h_not_subset
  rcases h_exists with ⟨x, hxp, hx_not⟩
  use x
  constructor
  · exact hxp
  · intro q hq hxq
    have h_in_union : x ∈ ⋃ q ∈ (S_fin : Set (Ideal R)), (q : Set R) := Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, hxq⟩⟩
    exact hx_not h_in_union

lemma not_prod_le_of_not_le.{v} {R : Type v} [CommRing R] [DecidableEq (Ideal R)] (S_fin : Finset (Ideal R)) (p : Ideal R) [hp : p.IsPrime]
    (h_not_le : ∀ m ∈ S_fin, ¬ (m ≤ p)) : ¬ ((∏ m ∈ S_fin, m) ≤ p) := by
  intro h_le
  have h_exists : ∃ m ∈ S_fin, m ≤ p := by convert hp.prod_le.mp h_le
  rcases h_exists with ⟨m, hm, hm_le⟩
  exact h_not_le m hm hm_le

lemma prod_le_of_mem.{v} {R : Type v} [CommRing R] [DecidableEq (Ideal R)] (S_fin : Finset (Ideal R)) (m : Ideal R) (hm : m ∈ S_fin) :
    (∏ k ∈ S_fin, k) ≤ m := by
  have h_prod : (∏ k ∈ S_fin, k) = m * ∏ k ∈ S_fin.erase m, k := (Finset.mul_prod_erase S_fin (fun x => x) hm).symm
  rw [h_prod]
  exact Ideal.mul_le_right

lemma exists_x_y_of_min_primes.{v} {R : Type v} [CommRing R] [IsReduced R]
    (h_min : (⊥ : Ideal R).minimalPrimes.Finite)
    (p q : Ideal R) (hp : p ∈ (⊥ : Ideal R).minimalPrimes)
    (hq : q ∈ (⊥ : Ideal R).minimalPrimes) (hne : p ≠ q) :
    ∃ x y : R, x * y = 0 ∧ x + y ∈ nonZeroDivisors R ∧ x ∈ p ∧ x ∉ q ∧ y ∈ q ∧ y ∉ p := by
  haveI : DecidableEq (Ideal R) := Classical.decEq _
  let S_fin := h_min.toFinset.filter (fun m => m ≠ p)
  haveI hp_prime : p.IsPrime := hp.1.1
  have h_prime_all : ∀ m ∈ S_fin, Ideal.IsPrime m := by
    intro m hm
    exact (h_min.mem_toFinset.mp (Finset.mem_filter.mp hm).1).1.1
  have h_not_le : ∀ m ∈ S_fin, ¬ (p ≤ m) := by
    intro m hm h_le
    have h1 := Finset.mem_filter.mp hm
    have hm_min : m ∈ (⊥ : Ideal R).minimalPrimes := h_min.mem_toFinset.mp h1.1
    have hm_le_p : m ≤ p := hm_min.2 hp.1 h_le
    have eq_m : p = m := le_antisymm h_le hm_le_p
    exact h1.2 eq_m.symm
  obtain ⟨x, hxp, hx_not⟩ := exists_x_y_of_min_primes_aux2 S_fin p h_prime_all h_not_le
  have h_q_in : q ∈ S_fin := Finset.mem_filter.mpr ⟨h_min.mem_toFinset.mpr hq, hne.symm⟩
  have hxq : x ∉ q := hx_not q h_q_in
  have h_not_le_p : ∀ m ∈ S_fin, ¬ (m ≤ p) := by
    intro m hm h_le
    have h1 := Finset.mem_filter.mp hm
    have hm_min : m ∈ (⊥ : Ideal R).minimalPrimes := h_min.mem_toFinset.mp h1.1
    have hm_le_p : p ≤ m := hp.2 hm_min.1 h_le
    have eq_m : m = p := le_antisymm h_le hm_le_p
    exact h1.2 eq_m
  have h_not_le_prod : ¬ ((∏ m ∈ S_fin, m) ≤ p) := not_prod_le_of_not_le S_fin p h_not_le_p
  obtain ⟨y, hy_in, hyp⟩ := Set.not_subset.mp h_not_le_prod
  have hyq : y ∈ q := by
    have h_le : (∏ m ∈ S_fin, m) ≤ q := prod_le_of_mem S_fin q h_q_in
    exact h_le hy_in
  have hxy : x * y = 0 := by
    have h_in_all : ∀ m : Ideal R, m ∈ (⊥ : Ideal R).minimalPrimes → x * y ∈ m := by
      intro m hm
      by_cases hmp : m = p
      · rw [hmp]
        exact Ideal.mul_mem_right y p hxp
      · have hm_in : m ∈ S_fin := Finset.mem_filter.mpr ⟨h_min.mem_toFinset.mpr hm, hmp⟩
        have h_le : (∏ k ∈ S_fin, k) ≤ m := prod_le_of_mem S_fin m hm_in
        have hy_m : y ∈ m := h_le hy_in
        exact Ideal.mul_mem_left m x hy_m
    have h_inf : x * y ∈ sInf (⊥ : Ideal R).minimalPrimes := by
      rw [Ideal.mem_sInf]
      intro m hm
      exact h_in_all m hm
    have h_rad : sInf (⊥ : Ideal R).minimalPrimes = (⊥ : Ideal R).radical := Ideal.sInf_minimalPrimes
    have h_nil : (⊥ : Ideal R).radical = ⊥ := nilradical_eq_bot_iff.mpr inferInstance
    rw [h_rad, h_nil] at h_inf
    exact Ideal.mem_bot.mp h_inf
  have hxy_reg : x + y ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff]
    have h_c_eq_zero : ∀ c, (x + y) * c = 0 → c = 0 := by
      intro c hc_mul
      have h_in_all : ∀ m : Ideal R, m ∈ (⊥ : Ideal R).minimalPrimes → c ∈ m := by
        intro m hm
        have h_prime : m.IsPrime := hm.1.1
        have h_mul_m : c * (x + y) ∈ m := by
          rw [mul_comm]
          rw [hc_mul]
          exact Ideal.zero_mem m
        have h_or := h_prime.mem_or_mem h_mul_m
        cases h_or with
        | inl hc => exact hc
        | inr hxy_m =>
          exfalso
          by_cases hmp : m = p
          · rw [hmp] at hxy_m
            have h_y_m : y ∈ p := by
              have eq_y : y = (x + y) - x := by ring
              rw [eq_y]
              exact Ideal.sub_mem p hxy_m hxp
            exact hyp h_y_m
          · have hm_in : m ∈ S_fin := Finset.mem_filter.mpr ⟨h_min.mem_toFinset.mpr hm, hmp⟩
            have h_le : (∏ k ∈ S_fin, k) ≤ m := prod_le_of_mem S_fin m hm_in
            have h_y_m : y ∈ m := h_le hy_in
            have h_x_m : x ∈ m := by
              have eq_x : x = (x + y) - y := by ring
              rw [eq_x]
              exact Ideal.sub_mem m hxy_m h_y_m
            exact hx_not m hm_in h_x_m
      have h_inf : c ∈ sInf (⊥ : Ideal R).minimalPrimes := by
        rw [Ideal.mem_sInf]
        intro m hm
        exact h_in_all m hm
      have h_rad : sInf (⊥ : Ideal R).minimalPrimes = (⊥ : Ideal R).radical := Ideal.sInf_minimalPrimes
      have h_nil : (⊥ : Ideal R).radical = ⊥ := nilradical_eq_bot_iff.mpr inferInstance
      rw [h_rad, h_nil] at h_inf
      exact Ideal.mem_bot.mp h_inf
    constructor
    · exact h_c_eq_zero
    · intro c hc_mul
      exact h_c_eq_zero c (by rw [mul_comm, hc_mul])
  use x, y
  exact ⟨hxy, hxy_reg, hxp, hxq, hyq, hyp⟩

lemma imp23_comaximal.{v} {R : Type v} [CommRing R] [IsReduced R]
    (h_min_primes : (⊥ : Ideal R).minimalPrimes.Finite)
    (h_int : IsIntegrallyClosed R) (p q : Ideal R) (hp : p ∈ (⊥ : Ideal R).minimalPrimes)
    (hq : q ∈ (⊥ : Ideal R).minimalPrimes) (hne : p ≠ q) : p + q = ⊤ := by
  obtain ⟨x, y, hxy, hxy_reg, hxp, hxq, hyq, hyp⟩ := exists_x_y_of_min_primes h_min_primes p q hp hq hne
  let K := FractionRing R
  let f := algebraMap R K
  have h_sum_unit := IsLocalization.map_units K (⟨x + y, hxy_reg⟩ : nonZeroDivisors R)
  let sum_K := f (x + y)
  let z := f x * h_sum_unit.unit⁻¹
  have hz_idemp : z * z = z := by
    have eq1 : f x * f x = f x * sum_K := by
      calc f x * f x = f (x * x) := by rw [←map_mul]
           _ = f (x * x + x * y) := by rw [hxy, add_zero]
           _ = f (x * (x + y)) := by rw [←mul_add]
           _ = f x * sum_K := by rw [map_mul]
    have eq2 : z * z = z := by
      calc (f x * h_sum_unit.unit⁻¹) * (f x * h_sum_unit.unit⁻¹)
        = (f x * f x) * (h_sum_unit.unit⁻¹ * h_sum_unit.unit⁻¹) := by ring
        _ = (f x * sum_K) * (h_sum_unit.unit⁻¹ * h_sum_unit.unit⁻¹) := by rw [eq1]
        _ = f x * (sum_K * h_sum_unit.unit⁻¹) * h_sum_unit.unit⁻¹ := by ring
        _ = f x * (h_sum_unit.unit * h_sum_unit.unit⁻¹) * h_sum_unit.unit⁻¹ := rfl
        _ = f x * 1 * h_sum_unit.unit⁻¹ := by rw [h_sum_unit.unit.mul_inv]
        _ = f x * h_sum_unit.unit⁻¹ := by rw [mul_one]
    exact eq2
  have hz_int : IsIntegral R z := by
    use Polynomial.X ^ 2 - Polynomial.X
    constructor
    · use Polynomial.monic_of_degree_le (2) (by compute_degree!) (by compute_degree!)
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
      have h_sq : z ^ 2 = z := by
        calc z ^ 2 = z * z := by ring
             _ = z := hz_idemp
      exact sub_eq_zero.mpr h_sq
  obtain ⟨w, hw⟩ := (isIntegrallyClosed_iff K).mp h_int hz_int
  have hw_idemp_K : f (w * w) = f w := by
    rw [map_mul, hw, hz_idemp]
  have hw_idemp : w * w = w := IsFractionRing.injective R K hw_idemp_K
  have eq_wx_K : f (w * (x + y)) = f x := by
    rw [map_mul, hw]
    have h_sum_eq : sum_K = (h_sum_unit.unit : K) := rfl
    calc z * sum_K = f x * h_sum_unit.unit⁻¹ * sum_K := rfl
         _ = f x * h_sum_unit.unit⁻¹ * h_sum_unit.unit := by rw [h_sum_eq]
         _ = f x * (h_sum_unit.unit⁻¹ * h_sum_unit.unit) := by rw [mul_assoc]
         _ = f x * 1 := by rw [h_sum_unit.unit.inv_mul]
         _ = f x := mul_one _
  have eq_wx : w * (x + y) = x := IsFractionRing.injective R K eq_wx_K
  have eq_wy : w * y = 0 := by
    calc w * y = w * (x + y) - w * x := by ring
         _ = x - w * x := by rw [eq_wx]
         _ = (1 - w) * x := by ring
         _ = (1 - w) * (w * (x + y)) := by rw [eq_wx]
         _ = (1 - w) * w * (x + y) := by rw [←mul_assoc]
         _ = (w - w * w) * (x + y) := by ring
         _ = (w - w) * (x + y) := by rw [hw_idemp]
         _ = 0 * (x + y) := by rw [sub_self]
         _ = 0 := zero_mul _
  have eq_1_w_x : (1 - w) * x = 0 := by
    calc (1 - w) * x = x - w * x := by ring
         _ = w * (x + y) - w * x := by rw [eq_wx]
         _ = w * y := by ring
         _ = 0 := eq_wy
  have hw_in_p : w ∈ p := by
    have hp_prime : p.IsPrime := hp.1.1
    have h_wy_in_p : w * y ∈ p := by rw [eq_wy]; exact p.zero_mem
    cases hp_prime.mem_or_mem h_wy_in_p with
    | inl h => exact h
    | inr h => exact False.elim (hyp h)
  have hw_in_q : 1 - w ∈ q := by
    have hq_prime : q.IsPrime := hq.1.1
    have h_1_w_x_in_q : (1 - w) * x ∈ q := by rw [eq_1_w_x]; exact q.zero_mem
    cases hq_prime.mem_or_mem h_1_w_x_in_q with
    | inl h => exact h
    | inr h => exact False.elim (hxq h)
  have h1 : (1 : R) = w + (1 - w) := by ring
  have h1_in_pq : (1 : R) ∈ p + q := by
    rw [h1]
    exact Submodule.add_mem (p + q) (Ideal.mem_sup_left hw_in_p) (Ideal.mem_sup_right hw_in_q)
  exact eq_top_iff.mpr (fun r _ => by
    have h_r : r = r * 1 := (mul_one r).symm
    rw [h_r]
    exact Ideal.mul_mem_left (p + q) r h1_in_pq
  )

lemma imp23_iso.{v} {R : Type v} [CommRing R] [IsReduced R]
    (h_min_primes : (⊥ : Ideal R).minimalPrimes.Finite)
    (h_int : IsIntegrallyClosed R) :
    Nonempty (R ≃+* ∀ i : { p : Ideal R // p ∈ (⊥ : Ideal R).minimalPrimes }, R ⧸ i.val) := by
  let S := { p : Ideal R // p ∈ (⊥ : Ideal R).minimalPrimes }
  have hS : Finite S := h_min_primes
  haveI : Fintype S := Fintype.ofFinite S
  have h_coprime : Pairwise (fun i j : S => IsCoprime i.val j.val) := by
    intro i j hij
    have h_ne : i.val ≠ j.val := fun h_eq => hij (Subtype.ext h_eq)
    have h_top : i.val + j.val = ⊤ := imp23_comaximal h_min_primes h_int i.val j.val i.prop j.prop h_ne
    exact Ideal.isCoprime_iff_sup_eq.mpr h_top
  have h_inf : ⨅ i : S, i.val = ⊥ := by
    have h1 : ⨅ i : S, i.val = sInf (⊥ : Ideal R).minimalPrimes := (sInf_eq_iInf' _).symm
    have h2 : sInf (⊥ : Ideal R).minimalPrimes = (⊥ : Ideal R).radical := Ideal.sInf_minimalPrimes
    have h3 : (⊥ : Ideal R).radical = nilradical R := rfl
    have h4 : nilradical R = ⊥ := nilradical_eq_bot_iff.mpr inferInstance
    rw [h1, h2, h3, h4]
  have e1 : R ≃+* R ⧸ (⊥ : Ideal R) := (RingEquiv.quotientBot R).symm
  have e2 : R ⧸ (⊥ : Ideal R) ≃+* R ⧸ ⨅ i : S, i.val := Ideal.quotEquivOfEq h_inf.symm
  have e3 : R ⧸ ⨅ i : S, i.val ≃+* ∀ i : S, R ⧸ i.val := Ideal.quotientInfRingEquivPiQuotient _ h_coprime
  exact ⟨e1.trans (e2.trans e3)⟩







lemma eval2_eq_sum_range_deg {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : Polynomial R) (x : S) (n : ℕ) (hn : p.natDegree ≤ n) :
    Polynomial.eval₂ f x p = ∑ k ∈ Finset.range (n + 1), f (p.coeff k) * x ^ k := by
  exact (eval₂_eq_sum_range _ _).trans ( Finset.sum_subset (by gcongr) (by simp_all[p.coeff_eq_zero_of_natDegree_lt,Nat.succ_le]))

lemma coeff_sum_monomial {R : Type*} [CommRing R] (n : ℕ) (c : ℕ → R) (k : ℕ) (hk : k ≤ n) :
    (∑ m ∈ Finset.range (n + 1), Polynomial.monomial m (c m)).coeff k = c k := by
  classical ·norm_num [hk,coeff_monomial,k.lt_succ_iff]

lemma monic_sum_monomial {R : Type*} [CommRing R] (n : ℕ) (c : ℕ → R) (hc : c n = 1) :
    Polynomial.Monic (∑ m ∈ Finset.range (n + 1), Polynomial.monomial m (c m)) := by
  exact (monic_of_degree_le (n : ℕ) ((degree_sum_le _ _).trans ( Finset.sup_le fun and=>.trans (degree_monomial_le _ _) ∘mod_cast Finset.mem_range_succ_iff.1)) (by simp_all -contextual [coeff_monomial]))

lemma eval_sum_monomial_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (R_i : ι → Type*)
    [∀ i, CommRing (R_i i)] (K_i : ι → Type*) [∀ i, CommRing (K_i i)]
    [∀ i, Algebra (R_i i) (K_i i)] (n : ℕ) (c : ℕ → ∀ i, R_i i) (x' : ∀ i, K_i i) :
    Polynomial.eval₂ (algebraMap (∀ i, R_i i) (∀ i, K_i i)) x' (∑ k ∈ Finset.range (n + 1), Polynomial.monomial k (c k)) =
    fun i => ∑ k ∈ Finset.range (n + 1), algebraMap (R_i i) (K_i i) (c k i) * x' i ^ k := by
  exact (eval₂_finset_sum _ _ _ _).trans ((funext fun and=>.trans ( Finset.sum_apply _ _ _) (congr_arg _ (funext fun and=>.trans (by rw [eval₂_monomial]) (by constructor)))))

lemma isFractionRing_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (R_i : ι → Type*)
    [∀ i, CommRing (R_i i)] [∀ i, IsDomain (R_i i)] :
    IsFractionRing (∀ i, R_i i) (∀ i, FractionRing (R_i i)) := by
  apply Rat.add_zero (2) |>.dvd.elim
  intros
  constructor
  use(? _),? _,(? _)
  · norm_num[Pi.isUnit_iff,funext_iff,Algebra.algebraMap_eq_smul_one]
    simp_rw [mem_nonZeroDivisors_iff]
    classical use fun and A B i=> (by norm_num[i] ∘congr_arg (· B)) ( (A.1 (Function.update 0 B (1))) (funext (by if a:·=B then cases a with norm_num[i]else norm_num[a])))
  · refine fun and=>(Classical.axiomOfChoice fun and' => IsFractionRing.div_surjective (A:=R_i and') (and and')).elim fun and(a)=>?_
    choose A B using a
    by_contra!
    use this ⟨ _,A,by norm_num[nonZeroDivisors.ne_zero (B _).1, mem_nonZeroDivisors_iff,funext_iff]⟩ (funext (B ·|>.2▸div_mul_cancel₀ _ (by norm_num[nonZeroDivisors.ne_zero (B _).1])))
  · exact (⟨⟨1,one_mem _,⟩,congr_arg _<|funext fun and=>IsFractionRing.injective _ _<|congrFun · and⟩)

lemma isIntegrallyClosed_factor_aux1 {ι : Type*} [Fintype ι] [DecidableEq ι] (R_i : ι → Type*)
    [∀ i, CommRing (R_i i)] [∀ i, IsDomain (R_i i)] (j : ι)
    (x : FractionRing (R_i j)) (p : Polynomial (R_i j)) (hp_monic : p.Monic) :
    Polynomial.Monic (∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.monomial k (fun i => if h : i = j then h.symm ▸ p.coeff k else (if k = p.natDegree then 1 else 0))) := by
  use monic_of_degree_le p.natDegree ((degree_sum_le _ _).trans ( Finset.sup_le fun and=>.trans (degree_monomial_le _ _) ∘mod_cast Finset.mem_range_succ_iff.1)) (funext fun and=>? _)
  simp_all[coeff_monomial,funext_iff]
  exact ( Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _) fun and A B=>if_neg B▸rfl).trans (by aesop)

lemma isIntegrallyClosed_factor_aux2_p_eq_1 {R : Type*} [CommRing R] [IsDomain R] (p : Polynomial R) (hp_monic : p.Monic) (hp_deg : p.natDegree = 0) : p = 1 := by apply hp_monic.natDegree_eq_zero.mp hp_deg

lemma isIntegrallyClosed_factor_aux2_sum_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (R_i : ι → Type*)
    [∀ i, CommRing (R_i i)] [∀ i, IsDomain (R_i i)] (j : ι) (p : Polynomial (R_i j)) (x : FractionRing (R_i j))
    (i : ι) (h : ¬ (i = j)) (hn_pos : 0 < p.natDegree) :
    (∑ k ∈ Finset.range (p.natDegree + 1), algebraMap (R_i i) (FractionRing (R_i i)) (if h2 : i = j then h2.symm ▸ p.coeff k else (if k = p.natDegree then 1 else 0)) * (if h2 : i = j then h2.symm ▸ x else 0) ^ k) = 0 := by norm_num [hn_pos.ne', h]

lemma isIntegrallyClosed_factor_aux2 {ι : Type*} [Fintype ι] [DecidableEq ι] (R_i : ι → Type*)
    [∀ i, CommRing (R_i i)] [∀ i, IsDomain (R_i i)] (j : ι)
    (x : FractionRing (R_i j)) (p : Polynomial (R_i j))
    (hp_monic : p.Monic)
    (hp_eval : Polynomial.eval₂ (algebraMap (R_i j) (FractionRing (R_i j))) x p = 0) :
    Polynomial.eval₂ (algebraMap (∀ i, R_i i) (∀ i, FractionRing (R_i i)))
      (fun i => if h : i = j then h.symm ▸ x else 0)
      (∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.monomial k (fun i => if h : i = j then h.symm ▸ p.coeff k else (if k = p.natDegree then 1 else 0))) = 0 := by
  let n := p.natDegree
  let c : ℕ → ∀ i, R_i i := fun k i => if h : i = j then h.symm ▸ p.coeff k else (if k = n then 1 else 0)
  let x' : ∀ i, FractionRing (R_i i) := fun i => if h : i = j then h.symm ▸ x else 0
  have h_eval_eq : Polynomial.eval₂ (algebraMap (∀ i, R_i i) (∀ i, FractionRing (R_i i))) x'
      (∑ k ∈ Finset.range (n + 1), Polynomial.monomial k (c k)) =
      fun i => ∑ k ∈ Finset.range (n + 1), algebraMap (R_i i) (FractionRing (R_i i)) (c k i) * x' i ^ k :=
    eval_sum_monomial_pi R_i (fun i => FractionRing (R_i i)) n c x'
  rw [h_eval_eq]
  ext i
  by_cases h : i = j
  · subst i
    have h_sum : (∑ k ∈ Finset.range (n + 1), algebraMap (R_i j) (FractionRing (R_i j)) (c k j) * x' j ^ k) =
        ∑ k ∈ Finset.range (n + 1), algebraMap (R_i j) (FractionRing (R_i j)) (p.coeff k) * x ^ k := by
      apply Finset.sum_congr rfl
      intro k _
      have hc_j : c k j = p.coeff k := by simp [c]
      have hx_j : x' j = x := by simp [x']
      rw [hc_j, hx_j]
    rw [h_sum]
    have h_eval_p : ∑ k ∈ Finset.range (n + 1), algebraMap (R_i j) (FractionRing (R_i j)) (p.coeff k) * x ^ k =
        Polynomial.eval₂ (algebraMap (R_i j) (FractionRing (R_i j))) x p := (eval2_eq_sum_range_deg _ p x n (le_refl n)).symm
    rw [h_eval_p]
    exact hp_eval
  · have hx_i : x' i = 0 := by simp [x', h]
    have hn_pos : 0 < n := by
      by_contra hn0
      have eq_0 : n = 0 := le_antisymm (not_lt.mp hn0) (Nat.zero_le _)
      have hp_deg : p.natDegree = 0 := eq_0
      have hp_eq_1 : p = 1 := isIntegrallyClosed_factor_aux2_p_eq_1 p hp_monic hp_deg
      have h_eval_1 : Polynomial.eval₂ (algebraMap (R_i j) (FractionRing (R_i j))) x p = 1 := by
        rw [hp_eq_1]
        exact Polynomial.eval₂_one _ x
      rw [hp_eval] at h_eval_1
      exact (zero_ne_one h_eval_1).elim
    have h_sum : (∑ k ∈ Finset.range (n + 1), algebraMap (R_i i) (FractionRing (R_i i)) (c k i) * x' i ^ k) = 0 := isIntegrallyClosed_factor_aux2_sum_zero R_i j p x i h hn_pos
    rw [h_sum]
    rfl

lemma isIntegrallyClosed_factor {ι : Type*} [Fintype ι] [DecidableEq ι] (R_i : ι → Type*)
    [∀ i, CommRing (R_i i)] [∀ i, IsDomain (R_i i)]
    (h : IsIntegrallyClosed (∀ i, R_i i)) (j : ι) : IsIntegrallyClosed (R_i j) := by
  haveI : IsFractionRing (∀ i, R_i i) (∀ i, FractionRing (R_i i)) := isFractionRing_pi R_i
  have h_int : ∀ x : ∀ i, FractionRing (R_i i), IsIntegral (∀ i, R_i i) x → ∃ y, algebraMap (∀ i, R_i i) (∀ i, FractionRing (R_i i)) y = x := fun x hx => (isIntegrallyClosed_iff (∀ i, FractionRing (R_i i))).mp h hx
  rw [isIntegrallyClosed_iff (FractionRing (R_i j))]
  intro x hx
  obtain ⟨p, hp_monic, hp_eval⟩ := hx
  let n := p.natDegree
  let c : ℕ → ∀ i, R_i i := fun k i => if h : i = j then h.symm ▸ p.coeff k else (if k = n then 1 else 0)
  let P : Polynomial (∀ i, R_i i) := ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k (c k)
  let x' : ∀ i, FractionRing (R_i i) := fun i => if h : i = j then h.symm ▸ x else 0
  have hx'_int : IsIntegral (∀ i, R_i i) x' := ⟨P, isIntegrallyClosed_factor_aux1 R_i j x p hp_monic, isIntegrallyClosed_factor_aux2 R_i j x p hp_monic hp_eval⟩
  obtain ⟨y, hy⟩ := h_int x' hx'_int
  use y j
  have eq_x : algebraMap (R_i j) (FractionRing (R_i j)) (y j) = x' j := by
    have h_map : algebraMap (∀ i, R_i i) (∀ i, FractionRing (R_i i)) y j = algebraMap (R_i j) (FractionRing (R_i j)) (y j) := rfl
    rw [←h_map, hy]
  have h_xj : x' j = x := by
    change (if h : j = j then h.symm ▸ x else 0) = x
    exact dif_pos rfl
  rw [h_xj] at eq_x
  exact eq_x

lemma imp23.{v} {R : Type v} [CommRing R] [IsReduced R]
    (h_min_primes : (⊥ : Ideal R).minimalPrimes.Finite)
    (h_int : IsIntegrallyClosed R) :
    ∃ (ι : Type) (_ : Finite ι) (R_i : ι → Type v)
        (_ : ∀ i, CommRing (R_i i)) (_ : ∀ i, NormalDomain (R_i i)),
        Nonempty (R ≃+* ∀ i, R_i i) := by
  let S := { p : Ideal R // p ∈ (⊥ : Ideal R).minimalPrimes }
  have hS : Finite S := h_min_primes
  haveI : Fintype S := Fintype.ofFinite S
  haveI : DecidableEq S := Classical.decEq S
  obtain ⟨n, ⟨e_fin⟩⟩ := Finite.exists_equiv_fin S
  have e1_ne := imp23_iso h_min_primes h_int
  obtain ⟨e1⟩ := e1_ne
  let e2 := RingEquiv.piCongrLeft' (fun (p : S) => R ⧸ p.val) e_fin
  have e_total : R ≃+* ∀ j : Fin n, R ⧸ (e_fin.symm j).val := e1.trans e2
  have h_pi_int : IsIntegrallyClosed (∀ i : S, R ⧸ i.val) := @isIntegrallyClosed_of_equiv _ _ _ _ e1.symm h_int
  have h_norm : ∀ j : Fin n, NormalDomain (R ⧸ (e_fin.symm j).val) := by
    intro j
    let i := e_fin.symm j
    have hp : i.val.IsPrime := i.property.1.1
    haveI : IsDomain (R ⧸ i.val) := Ideal.Quotient.isDomain i.val
    have h_doms : ∀ k : S, IsDomain (R ⧸ k.val) := fun k => by
      haveI : k.val.IsPrime := k.property.1.1
      exact Ideal.Quotient.isDomain k.val
    haveI h_ri : IsIntegrallyClosed (R ⧸ i.val) := @isIntegrallyClosed_factor S _ _ (fun k => R ⧸ k.val) _ h_doms h_pi_int i
    exact { }
  exact ⟨Fin n, inferInstance, fun j => R ⧸ (e_fin.symm j).val, fun j => inferInstance, h_norm, ⟨e_total⟩⟩



lemma eval2_comm_pi {ι : Type*} [Finite ι] (R_i : ι → Type*)
    [∀ i, CommRing (R_i i)] (K_i : ι → Type*) [∀ i, CommRing (K_i i)]
    [∀ i, Algebra (R_i i) (K_i i)] (x : ∀ i, K_i i) (p : Polynomial (∀ i, R_i i)) (i : ι) :
    (Polynomial.eval₂ (algebraMap (∀ i, R_i i) (∀ i, K_i i)) x p) i =
      Polynomial.eval₂ (algebraMap (R_i i) (K_i i)) (x i) (p.map (Pi.evalRingHom (fun j => R_i j) i)) := by
  norm_num[ eval₂_map, false,eval₂_eq_sum_range]
  exact ( Finset.sum_subset (@List.range_subset.mpr (by push_cast [natDegree_map_le])) fun and I I =>mul_eq_zero_of_left.comp (congr_arg ↑_ ((coeff_map _ _).symm.trans (coeff_eq_zero_of_natDegree_lt (not_lt.mp (I.comp (List.mem_range.mpr)))))).trans ( RingHom.map_zero _) @_).symm

lemma isIntegrallyClosed_pi_eval_zero.{v} {ι : Type*} [Finite ι] (R_i : ι → Type v)
    [∀ i, CommRing (R_i i)] (K_i : ι → Type v) [∀ i, CommRing (K_i i)]
    [∀ i, Algebra (R_i i) (K_i i)] (x : ∀ i, K_i i) (p : Polynomial (∀ i, R_i i))
    (hp : Polynomial.eval₂ (algebraMap (∀ i, R_i i) (∀ i, K_i i)) x p = 0) (i : ι) :
    Polynomial.eval₂ (algebraMap (R_i i) (K_i i)) (x i) (p.map (Pi.evalRingHom (fun j => R_i j) i)) = 0 := by
  have h_eval_pi : (Polynomial.eval₂ (algebraMap (∀ i, R_i i) (∀ i, K_i i)) x p) i = 0 := by rw [hp]; rfl
  have h_eval_comm : (Polynomial.eval₂ (algebraMap (∀ i, R_i i) (∀ i, K_i i)) x p) i =
      Polynomial.eval₂ (algebraMap (R_i i) (K_i i)) (x i) (p.map (Pi.evalRingHom (fun j => R_i j) i)) := eval2_comm_pi R_i K_i x p i
  rw [←h_eval_comm]
  exact h_eval_pi

lemma isIntegrallyClosed_pi.{v} {ι : Type*} [Finite ι] (R_i : ι → Type v)
    [∀ i, CommRing (R_i i)] [∀ i, NormalDomain (R_i i)] :
    IsIntegrallyClosed (∀ i, R_i i) := by
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : DecidableEq ι := Classical.decEq ι
  haveI : ∀ i, IsDomain (R_i i) := inferInstance
  haveI : ∀ i, IsIntegrallyClosed (R_i i) := inferInstance
  have h_frac := isFractionRing_pi R_i
  rw [isIntegrallyClosed_iff (∀ i, FractionRing (R_i i))]
  intro x hx
  have hx_i : ∀ i, ∃ y_i : R_i i, algebraMap (R_i i) (FractionRing (R_i i)) y_i = x i := by
    intro i
    have hx_integral : IsIntegral (R_i i) (x i) := by
      obtain ⟨p, hp_monic, hp_eval⟩ := hx
      use p.map (Pi.evalRingHom (fun j => R_i j) i)
      constructor
      · exact hp_monic.map _
      · exact isIntegrallyClosed_pi_eval_zero R_i (fun j => FractionRing (R_i j)) x p hp_eval i
    exact (isIntegrallyClosed_iff (FractionRing (R_i i))).mp (inferInstance : IsIntegrallyClosed (R_i i)) hx_integral
  choose y hy using hx_i
  use y
  ext i
  exact hy i

lemma imp32.{v} {R : Type v} [CommRing R] [IsReduced R]
    (h_min_primes : (⊥ : Ideal R).minimalPrimes.Finite)
    (h : ∃ (ι : Type) (_ : Finite ι) (R_i : ι → Type v)
        (_ : ∀ i, CommRing (R_i i)) (_ : ∀ i, NormalDomain (R_i i)),
        Nonempty (R ≃+* ∀ i, R_i i)) : IsIntegrallyClosed R := by
  obtain ⟨ι, hfin, R_i, hc, hn, ⟨e⟩⟩ := h
  haveI : IsIntegrallyClosed (∀ i, R_i i) := @isIntegrallyClosed_pi ι hfin R_i hc hn
  exact @isIntegrallyClosed_of_equiv _ _ _ _ e inferInstance

lemma pi_prime_idempotent.{v} {ι : Type*} [Fintype ι] [DecidableEq ι] (R_i : ι → Type v)
    [∀ i, CommRing (R_i i)] (M : Ideal (∀ i, R_i i)) [hM : M.IsPrime] :
    ∃ j : ι, (fun i => if i = j then (1 : R_i i) else 0) ∉ M := by
  by_contra h
  push_neg at h
  have h_sum : (∑ j : ι, (fun i => if i = j then (1 : R_i i) else 0)) ∈ M := Ideal.sum_mem M fun j _ => h j
  have h_one : (∑ j : ι, (fun i => if i = j then (1 : R_i i) else 0)) = (1 : ∀ i, R_i i) := by
    ext i
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · intro hi
      exfalso
      exact hi (Finset.mem_univ i)
  rw [h_one] at h_sum
  have h_top : M = ⊤ := eq_top_iff.mpr (fun x _ => by
    have h1 : x * (1 : ∀ i, R_i i) ∈ M := Ideal.mul_mem_left M x h_sum
    rwa [mul_one] at h1
  )
  exact hM.ne_top h_top

def loc_equiv_of_eq.{v} {R : Type v} [CommRing R] (M P : Ideal R) [M.IsPrime] [P.IsPrime] (h : P = M) :
    Localization.AtPrime P ≃+* Localization.AtPrime M := by
  subst h
  exact RingEquiv.refl _

lemma pi_localization_equiv.{v} {ι : Type*} [Fintype ι] [DecidableEq ι] (R_i : ι → Type v)
    [∀ i, CommRing (R_i i)] (M : Ideal (∀ i, R_i i)) [M.IsPrime]
    (j : ι) (hj : (fun i => if i = j then (1 : R_i i) else 0) ∉ M)
    [hMj : (M.map (Pi.evalRingHom R_i j)).IsPrime] :
    Nonempty (Localization.AtPrime M ≃+* Localization.AtPrime (M.map (Pi.evalRingHom R_i j))) := by
  let M_j := M.map (Pi.evalRingHom R_i j)
  have h_surj : Function.Surjective (Pi.evalRingHom R_i j) := fun y =>
    ⟨fun i => if h : j = i then h ▸ y else 0, dif_pos rfl⟩
  let P := M_j.comap (Pi.evalRingHom R_i j)
  have h_eq : P = M := by
    ext x
    constructor
    · intro hx
      have hx' : (Pi.evalRingHom R_i j) x ∈ M_j := hx
      obtain ⟨y, hy_M, hy_eq⟩ := (Ideal.mem_map_iff_of_surjective (Pi.evalRingHom R_i j) h_surj).mp hx'
      let e_j : ∀ i, R_i i := fun i => if i = j then 1 else 0
      have he : e_j * (1 - e_j) = 0 := by
        ext i
        by_cases h : i = j
        · have hi_e : e_j i = 1 := dif_pos h
          simp [hi_e]
        · have hi_e : e_j i = 0 := dif_neg h
          simp [hi_e]
      have heM : e_j * (1 - e_j) ∈ M := by
        rw [he]
        exact M.zero_mem
      have h1_e_j : 1 - e_j ∈ M := by
        cases (inferInstance : M.IsPrime).mem_or_mem heM with
        | inl h =>
          have he_j : e_j = fun i => if i = j then 1 else 0 := rfl
          rw [he_j] at h
          exact False.elim (hj h)
        | inr h => exact h
      have h_x_eq : x = y * e_j + x * (1 - e_j) := by
        ext i
        by_cases h : i = j
        · subst i
          have hj_e : e_j j = 1 := dif_pos rfl
          change x j = y j * e_j j + x j * (1 - e_j j)
          rw [hj_e]
          simp only [sub_self, mul_zero, add_zero, mul_one]
          exact hy_eq.symm
        · have hi_e : e_j i = 0 := dif_neg h
          change x i = y i * e_j i + x i * (1 - e_j i)
          rw [hi_e]
          simp only [sub_zero, mul_zero, zero_add, mul_one]
      rw [h_x_eq]
      apply Ideal.add_mem
      · exact Ideal.mul_mem_right _ _ hy_M
      · exact Ideal.mul_mem_left _ _ h1_e_j
    · intro hx
      exact Ideal.mem_map_of_mem _ hx
  obtain ⟨e⟩ := prime_prod_equiv R_i j M_j
  have e_loc := loc_equiv_of_eq P M h_eq.symm
  exact ⟨e_loc.trans e⟩

lemma normalDomain_of_localization.{v} {R : Type v} [CommRing R] [NormalDomain R]
  (p : Ideal R) [p.IsPrime] : NormalDomain (Localization.AtPrime p) := by
  have h_le : p.primeCompl ≤ nonZeroDivisors R := by
    intro x hx
    have h_x_neq_0 : x ≠ 0 := by
      intro h_eq
      rw [h_eq] at hx
      exact hx (Ideal.zero_mem p)
    exact mem_nonZeroDivisors_iff_ne_zero.mpr h_x_neq_0
  haveI h_dom : IsDomain (Localization.AtPrime p) := IsLocalization.isDomain_localization h_le
  haveI h_int : IsIntegrallyClosed (Localization.AtPrime p) := isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl h_le
  constructor

lemma pi_ideal_map_prime.{v} {ι : Type*} [Fintype ι] [DecidableEq ι] (R_i : ι → Type v)
    [∀ i, CommRing (R_i i)] (M : Ideal (∀ i, R_i i)) [M.IsPrime]
    (j : ι) (hj : (fun i => if i = j then (1 : R_i i) else 0) ∉ M) :
    (M.map (Pi.evalRingHom R_i j)).IsPrime := by
  let e_j : ∀ i, R_i i := fun i => if i = j then 1 else 0
  have h_ej_not : e_j ∉ M := hj
  have he : e_j * (1 - e_j) = 0 := by
    ext i
    by_cases h : i = j
    · subst i
      change e_j j * (1 - e_j j) = 0
      have hj_e : e_j j = 1 := dif_pos rfl
      rw [hj_e]
      ring
    · have hi_e : e_j i = 0 := dif_neg h
      change e_j i * (1 - e_j i) = 0
      rw [hi_e]
      ring
  have he_M : e_j * (1 - e_j) ∈ M := by rw [he]; exact M.zero_mem
  have h1_ej : 1 - e_j ∈ M := by
    cases (inferInstance : M.IsPrime).mem_or_mem he_M with
    | inl h => exact False.elim (h_ej_not h)
    | inr h => exact h
  have h_ker : RingHom.ker (Pi.evalRingHom R_i j) ≤ M := by
    intro x hx
    have hx_j : x j = 0 := hx
    have h_x_eq : x = x * (1 - e_j) := by
      ext i
      by_cases h : i = j
      · subst i
        change x j = x j * (1 - e_j j)
        rw [hx_j]
        ring
      · have hi_e : e_j i = 0 := dif_neg h
        change x i = x i * (1 - e_j i)
        rw [hi_e]
        ring
    rw [h_x_eq]
    exact Ideal.mul_mem_left M x h1_ej
  have h_surj : Function.Surjective (Pi.evalRingHom R_i j) := fun y => ⟨fun i => if h : i = j then h.symm ▸ y else 0, dif_pos rfl⟩
  exact Ideal.map_isPrime_of_surjective h_surj h_ker

lemma normalRing_of_pi.{v} {ι : Type*} [Fintype ι] [DecidableEq ι] (R_i : ι → Type v)
    [∀ i, CommRing (R_i i)] [∀ i, NormalDomain (R_i i)] :
    NormalRing (∀ i, R_i i) := by
  constructor
  intro M hM
  have h_exists : ∃ j : ι, (fun i => if i = j then (1 : R_i i) else 0) ∉ M := pi_prime_idempotent R_i M
  rcases h_exists with ⟨j, hj⟩
  let M_j := M.map (Pi.evalRingHom R_i j)
  haveI hMj : M_j.IsPrime := pi_ideal_map_prime R_i M j hj
  have e : Nonempty (Localization.AtPrime M ≃+* Localization.AtPrime M_j) := pi_localization_equiv R_i M j hj
  have h_nd : NormalDomain (Localization.AtPrime M_j) := normalDomain_of_localization M_j
  exact @normalDomain_of_equiv_nonempty _ _ _ _ e h_nd

lemma imp31.{v} {R : Type v} [CommRing R] [IsReduced R]
    (h_min_primes : (⊥ : Ideal R).minimalPrimes.Finite)
    (h : ∃ (ι : Type) (_ : Finite ι) (R_i : ι → Type v)
        (_ : ∀ i, CommRing (R_i i)) (_ : ∀ i, NormalDomain (R_i i)),
        Nonempty (R ≃+* ∀ i, R_i i)) : NormalRing R := by
  obtain ⟨ι, hfin, R_i, hc, hn, ⟨e⟩⟩ := h
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : DecidableEq ι := Classical.decEq ι
  have h_norm : NormalRing (∀ i, R_i i) := @normalRing_of_pi ι _ _ R_i _ _
  exact @NormalRing_of_equiv _ _ _ _ e h_norm

lemma main_lemma.{v} {R : Type v} [CommRing R] [IsReduced R]
    (h_min_primes : (⊥ : Ideal R).minimalPrimes.Finite) :
    List.TFAE [
      NormalRing R,
      IsIntegrallyClosed R,
      ∃ (ι : Type) (_ : Finite ι) (R_i : ι → Type v)
        (_ : ∀ i, CommRing (R_i i)) (_ : ∀ i, NormalDomain (R_i i)),
        Nonempty (R ≃+* ∀ i, R_i i)
    ] := by
  tfae_have 1 → 3 := by
    intro h
    exact imp13 h_min_primes h
  tfae_have 3 → 1 := by
    intro h
    exact imp31 h_min_primes h
  tfae_have 3 → 2 := by
    intro h
    exact imp32 h_min_primes h
  tfae_have 2 → 3 := by
    intro h
    exact imp23 h_min_primes h
  tfae_finish

-- EVOLVE-BLOCK-END

theorem normalRing_characterization {R : Type u} [CommRing R] [IsReduced R]
    (h_min_primes : (⊥ : Ideal R).minimalPrimes.Finite) :
    List.TFAE [
      NormalRing R,
      IsIntegrallyClosed R,
      ∃ (ι : Type) (_ : Finite ι) (R_i : ι → Type u)
        (_ : ∀ i, CommRing (R_i i)) (_ : ∀ i, NormalDomain (R_i i)),
        Nonempty (R ≃+* ∀ i, R_i i)
    ] := by
  -- EVOLVE-BLOCK-START
  exact main_lemma h_min_primes
  -- EVOLVE-BLOCK-END
