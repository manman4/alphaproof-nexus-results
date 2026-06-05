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
-- Helper lemma: quotient of a reduced ring by an idempotent is reduced.
lemma reduced_quotient_directed_idempotents {R : Type*} [CommRing R] [IsReduced R]
    (I : Ideal R)
    (hI : ∀ x ∈ I, ∃ e ∈ I, e * e = e ∧ x = x * e) :
    IsReduced (R ⧸ I) := by
  constructor
  rintro ⟨x⟩ h_nil
  obtain ⟨n, hn⟩ := h_nil
  have h1 : x ^ n ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hn
  cases n with
  | zero =>
    have h_one_in : (1 : R) ∈ I := by
      have h_pow_zero : x ^ 0 = 1 := pow_zero x
      rwa [h_pow_zero] at h1
    have h_x_in : x ∈ I := by
      have h_mul : x = x * 1 := (mul_one x).symm
      rw [h_mul]
      exact Ideal.mul_mem_left I x h_one_in
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr h_x_in
  | succ m =>
    have h2 : ∃ e ∈ I, e * e = e ∧ x ^ (Nat.succ m) = x ^ (Nat.succ m) * e := hI (x ^ (Nat.succ m)) h1
    rcases h2 with ⟨e, heI, hee, hxe⟩
    have h_idem_1_e : (1 - e) * (1 - e) = 1 - e := by
      calc (1 - e) * (1 - e) = 1 - e - e + e * e := by ring
        _ = 1 - e := by rw [hee]; ring
    have h_pow_e : ∀ k : ℕ, k > 0 → (1 - e) ^ k = 1 - e := by
      intro k hk
      induction k with
      | zero =>
        exfalso; exact Nat.lt_asymm hk hk
      | succ j ih =>
        cases j with
        | zero =>
          exact pow_one (1 - e)
        | succ i =>
          have hj_pos : Nat.succ i > 0 := Nat.zero_lt_succ i
          rw [pow_succ, ih hj_pos, h_idem_1_e]
    have h3 : IsNilpotent (x - x * e) := by
      use (Nat.succ m)
      have h_sub : x - x * e = x * (1 - e) := by ring
      rw [h_sub, mul_pow]
      have hm_pos : Nat.succ m > 0 := Nat.zero_lt_succ m
      rw [h_pow_e (Nat.succ m) hm_pos]
      calc x ^ (Nat.succ m) * (1 - e) = x ^ (Nat.succ m) - x ^ (Nat.succ m) * e := by ring
        _ = 0 := sub_eq_zero.mpr hxe
    have h4 : x - x * e = 0 := IsReduced.eq_zero _ h3
    have h5 : x = x * e := sub_eq_zero.mp h4
    have h6 : x ∈ I := by
      rw [h5]
      exact Ideal.mul_mem_left I x heI
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr h6

lemma retract_reduced {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : S →+* R) (h : f.comp g = RingHom.id S) [IsReduced R] : IsReduced S := by
  constructor
  intro x hx
  have h1 : IsNilpotent (g x) := hx.map g
  have h2 : g x = 0 := IsReduced.eq_zero _ h1
  have h3 : f (g x) = 0 := by rw [h2, map_zero]
  have h4 : f (g x) = x := by
    calc f (g x) = (f.comp g) x := rfl
      _ = x := by rw [h]; rfl
  rwa [h4] at h3



lemma isAlgebraic_of_isSeparable (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [Algebra.IsSeparable k k'] : Algebra.IsAlgebraic k k' := Algebra.IsSeparable.isAlgebraic k k'





lemma reduced_of_surjective_directed_idempotents {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (h_ker : ∀ x, f x = 0 → ∃ e, e * e = e ∧ f e = 0 ∧ x = x * e)
    [IsReduced R] : IsReduced S := by
  constructor
  intro s hs
  obtain ⟨n, hn⟩ := hs
  obtain ⟨r, rfl⟩ := hf s
  have h1 : f (r ^ n) = 0 := by rw [map_pow, hn]
  obtain ⟨e, he_idemp, he_ker, he_x⟩ := h_ker (r ^ n) h1
  cases n with
  | zero =>
    have h_one : (1 : S) = 0 := by
      calc (1 : S) = f r ^ 0 := (pow_zero _).symm
        _ = 0 := hn
    calc f r = f r * 1 := (mul_one _).symm
      _ = f r * 0 := by rw [h_one]
      _ = 0 := mul_zero _
  | succ m =>
    have hm_pos : Nat.succ m > 0 := Nat.zero_lt_succ m
    have h_idemp2 : (1 - e) * (1 - e) = 1 - e := by
      calc (1 - e) * (1 - e) = 1 - e - e + e * e := by ring
        _ = 1 - e - e + e := by rw [he_idemp]
        _ = 1 - e := by ring
    have h_pow_e : ∀ k : ℕ, k > 0 → (1 - e) ^ k = 1 - e := by
      intro k hk
      induction k with
      | zero => exfalso; exact Nat.lt_asymm hk hk
      | succ j ih =>
        cases j with
        | zero => exact pow_one (1 - e)
        | succ i => rw [pow_succ, ih (Nat.zero_lt_succ i), h_idemp2]
    have h2 : (r * (1 - e)) ^ (Nat.succ m) = 0 := by
      rw [mul_pow, h_pow_e (Nat.succ m) hm_pos]
      calc r ^ (Nat.succ m) * (1 - e) = r ^ (Nat.succ m) - r ^ (Nat.succ m) * e := by ring
        _ = 0 := sub_eq_zero.mpr he_x
    have h3 : r * (1 - e) = 0 := IsReduced.eq_zero _ ⟨Nat.succ m, h2⟩
    have h4 : r = r * e := by
      calc r = r - 0 := by ring
        _ = r - r * (1 - e) := by rw [h3]
        _ = r * e := by ring
    calc f r = f (r * e) := congrArg f h4
      _ = f r * f e := map_mul _ _ _
      _ = f r * 0 := by rw [he_ker]
      _ = 0 := mul_zero _



lemma ideal_generated_by_idempotents {R : Type*} [CommRing R] (S : Set R) (I : Ideal R) (hI : I = Ideal.span S)
    (hS : ∀ s ∈ S, ∃ e ∈ I, e * e = e ∧ s = s * e) :
    ∀ x ∈ I, ∃ e ∈ I, e * e = e ∧ x = x * e := by
  intro x hx
  rw [hI] at hx
  induction hx using Submodule.span_induction with
  | mem s hs =>
    exact hS s hs
  | zero =>
    use 0
    refine ⟨I.zero_mem, by ring, by ring⟩
  | add x y hx_mem hy_mem hx_ih hy_ih =>
    rcases hx_ih with ⟨ex, hex_mem, hex_id, hex_eq⟩
    rcases hy_ih with ⟨ey, hey_mem, hey_id, hey_eq⟩
    use ex + ey - ex * ey
    refine ⟨?_, ?_, ?_⟩
    · exact I.sub_mem (I.add_mem hex_mem hey_mem) (I.mul_mem_left ex hey_mem)
    · calc (ex + ey - ex * ey) * (ex + ey - ex * ey)
        = ex * ex + ey * ey + (ex * ex) * (ey * ey) + 2 * ex * ey - 2 * (ex * ex) * ey - 2 * ex * (ey * ey) := by ring
        _ = ex + ey + ex * ey + 2 * ex * ey - 2 * ex * ey - 2 * ex * ey := by rw [hex_id, hey_id]
        _ = ex + ey - ex * ey := by ring
    · have hx_eq' : x * ex = x := hex_eq.symm
      have hy_eq' : y * ey = y := hey_eq.symm
      have h1 : x * ex + x * ey - x * ex * ey = x := by
        calc x * ex + x * ey - x * ex * ey = x + x * ey - (x * ex) * ey := by rw [hx_eq']
        _ = x + x * ey - x * ey := by rw [hx_eq']
        _ = x := by ring
      have h2 : y * ex + y * ey - y * ex * ey = y := by
        calc y * ex + y * ey - y * ex * ey = y * ex + y - y * ex * ey := by rw [hy_eq']
        _ = y * ex + y - (y * ey) * ex := by ring
        _ = y * ex + y - y * ex := by rw [hy_eq']
        _ = y := by ring
      calc x + y
        = (x * ex + x * ey - x * ex * ey) + (y * ex + y * ey - y * ex * ey) := by rw [h1, h2]
        _ = (x + y) * (ex + ey - ex * ey) := by ring
  | smul a x hx_mem hx_ih =>
    rcases hx_ih with ⟨e, he_mem, he_id, he_eq⟩
    use e
    refine ⟨he_mem, he_id, ?_⟩
    change a * x = a * x * e
    calc a * x = a * (x * e) := by rw [← he_eq]
      _ = a * x * e := by ring

lemma eval_poly_trick {L k_b : Type*} [Field k_b] [Field L] [Algebra k_b L]
  (P : k_b[X]) (hsep : P.Separable) (y : L) (hy : aeval y P = 0) :
  ∃ Q : L[X], (P.map (algebraMap k_b L)) = (X - C y) * Q ∧ IsCoprime (X - C y) Q := by
  have h1 : IsRoot (P.map (algebraMap k_b L)) y := by
    rw [IsRoot.def, eval_map, ← aeval_def]
    exact hy
  have h2 : (X - C y) ∣ P.map (algebraMap k_b L) := dvd_iff_isRoot.mpr h1
  rcases h2 with ⟨Q, hQ⟩
  use Q
  constructor
  · exact hQ
  · have hsep_L : (P.map (algebraMap k_b L)).Separable := Separable.map hsep
    rw [hQ] at hsep_L
    exact Separable.isCoprime hsep_L

lemma eval_poly_idemp {L k_b A : Type*} [Field k_b] [Field L] [CommRing A]
  [Algebra k_b L] [Algebra k_b A]
  (P : k_b[X]) (hsep : P.Separable) (y_L : L) (hy_L : aeval y_L P = 0)
  (y_A : A) (hy_A : aeval y_A P = 0) :
  ∃ e : L ⊗[k_b] A, e * e = e ∧
    (y_L ⊗ₜ[k_b] (1 : A) - (1 : L) ⊗ₜ[k_b] y_A) * (1 - e) = (y_L ⊗ₜ[k_b] 1 - 1 ⊗ₜ[k_b] y_A) ∧
    ∃ c : L ⊗[k_b] A, 1 - e = c * (y_L ⊗ₜ[k_b] 1 - 1 ⊗ₜ[k_b] y_A) := by
  have hQ := eval_poly_trick P hsep y_L hy_L
  rcases hQ with ⟨Q, hQ1, hQ2⟩
  rcases hQ2 with ⟨U, V, hUV⟩
  let ev := aeval (R := L) ((1 : L) ⊗ₜ[k_b] y_A)
  have h_eval_X : ev X = (1 : L) ⊗ₜ[k_b] y_A := aeval_X _
  have h_eval_C : ev (C y_L) = y_L ⊗ₜ[k_b] (1 : A) := by
    rw [aeval_C, Algebra.TensorProduct.algebraMap_apply]
    congr
  have h_eval_P : ev (P.map (algebraMap k_b L)) = 0 := by
    rw [aeval_map_algebraMap]
    let f := Algebra.TensorProduct.includeRight (R := k_b) (A := L) (B := A)
    have h1 : f y_A = (1 : L) ⊗ₜ[k_b] y_A := rfl
    have h2 : (aeval (f y_A)) P = f ((aeval y_A) P) := by exact aeval_algHom_apply f y_A P
    rw [h1] at h2
    rw [h2, hy_A, map_zero]

  let u := y_L ⊗ₜ[k_b] (1 : A) - (1 : L) ⊗ₜ[k_b] y_A
  have hu : ev (X - C y_L) = -u := by
    rw [map_sub, h_eval_X, h_eval_C]
    exact (neg_sub (y_L ⊗ₜ[k_b] (1 : A)) ((1 : L) ⊗ₜ[k_b] y_A)).symm
  let w := ev Q
  have huw : u * w = 0 := by
    have h_prod : ev (X - C y_L) * ev Q = 0 := by
      rw [← map_mul]
      rw [← hQ1]
      exact h_eval_P
    rw [hu, neg_mul, neg_eq_zero] at h_prod
    exact h_prod
  let a := - ev U
  let b := ev V
  have h_lin : a * u + b * w = 1 := by
    have h1 : ev (U * (X - C y_L) + V * Q) = ev 1 := by rw [hUV]
    rw [map_add, map_mul, map_mul, hu, map_one] at h1
    have h2 : ev U * -u = -ev U * u := by rw [mul_neg, neg_mul]
    rw [h2] at h1
    exact h1
  let e := b * w
  use e
  have hee : e * e = e := by
    have h1 : e * e - e = 0 := by
      calc e * e - e = b * w * (b * w - 1) := by ring
        _ = b * w * (- a * u) := by
          have : b * w - 1 = - a * u := by
            calc b * w - 1 = (a * u + b * w) - 1 - a * u := by ring
              _ = 1 - 1 - a * u := by rw [h_lin]
              _ = - a * u := by ring
          rw [this]
        _ = - a * b * (u * w) := by ring
        _ = - a * b * 0 := by rw [huw]
        _ = 0 := by ring
    exact sub_eq_zero.mp h1
  have hue : u * (1 - e) = u := by
    have h1 : u * (1 - e) - u = 0 := by
      calc u * (1 - e) - u = - u * e := by ring
        _ = - u * (b * w) := rfl
        _ = - b * (u * w) := by ring
        _ = - b * 0 := by rw [huw]
        _ = 0 := by ring
    exact sub_eq_zero.mp h1
  have h1e : 1 - e = a * u := by
    calc 1 - e = 1 - b * w := rfl
      _ = a * u + b * w - b * w := by rw [← h_lin]
      _ = a * u := by ring
  exact ⟨hee, hue, a, h1e⟩

lemma idemp_of_two {R : Type*} [CommRing R] (u1 u2 e1 e2 : R)
  (h1 : e1 * e1 = e1) (hu1 : u1 * (1 - e1) = u1) (he1 : ∃ a, 1 - e1 = a * u1)
  (h2 : e2 * e2 = e2) (hu2 : u2 * (1 - e2) = u2) (he2 : ∃ a, 1 - e2 = a * u2) :
  ∃ e : R, e * e = e ∧
    u1 * (1 - e) = u1 ∧ u2 * (1 - e) = u2 ∧
    ∃ a b : R, 1 - e = a * u1 + b * u2 := by
  use e1 * e2
  have he : (e1 * e2) * (e1 * e2) = e1 * e2 := by
    calc (e1 * e2) * (e1 * e2) = (e1 * e1) * (e2 * e2) := by ring
      _ = e1 * e2 := by rw [h1, h2]
  have h1e : u1 * (1 - e1 * e2) = u1 := by
    calc u1 * (1 - e1 * e2) = u1 - u1 * e1 * e2 := by ring
      _ = u1 - (u1 - u1 * (1 - e1)) * e2 := by ring
      _ = u1 - (u1 - u1) * e2 := by rw [hu1]
      _ = u1 := by ring
  have h2e : u2 * (1 - e1 * e2) = u2 := by
    calc u2 * (1 - e1 * e2) = u2 - u2 * e1 * e2 := by ring
      _ = u2 - (u2 - u2 * (1 - e2)) * e1 := by ring
      _ = u2 - (u2 - u2) * e1 := by rw [hu2]
      _ = u2 := by ring
  rcases he1 with ⟨a1, ha1⟩
  rcases he2 with ⟨a2, ha2⟩
  have heq : 1 - e1 * e2 = a1 * u1 + e1 * a2 * u2 := by
    calc 1 - e1 * e2 = (1 - e1) + e1 * (1 - e2) := by ring
      _ = a1 * u1 + e1 * (a2 * u2) := by rw [ha1, ha2]
      _ = a1 * u1 + (e1 * a2) * u2 := by ring
  exact ⟨he, h1e, h2e, a1, e1 * a2, heq⟩

def u_elem (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] (y : k') : L ⊗[k] A :=
  (algebraMap k' L y) ⊗ₜ[k] (1 : A) - (1 : L) ⊗ₜ[k] (algebraMap k' A y)

def I_rel (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] : Ideal (L ⊗[k] A) :=
  Ideal.span (Set.range (u_elem k k' A L))

def S_ring (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] : Type _ :=
  (L ⊗[k] A) ⧸ I_rel k k' A L

instance (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] : CommRing (S_ring k k' A L) :=
  Ideal.Quotient.commRing _

def fL_hom (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] : L →+* S_ring k k' A L :=
  (Ideal.Quotient.mk (I_rel k k' A L)).comp (Algebra.TensorProduct.includeLeft : L →ₐ[k] L ⊗[k] A).toRingHom

def fA_hom (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] : A →+* S_ring k k' A L :=
  (Ideal.Quotient.mk (I_rel k k' A L)).comp (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A).toRingHom



lemma fL_fA_comm (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] (l : L) (a : A) :
    Commute (fL_hom k k' A L l) (fA_hom k k' A L a) := by
  have h_comm : Commute (l ⊗ₜ[k] (1 : A)) ((1 : L) ⊗ₜ[k] a) := by
    exact Commute.all (l ⊗ₜ[k] (1 : A)) ((1 : L) ⊗ₜ[k] a)
  exact h_comm.map (Ideal.Quotient.mk (I_rel k k' A L))


def S_algebra_L (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] : Algebra L (S_ring k k' A L) :=
  RingHom.toAlgebra (fL_hom k k' A L)

def S_algebra_A (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] : Algebra A (S_ring k k' A L) :=
  RingHom.toAlgebra (fA_hom k k' A L)

def S_algebra_k' (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] : Algebra k' (S_ring k k' A L) :=
  RingHom.toAlgebra ((fL_hom k k' A L).comp (algebraMap k' L))

attribute [local instance] S_algebra_k'

def fL_alg (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] : L →ₐ[k'] S_ring k k' A L :=
  AlgHom.mk (fL_hom k k' A L) (by intro r; rfl)

def fA_alg (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] : A →ₐ[k'] S_ring k k' A L :=
  AlgHom.mk (fA_hom k k' A L) (by
    intro r
    change (fA_hom k k' A L) (algebraMap k' A r) = (fL_hom k k' A L) (algebraMap k' L r)
    have h1 : (fL_hom k k' A L) (algebraMap k' L r) - (fA_hom k k' A L) (algebraMap k' A r) = 0 := by
      have hd : (fL_hom k k' A L) (algebraMap k' L r) - (fA_hom k k' A L) (algebraMap k' A r) =
        Ideal.Quotient.mk (I_rel k k' A L) (u_elem k k' A L r) := rfl
      rw [hd]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨r, rfl⟩)
    exact (sub_eq_zero.mp h1).symm
  )


def lift_to_S (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] : (L ⊗[k'] A) →ₐ[k'] S_ring k k' A L :=
  Algebra.TensorProduct.lift (fL_alg k k' A L) (fA_alg k k' A L) (fL_fA_comm k k' A L)

def base_change_map (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] :
    (L ⊗[k] A) →+* L ⊗[k'] A :=
  (Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft : L →ₐ[k'] L ⊗[k'] A).restrictScalars k)
    ((Algebra.TensorProduct.includeRight : A →ₐ[k'] L ⊗[k'] A).restrictScalars k)
    (by intro l a; exact Commute.all _ _)).toRingHom

def S_to_base_change (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] :
    S_ring k k' A L →+* L ⊗[k'] A :=
  Ideal.Quotient.lift (I_rel k k' A L) (base_change_map k k' A L) (by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨y, hy⟩
      rw [← hy]
      change (base_change_map k k' A L) (u_elem k k' A L y) = 0
      have hd : u_elem k k' A L y = (algebraMap k' L y) ⊗ₜ[k] (1 : A) - (1 : L) ⊗ₜ[k] (algebraMap k' A y) := rfl
      rw [hd, map_sub]
      have hl : (base_change_map k k' A L) ((algebraMap k' L y) ⊗ₜ[k] (1 : A)) = (algebraMap k' L y) ⊗ₜ[k'] (1 : A) := by
        dsimp [base_change_map]
        simp
      have hr : (base_change_map k k' A L) ((1 : L) ⊗ₜ[k] (algebraMap k' A y)) = (1 : L) ⊗ₜ[k'] (algebraMap k' A y) := by
        dsimp [base_change_map]
        simp




      rw [hl, hr]
      have heq : (algebraMap k' L y) ⊗ₜ[k'] (1 : A) = (1 : L) ⊗ₜ[k'] (algebraMap k' A y) := by
        calc (algebraMap k' L y) ⊗ₜ[k'] (1 : A) = (y • (1 : L)) ⊗ₜ[k'] (1 : A) := by rw [Algebra.algebraMap_eq_smul_one]
          _ = y • ((1 : L) ⊗ₜ[k'] (1 : A)) := by rw [TensorProduct.smul_tmul']
          _ = (1 : L) ⊗ₜ[k'] (y • (1 : A)) := by rw [TensorProduct.tmul_smul]
          _ = (1 : L) ⊗ₜ[k'] (algebraMap k' A y) := by rw [Algebra.algebraMap_eq_smul_one]
      rw [heq, sub_self]
    | zero => exact map_zero _
    | add x y hx_mem hy_mem ih_x ih_y => rw [map_add, ih_x, ih_y, add_zero]
    | smul c x hx_mem ih_x =>
      change (base_change_map k k' A L) (c * x) = 0
      rw [map_mul, ih_x, mul_zero]
  )


lemma S_ring_isReduced (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    (h_red : IsReduced (L ⊗[k] A)) (h_sep : Algebra.IsSeparable k k') :
    IsReduced (S_ring k k' A L) := by
  apply reduced_quotient_directed_idempotents (I_rel k k' A L)
  apply ideal_generated_by_idempotents
  · rfl

  · rintro s ⟨y, hy⟩
    let P := minpoly k y
    have hsep_poly : P.Separable := Algebra.IsSeparable.isSeparable k y
    let y_L : L := algebraMap k' L y
    have hy_L : aeval y_L P = 0 := by
      have h2 : aeval (algebraMap k' L y) P = algebraMap k' L (aeval y P) := Polynomial.aeval_algebraMap_apply L y P
      rw [h2]
      have h3 : aeval y P = 0 := minpoly.aeval k y
      rw [h3, map_zero]
    let y_A : A := algebraMap k' A y
    have hy_A : aeval y_A P = 0 := by
      have h2 : aeval (algebraMap k' A y) P = algebraMap k' A (aeval y P) := Polynomial.aeval_algebraMap_apply A y P
      rw [h2]
      have h3 : aeval y P = 0 := minpoly.aeval k y
      rw [h3, map_zero]
    have h_idemp := eval_poly_idemp P hsep_poly y_L hy_L y_A hy_A
    rcases h_idemp with ⟨e, hee, he_absorb, c, hc⟩
    use 1 - e
    have h_u : y_L ⊗ₜ[k] (1 : A) - (1 : L) ⊗ₜ[k] y_A = s := by
      have h1 : y_L ⊗ₜ[k] (1 : A) - (1 : L) ⊗ₜ[k] y_A = u_elem k k' A L y := rfl
      rw [h1, hy]

    refine ⟨?_, ?_, ?_⟩
    · rw [hc, h_u]
      exact Ideal.mul_mem_left _ c (Ideal.subset_span ⟨y, hy⟩)
    · calc (1 - e) * (1 - e) = 1 - e - e + e * e := by ring
        _ = 1 - e - e + e := by rw [hee]
        _ = 1 - e := by ring
    · have h_abs2 : s * (1 - e) = s := by
        rw [← h_u]
        exact he_absorb
      exact h_abs2.symm














lemma isAlgClosure_of_isAlgebraic (L : Type*) [Field L] [Algebra k L]
  (k' : Type*) [Field k'] [Algebra k k'] [Algebra.IsAlgebraic k k']
  [Algebra k' L] [IsScalarTower k k' L] [IsAlgClosure k' L] : IsAlgClosure k L := by
  constructor
  · exact IsAlgClosure.isAlgClosed k'
  · exact Algebra.IsAlgebraic.trans k k' L

lemma isReduced_equiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) : IsReduced R ↔ IsReduced S := by
  constructor
  · intro h
    exact @retract_reduced R S _ _ e.toRingHom e.symm.toRingHom (RingHom.ext e.apply_symm_apply) h
  · intro h
    exact @retract_reduced S R _ _ e.symm.toRingHom e.toRingHom (RingHom.ext e.symm_apply_apply) h

lemma geom_reduced_of_alg_closure
    (k : Type*) (A : Type*) [Field k] [CommRing A] [Algebra k A]
    (L : Type*) [Field L] [Algebra k L] [IsAlgClosure k L] :
    Algebra.IsGeometricallyReduced k A ↔ IsReduced (L ⊗[k] A) := by
  have e : L ≃ₐ[k] AlgebraicClosure k := IsAlgClosure.equiv k L (AlgebraicClosure k)
  have e2 : L ⊗[k] A ≃ₐ[k] AlgebraicClosure k ⊗[k] A := Algebra.TensorProduct.congr e (AlgEquiv.refl : A ≃ₐ[k] A)
  rw [Algebra.isGeometricallyReduced_iff k A]
  exact (isReduced_equiv e2.toRingEquiv).symm

lemma zero_of_coprime_annihilators {B : Type*} [CommRing B] (u w x : B) (huw : u * w = 0)
    (h_coprime : IsCoprime u w)
    (h_u : x ∈ Ideal.span {u})
    (h_w : x ∈ Ideal.span {w}) :
    x = 0 := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h_u
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp h_w
  rcases h_coprime with ⟨c, d, hcd⟩
  calc x = x * 1 := (mul_one _).symm
    _ = x * (c * u + d * w) := by rw [hcd]
    _ = x * c * u + x * d * w := by ring
    _ = (b * w) * c * u + (a * u) * d * w := by rw [hb, ha]
    _ = b * c * (w * u) + a * d * (u * w) := by ring
    _ = b * c * (u * w) + a * d * (u * w) := by rw [mul_comm w u]
    _ = b * c * 0 + a * d * 0 := by rw [huw]
    _ = 0 := by ring

lemma zero_of_prod_linear_aux {L : Type*} [Field L] (l : List L) :
  ∀ {B : Type*} [CommRing B] [Algebra L B] (y x : B)
  (hsep : (l.map (fun r => (X : L[X]) - C r)).prod.Separable)
  (hy : aeval y (l.map (fun r => (X : L[X]) - C r)).prod = 0)
  (h_quot : ∀ r ∈ l, x ∈ Ideal.span {y - algebraMap L B r}),
  x = 0 := by
  induction l with
  | nil =>
    intro B _ _ y x _ hy _
    have h1 : (List.map (fun r => (X : L[X]) - C r) []).prod = 1 := rfl
    rw [h1, map_one] at hy
    calc x = x * 1 := (mul_one x).symm
      _ = x * 0 := by rw [← hy]
      _ = 0 := mul_zero x
  | cons r t ih =>
    intro B _ _ y x hsep hy h_quot
    have h_prod : (List.map (fun r' => (X : L[X]) - C r') (r :: t)).prod = ((X : L[X]) - C r) * (List.map (fun r' => (X : L[X]) - C r') t).prod := rfl
    have hsep' := hsep
    rw [h_prod] at hsep'
    have hsep_t : (List.map (fun r' => (X : L[X]) - C r') t).prod.Separable := Separable.of_mul_right hsep'
    have h_coprime_poly : IsCoprime ((X : L[X]) - C r) (List.map (fun r' => (X : L[X]) - C r') t).prod := Separable.isCoprime hsep'
    have huw : aeval y ((X : L[X]) - C r) * aeval y (List.map (fun r' => (X : L[X]) - C r') t).prod = 0 := by
      rw [← map_mul, ← h_prod, hy]
    let u := aeval y ((X : L[X]) - C r)
    let w := aeval y (List.map (fun r' => (X : L[X]) - C r') t).prod
    have h_coprime : IsCoprime u w := by
      rcases h_coprime_poly with ⟨A_poly, B_poly, hAB⟩
      use aeval y A_poly, aeval y B_poly
      calc aeval y A_poly * u + aeval y B_poly * w = aeval y (A_poly * ((X : L[X]) - C r) + B_poly * (List.map (fun r' => (X : L[X]) - C r') t).prod) := by rw [map_add, map_mul, map_mul]
        _ = aeval y 1 := by rw [hAB]
        _ = 1 := map_one _
    have hu_eq : u = y - algebraMap L B r := by
      calc u = aeval y (X : L[X]) - aeval y (C r) := map_sub _ _ _
        _ = y - algebraMap L B r := by rw [aeval_X, aeval_C]
    have h_u : x ∈ Ideal.span {u} := by
      rw [hu_eq]
      exact h_quot r (List.Mem.head _)
    have h_w : x ∈ Ideal.span {w} := by
      let B_w := B ⧸ Ideal.span {w}
      let y_w := Ideal.Quotient.mk (Ideal.span {w}) y
      let x_w := Ideal.Quotient.mk (Ideal.span {w}) x
      have h_x_w_zero : x_w = 0 := by
        apply ih (B := B_w) y_w x_w hsep_t
        · have h_aeval_w : aeval y_w (List.map (fun r' => (X : L[X]) - C r') t).prod = Ideal.Quotient.mk (Ideal.span {w}) w := by
            exact Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ L (Ideal.span {w})) y _
          rw [h_aeval_w]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton w))
        · intro r' hr'
          have h1 : x ∈ Ideal.span {y - algebraMap L B r'} := h_quot r' (List.Mem.tail r hr')
          obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
          have h2 : x_w = Ideal.Quotient.mk (Ideal.span {w}) c * (y_w - algebraMap L B_w r') := by
            dsimp [x_w, y_w]
            rw [← hc, map_mul, map_sub]
            rfl
          apply Ideal.mem_span_singleton'.mpr
          use Ideal.Quotient.mk (Ideal.span {w}) c
          exact h2.symm
      exact Ideal.Quotient.eq_zero_iff_mem.mp h_x_w_zero
    exact zero_of_coprime_annihilators u w x huw h_coprime h_u h_w

lemma mem_ideal_span_of_poly_aux {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] (U V : R) (Q : k[X]) :
    aeval U Q - aeval V Q ∈ Ideal.span { U - V } := by
  norm_num [aeval_eq_sum_range,Ideal.mem_span_singleton',funext_iff]
  exact ( Finset.dvd_sum fun and n=>by simp_rw [Algebra.smul_def,←mul_sub,(sub_dvd_pow_sub_pow U _ _).mul_left]).imp fun and=>.trans (mul_comm _ _) ∘symm ∘.trans ( Finset.sum_sub_distrib ..).symm

lemma mem_ideal_span_of_poly (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    (y : k') (Q : k[X]) :
    u_elem k k' A L (aeval y Q) ∈ Ideal.span { u_elem k k' A L y } := by
  let U := (algebraMap k' L y) ⊗ₜ[k] (1 : A)
  let V := (1 : L) ⊗ₜ[k] (algebraMap k' A y)
  have hU : aeval U Q = (algebraMap k' L (aeval y Q)) ⊗ₜ[k] (1 : A) := by
    have h_hom : aeval U Q = aeval ((Algebra.TensorProduct.includeLeft : L →ₐ[k] L ⊗[k] A) (algebraMap k' L y)) Q := rfl
    rw [h_hom]
    have h_aeval := Polynomial.aeval_algHom_apply (Algebra.TensorProduct.includeLeft : L →ₐ[k] L ⊗[k] A) (algebraMap k' L y) Q
    rw [h_aeval]
    have h_aeval_L := Polynomial.aeval_algebraMap_apply L y Q
    rw [h_aeval_L]
    rfl
  have hV : aeval V Q = (1 : L) ⊗ₜ[k] (algebraMap k' A (aeval y Q)) := by
    have h_hom : aeval V Q = aeval ((Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A) (algebraMap k' A y)) Q := rfl
    rw [h_hom]
    have h_aeval := Polynomial.aeval_algHom_apply (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A) (algebraMap k' A y) Q
    rw [h_aeval]
    have h_aeval_A := Polynomial.aeval_algebraMap_apply A y Q
    rw [h_aeval_A]
    rfl
  have h_aux := mem_ideal_span_of_poly_aux U V Q
  rw [hU, hV] at h_aux
  exact h_aux

lemma fd_helper (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [Algebra.IsSeparable k k'] (S : List k') :
  FiniteDimensional k (IntermediateField.adjoin k {x | x ∈ S}) := by
  have h_alg : ∀ x : k', IsIntegral k x := fun x => IsAlgebraic.isIntegral ((isAlgebraic_of_isSeparable k k').1 x)
  have h_fin : Finite {x | x ∈ S} := Set.Finite.to_subtype (List.finite_toSet S)
  exact IntermediateField.finiteDimensional_adjoin (fun x hx => h_alg x)

lemma sep_helper (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [Algebra.IsSeparable k k'] (S : List k') :
  Algebra.IsSeparable k (IntermediateField.adjoin k {x | x ∈ S}) := inferInstance

lemma alg_helper (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [Algebra.IsSeparable k k'] (S : List k') (y_E : IntermediateField.adjoin k {x | x ∈ S}) :
  IsIntegral k y_E := by
  cases y_E
  exact (‹Algebra.IsSeparable k k'›.1 (by valid)).isIntegral.imp (by simp_all[Subtype.eq_iff,eval₂_eq_sum_range])

lemma in_adjoin_helper (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [Algebra.IsSeparable k k'] (S : List k') (y_E : IntermediateField.adjoin k {x | x ∈ S}) (hy_E : IntermediateField.adjoin k {y_E} = ⊤) (s_E : IntermediateField.adjoin k {x | x ∈ S}) :
  s_E ∈ IntermediateField.adjoin k {y_E} := by
  refine hy_E▸trivial

lemma range_helper (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [Algebra.IsSeparable k k'] (S : List k') (y_E : IntermediateField.adjoin k {x | x ∈ S}) (s_E : IntermediateField.adjoin k {x | x ∈ S}) (hs : s_E ∈ IntermediateField.adjoin k {y_E}) :
  s_E ∈ (Polynomial.aeval (R := k) y_E).range := by
  have:=IntermediateField.adjoin_simple_toSubalgebra_of_integral<|show IsIntegral k y_E from(Algebra.IsSeparable.isIntegral _ _)
  rwa[←Algebra.adjoin_singleton_eq_range_aeval, this.symm]

lemma eq_helper (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [Algebra.IsSeparable k k'] (S : List k') (y_E : IntermediateField.adjoin k {x | x ∈ S}) (s : k') (hs : s ∈ S) (Q : k[X]) (hQ : aeval (R := k) y_E Q = (⟨s, IntermediateField.subset_adjoin k {x | x ∈ S} hs⟩ : IntermediateField.adjoin k {x | x ∈ S})) :
  s = aeval (R := k) (y_E : k') Q := by
  simp_all only[aeval_eq_sum_range, push_cast,Subtype.eq_iff]

lemma exists_primitive_element_of_list (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [Algebra.IsSeparable k k'] (S : List k') :
  ∃ y : k', ∀ s ∈ S, ∃ Q : k[X], s = aeval y Q := by
  let E := IntermediateField.adjoin k {x | x ∈ S}
  have h_alg : ∀ x : k', IsAlgebraic k x := (isAlgebraic_of_isSeparable k k').1
  have h_fd : FiniteDimensional k E := fd_helper k k' S
  have h_sep : Algebra.IsSeparable k E := sep_helper k k' S
  obtain ⟨y_E, hy_E⟩ := Field.exists_primitive_element k E
  use (y_E : k')
  intro s hs
  have hs_E : s ∈ E := IntermediateField.subset_adjoin k {x | x ∈ S} hs
  let s_E : E := ⟨s, hs_E⟩
  have hs_in_adjoin : s_E ∈ IntermediateField.adjoin k {y_E} := in_adjoin_helper k k' S y_E hy_E s_E
  have h_range : s_E ∈ (Polynomial.aeval (R := k) y_E).range := range_helper k k' S y_E s_E hs_in_adjoin
  rcases h_range with ⟨Q, hQ⟩
  use Q
  exact eq_helper k k' S y_E s hs Q hQ

lemma common_primitive_of_two (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    [Algebra.IsSeparable k k']
    (y1 y2 : k') :
    ∃ y : k', u_elem k k' A L y1 ∈ Ideal.span { u_elem k k' A L y } ∧
               u_elem k k' A L y2 ∈ Ideal.span { u_elem k k' A L y } := by
  have hS := exists_primitive_element_of_list k k' [y1, y2]
  rcases hS with ⟨y, hy⟩
  have h1 : ∃ Q1 : k[X], y1 = aeval y Q1 := hy y1 (by simp)
  have h2 : ∃ Q2 : k[X], y2 = aeval y Q2 := hy y2 (by simp)
  rcases h1 with ⟨Q1, hQ1⟩
  rcases h2 with ⟨Q2, hQ2⟩
  use y
  constructor
  · rw [hQ1]
    exact mem_ideal_span_of_poly k k' A L y Q1
  · rw [hQ2]
    exact mem_ideal_span_of_poly k k' A L y Q2

lemma exists_primitive_of_I_rel (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    [Algebra.IsSeparable k k']
    (x : L ⊗[k] A) (hx : x ∈ I_rel k k' A L) :
    ∃ y : k', x ∈ Ideal.span { u_elem k k' A L y } := by
  induction hx using Submodule.span_induction with
  | mem s hs =>
    rcases hs with ⟨y, rfl⟩
    use y
    exact Ideal.subset_span (Set.mem_singleton _)
  | zero =>
    use 0
    exact Ideal.zero_mem _
  | add x1 x2 hx1 hx2 ih1 ih2 =>
    rcases ih1 with ⟨y1, hy1⟩
    rcases ih2 with ⟨y2, hy2⟩
    have h_common := common_primitive_of_two k k' A L y1 y2
    rcases h_common with ⟨y, hy1_y, hy2_y⟩
    use y
    have hy1' : x1 ∈ Ideal.span { u_elem k k' A L y } := by
      have h_sub : Ideal.span { u_elem k k' A L y1 } ≤ Ideal.span { u_elem k k' A L y } := by
        rw [Ideal.span_le]
        intro u hu
        have h_eq : u = u_elem k k' A L y1 := Set.mem_singleton_iff.mp hu
        rw [h_eq]
        exact hy1_y
      exact h_sub hy1
    have hy2' : x2 ∈ Ideal.span { u_elem k k' A L y } := by
      have h_sub : Ideal.span { u_elem k k' A L y2 } ≤ Ideal.span { u_elem k k' A L y } := by
        rw [Ideal.span_le]
        intro u hu
        have h_eq : u = u_elem k k' A L y2 := Set.mem_singleton_iff.mp hu
        rw [h_eq]
        exact hy2_y
      exact h_sub hy2
    exact Ideal.add_mem _ hy1' hy2'
  | smul a x hx ih =>
    rcases ih with ⟨y, hy⟩
    use y
    exact Ideal.mul_mem_left _ a hy

lemma fwd_dir
    (k' : Type u) (A : Type v) [Field k'] [CommRing A]
    [Algebra k k'] [Algebra.IsSeparable k k'] [Algebra k' A] [Algebra k A]
    [IsScalarTower k k' A] (h : Algebra.IsGeometricallyReduced k A) :
    Algebra.IsGeometricallyReduced k' A := by
  let L := AlgebraicClosure k'
  have isAlg_k_k' := isAlgebraic_of_isSeparable k k'
  have isAlgClosure_k_L : IsAlgClosure k L := isAlgClosure_of_isAlgebraic L k'
  have h_red_L_A_k : IsReduced (L ⊗[k] A) := (geom_reduced_of_alg_closure k A L).mp h
  have h_S_red := S_ring_isReduced k k' A L h_red_L_A_k ‹Algebra.IsSeparable k k'›
  have h_comp : (S_to_base_change k k' A L).comp (lift_to_S k k' A L).toRingHom = RingHom.id (L ⊗[k'] A) := by
    apply RingHom.ext; intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      have h1 : (lift_to_S k k' A L).toRingHom (l ⊗ₜ[k'] a) = fL_hom k k' A L l * fA_hom k k' A L a := rfl
      have h2 : fL_hom k k' A L l = Ideal.Quotient.mk (I_rel k k' A L) (l ⊗ₜ[k] (1 : A)) := rfl
      have h3 : fA_hom k k' A L a = Ideal.Quotient.mk (I_rel k k' A L) ((1 : L) ⊗ₜ[k] a) := rfl
      change (S_to_base_change k k' A L) ((lift_to_S k k' A L).toRingHom (l ⊗ₜ[k'] a)) = l ⊗ₜ[k'] a
      rw [h1, map_mul, h2, h3]
      have hc : (S_to_base_change k k' A L) (Ideal.Quotient.mk (I_rel k k' A L) (l ⊗ₜ[k] (1 : A))) = (base_change_map k k' A L) (l ⊗ₜ[k] (1 : A)) := rfl
      rw [hc]
      have hc2 : (S_to_base_change k k' A L) (Ideal.Quotient.mk (I_rel k k' A L) ((1 : L) ⊗ₜ[k] a)) = (base_change_map k k' A L) ((1 : L) ⊗ₜ[k] a) := rfl
      rw [hc2]
      have hl : (base_change_map k k' A L) (l ⊗ₜ[k] (1 : A)) = l ⊗ₜ[k'] (1 : A) := by
        dsimp [base_change_map]
        simp
      have ha : (base_change_map k k' A L) ((1 : L) ⊗ₜ[k] a) = (1 : L) ⊗ₜ[k'] a := by
        dsimp [base_change_map]
        simp
      rw [hl, ha]
      calc l ⊗ₜ[k'] (1 : A) * (1 : L) ⊗ₜ[k'] a = (l * 1) ⊗ₜ[k'] (1 * a) := by exact Algebra.TensorProduct.tmul_mul_tmul l (1 : L) (1 : A) a
        _ = l ⊗ₜ[k'] a := by rw [mul_one, one_mul]
    | add x y hx hy =>
      change (S_to_base_change k k' A L) ((lift_to_S k k' A L).toRingHom (x + y)) = x + y
      rw [map_add, map_add]
      have hx' : (S_to_base_change k k' A L) ((lift_to_S k k' A L).toRingHom x) = x := hx
      have hy' : (S_to_base_change k k' A L) ((lift_to_S k k' A L).toRingHom y) = y := hy
      rw [hx', hy']
  have h_colimit : IsReduced (L ⊗[k'] A) :=
    @retract_reduced (S_ring k k' A L) (L ⊗[k'] A) _ _
      (S_to_base_change k k' A L)
      (lift_to_S k k' A L).toRingHom
      h_comp h_S_red

  exact (geom_reduced_of_alg_closure k' A L).mpr h_colimit










open Classical

lemma finite_conjugates_aux {k L A : Type*} [Field k] [Field L] [CommRing A]
  [Algebra k L] [Algebra k A] [Algebra.IsAlgebraic k L] (x : L ⊗[k] A) :
  ∃ S : Finset (L ⊗[k] A), ∀ σ : L →ₐ[k] L, (Algebra.TensorProduct.map σ (AlgHom.id k A)) x ∈ S := by
  induction x using TensorProduct.induction_on with
  | zero =>
    use {0}
    intro σ; simp
  | tmul l a =>
    let P := minpoly k l
    let roots := (P.map (algebraMap k L)).roots.toFinset
    let S := roots.image (fun r => r ⊗ₜ[k] a)
    use S
    intro σ
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have h1 : σ l ∈ roots := by
      simp_all [roots, P, true, (minpoly.ne_zero (Algebra.IsIntegral.isIntegral _))]
    exact Finset.mem_image_of_mem (fun r => r ⊗ₜ[k] a) h1
  | add x y hx hy =>
    rcases hx with ⟨Sx, hx⟩
    rcases hy with ⟨Sy, hy⟩
    use Finset.image₂ (· + ·) Sx Sy
    intro σ
    rw [map_add]
    exact Finset.mem_image₂_of_mem (hx σ) (hy σ)

lemma exists_algEquiv_of_roots {k L : Type*} [Field k] [Field L] [Algebra k L] [IsAlgClosed L] [Algebra.IsAlgebraic k L]
  (r1 r2 : L) (h_minpoly : minpoly k r1 = minpoly k r2) :
  ∃ σ : L ≃ₐ[k] L, σ r1 = r2 := by
  have hr2 : aeval r2 (minpoly k r1) = 0 := by
    rw [h_minpoly]
    exact minpoly.aeval k r2
  convert (IntermediateField.exists_algHom_of_splits_of_aeval ( _) (@hr2)).elim fun and x => (by_contra fun and' => _)
  · norm_num[IsAlgClosed.splits_codomain,(Algebra.IsIntegral.isIntegral)]
  · refine and' ⟨.ofBijective and (Algebra.IsAlgebraic.algHom_bijective _), x⟩

noncomputable def get_y_fun (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    [Algebra.IsSeparable k k'] (s : L ⊗[k] A) : k' :=
  if h : s ∈ I_rel k k' A L then
    Classical.choose (exists_primitive_of_I_rel k k' A L s h)
  else 0

lemma get_y_spec (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    [Algebra.IsSeparable k k'] (s : L ⊗[k] A) (h : s ∈ I_rel k k' A L) :
  s ∈ Ideal.span { u_elem k k' A L (get_y_fun k k' A L s) } := by
  rw [get_y_fun, dif_pos h]
  exact Classical.choose_spec (exists_primitive_of_I_rel k k' A L s h)

lemma lift_comp_S_to_base_change
    (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L] :
    (lift_to_S k k' A L).toRingHom.comp (S_to_base_change k k' A L) = RingHom.id (S_ring k k' A L) := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
    change (lift_to_S k k' A L) ((S_to_base_change k k' A L) (Ideal.Quotient.mk _ (l ⊗ₜ[k] a))) = Ideal.Quotient.mk _ (l ⊗ₜ[k] a)
    have hc : (S_to_base_change k k' A L) (Ideal.Quotient.mk _ (l ⊗ₜ[k] a)) = l ⊗ₜ[k'] a := by
      change (base_change_map k k' A L) (l ⊗ₜ[k] a) = l ⊗ₜ[k'] a
      dsimp [base_change_map]
      simp
    rw [hc]
    have hc2 : (lift_to_S k k' A L) (l ⊗ₜ[k'] a) = fL_hom k k' A L l * fA_hom k k' A L a := rfl
    rw [hc2]
    have h2 : fL_hom k k' A L l = Ideal.Quotient.mk (I_rel k k' A L) (l ⊗ₜ[k] (1 : A)) := rfl
    have h3 : fA_hom k k' A L a = Ideal.Quotient.mk (I_rel k k' A L) ((1 : L) ⊗ₜ[k] a) := rfl
    rw [h2, h3]
    change Ideal.Quotient.mk (I_rel k k' A L) (l ⊗ₜ[k] 1 * 1 ⊗ₜ[k] a) = Ideal.Quotient.mk (I_rel k k' A L) (l ⊗ₜ[k] a)
    congr 1
    exact Algebra.TensorProduct.tmul_mul_tmul l (1 : L) (1 : A) a |>.trans (by rw [mul_one, one_mul])
  | add x y hx hy =>
    simp only [map_add]
    rw [hx, hy]

lemma x_in_I_rel_of_base_change_zero (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    (x : L ⊗[k] A) (hx : base_change_map k k' A L x = 0) :
    x ∈ I_rel k k' A L := by
  have h_S : (S_to_base_change k k' A L) (Ideal.Quotient.mk (I_rel k k' A L) x) = 0 := hx
  have h_comp : (lift_to_S k k' A L).toRingHom ((S_to_base_change k k' A L) (Ideal.Quotient.mk (I_rel k k' A L) x)) = (lift_to_S k k' A L).toRingHom 0 := by rw [h_S]
  rw [map_zero] at h_comp
  have h_id : (lift_to_S k k' A L).toRingHom ((S_to_base_change k k' A L) (Ideal.Quotient.mk (I_rel k k' A L) x)) = Ideal.Quotient.mk (I_rel k k' A L) x := by
    have h_hom := RingHom.congr_fun (lift_comp_S_to_base_change k k' A L) (Ideal.Quotient.mk (I_rel k k' A L) x)
    exact h_hom
  rw [h_id] at h_comp
  exact Ideal.Quotient.eq_zero_iff_mem.mp h_comp

lemma nilpotent_mem_I_rel (k k' A L : Type*) [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    (h_red : IsReduced (L ⊗[k'] A)) (z : L ⊗[k] A) (hz : IsNilpotent z) :
    z ∈ I_rel k k' A L := by
  have hz_map : IsNilpotent ((base_change_map k k' A L) z) := hz.map _
  have h_zero : (base_change_map k k' A L) z = 0 := IsReduced.eq_zero _ hz_map
  exact x_in_I_rel_of_base_change_zero k k' A L z h_zero

lemma h_sep_roots_lemma {k L : Type*} [Field k] [Field L] [Algebra k L]
  (P : k[X]) (h_sep : P.Separable) (l_roots : List L) (hl : l_roots = (P.map (algebraMap k L)).roots.toList) :
  (l_roots.map (fun r => (X : L[X]) - C r)).prod.Separable := by
  norm_num [*]
  apply(h_sep.map.of_dvd) (prod_multiset_X_sub_C_dvd _)

lemma h_aeval_lemma {k k' A L : Type*} [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    (Y : k') (P : k[X]) (hP_monic : P.Monic) (hP_eval : aeval Y P = 0) (l_roots : List L) (hl : l_roots = (P.map (algebraMap k L)).roots.toList)
    [IsAlgClosed L] :
    aeval ((1 : L) ⊗ₜ[k] algebraMap k' A Y) (l_roots.map (fun r => (X : L[X]) - C r)).prod = 0 := by
  norm_num[aeval_eq_sum_range,eval_eq_sum_range,hl,funext_iff]at hP_eval⊢
  replace hP_eval:eval (algebraMap k' L Y) (P.map (algebraMap _ _))=0 := by_contra fun and=>absurd (eq_prod_roots_of_monic_of_splits_id (IsAlgClosed.splits (P.map (algebraMap k L)))) (and ∘? _)
  · have:=(P.map (algebraMap k L)).eq_prod_roots_of_monic_of_splits_id
    norm_num[eval_multiset_prod, Algebra.smul_def, this (IsAlgClosed.splits ( _)) (hP_monic.map _)▸eval_map _ _] at hP_eval⊢
    norm_num[aeval_eq_sum_range,funext_iff]at*
    use this (IsAlgClosed.splits _) hP_monic▸by_contra fun and=>absurd (congr_arg (algebraMap k' A) (hP_eval)) (and ∘? _)
    norm_num+contextual[←IsScalarTower.algebraMap_apply,←this (IsAlgClosed.splits _) hP_monic▸natDegree_map_eq_of_injective (algebraMap k L).injective P,TensorProduct.sum_tmul, Algebra.smul_def]
    norm_num[TensorProduct.smul_tmul',funext_iff,Algebra.algebraMap_eq_smul_one]
    norm_num[TensorProduct.smul_tmul,←TensorProduct.sum_tmul]
    use (by norm_num[TensorProduct.tmul_sum]) ∘congr_arg (TensorProduct.tmul k (1:L))
  · use@fun j=>(eval_map _ _).trans (.trans (by norm_num[eval₂_eq_sum_range, Algebra.smul_def,←IsScalarTower.algebraMap_apply] ) (congr_arg (algebraMap k' L) (hP_eval) |>.trans ( RingHom.map_zero _) ) )

lemma h_P_r_lemma {k L : Type*} [Field k] [Field L] [Algebra k L]
  (P : k[X]) (l_roots : List L) (hl : l_roots = (P.map (algebraMap k L)).roots.toList) (r : L) (hr : r ∈ l_roots) :
  aeval r P = 0 := by
  simp_all[aeval_def, true,eval_map]

lemma h_inv_lemma {k L A : Type*} [Field k] [Field L] [CommRing A]
  [Algebra k L] [Algebra k A] (σ : L ≃ₐ[k] L) (x : L ⊗[k] A) :
  x = (Algebra.TensorProduct.map (σ.symm : L →ₐ[k] L) (AlgHom.id k A)) ((Algebra.TensorProduct.map (σ : L →ₐ[k] L) (AlgHom.id k A)) x) := by
  exact (symm (by induction x with simp_all))

lemma h_map_u_lemma {k k' A L : Type*} [Field k] [Field k'] [CommRing A] [Field L]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    (Y : k') (σ : L ≃ₐ[k] L) (r : L) (h_sig : σ r = algebraMap k' L Y) :
    (Algebra.TensorProduct.map (σ.symm : L →ₐ[k] L) (AlgHom.id k A)) (u_elem k k' A L Y) = r ⊗ₜ[k] (1 : A) - (1 : L) ⊗ₜ[k] algebraMap k' A Y := by
  norm_num[u_elem, Algebra.algebraMap_eq_smul_one,←σ.symm_apply_eq,←by valid,TensorProduct.sub_tmul]

lemma ideal_span_singleton_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x y : R) (h : x ∈ Ideal.span {y}) :
  f x ∈ Ideal.span {f y} := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp h
  rw [map_mul]
  exact Ideal.mem_span_singleton'.mpr ⟨f a, rfl⟩

lemma rev_dir_reduced
    (k' : Type u) (A : Type v) [Field k'] [CommRing A]
    [Algebra k k'] [Algebra.IsSeparable k k'] [Algebra k' A] [Algebra k A]
    [IsScalarTower k k' A] (L : Type*) [Field L] [Algebra k L] [Algebra k' L] [IsScalarTower k k' L]
    [IsAlgClosure k' L]
    (h_red_L_A_k' : IsReduced (L ⊗[k'] A)) : IsReduced (L ⊗[k] A) := by
  constructor
  rintro x ⟨n, hn⟩
  have isAlg_k : Algebra.IsAlgebraic k k' := isAlgebraic_of_isSeparable k k'
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed k'
  have isAlg_L : Algebra.IsAlgebraic k L := isAlgClosure_of_isAlgebraic L k' |>.isAlgebraic
  have hn_nil : IsNilpotent x := ⟨n, hn⟩

  obtain ⟨S, hS⟩ := finite_conjugates_aux x
  let L_y := (S.toList).map (get_y_fun k k' A L)

  obtain ⟨Y, hY⟩ := exists_primitive_element_of_list k k' L_y

  have h_sigma : ∀ σ : L →ₐ[k] L, (Algebra.TensorProduct.map σ (AlgHom.id k A)) x ∈ Ideal.span { u_elem k k' A L Y } := by
    intro σ
    let s := (Algebra.TensorProduct.map σ (AlgHom.id k A)) x
    have hs_S : s ∈ S := hS σ
    have hs_I : s ∈ I_rel k k' A L := nilpotent_mem_I_rel k k' A L h_red_L_A_k' s (hn_nil.map _)
    have hs_span := get_y_spec k k' A L s hs_I
    have hy_mem : get_y_fun k k' A L s ∈ L_y := List.mem_map.mpr ⟨s, Finset.mem_toList.mpr hs_S, rfl⟩
    rcases hY (get_y_fun k k' A L s) hy_mem with ⟨Q, hQ⟩
    have h_span2 := mem_ideal_span_of_poly k k' A L Y Q
    have h_eq : get_y_fun k k' A L s = aeval Y Q := hQ
    have h_eq2 : u_elem k k' A L (get_y_fun k k' A L s) = u_elem k k' A L (aeval Y Q) := by rw [h_eq]
    rw [h_eq2] at hs_span
    have h_sub : Ideal.span { u_elem k k' A L (aeval Y Q) } ≤ Ideal.span { u_elem k k' A L Y } := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h_span2)
    exact h_sub hs_span

  let P := minpoly k Y
  let l_roots := (P.map (algebraMap k L)).roots.toList
  have h_sep : P.Separable := Algebra.IsSeparable.isSeparable k Y
  have hP_monic : P.Monic := minpoly.monic (isAlg_k.isAlgebraic Y).isIntegral
  have hP_eval : aeval Y P = 0 := minpoly.aeval k Y
  have h_sep_roots : (l_roots.map (fun r => (X : L[X]) - C r)).prod.Separable := h_sep_roots_lemma P h_sep l_roots rfl
  have h_aeval : aeval ((1 : L) ⊗ₜ[k] algebraMap k' A Y) (l_roots.map (fun r => (X : L[X]) - C r)).prod = 0 := h_aeval_lemma Y P hP_monic hP_eval l_roots rfl

  have h_quot : ∀ r ∈ l_roots, x ∈ Ideal.span { ((1 : L) ⊗ₜ[k] algebraMap k' A Y) - (r ⊗ₜ[k] (1 : A)) } := by
    intro r hr
    have h_P_r : aeval r P = 0 := h_P_r_lemma P l_roots rfl r hr
    have h_P_Y : aeval (algebraMap k' L Y) P = 0 := by rw [Polynomial.aeval_algebraMap_apply, minpoly.aeval, map_zero]
    have h_irred : Irreducible P := minpoly.irreducible (isAlg_k.isAlgebraic Y).isIntegral
    have h_minpoly : minpoly k r = minpoly k (algebraMap k' L Y) := by
      norm_num[aeval_eq_sum_range,funext_iff]at h_P_r h_P_Y
      repeat rw [← (minpoly.eq_of_irreducible (by assumption)) (.trans (aeval_eq_sum_range _) h_P_r), (minpoly.eq_of_irreducible (by assumption)) (.trans (aeval_eq_sum_range _) h_P_Y)]
    obtain ⟨σ, hσ⟩ := exists_algEquiv_of_roots r (algebraMap k' L Y) h_minpoly
    have h_sig_x := h_sigma (σ : L →ₐ[k] L)
    have h_inv := h_inv_lemma σ x
    have h_span_inv : x ∈ Ideal.span { (Algebra.TensorProduct.map (σ.symm : L →ₐ[k] L) (AlgHom.id k A)) (u_elem k k' A L Y) } := by
      rw [h_inv]
      exact ideal_span_singleton_map ((Algebra.TensorProduct.map (σ.symm : L →ₐ[k] L) (AlgHom.id k A)).toRingHom) ((Algebra.TensorProduct.map (σ : L →ₐ[k] L) (AlgHom.id k A)) x) (u_elem k k' A L Y) h_sig_x
    have h_map_u := h_map_u_lemma (k:=k) (k':=k') (A:=A) (L:=L) Y σ r hσ
    rw [h_map_u] at h_span_inv
    have h_neg : Ideal.span { r ⊗ₜ[k] (1 : A) - (1 : L) ⊗ₜ[k] algebraMap k' A Y } = Ideal.span { ((1 : L) ⊗ₜ[k] algebraMap k' A Y) - (r ⊗ₜ[k] (1 : A)) } := by
      rw [← Ideal.span_singleton_neg]
      rw [neg_sub]
    rw [← h_neg]
    exact h_span_inv

  exact zero_of_prod_linear_aux l_roots ((1 : L) ⊗ₜ[k] algebraMap k' A Y) x h_sep_roots h_aeval h_quot

lemma rev_dir
    (k' : Type u) (A : Type v) [Field k'] [CommRing A]
    [Algebra k k'] [Algebra.IsSeparable k k'] [Algebra k' A] [Algebra k A]
    [IsScalarTower k k' A] (h : Algebra.IsGeometricallyReduced k' A) :
    Algebra.IsGeometricallyReduced k A := by
  let L := AlgebraicClosure k'
  have isAlg_k_k' := isAlgebraic_of_isSeparable k k'
  have isAlgClosure_k_L : IsAlgClosure k L := isAlgClosure_of_isAlgebraic L k'
  have h_red_L_A_k' : IsReduced (L ⊗[k'] A) := (geom_reduced_of_alg_closure k' A L).mp h
  have h_colimit : IsReduced (L ⊗[k] A) := rev_dir_reduced k' A L h_red_L_A_k'
  exact (geom_reduced_of_alg_closure k A L).mpr h_colimit

-- EVOLVE-BLOCK-END

theorem isGeometricallyReduced_iff_of_separable_algebraic
    (k' : Type u) (A : Type v) [Field k'] [CommRing A]
    [Algebra k k'] [Algebra.IsSeparable k k'] [Algebra k' A] [Algebra k A]
    [IsScalarTower k k' A] :
    Algebra.IsGeometricallyReduced k A ↔ Algebra.IsGeometricallyReduced k' A := by
  -- EVOLVE-BLOCK-START
  exact ⟨fwd_dir k' A, rev_dir k' A⟩
  -- EVOLVE-BLOCK-END
