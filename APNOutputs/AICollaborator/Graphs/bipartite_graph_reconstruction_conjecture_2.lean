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


open SimpleGraph Finset Classical

noncomputable section

-- Vertex type
variable {V : Type*} [Fintype V] [DecidableEq V]
-- Bipartite graph
variable (G : SimpleGraph V)
variable (leftU rightV : Finset V)
variable (hBipartite : G.IsBipartiteWith leftU rightV)

abbrev edgeCount (G : SimpleGraph V) : ℕ := Nat.card G.edgeSet

/-- Strict bipartite isomorphism that explicitly preserves the left and right partitions. -/
structure BipartiteIso (G H : SimpleGraph V) (leftU rightV : Finset V) extends G ≃g H where
  -- The isomorphism maps the left partition to the left partition
  map_left : ∀ v, v ∈ leftU ↔ toEquiv v ∈ leftU
  -- The isomorphism maps the right partition to the right partition
  map_right : ∀ v, v ∈ rightV ↔ toEquiv v ∈ rightV

-- Deleting the incidence set of a vertex keeps the graph bipartite with the same partitions.
lemma isBipartiteWith_deleteIncidenceSet (v : V)
    (hBipartite : G.IsBipartiteWith leftU rightV) :
    (G.deleteIncidenceSet v).IsBipartiteWith leftU rightV := by
    -- Proof found by Gemini: IsBipartiteWith is a conjunction of Disjoint and an adjacency implication.
    -- Since deleteIncidenceSet removes edges (it forms a subgraph), adjacency transfers over.
  obtain ⟨h_disj, h_adj⟩ := hBipartite
  exact ⟨h_disj, fun a b hab => h_adj (SimpleGraph.deleteIncidenceSet_le G v hab)⟩

/-- Deck of a bipartite graph.
Deck is the multiset of all vertex-deleted subgraphs  viewed unlabeled up to bipartite isomorphism. -/
def bipartiteDeck : Multiset (Set (SimpleGraph V)) :=
  Multiset.map
    -- NOTE: deleteIncidenceSet removes the edges incident to one vertex from the edge set,
    -- but it doesn't remove the vertex itself
    (fun v => {H : SimpleGraph V | Nonempty (BipartiteIso H (G.deleteIncidenceSet v) leftU rightV)})
    (univ : Finset V).val

/-
The neighbor-degree profile of x ∈ U ⊔ V is the multiset P(x) = {deg_G(y) : y ∈ Neighbors(x)}
-/
def degreeProfile (x : V) : Multiset ℕ :=
  (G.neighborFinset x).val.map (G.degree ·)

/-
The type of x is τ(x) = (deg_G(x), P(x))
-/
def τ (x : V) : ℕ × Multiset ℕ :=
  (G.degree x, degreeProfile G x)

/-
The typecount R(u, t) is the number of neighbors of u in rightV whose type τ equals t.
Symmetrically, R'(v, s) is the number of neighbors of v in leftU whose type τ equals s.
-/
def R (u : V) (t : ℕ × Multiset ℕ) : ℕ :=
  ((G.neighborFinset u).filter (fun v => v ∈ rightV ∧ τ G v = t)).card

def R' (v : V) (s : ℕ × Multiset ℕ) : ℕ :=
  ((G.neighborFinset v).filter (fun u => u ∈ leftU ∧ τ G u = s)).card

/-
The double deck is D_2(G) = {G - x - y := x ≠ y ∈ U ⊔ V} viewed unlabeled up t bipartite isomorphism.
-/
def doubleDeck : Multiset (Set (SimpleGraph V)) :=
  Multiset.map
    (fun p : V × V =>
      {H : SimpleGraph V |
        Nonempty (BipartiteIso H ((G.deleteIncidenceSet p.1).deleteIncidenceSet p.2) leftU rightV)})
    (Finset.filter (fun p : V × V => p.1 ≠ p.2) Finset.univ).val

-- EVOLVE-BLOCK-START

lemma multiset_map_eq_implies_bij {α β : Type*} [Fintype α] (f g : α → β)
    (h : Multiset.map f (Finset.univ : Finset α).val = Multiset.map g (Finset.univ : Finset α).val) :
    ∃ (e : α ≃ α), ∀ a, f a = g (e a) := by
  let' := Finset.all_card_le_biUnion_card_iff_exists_injective (@ { x | (g x =f ·) ·})
  replace:= this.mp fun and=> (and.card_eq_sum_card_fiberwise fun and' => and.mem_image_of_mem (f))▸(? _)
  · exact this.elim fun and(A) =>⟨.ofBijective and A.1.bijective_of_finite, A.elim (by norm_num+contextual)⟩
  trans∑ a ∈ (and.image f), Finset.card {x | (g x) = a}
  · refine Finset.sum_le_sum fun a s=>(Finset.card_mono (and.filter_subset_filter (@_) and.subset_univ)).trans_eq (by linear_combination2 (norm:=norm_num[ Finset.univ])congr_arg ↑(·.map (if· = a then(1)else 0) |>.sum) (h ) )
  · exact ( Finset.card_biUnion fun and _ _ _ _=> Finset.disjoint_filter.2 (by bound)).ge.trans ( Finset.card_mono fun and=>by·norm_num[eq_comm])

def BipartiteIso_refl (G : SimpleGraph V) (leftU rightV : Finset V) :
    BipartiteIso G G leftU rightV :=
  { RelIso.refl G.Adj with
    map_left := fun _ => Iff.rfl,
    map_right := fun _ => Iff.rfl }

def BipartiteIso_symm {G H : SimpleGraph V} {leftU rightV : Finset V}
    (iso : BipartiteIso G H leftU rightV) : BipartiteIso H G leftU rightV :=
  { iso.toRelIso.symm with
    map_left := fun v => by
      have h := iso.map_left (iso.toEquiv.symm v)
      simp only [Equiv.apply_symm_apply] at h
      exact h.symm
    map_right := fun v => by
      have h := iso.map_right (iso.toEquiv.symm v)
      simp only [Equiv.apply_symm_apply] at h
      exact h.symm }

lemma BipartiteIso_edgeCount {G H : SimpleGraph V} {leftU rightV : Finset V}
    (iso : BipartiteIso G H leftU rightV) : edgeCount G = edgeCount H := by
  rcases @iso with ⟨ ⟨⟩⟩
  delta edgeCount
  refine Nat.card_congr (.subtypeEquiv ⟨.map (‹V ≃V›),.map (Equiv.symm (by assumption)), fun and=>by cases and with norm_num, fun and=>by cases and with norm_num⟩ (by cases. with norm_num[*]))

lemma edgeCount_deleteIncidenceSet (v : V) [DecidableRel G.Adj] :
    edgeCount (G.deleteIncidenceSet v) = edgeCount G - G.degree v := by
  norm_num[edgeCount, false, SimpleGraph.degree, G.neighborFinset_eq_filter, true,SimpleGraph.deleteIncidenceSet]
  norm_num[SimpleGraph.incidenceSet, false, Finset.filter_not, Finset.card_sdiff]
  simp_all[ Finset.filter_not, Finset.card_sdiff, Finset.filter_congr fun and=>imp_iff_right ∘_]
  refine (congr_arg _) ((congr_arg ↑_ (Finset.ext fun x => Finset.mem_inter.trans (?_))).trans ( Finset.card_image_of_injOn (show Function.Injective (s(v, · ) ) from fun and=> by aesop).injOn) )
  use (by cases x with| h x y=>cases Sym2.mem_iff.1<| Finset.mem_filter.1 ·.1|>.2 with simp_all[Exists.intro x, G.adj_comm,Exists.intro y]), by aesop

noncomputable def classEdgeCount (S : Set (SimpleGraph V)) : ℕ :=
  sInf {n | ∃ H ∈ S, edgeCount H = n}

lemma classEdgeCount_eq (v : V) :
    classEdgeCount {H : SimpleGraph V | Nonempty (BipartiteIso H (G.deleteIncidenceSet v) leftU rightV)} =
    edgeCount (G.deleteIncidenceSet v) := by
  delta classEdgeCount edgeCount SimpleGraph.deleteIncidenceSet
  use IsLeast.csInf_eq ⟨⟨ _,?_, rfl⟩,Set.forall_mem_image.mpr fun and ⟨a⟩ =>? _,⟩
  · repeat constructor
    swap
    use fun and=>show _ ↔RelIso.toEquiv (1) and ∈_ from .rfl
    bound
  · rcases(a)
    cases‹_ ≃r_›
    use Nat.card_le_card_of_injective (fun⟨A, B⟩=>⟨A.map ‹V ≃V›.symm,by cases A with use (by norm_num[←‹∀ (x _),_›] ∘(.)) B⟩) fun and=>?_
    norm_num [Sym2.map.injective ↑( fun and=> _)|>.eq_iff,and.eq_iff]

lemma bipartiteDeck_edgeCountDeck {G H : SimpleGraph V}
    (h : bipartiteDeck G leftU rightV = bipartiteDeck H leftU rightV) :
    Multiset.map classEdgeCount (bipartiteDeck G leftU rightV) =
    Multiset.map classEdgeCount (bipartiteDeck H leftU rightV) := by
  rw [h]

lemma sum_edgeCount_deleteIncidenceSet (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v : V, edgeCount (G.deleteIncidenceSet v) = Fintype.card V * edgeCount G - 2 * edgeCount G := by
  norm_num [edgeCount, two_mul, SimpleGraph.deleteIncidenceSet, false,Nat.eq_div_of_mul_eq_right ( _) G.sum_degrees_eq_twice_card_edges.symm, false,SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  norm_num [SimpleGraph.incidenceSet,←two_mul,Nat.eq_sub_of_add_eq ( Finset.card_sdiff_add_card_inter _ _)]
  use(Fintype.sum_congr _ _ fun and=> Finset.card_filter _ _).trans ( Finset.sum_comm.trans (.trans ( Finset.sum_congr rfl fun R M=>? _) (( Finset.sum_const (Fintype.card V-2)).trans (by simp_all[tsub_mul,mul_comm (Finset.card _),]))))
  cases R with use(Finset.card_filter _ _).symm.trans ( ((congr_arg _) (Finset.ext (by simp_all))).trans (.trans ( Finset.card_compl _) ((congr_arg _) (Finset.card_pair (Set.mem_toFinset.1 M).ne))))

lemma sum_classEdgeCount_deck (G : SimpleGraph V) (leftU rightV : Finset V) :
    (Multiset.map classEdgeCount (bipartiteDeck G leftU rightV)).sum =
    ∑ v : V, edgeCount (G.deleteIncidenceSet v) := by
  have h_map : Multiset.map classEdgeCount (bipartiteDeck G leftU rightV) =
      Multiset.map (fun v => edgeCount (G.deleteIncidenceSet v)) (univ : Finset V).val := by
    unfold bipartiteDeck
    rw [Multiset.map_map]
    congr 1
    funext v
    exact classEdgeCount_eq G leftU rightV v
  have h_sum : (Multiset.map (fun v => edgeCount (G.deleteIncidenceSet v)) (univ : Finset V).val).sum =
      ∑ v : V, edgeCount (G.deleteIncidenceSet v) := by
    exact (Finset.sum_eq_multiset_sum (univ : Finset V) (fun v => edgeCount (G.deleteIncidenceSet v))).symm
  rw [h_map, h_sum]

lemma multiset_sum_eq {G H : SimpleGraph V} (leftU rightV : Finset V)
    (h : bipartiteDeck G leftU rightV = bipartiteDeck H leftU rightV) :
    (Multiset.map classEdgeCount (bipartiteDeck G leftU rightV)).sum =
    (Multiset.map classEdgeCount (bipartiteDeck H leftU rightV)).sum := by
  rw [h]

lemma bipartiteDeck_determines_edgeCount {G H : SimpleGraph V} (hV : Fintype.card V ≥ 3)
    (h : bipartiteDeck G leftU rightV = bipartiteDeck H leftU rightV) :
    edgeCount G = edgeCount H := by
  have h1 := multiset_sum_eq leftU rightV h
  have h2G := sum_classEdgeCount_deck G leftU rightV
  have h2H := sum_classEdgeCount_deck H leftU rightV
  have h3G : ∑ v : V, edgeCount (G.deleteIncidenceSet v) = Fintype.card V * edgeCount G - 2 * edgeCount G := sum_edgeCount_deleteIncidenceSet G
  have h3H : ∑ v : V, edgeCount (H.deleteIncidenceSet v) = Fintype.card V * edgeCount H - 2 * edgeCount H := sum_edgeCount_deleteIncidenceSet H
  rw [h2G, h3G] at h1
  rw [h2H, h3H] at h1
  have h_card : Fintype.card V - 2 > 0 := by use(2).sub_pos_of_lt hV
  have h_mul_G : Fintype.card V * edgeCount G - 2 * edgeCount G = (Fintype.card V - 2) * edgeCount G := by rw [←Nat.sub_mul]
  have h_mul_H : Fintype.card V * edgeCount H - 2 * edgeCount H = (Fintype.card V - 2) * edgeCount H := by rw [←Nat.sub_mul]
  rw [h_mul_G, h_mul_H] at h1
  exact Nat.eq_of_mul_eq_mul_left h_card h1

def degreeMultiset (G : SimpleGraph V) : Multiset ℕ :=
  Multiset.map (fun v => G.degree v) (univ : Finset V).val

lemma deck_edgeCounts_eq {G H : SimpleGraph V}
    (h : bipartiteDeck G leftU rightV = bipartiteDeck H leftU rightV) :
    Multiset.map (fun v => edgeCount (G.deleteIncidenceSet v)) (univ : Finset V).val =
    Multiset.map (fun v => edgeCount (H.deleteIncidenceSet v)) (univ : Finset V).val := by
  have hG : Multiset.map classEdgeCount (bipartiteDeck G leftU rightV) =
            Multiset.map (fun v => edgeCount (G.deleteIncidenceSet v)) (univ : Finset V).val := by
    unfold bipartiteDeck
    rw [Multiset.map_map]
    congr 1
    funext v
    exact classEdgeCount_eq G leftU rightV v
  have hH : Multiset.map classEdgeCount (bipartiteDeck H leftU rightV) =
            Multiset.map (fun v => edgeCount (H.deleteIncidenceSet v)) (univ : Finset V).val := by
    unfold bipartiteDeck
    rw [Multiset.map_map]
    congr 1
    funext v
    exact classEdgeCount_eq H leftU rightV v
  rw [←hG, ←hH, h]

lemma degreeMultiset_eq_map_edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] :
    degreeMultiset G = Multiset.map (fun v => edgeCount G - edgeCount (G.deleteIncidenceSet v)) (univ : Finset V).val := by
  delta edgeCount degreeMultiset SimpleGraph.deleteIncidenceSet SimpleGraph.degree
  norm_num[SimpleGraph.deleteEdges,SimpleGraph.neighborFinset_eq_filter, Fintype.card_subtype]
  refine Multiset.map_congr rfl fun and x =>Nat.eq_sub_of_add_eq' ?_
  simp_all[Sym2.forall,SimpleGraph.incidenceSet,← Finset.card_sdiff_add_card_inter {a| a ∈_} {M|M ∈ G.incidenceSet and}, Finset.inter_comm, Finset.sdiff_eq_inter_compl]
  exact (congr_arg₂ _) ((by rw [ Finset.filter_and])) (Finset.card_bij (fun A B=>s(and, A)) (by simp_all) ( by aesop) (Sym2.ind (by simp_all[ G.ne_of_adj, G.adj_comm, or_imp])))

lemma bipartiteDeck_determines_degreeMultiset {G H : SimpleGraph V} (hV : Fintype.card V ≥ 3)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : bipartiteDeck G leftU rightV = bipartiteDeck H leftU rightV) :
    degreeMultiset G = degreeMultiset H := by
  have heG : degreeMultiset G = Multiset.map (fun v => edgeCount G - edgeCount (G.deleteIncidenceSet v)) (univ : Finset V).val := degreeMultiset_eq_map_edgeCount G
  have heH : degreeMultiset H = Multiset.map (fun v => edgeCount H - edgeCount (H.deleteIncidenceSet v)) (univ : Finset V).val := degreeMultiset_eq_map_edgeCount H
  have hec : edgeCount G = edgeCount H := bipartiteDeck_determines_edgeCount leftU rightV hV h
  have h_counts := deck_edgeCounts_eq leftU rightV h
  have h_map : Multiset.map (fun v => edgeCount G - edgeCount (G.deleteIncidenceSet v)) (univ : Finset V).val =
               Multiset.map (fun x => edgeCount G - x) (Multiset.map (fun v => edgeCount (G.deleteIncidenceSet v)) (univ : Finset V).val) := by
    rw[ Multiset.map_map,Function.comp_def]
  have h_map_H : Multiset.map (fun v => edgeCount H - edgeCount (H.deleteIncidenceSet v)) (univ : Finset V).val =
               Multiset.map (fun x => edgeCount H - x) (Multiset.map (fun v => edgeCount (H.deleteIncidenceSet v)) (univ : Finset V).val) := by
    exact (.symm (Multiset.map_map _ _ _))
  rw [heG, heH, h_map, h_map_H, hec, h_counts]

lemma degreeMultiset_eq_of_bipartiteIso {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (leftU rightV : Finset V)
    (iso : BipartiteIso G H leftU rightV) :
    degreeMultiset G = degreeMultiset H := by
  rcases ↑iso with ⟨ ⟨⟩⟩
  norm_num[degreeMultiset, *]
  exact Multiset.map_map _ _ _ |>.symm.trans (congr_arg _ (Multiset.map_univ_val_equiv (by assumption))) |>.subst (Multiset.map_congr rfl fun and x => Finset.card_equiv (by assumption) (by norm_num[*]))

lemma degree_deleteIncidenceSet {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (v u : V) [DecidableRel G.Adj] :
  (G.deleteIncidenceSet v).degree u = if v = u then 0 else if G.Adj v u then G.degree u - 1 else G.degree u := by
  norm_num[SimpleGraph.degree, false,SimpleGraph.neighborFinset_eq_filter, false,SimpleGraph.deleteIncidenceSet]
  norm_num [SimpleGraph.incidenceSet, G.adj_comm v]
  use if a:v = u then by aesop else if I:_ then (if_neg a▸if_pos I▸.trans (congr_arg _ (by aesop)) ( Finset.card_erase_of_mem (by simp_all:v ∈_)))else (if_neg a▸if_neg I▸congr_arg _ (by aesop))

lemma count_degreeMultiset (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    Multiset.count k (degreeMultiset G) = (univ.filter (fun x => G.degree x = k)).card := by
  delta degree Multiset.count degreeMultiset
  norm_num[Multiset.countP_map _,←Multiset.toFinset_card_of_nodup (Finset.univ.nodup.filter _),comm (a:=k),Multiset.filter_map]
  congr
  congr!

lemma count_degreeMultiset_del (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (k : ℕ) :
    Multiset.count k (degreeMultiset (G.deleteIncidenceSet v)) = (univ.filter (fun x => (G.deleteIncidenceSet v).degree x = k)).card := by
  delta degreeMultiset
  norm_num[Multiset.count_map _,←Multiset.toFinset_card_of_nodup (Finset.univ.nodup.filter _),id]
  simp_rw [comm]
  congr!

lemma count_degreeProfile_eq (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (k : ℕ) :
    Multiset.count k (degreeProfile G v) = ((G.neighborFinset v).filter (fun x => G.degree x = k)).card := by
  delta degreeProfile
  norm_num[Multiset.count_map _,←Multiset.toFinset_card_of_nodup (( Finset.nodup @_).filter _),id]
  simp_rw [comm]
  congr!

lemma sum_indicator_eq (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (k : ℕ) :
  ((G.neighborFinset v).filter (fun x => G.degree x = k)).card +
  (univ.filter (fun x => (G.deleteIncidenceSet v).degree x = k)).card +
  (if G.degree v = k then 1 else 0) =
  (univ.filter (fun x => G.degree x = k)).card +
  ((G.neighborFinset v).filter (fun x => G.degree x = k + 1)).card +
  (if k = 0 then 1 else 0) := by
  push_cast[SimpleGraph.degree, true,SimpleGraph.neighborFinset_eq_filter, true, Finset.card_filter, true,← Finset.sum_erase_add _ _ ↑( Finset.mem_univ v)]
  norm_num[←add_assoc, G.adj_comm,← Finset.sum_erase_add _ _ (Finset.mem_univ v),eq_comm (a:=0), Finset.sum_filter _ _]
  simp_rw [SimpleGraph.deleteIncidenceSet, Finset.card_filter, ← Finset.sum_add_distrib]
  refine(add_right_comm _ _ _).trans ((congr_arg₂ _) ((congr_arg₂ _ (( Finset.sum_congr rfl fun and x =>?_).trans Finset.sum_add_distrib) rfl ).trans (add_right_comm _ _ _)) (by simp_all[eq_comm]))
  simp_all-contextual[SimpleGraph.incidenceSet, G.adj_comm,← Finset.sum_erase_add _ _ x, Finset.sum_congr rfl]
  exact (.trans (by rw [ Finset.filter_congr fun and=>and_iff_left ∘by simp_all[comm]]) (by aesop))

lemma count_degreeMultiset_deleteIncidenceSet_add {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (d : ℕ) :
  Multiset.count d (degreeMultiset (G.deleteIncidenceSet v)) + (if G.degree v = d then 1 else 0) + Multiset.count d (degreeProfile G v) =
  (if d = 0 then 1 else 0) + Multiset.count (d + 1) (degreeProfile G v) + Multiset.count d (degreeMultiset G) := by
  have h1 := count_degreeProfile_eq G v d
  have h2 := count_degreeMultiset_del G v d
  have h3 := count_degreeMultiset G d
  have h4 := count_degreeProfile_eq G v (d + 1)
  have h5 := sum_indicator_eq G v d
  omega

lemma eq_of_add_eq_add_succ (f g : ℕ → ℕ) (h : ∀ d, f d + g (d + 1) = f (d + 1) + g d)
  (h_zero : ∃ N, ∀ n ≥ N, f n = 0 ∧ g n = 0) :
  ∀ d, f d = g d := by
  refine h_zero.elim fun and R M=>(R (M +and) (le_add_self)).elim ?_
  use fun A B=>by_contra fun and' =>absurd B (A▸and.rec (Ne.symm and') fun and=>mt (by linarith! only[.,h (M+and)]))

lemma count_degreeProfile_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (v : V) (n : ℕ) (hn : n ≥ Fintype.card V) :
  Multiset.count n (degreeProfile G v) = 0 := by
  simp_all only[degreeProfile,Multiset.count_eq_zero,.≥ ·]
  exact (hn).not_gt.comp (Multiset.mem_map.1 · |>.choose_spec.right▸ G.degree_lt_card_verts _)

lemma profile_eq_of_iso {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (leftU rightV : Finset V)
    (h_degG_eq_degH : degreeMultiset G = degreeMultiset H)
    (v : V) (u : V)
    (h_deg_vu : G.degree v = H.degree u)
    (iso : BipartiteIso (G.deleteIncidenceSet v) (H.deleteIncidenceSet u) leftU rightV) :
    degreeProfile G v = degreeProfile H u := by
  have h_iso_deg : degreeMultiset (G.deleteIncidenceSet v) = degreeMultiset (H.deleteIncidenceSet u) := by
    exact degreeMultiset_eq_of_bipartiteIso leftU rightV iso
  have h_count : ∀ d, Multiset.count d (degreeProfile G v) + Multiset.count (d + 1) (degreeProfile H u) =
                      Multiset.count (d + 1) (degreeProfile G v) + Multiset.count d (degreeProfile H u) := by
    intro d
    have hG := count_degreeMultiset_deleteIncidenceSet_add G v d
    have hH := count_degreeMultiset_deleteIncidenceSet_add H u d
    have h1 : Multiset.count d (degreeMultiset (G.deleteIncidenceSet v)) = Multiset.count d (degreeMultiset (H.deleteIncidenceSet u)) := by rw [h_iso_deg]
    have h2 : (if G.degree v = d then 1 else 0) = (if H.degree u = d then 1 else 0) := by rw [h_deg_vu]
    have h3 : Multiset.count d (degreeMultiset G) = Multiset.count d (degreeMultiset H) := by rw [h_degG_eq_degH]
    omega
  let f := fun d => Multiset.count d (degreeProfile G v)
  let g := fun d => Multiset.count d (degreeProfile H u)
  have h_fg : ∀ d, f d + g (d + 1) = f (d + 1) + g d := h_count
  have h_zero : ∃ N, ∀ n ≥ N, f n = 0 ∧ g n = 0 := by
    use Fintype.card V
    intro n hn
    constructor
    · exact count_degreeProfile_eq_zero G v n hn
    · exact count_degreeProfile_eq_zero H u n hn
  have h_eq : ∀ d, f d = g d := eq_of_add_eq_add_succ f g h_fg h_zero
  apply Multiset.ext.mpr
  exact h_eq

lemma unique_isolated_of_2_connected {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (h2 : G.Connected ∧ ∀ v, (G.induce {x | x ≠ v}).Connected) (hV : Fintype.card V ≥ 3)
  (v : V) : ∀ x : V, (G.deleteIncidenceSet v).degree x = 0 ↔ x = v := by
  simp_all -contextual [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, SimpleGraph.deleteIncidenceSet, Finset.ext_iff]
  use fun and=>⟨fun x =>by_contra fun and' => if a: Finset.univ={and,v} then(? _)else(? _),by simp_all[SimpleGraph.incidenceSet]⟩
  · simp_all[ Fintype.card]
  use a (Finset.ext fun R=>by_contra fun andK=>((h2.2 R) ⟨and, andK ∘ (by norm_num[.])⟩ ⟨v, andK ∘ (by norm_num[.])⟩).elim fun and=>? _)
  cases and with |nil=>contradiction |cons=>_
  simp_all[SimpleGraph.incidenceSet]
  cases h2.1 and R
  induction‹_› with|nil=>norm_num at andK | cons=>_
  contrapose! h2
  norm_num[SimpleGraph.connected_iff_exists_forall_reachable, Ne.symm and']at andK⊢
  use fun and k=>⟨v,fun A B=>by_contra fun and=>?_⟩
  use and ⟨_, and',(·.symm.trans (not_not.1 (and ⟨_, andK.2,.⟩))|>.elim (by cases. with|nil=>bound|cons M=>use(x _ M).elim (Ne.symm and') (Ne.symm (by bound))))⟩

lemma iso_maps_isolated {V : Type*} [Fintype V] [DecidableEq V]
  (G1 G2 : SimpleGraph V) (leftU rightV : Finset V)
  (iso : BipartiteIso G1 G2 leftU rightV)
  (x y : V)
  (hx : ∀ z, G1.degree z = 0 ↔ z = x)
  (hy : ∀ z, G2.degree z = 0 ↔ z = y) :
  iso.toEquiv x = y := by
  rcases iso with ⟨⟨⟩⟩
  exact (hy _).1 (( Finset.card_equiv (by valid) (by norm_num[*])).symm.trans.comp (hx _).2 rfl )

lemma f_preserves_partitions {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) (leftU rightV : Finset V)
  (hG_2_conn : G.Connected ∧ ∀ v, (G.induce {x | x ≠ v}).Connected)
  (hH_2_conn : H.Connected ∧ ∀ v, (H.induce {x | x ≠ v}).Connected)
  (hV : Fintype.card V ≥ 3)
  (f : V ≃ V)
  (hf_iso : ∀ v, Nonempty (BipartiteIso (G.deleteIncidenceSet v) (H.deleteIncidenceSet (f v)) leftU rightV)) :
  (∀ v, v ∈ leftU ↔ f v ∈ leftU) ∧ (∀ v, v ∈ rightV ↔ f v ∈ rightV) := by
  have h_left : ∀ v, v ∈ leftU ↔ f v ∈ leftU := by
    intro v
    have iso := Classical.choice (hf_iso v)
    have h_eq : iso.toEquiv v = f v := by
      apply iso_maps_isolated (G.deleteIncidenceSet v) (H.deleteIncidenceSet (f v)) leftU rightV iso v (f v)
      · intro z; convert unique_isolated_of_2_connected G hG_2_conn hV v z
      · intro z; convert unique_isolated_of_2_connected H hH_2_conn hV (f v) z
    have h_iso_left := iso.map_left v
    rw [h_eq] at h_iso_left
    exact h_iso_left
  have h_right : ∀ v, v ∈ rightV ↔ f v ∈ rightV := by
    intro v
    have iso := Classical.choice (hf_iso v)
    have h_eq : iso.toEquiv v = f v := by
      apply iso_maps_isolated (G.deleteIncidenceSet v) (H.deleteIncidenceSet (f v)) leftU rightV iso v (f v)
      · intro z; convert unique_isolated_of_2_connected G hG_2_conn hV v z
      · intro z; convert unique_isolated_of_2_connected H hH_2_conn hV (f v) z
    have h_iso_right := iso.map_right v
    rw [h_eq] at h_iso_right
    exact h_iso_right
  exact ⟨h_left, h_right⟩

lemma connected_of_induce_connected {V : Type*} [Fintype V] [DecidableEq V]
  (H : SimpleGraph V) (hV : Fintype.card V ≥ 3)
  (h2 : ∀ v, (H.induce {x | x ≠ v}).Connected) :
  H.Connected := by
  convert H.connected_iff_exists_forall_reachable.mpr ((isEmpty_or_nonempty _).elim fun and=>by simp_all fun ⟨a⟩=> ⟨a, (if R:· = a then R▸by rw []else _)⟩)
  by_cases h: ( Finset.univ={by assumption, a})
  · simp_all[ Fintype.card]
  · exact ( Finset.exists_of_ssubset (Finset.ssubset_univ_iff.2 (Ne.symm h))).elim fun and x =>(h2 and ⟨a,x.2 ∘by norm_num+contextual⟩ ⟨ _,x.2 ∘ Finset.mem_insert.2 ∘.inl ∘symm⟩).map ⟨Subtype.val,by bound⟩

lemma unique_isolated_mapped {V : Type*} [Fintype V] [DecidableEq V]
  (G1 G2 : SimpleGraph V) [DecidableRel G1.Adj] [DecidableRel G2.Adj] (iso : G1 ≃g G2) (v1 v2 : V)
  (h1 : ∀ x, G1.degree x = 0 ↔ x = v1)
  (h2_iso : G2.degree v2 = 0) :
  iso v1 = v2 := by
  rcases @iso
  norm_num[←(h1 (‹V ≃V›.symm v2)).1 (by exact h2_iso▸ Finset.card_equiv (by valid) (by norm_num[←by valid]))]

lemma deleteIncidenceSet_induce_connected {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) (v u : V)
  (hG_conn : (G.induce {x | x ≠ v}).Connected) (hV : Fintype.card V ≥ 3)
  (iso : G.deleteIncidenceSet v ≃g H.deleteIncidenceSet u)
  (h_iso_vu : iso v = u) :
  (H.induce {x | x ≠ u}).Connected := by
  delta SimpleGraph.deleteIncidenceSet Ne at *
  norm_num[SimpleGraph.deleteEdges,SimpleGraph.connected_iff_exists_forall_reachable]at*
  refine h_iso_vu▸hG_conn.elim fun and⟨A, B⟩=>⟨ _,iso.injective.ne A,fun a s=>(B _ (iso.symm_apply_eq.ne.2 s)).elim fun and=>?_⟩
  rcases and
  · hint
  induction iso
  norm_num at‹ G.Adj _ _›‹∀ (x _),_›s⊢
  revert‹_ ≃V›‹ {x :V|_}›
  use fun and _ _ _ p R M=>.trans (? _) ((p.map ⟨(⟨_, and.injective.ne ·.2⟩),fun a=>?_⟩).reachable.trans (by norm_num))
  exact (SimpleGraph.Adj.reachable (by use(M.2 ⟨ R,(·.elim (by norm_num[Ne.symm A.out, Ne.symm (_: {x :V|¬x =v}).2]))⟩).1))
  use(M.2 ⟨a, a.ne ∘Subtype.eq ∘by norm_num[SimpleGraph.incidenceSet, Ne.symm (_: {x :V|¬x =v}).2]⟩).1

lemma H_is_2_connected {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V)
  (hG_2_conn : G.Connected ∧ ∀ v, (G.induce {x | x ≠ v}).Connected)
  (hV : Fintype.card V ≥ 3)
  (f : V ≃ V)
  (hf_iso : ∀ v, Nonempty (G.deleteIncidenceSet v ≃g H.deleteIncidenceSet (f v))) :
  H.Connected ∧ ∀ v, (H.induce {x | x ≠ v}).Connected := by
  have h2 : ∀ u, (H.induce {x | x ≠ u}).Connected := by
    intro u
    let v := f.symm u
    have h_iso : Nonempty (G.deleteIncidenceSet v ≃g H.deleteIncidenceSet (f v)) := hf_iso v
    have iso := Classical.choice h_iso
    have hu : f v = u := Equiv.apply_symm_apply f u
    have h_iso_u : Nonempty (G.deleteIncidenceSet v ≃g H.deleteIncidenceSet u) := by
      rw [← hu]
      exact ⟨iso⟩
    have iso_u := Classical.choice h_iso_u
    have h_iso_vu : iso_u v = u := by
      have h1 : ∀ x, (G.deleteIncidenceSet v).degree x = 0 ↔ x = v := by
        intro x
        convert unique_isolated_of_2_connected G hG_2_conn hV v x
      have h2_iso : (H.deleteIncidenceSet u).degree u = 0 := by
        let _ : DecidableRel H.Adj := Classical.decRel H.Adj
        have h_deg := degree_deleteIncidenceSet H u u
        simp only [if_true] at h_deg
        convert h_deg
      exact unique_isolated_mapped (G.deleteIncidenceSet v) (H.deleteIncidenceSet u) iso_u v u h1 h2_iso
    have h_ind_G := hG_2_conn.2 v
    exact deleteIncidenceSet_induce_connected G H v u h_ind_G hV iso_u h_iso_vu
  have h_conn : H.Connected := connected_of_induce_connected H hV h2
  exact ⟨h_conn, h2⟩

def typeDrop (t : ℕ × Multiset ℕ) (d : ℕ) : ℕ × Multiset ℕ :=
  (t.1 - 1, t.2.erase d)

def rightV_types {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (rightV : Finset V) : Multiset (ℕ × Multiset ℕ) :=
  Multiset.map (fun v => τ G v) rightV.val

lemma count_map_eq_card_filter {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β) (S : Multiset α) (x : β) :
  Multiset.count x (Multiset.map f S) = (Multiset.filter (fun y => f y = x) S).card := by
  norm_num [ Multiset.count_map]
  simp_rw [comm]

lemma multiset_eq_of_add_map_drop {α : Type*} [DecidableEq α]
  (S T : Multiset α) (drop : α → α) (deg : α → ℕ)
  (h_drop : ∀ x, deg x > 0 → deg (drop x) < deg x)
  (hS : ∀ x ∈ S, deg x > 0)
  (hT : ∀ x ∈ T, deg x > 0)
  (h_eq : S + Multiset.map drop T = T + Multiset.map drop S) :
  S = T := by
  let max_deg := (S.toFinset ∪ T.toFinset).sup deg
  have h_max_S : ∀ x ∈ S, deg x ≤ max_deg := by
    intro x hx
    apply Finset.le_sup
    exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hx)
  have h_max_T : ∀ x ∈ T, deg x ≤ max_deg := by
    intro x hx
    apply Finset.le_sup
    exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hx)
  have h_ind : ∀ n, n ≤ max_deg + 1 → ∀ x, deg x ≥ (max_deg + 1) - n → Multiset.count x S = Multiset.count x T := by
    intro n
    induction n with
    | zero =>
      intro _ x hx
      have hxS : x ∉ S := by intro h; have := h_max_S x h; omega
      have hxT : x ∉ T := by intro h; have := h_max_T x h; omega
      rw [Multiset.count_eq_zero.mpr hxS, Multiset.count_eq_zero.mpr hxT]
    | succ n ih =>
      intro hn x hx
      by_cases h_strict : deg x ≥ (max_deg + 1) - n
      · exact ih (by omega) x h_strict
      · have heq_deg : deg x = (max_deg + 1) - (n + 1) := by omega
        have h_eq_count : Multiset.count x (S + Multiset.map drop T) = Multiset.count x (T + Multiset.map drop S) := by rw [h_eq]
        rw [Multiset.count_add, Multiset.count_add] at h_eq_count
        have h_filter_eq : Multiset.filter (fun y => drop y = x) S = Multiset.filter (fun y => drop y = x) T := by
          apply Multiset.ext.mpr
          intro y
          rw [Multiset.count_filter, Multiset.count_filter]
          split_ifs with hy
          · by_cases hyS : y ∈ S
            · have hy_pos : deg y > 0 := hS y hyS
              have h_deg_y : deg (drop y) < deg y := h_drop y hy_pos
              have h_deg_y2 : deg x < deg y := by
                have h_eq_dx : deg (drop y) = deg x := congrArg deg hy
                omega
              exact ih (by omega) y (by omega)
            · by_cases hyT : y ∈ T
              · have hy_pos : deg y > 0 := hT y hyT
                have h_deg_y : deg (drop y) < deg y := h_drop y hy_pos
                have h_deg_y2 : deg x < deg y := by
                  have h_eq_dx : deg (drop y) = deg x := congrArg deg hy
                  omega
                exact ih (by omega) y (by omega)
              · have cS : Multiset.count y S = 0 := Multiset.count_eq_zero.mpr hyS
                have cT : Multiset.count y T = 0 := Multiset.count_eq_zero.mpr hyT
                omega
          · rfl
        have hcS : Multiset.count x (Multiset.map drop S) = (Multiset.filter (fun y => drop y = x) S).card := count_map_eq_card_filter drop S x
        have hcT : Multiset.count x (Multiset.map drop T) = (Multiset.filter (fun y => drop y = x) T).card := count_map_eq_card_filter drop T x
        rw [hcS, hcT, h_filter_eq] at h_eq_count
        omega
  apply Multiset.ext.mpr
  intro x
  exact h_ind (max_deg + 1) (by omega) x (by omega)

lemma tau_deleteIncidenceSet_rightV_proof {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (leftU rightV : Finset V)
  (hBipartite : G.IsBipartiteWith leftU rightV)
  (u : V) (hu : u ∈ leftU) (v : V) (hv : v ∈ rightV) :
  τ (G.deleteIncidenceSet u) v = if G.Adj u v then typeDrop (τ G v) (G.degree u) else τ G v := by
  have huv : u ≠ v := by
    obtain ⟨h_disj, _⟩ := hBipartite
    intro h
    rw [h] at hu
    exact Set.disjoint_left.mp h_disj hu hv
  unfold τ
  split_ifs with h_adj
  · unfold typeDrop
    apply Prod.ext
    · dsimp only
      let _ : DecidableRel G.Adj := Classical.decRel G.Adj
      have hdeg := degree_deleteIncidenceSet G u v
      simp only [huv, if_false, h_adj, if_true] at hdeg
      convert hdeg
    · dsimp only
      delta degreeProfile SimpleGraph.degree SimpleGraph.deleteIncidenceSet
      norm_num[SimpleGraph.deleteEdges,SimpleGraph.neighborFinset_eq_filter,SimpleGraph.incidenceSet, Finset.filter_and, Finset.filter_ne]
      simp_all[imp_iff_not_or, G.adj_comm, Finset.filter_or, Finset.filter_eq]
      cases Multiset.exists_cons_of_mem (by simp_all[h_adj.symm]:u ∈ Finset.univ.filter (G.Adj v))
      simp_all[SimpleGraph.IsBipartiteWith, G.adj_comm, Finset.inter_union_distrib_left, Finset.filter_and, Finset.filter_ne]
      convert Multiset.map_congr rfl fun and Y=>_ using 2
      · norm_num[h_adj.symm, Ne.symm huv,Multiset.ext]
        refine fun and=>not_lt.mp (absurd (congr_arg Multiset.Nodup (by assumption)) ∘? _)
        obtain ⟨rfl⟩ :=eq_or_ne (u) and
        · norm_num[Multiset.count_eq_zero.2 ∘mt (‹_›▸Multiset.mem_cons_of_mem)]
          norm_num[*,h_adj.symm]
          exact (Multiset.count_eq_zero.mpr ( absurd (‹_›▸ Finset.univ.nodup.filter _) ∘by simp_all)).trans_le bot_le
        · norm_num[‹_›,Finset.nodup]
          exact (Multiset.nodup_iff_count_le_one.mp ((‹_ = _›▸ Finset.univ.nodup.filter _).of_cons) and).not_gt.elim
      · cases hBipartite
        obtain ⟨@c⟩ :=eq_or_ne (u) and
        · simp_all[h_adj.symm]
        simp_all[mt (‹∀ R M, G.Adj R M →_› _ _),←‹_ = _›,Set.disjoint_left, Finset.inter_erase, Finset.filter_not]
        rw[ Finset.erase_eq_of_notMem (by cases‹∀ (x y _),_› _ _<|by use Finset.mem_filter.1 ·|>.2 with cases‹∀ (x y _),_› _ _ Y.symm with tauto)]
  · apply Prod.ext
    · dsimp only
      let _ : DecidableRel G.Adj := Classical.decRel G.Adj
      have hdeg := degree_deleteIncidenceSet G u v
      simp only [huv, if_false, h_adj, if_false] at hdeg
      convert hdeg
    · dsimp only
      delta degreeProfile SimpleGraph.deleteIncidenceSet Ne at*
      cases hBipartite
      convert Multiset.map_congr rfl fun and Y=>_ using 2
      · exact (congr_arg _) (Finset.ext (by cases eq_or_ne u · with ·simp_all[SimpleGraph.incidenceSet, G.adj_comm]))
      simp_all[SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter,SimpleGraph.incidenceSet,Set.disjoint_left]
      rw[ Finset.filter_congr fun and x=>and_iff_left_of_imp fun and I I=>by cases‹∀ (x y _),_› _ _ (by valid) with cases‹∀ (x y _),_› _ _ (by use Y.1.symm) with simp_all only]

lemma rightV_types_deleteIncidenceSet_map {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (leftU rightV : Finset V)
  (hBipartite : G.IsBipartiteWith leftU rightV)
  (u : V) (hu : u ∈ leftU) :
  rightV_types (G.deleteIncidenceSet u) rightV =
  Multiset.map (fun v => if G.Adj u v then typeDrop (τ G v) (G.degree u) else τ G v) rightV.val := by
  unfold rightV_types
  apply Multiset.map_congr rfl
  intro v hv
  exact tau_deleteIncidenceSet_rightV_proof G leftU rightV hBipartite u hu v hv

lemma rightV_val_eq_filter_add_sdiff {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (rightV : Finset V) (u : V) :
  rightV.val = (rightV.filter (fun v => G.Adj u v)).val + (rightV \ G.neighborFinset u).val := by
  have h_eq : rightV \ G.neighborFinset u = rightV.filter (fun v => ¬ G.Adj u v) := by
    ext x
    simp [SimpleGraph.mem_neighborFinset]
  rw [h_eq]
  exact (Multiset.filter_add_not (fun v => G.Adj u v) rightV.val).symm

def S_multiset (G : SimpleGraph V) (rightV : Finset V) (u : V) : Multiset (ℕ × Multiset ℕ) :=
  ((G.neighborFinset u).filter (fun v => v ∈ rightV)).val.map (τ G)

def T_multiset (G : SimpleGraph V) (rightV : Finset V) (u : V) : Multiset (ℕ × Multiset ℕ) :=
  (rightV \ G.neighborFinset u).val.map (τ G)

lemma rightV_types_eq_S_add_T {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (rightV : Finset V) (u : V) :
  rightV_types G rightV = S_multiset G rightV u + T_multiset G rightV u := by
  unfold rightV_types S_multiset T_multiset
  have h_val := rightV_val_eq_filter_add_sdiff G rightV u
  rw [h_val]
  rw [Multiset.map_add]
  congr 1
  · have hs1 : rightV.filter (fun v => G.Adj u v) = (G.neighborFinset u).filter (fun v => v ∈ rightV) := by
      ext x
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [hs1]

lemma rightV_types_del_eq {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (leftU rightV : Finset V)
  (hBipartite : G.IsBipartiteWith leftU rightV)
  (u : V) (hu : u ∈ leftU) :
  rightV_types (G.deleteIncidenceSet u) rightV =
  Multiset.map (fun t => typeDrop t (G.degree u)) (S_multiset G rightV u) + T_multiset G rightV u := by
  have h1 := rightV_types_deleteIncidenceSet_map G leftU rightV hBipartite u hu
  rw [h1]
  unfold S_multiset T_multiset
  have hs1 : (G.neighborFinset u).filter (fun v => v ∈ rightV) = rightV.filter (fun v => G.Adj u v) := by
    ext x
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  have ht1 : rightV \ G.neighborFinset u = rightV.filter (fun v => ¬ G.Adj u v) := by
    ext x
    simp [SimpleGraph.mem_neighborFinset]
  rw [hs1, ht1]
  have h_add := Multiset.filter_add_not (fun v => G.Adj u v) rightV.val
  conv =>
    lhs
    rw [← h_add]
  rw [Multiset.map_add]
  congr 1
  · rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro x hx
    have hx_adj : G.Adj u x := by exact (Multiset.mem_filter.mp hx).2
    simp [hx_adj]
  · apply Multiset.map_congr rfl
    intro x hx
    have hx_adj : ¬ G.Adj u x := by exact (Multiset.mem_filter.mp hx).2
    simp [hx_adj]









lemma BipartiteIso_degree_eq {V : Type*} [Fintype V] [DecidableEq V]
  {G H : SimpleGraph V} {leftU rightV : Finset V}
  (iso : BipartiteIso G H leftU rightV) (v : V) :
  G.degree v = H.degree (iso.toEquiv v) := by
  have h_map : G.neighborFinset v = (H.neighborFinset (iso.toEquiv v)).map iso.toEquiv.symm.toEmbedding := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro hx
      use iso.toEquiv x
      constructor
      · exact iso.map_rel_iff'.mpr hx
      · exact Equiv.symm_apply_apply iso.toEquiv x
    · rintro ⟨y, hy, rfl⟩
      have hy_rewritten : H.Adj (iso.toEquiv v) (iso.toEquiv (iso.toEquiv.symm y)) := by
        simp only [Equiv.apply_symm_apply]
        exact hy
      exact iso.map_rel_iff'.mp hy_rewritten
  have h1 : (G.neighborFinset v).card = G.degree v := by rfl
  have h2 : (H.neighborFinset (iso.toEquiv v)).card = H.degree (iso.toEquiv v) := by rfl
  have h3 : (G.neighborFinset v).card = (H.neighborFinset (iso.toEquiv v)).card := by
    rw [h_map, Finset.card_map]
  rw [← h1, ← h2, h3]

lemma BipartiteIso_degreeProfile_eq {V : Type*} [Fintype V] [DecidableEq V]
  {G H : SimpleGraph V} {leftU rightV : Finset V}
  (iso : BipartiteIso G H leftU rightV) (v : V) :
  degreeProfile G v = degreeProfile H (iso.toEquiv v) := by
  unfold degreeProfile
  have h_map : (G.neighborFinset v).val.map (fun x => G.degree x) = (G.neighborFinset v).val.map (fun x => H.degree (iso.toEquiv x)) := by
    apply Multiset.map_congr rfl
    intro x _
    exact BipartiteIso_degree_eq iso x
  rw [h_map]
  have h_comp : (G.neighborFinset v).val.map (fun x => H.degree (iso.toEquiv x)) = ((G.neighborFinset v).val.map iso.toEquiv).map (fun x => H.degree x) := by
    exact (Multiset.map_map (fun x => H.degree x) iso.toEquiv (G.neighborFinset v).val).symm
  rw [h_comp]
  have h_f : (G.neighborFinset v).val.map iso.toEquiv = (H.neighborFinset (iso.toEquiv v)).val := by
    have h_map_equiv : G.neighborFinset v = (H.neighborFinset (iso.toEquiv v)).map iso.toEquiv.symm.toEmbedding := by
      ext x
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map, Equiv.coe_toEmbedding]
      constructor
      · intro hx
        use iso.toEquiv x
        constructor
        · exact iso.map_rel_iff'.mpr hx
        · exact Equiv.symm_apply_apply iso.toEquiv x
      · rintro ⟨y, hy, rfl⟩
        have hy_rewritten : H.Adj (iso.toEquiv v) (iso.toEquiv (iso.toEquiv.symm y)) := by
          simp only [Equiv.apply_symm_apply]
          exact hy
        exact iso.map_rel_iff'.mp hy_rewritten
    rw [h_map_equiv]
    have h_val : ((H.neighborFinset (iso.toEquiv v)).map iso.toEquiv.symm.toEmbedding).val = Multiset.map iso.toEquiv.symm.toEmbedding (H.neighborFinset (iso.toEquiv v)).val := Finset.map_val iso.toEquiv.symm.toEmbedding (H.neighborFinset (iso.toEquiv v))
    rw [h_val]
    rw [Multiset.map_map]
    have h_id : Multiset.map (iso.toEquiv ∘ ⇑iso.toEquiv.symm.toEmbedding) (H.neighborFinset (iso.toEquiv v)).val = Multiset.map id (H.neighborFinset (iso.toEquiv v)).val := by
      apply Multiset.map_congr rfl
      intro x _
      simp only [Function.comp_apply, Equiv.coe_toEmbedding, Equiv.apply_symm_apply, id_eq]
    rw [h_id]
    exact Multiset.map_id (H.neighborFinset (iso.toEquiv v)).val
  rw [h_f]

lemma tau_eq_of_iso {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) (leftU rightV : Finset V)
  (iso : BipartiteIso G H leftU rightV) (v : V) :
  τ G v = τ H (iso.toEquiv v) := by
  unfold τ
  have h1 := BipartiteIso_degree_eq iso v
  have h2 := BipartiteIso_degreeProfile_eq iso v
  rw [h1, h2]

lemma rightV_types_eq_of_bij {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) (rightV : Finset V)
  (f : V ≃ V)
  (hf_type : ∀ v, τ G v = τ H (f v))
  (hf_right : ∀ v, v ∈ rightV ↔ f v ∈ rightV) :
  rightV_types G rightV = rightV_types H rightV := by
  unfold rightV_types
  have h_map : Multiset.map (fun v => τ G v) rightV.val = Multiset.map (fun v => τ H (f v)) rightV.val := by
    apply Multiset.map_congr rfl
    intro x _
    exact hf_type x
  rw [h_map]
  have h_comp : Multiset.map (fun v => τ H (f v)) rightV.val = Multiset.map (fun v => τ H v) (Multiset.map f rightV.val) := by
    exact (Multiset.map_map (fun v => τ H v) f rightV.val).symm
  rw [h_comp]
  have h_f : Multiset.map f rightV.val = rightV.val := by
    apply Multiset.ext.mpr
    intro x
    have h1 := count_map_eq_card_filter f rightV.val x
    rw [h1]
    by_cases hx : x ∈ rightV
    · have hx2 : f.symm x ∈ rightV := by
        have hh := hf_right (f.symm x)
        simp only [Equiv.apply_symm_apply] at hh
        exact hh.mpr hx
      have h_filter : Multiset.filter (fun y => f y = x) rightV.val = {f.symm x} := by
        apply Multiset.ext.mpr
        intro y
        rw [Multiset.count_filter]
        split_ifs with hy
        · have hy2 : y = f.symm x := by
            apply f.injective
            simp only [Equiv.apply_symm_apply]
            exact hy
          rw [hy2]
          have h_count : Multiset.count (f.symm x) rightV.val = 1 := by
            exact Multiset.count_eq_one_of_mem rightV.nodup hx2
          rw [h_count]
          exact (Multiset.count_singleton_self (f.symm x)).symm
        · have hy2 : y ≠ f.symm x := by
            intro h
            apply hy
            rw [h, Equiv.apply_symm_apply]
          have h_count1 : Multiset.count y {f.symm x} = 0 := by
            have hn : y ∉ ({f.symm x} : Multiset V) := by simp [hy2]
            exact Multiset.count_eq_zero.mpr hn
          rw [h_count1]
      rw [h_filter]
      have hc : Multiset.card {f.symm x} = 1 := Multiset.card_singleton (f.symm x)
      rw [hc]
      exact (Multiset.count_eq_one_of_mem rightV.nodup hx).symm
    · have hx2 : f.symm x ∉ rightV := by
        intro h
        have hh := hf_right (f.symm x)
        simp only [Equiv.apply_symm_apply] at hh
        exact hx (hh.mp h)
      have h_filter : Multiset.filter (fun y => f y = x) rightV.val = ∅ := by
        apply Multiset.ext.mpr
        intro y
        rw [Multiset.count_filter]
        split_ifs with hy
        · have hy2 : y = f.symm x := by
            apply f.injective
            simp only [Equiv.apply_symm_apply]
            exact hy
          rw [hy2]
          have h_count : Multiset.count (f.symm x) rightV.val = 0 := Multiset.count_eq_zero.mpr hx2
          rw [h_count]
          rfl
        · rfl
      rw [h_filter]
      have hc : Multiset.card (∅ : Multiset V) = 0 := rfl
      rw [hc]
      exact (Multiset.count_eq_zero.mpr hx).symm
  rw [h_f]

lemma rightV_types_eq_of_bipartiteIso {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) (leftU rightV : Finset V)
  (iso : BipartiteIso G H leftU rightV) :
  rightV_types G rightV = rightV_types H rightV := by
  apply rightV_types_eq_of_bij G H rightV iso.toEquiv
  · intro v
    exact tau_eq_of_iso G H leftU rightV iso v
  · exact iso.map_right

lemma rightV_types_del_eq_of_iso {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) (leftU rightV : Finset V)
  (u : V) (fu : V)
  (iso : BipartiteIso (G.deleteIncidenceSet u) (H.deleteIncidenceSet fu) leftU rightV) :
  rightV_types (G.deleteIncidenceSet u) rightV = rightV_types (H.deleteIncidenceSet fu) rightV := by
  exact rightV_types_eq_of_bipartiteIso (G.deleteIncidenceSet u) (H.deleteIncidenceSet fu) leftU rightV iso



lemma S_add_map_T_eq {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) (leftU rightV : Finset V)
  (hBipartiteG : G.IsBipartiteWith leftU rightV)
  (hBipartiteH : H.IsBipartiteWith leftU rightV)
  (f : V ≃ V)
  (hf_iso : ∀ v, Nonempty (BipartiteIso (G.deleteIncidenceSet v) (H.deleteIncidenceSet (f v)) leftU rightV))
  (hf_type : ∀ v, τ G v = τ H (f v))
  (hf_left : ∀ v, v ∈ leftU ↔ f v ∈ leftU)
  (hf_right : ∀ v, v ∈ rightV ↔ f v ∈ rightV)
  (u : V) (hu : u ∈ leftU) :
  S_multiset G rightV u + Multiset.map (fun t => typeDrop t (G.degree u)) (S_multiset H rightV (f u)) =
  S_multiset H rightV (f u) + Multiset.map (fun t => typeDrop t (G.degree u)) (S_multiset G rightV u) := by
  have h_iso_vu := Classical.choice (hf_iso u)
  have e_del := rightV_types_del_eq_of_iso G H leftU rightV u (f u) h_iso_vu
  have e_G_del := rightV_types_del_eq G leftU rightV hBipartiteG u hu
  have hu_H : f u ∈ leftU := (hf_left u).mp hu
  have e_H_del := rightV_types_del_eq H leftU rightV hBipartiteH (f u) hu_H
  have h_deg : G.degree u = H.degree (f u) := by
    have ht := hf_type u
    exact congrArg Prod.fst ht
  rw [h_deg] at e_G_del
  rw [e_G_del, e_H_del] at e_del
  have e_G := rightV_types_eq_S_add_T G rightV u
  have e_H := rightV_types_eq_S_add_T H rightV (f u)
  have e_types := rightV_types_eq_of_bij G H rightV f hf_type hf_right
  rw [e_G, e_H] at e_types
  have H1 : S_multiset G rightV u + Multiset.map (fun t => typeDrop t (H.degree (f u))) (S_multiset H rightV (f u)) + T_multiset G rightV u + T_multiset H rightV (f u) =
            S_multiset H rightV (f u) + Multiset.map (fun t => typeDrop t (H.degree (f u))) (S_multiset G rightV u) + T_multiset H rightV (f u) + T_multiset G rightV u := by
    calc
      S_multiset G rightV u + Multiset.map (fun t => typeDrop t (H.degree (f u))) (S_multiset H rightV (f u)) + T_multiset G rightV u + T_multiset H rightV (f u)
        = (S_multiset G rightV u + T_multiset G rightV u) + (Multiset.map (fun t => typeDrop t (H.degree (f u))) (S_multiset H rightV (f u)) + T_multiset H rightV (f u)) := by abel
      _ = (S_multiset H rightV (f u) + T_multiset H rightV (f u)) + (Multiset.map (fun t => typeDrop t (H.degree (f u))) (S_multiset G rightV u) + T_multiset G rightV u) := by rw [e_types, ← e_del]
      _ = S_multiset H rightV (f u) + Multiset.map (fun t => typeDrop t (H.degree (f u))) (S_multiset G rightV u) + T_multiset H rightV (f u) + T_multiset G rightV u := by abel
  have H1_comm : (S_multiset G rightV u + Multiset.map (fun t => typeDrop t (H.degree (f u))) (S_multiset H rightV (f u))) + (T_multiset G rightV u + T_multiset H rightV (f u)) =
                 (S_multiset H rightV (f u) + Multiset.map (fun t => typeDrop t (H.degree (f u))) (S_multiset G rightV u)) + (T_multiset G rightV u + T_multiset H rightV (f u)) := by
    calc
      _ = S_multiset G rightV u + Multiset.map (fun t => typeDrop t (H.degree (f u))) (S_multiset H rightV (f u)) + T_multiset G rightV u + T_multiset H rightV (f u) := by abel
      _ = S_multiset H rightV (f u) + Multiset.map (fun t => typeDrop t (H.degree (f u))) (S_multiset G rightV u) + T_multiset H rightV (f u) + T_multiset G rightV u := H1
      _ = _ := by abel
  have H2 := add_right_cancel H1_comm
  rw [← h_deg] at H2
  exact H2

lemma S_multiset_eq {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) (leftU rightV : Finset V)
  (hBipartiteG : G.IsBipartiteWith leftU rightV)
  (hBipartiteH : H.IsBipartiteWith leftU rightV)
  (f : V ≃ V)
  (hf_iso : ∀ v, Nonempty (BipartiteIso (G.deleteIncidenceSet v) (H.deleteIncidenceSet (f v)) leftU rightV))
  (hf_type : ∀ v, τ G v = τ H (f v))
  (hf_left : ∀ v, v ∈ leftU ↔ f v ∈ leftU)
  (hf_right : ∀ v, v ∈ rightV ↔ f v ∈ rightV)
  (u : V) (hu : u ∈ leftU) :
  S_multiset G rightV u = S_multiset H rightV (f u) := by
  have heq := S_add_map_T_eq G H leftU rightV hBipartiteG hBipartiteH f hf_iso hf_type hf_left hf_right u hu
  by_cases h_deg : G.degree u = 0
  · have h1 : S_multiset G rightV u = ∅ := by norm_num[S_multiset]
                                              use fun and a s=> Finset.card_ne_zero.2 ⟨and,by norm_num[a]⟩ h_deg
    have h_deg_H : H.degree (f u) = 0 := by
      have ht := hf_type u
      have ht1 : (τ G u).1 = (τ H (f u)).1 := congrArg Prod.fst ht
      exact ht1.symm.trans h_deg
    have h2 : S_multiset H rightV (f u) = ∅ := by norm_num[S_multiset]
                                                  refine fun and a s=> Finset.card_ne_zero_of_mem (by norm_num[a]:and ∈ _) h_deg_H
    rw [h1, h2]
  · apply multiset_eq_of_add_map_drop (S_multiset G rightV u) (S_multiset H rightV (f u)) (fun t => typeDrop t (G.degree u)) Prod.fst
    · intro x hx
      unfold typeDrop
      dsimp
      omega
    · intro x hx
      norm_num[S_multiset] at hx⊢
      use hx.elim fun A B=>B.2▸show 0<( _, _).1 from(? _)
      use Finset.card_pos.mpr ⟨u, (by. (norm_num [B.left.1.symm]))⟩
    · intro x hx
      norm_num[S_multiset] at hx⊢
      use hx.elim fun and (s) =>s.2▸show (0<Prod.fst (_, _)) from(? _)
      use Finset.card_pos.2 ⟨f @u,by·norm_num[s.1.1.symm]⟩
    · exact heq

def typeProfile (G : SimpleGraph V) (x : V) : Multiset (ℕ × Multiset ℕ) :=
  (G.neighborFinset x).val.map (τ G)

lemma typeProfile_eq_S {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (leftU rightV : Finset V)
  (hBipartite : G.IsBipartiteWith leftU rightV)
  (u : V) (hu : u ∈ leftU) :
  typeProfile G u = S_multiset G rightV u := by
  cases hBipartite
  delta S_multiset typeProfile
  rw [ Finset.filter_true_of_mem fun and β=>by cases‹∀ _ _ __, _› (u) and (by rwa[G.mem_neighborFinset]at β) with simp_all[Set.disjoint_left]]

lemma typeProfile_eq_S_right {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (leftU rightV : Finset V)
  (hBipartite : G.IsBipartiteWith leftU rightV)
  (v : V) (hv : v ∈ rightV) :
  typeProfile G v = S_multiset G leftU v := by
  show(id _)=((id) _)
  cases hBipartite
  rw [ Finset.filter_true_of_mem (by cases‹∀ (x y _),_› v ·<|by_contra fun and=>by norm_num[*]at. with simp_all[Set.disjoint_right])]

lemma count_typeProfile_eq_one_iff_adj {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V)
  (h_distinct : ∀ x y : V, x ≠ y → τ G x ≠ τ G y)
  (x y : V) :
  Multiset.count (τ G y) (typeProfile G x) = 1 ↔ G.Adj x y := by
  delta Ne typeProfile τ at *
  norm_num[Multiset.count_map _, Finset.nodup,Function.Injective.eq_iff (not_imp_not.1<|h_distinct · ·),ite_and]
  norm_num[ Multiset.filter_eq]
  norm_num[Multiset.count_eq_of_nodup,Finset.nodup]

lemma adjacency_preserved_left {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) (leftU rightV : Finset V)
  (f : V ≃ V)
  (h_distinct : ∀ x y : V, x ≠ y → τ G x ≠ τ G y)
  (h_tau : ∀ v, τ G v = τ H (f v))
  (h_typeProfile : ∀ u, u ∈ leftU → typeProfile G u = typeProfile H (f u))
  (x y : V) (hx : x ∈ leftU) :
  G.Adj x y ↔ H.Adj (f x) (f y) := by
  revert‹∀_, _›hx rightV
  delta τ Ne at*
  use fun and R M=>by_contra fun and=>absurd (R x M) (show id _≠(id _) from ? _)
  norm_num[τ]at*
  use and ∘ fun and=>⟨fun x =>(Multiset.mem_map.1 (and▸Multiset.mem_map.2 ⟨y,by norm_num[x], rfl⟩)).elim fun and h=>? _, fun and' =>?_⟩
  · use f.surjective and|>.elim fun and c=>by_contra (absurd (h_distinct and y) ∘ by aesop)
  · exact (Multiset.mem_map.1 (and.symm▸Multiset.mem_map.2 ⟨f y,by simp_all, rfl⟩)).elim (by cases eq_or_ne · y with simp_all)

lemma type_preserving_bijection_is_iso {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) (leftU rightV : Finset V)
  (hG_bipartite : G.IsBipartiteWith leftU rightV)
  (hH_bipartite : H.IsBipartiteWith leftU rightV)
  (hG_distinct : ∀ x y : V, x ≠ y → τ G x ≠ τ G y)
  (hG_2_conn : G.Connected ∧ ∀ v, (G.induce {x | x ≠ v}).Connected)
  (hV : Fintype.card V ≥ 3)
  (hV_parts : (univ : Finset V) = leftU ∪ rightV)
  (f : V ≃ V)
  (hf_iso : ∀ v, Nonempty (BipartiteIso (G.deleteIncidenceSet v) (H.deleteIncidenceSet (f v)) leftU rightV))
  (hf_type : ∀ v, τ G v = τ H (f v))
  (hf_left : ∀ v, v ∈ leftU ↔ f v ∈ leftU)
  (hf_right : ∀ v, v ∈ rightV ↔ f v ∈ rightV) :
  Nonempty (BipartiteIso G H leftU rightV) := by
  have h_S : ∀ u, u ∈ leftU → S_multiset G rightV u = S_multiset H rightV (f u) := by
    intro u hu
    exact S_multiset_eq G H leftU rightV hG_bipartite hH_bipartite f hf_iso hf_type hf_left hf_right u hu
  have h_typeProfile : ∀ u, u ∈ leftU → typeProfile G u = typeProfile H (f u) := by
    intro u hu
    have hu_H : f u ∈ leftU := (hf_left u).mp hu
    have e1 : typeProfile G u = S_multiset G rightV u := typeProfile_eq_S G leftU rightV hG_bipartite u hu
    have e2 : typeProfile H (f u) = S_multiset H rightV (f u) := typeProfile_eq_S H leftU rightV hH_bipartite (f u) hu_H
    rw [e1, e2, h_S u hu]
  have h_adj : ∀ x y : V, x ∈ leftU → (G.Adj x y ↔ H.Adj (f x) (f y)) := by
    intro x y hx
    exact adjacency_preserved_left G H leftU rightV f hG_distinct hf_type h_typeProfile x y hx
  have h_adj_all : ∀ u v : V, G.Adj u v ↔ H.Adj (f u) (f v) := by
    intro u v
    by_cases hu : u ∈ leftU
    · exact h_adj u v hu
    · have hu_right : u ∈ rightV := by
        have hu_univ : u ∈ (univ : Finset V) := mem_univ u
        rw [hV_parts, Finset.mem_union] at hu_univ
        exact hu_univ.resolve_left hu
      by_cases hv : v ∈ leftU
      · have h1 := h_adj v u hv
        rw [G.adj_comm, H.adj_comm]
        exact h1
      · have hv_right : v ∈ rightV := by
          have hv_univ : v ∈ (univ : Finset V) := mem_univ v
          rw [hV_parts, Finset.mem_union] at hv_univ
          exact hv_univ.resolve_left hv
        have hG_false : ¬ G.Adj u v := by
          intro h
          obtain ⟨h_disj, h_adj_G⟩ := hG_bipartite
          cases h_adj_G h with
          | inl h_l => exact (Set.disjoint_left.mp h_disj h_l.1) hu_right
          | inr h_r => exact (Set.disjoint_left.mp h_disj h_r.2) hv_right
        have hH_false : ¬ H.Adj (f u) (f v) := by
          intro h
          obtain ⟨h_disj, h_adj_H⟩ := hH_bipartite
          have fu_right : f u ∈ rightV := (hf_right u).mp hu_right
          have fv_right : f v ∈ rightV := (hf_right v).mp hv_right
          cases h_adj_H h with
          | inl h_l => exact (Set.disjoint_left.mp h_disj h_l.1) fu_right
          | inr h_r => exact (Set.disjoint_left.mp h_disj h_r.2) fv_right
        exact iff_of_false hG_false hH_false
  have h_iso : BipartiteIso G H leftU rightV := {
    toEquiv := f
    map_rel_iff' := fun {a b} => (h_adj_all a b).symm
    map_left := hf_left
    map_right := hf_right
  }
  exact ⟨h_iso⟩

-- EVOLVE-BLOCK-END

/-
Let G = (U ⊔ V, E) be a finite simple bipartite graph with |U| = u, |V| = v, n = u + v ≥ 3.
Assume:
1. G is 2-connected.
2. G is not a regular graph (the degree sequence is non-constant on U ⊔ V)
3. All vertex types are pairwise distinct
Then deck(G) determines G uniquely up to bipartite isomorphism.
-/
theorem Conjecture2
    -- G, H are finite simple bipartite graphs on at least 3 vertices.
  (V : Type*) [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) (leftU rightV : Finset V)
  (hGBipartite : G.IsBipartiteWith leftU rightV)
  (hHBipartite : H.IsBipartiteWith leftU rightV)
  (hV : Fintype.card V ≥ 3)
  (hV_parts : (univ : Finset V) = leftU ∪ rightV)
    -- G is 2-connected means G is connected, and the subgraph after removal of any vertex is still connected.
  (G_2_connected : G.Connected ∧ ∀ (v : V), (G.induce {x | x ≠ v}).Connected)
    -- G is not a regular graph
  (G_not_regular : ∀ d : ℕ, ¬ G.IsRegularOfDegree d)
  -- all vertex types are pairwise distinct
  (G_distinct_types : ∀ x y : V, x ≠ y → τ G x ≠ τ G y)
  -- then, if the bipartite decks are the same, the two graphs must be bipartite isomorphic
  : bipartiteDeck G leftU rightV = bipartiteDeck H leftU rightV → Nonempty (BipartiteIso G H leftU rightV)
  := by
  -- EVOLVE-BLOCK-START
  intro hDeck
  have h_bij' : ∃ (e : V ≃ V), ∀ v,
      (fun v => {H' : SimpleGraph V | Nonempty (BipartiteIso H' (G.deleteIncidenceSet v) leftU rightV)}) v =
      (fun v => {H' : SimpleGraph V | Nonempty (BipartiteIso H' (H.deleteIncidenceSet v) leftU rightV)}) (e v) := by
    exact multiset_map_eq_implies_bij _ _ hDeck

  have h_bij : ∃ (f : V ≃ V), ∀ v, Nonempty (BipartiteIso (G.deleteIncidenceSet v) (H.deleteIncidenceSet (f v)) leftU rightV) := by
    obtain ⟨e, he⟩ := h_bij'
    use e
    intro v
    have he_v : {H' : SimpleGraph V | Nonempty (BipartiteIso H' (G.deleteIncidenceSet v) leftU rightV)} =
                {H' : SimpleGraph V | Nonempty (BipartiteIso H' (H.deleteIncidenceSet (e v)) leftU rightV)} := he v
    have h_self : G.deleteIncidenceSet v ∈ {H' : SimpleGraph V | Nonempty (BipartiteIso H' (G.deleteIncidenceSet v) leftU rightV)} := by
      exact ⟨by repeat use by tauto⟩
    have h_in_H : G.deleteIncidenceSet v ∈ {H' : SimpleGraph V | Nonempty (BipartiteIso H' (H.deleteIncidenceSet (e v)) leftU rightV)} := by
      exact he_v ▸ h_self
    exact h_in_H

  have h_edgeCount_eq : edgeCount G = edgeCount H := bipartiteDeck_determines_edgeCount leftU rightV hV hDeck

  have h_degMultiset_eq : degreeMultiset G = degreeMultiset H :=
    bipartiteDeck_determines_degreeMultiset leftU rightV hV hDeck

  have h_deg_eq : ∀ f : V ≃ V, (∀ v, Nonempty (BipartiteIso (G.deleteIncidenceSet v) (H.deleteIncidenceSet (f v)) leftU rightV)) → ∀ v, G.degree v = H.degree (f v) := by
    intro f hf v
    let _ : DecidableRel G.Adj := Classical.decRel G.Adj
    let _ : DecidableRel H.Adj := Classical.decRel H.Adj
    have iso := Classical.choice (hf v)
    have hec_del : edgeCount (G.deleteIncidenceSet v) = edgeCount (H.deleteIncidenceSet (f v)) := BipartiteIso_edgeCount iso
    have eG := edgeCount_deleteIncidenceSet (G := G) v
    have eH := edgeCount_deleteIncidenceSet (G := H) (f v)
    simp_all only[edgeCount,degreeMultiset]
    convert(hec_del▸Nat.sub_sub_self _)▸Nat.sub_sub_self _
    · exact (h_edgeCount_eq▸Nat.card_eq_fintype_card.trans ( Fintype.card_subtype _)).ge.trans' (Finset.card_le_card_of_injOn (s(v,.)) ( fun and=>by norm_num) fun and=>by grind)
    · exact (Nat.card_eq_fintype_card.trans ( Fintype.card_subtype _)).ge.trans' (Finset.card_le_card_of_injOn (s(f v,·)) ( fun and=>by norm_num) (fun _ _ _ _=>not_imp_not.1 (by norm_num+contextual)))

  have h_profile_eq : ∀ f : V ≃ V, (∀ v, Nonempty (BipartiteIso (G.deleteIncidenceSet v) (H.deleteIncidenceSet (f v)) leftU rightV)) → ∀ v, degreeProfile G v = degreeProfile H (f v) := by
    intro f hf v
    have h_iso := hf v
    have iso := Classical.choice h_iso
    exact profile_eq_of_iso leftU rightV h_degMultiset_eq v (f v) (h_deg_eq f hf v) iso

  have h_tau_eq : ∀ f : V ≃ V, (∀ v, Nonempty (BipartiteIso (G.deleteIncidenceSet v) (H.deleteIncidenceSet (f v)) leftU rightV)) → ∀ v, τ G v = τ H (f v) := by
    intro f hf v
    unfold τ
    rw [h_deg_eq f hf v, h_profile_eq f hf v]

  have h_H_distinct_types : ∀ f : V ≃ V, (∀ v, Nonempty (BipartiteIso (G.deleteIncidenceSet v) (H.deleteIncidenceSet (f v)) leftU rightV)) → ∀ x y : V, x ≠ y → τ H x ≠ τ H y := by
    intro f hf x y hxy
    have h1 := h_tau_eq f hf (f.symm x)
    have h2 := h_tau_eq f hf (f.symm y)
    rw [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2]
    apply G_distinct_types
    intro h_eq
    apply hxy
    rw [← Equiv.apply_symm_apply f x, ← Equiv.apply_symm_apply f y]
    rw [h_eq]

  obtain ⟨e, he_iso⟩ := h_bij

  have h_H_2_conn : H.Connected ∧ ∀ v, (H.induce {x | x ≠ v}).Connected := by
    apply H_is_2_connected G H G_2_connected hV e
    intro v
    have iso := Classical.choice (he_iso v)
    exact ⟨iso.toRelIso⟩

  have h_parts := f_preserves_partitions G H leftU rightV G_2_connected h_H_2_conn hV e he_iso
  obtain ⟨hf_left, hf_right⟩ := h_parts

  have hf_type : ∀ v, τ G v = τ H (e v) := h_tau_eq e he_iso

  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  let _ : DecidableRel H.Adj := Classical.decRel H.Adj
  exact type_preserving_bijection_is_iso G H leftU rightV hGBipartite hHBipartite G_distinct_types G_2_connected hV hV_parts e he_iso hf_type hf_left hf_right
  -- EVOLVE-BLOCK-END
