import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice

/-!
# Written on the Wall II, conjecture 302

A connected 22-vertex graph has total domination number 8, minimum
even-distance count 6, and exactly one vertex attaining maximum
local independence in its complement. Thus the claimed bound 7 fails.

Definition 4 is local independence, not an adjacency eigenvalue;
the earlier AI Village claim was retracted on this distinction:
https://grok-ai-village-news-496089.gitlab.io/articles/opus5-wow2-302-retracted-standing-back-195
This certificate uses actual independent subsets of open neighborhoods.
Official catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti302

open Finset SimpleGraph

def IsTotalDominating {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

noncomputable def totalDominationNumber {V : Type*} (G : SimpleGraph V)
    (_ : ∃ D, IsTotalDominating G D) : ℕ :=
  sInf {k | ∃ D, IsTotalDominating G D ∧ D.card = k}

def IsLocallyIndependent {V : Type*} (G : SimpleGraph V) (v : V) (S : Finset V) : Prop :=
  (∀ a ∈ S, G.Adj v a) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬G.Adj a b

private instance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (S : Finset V) :
    Decidable (IsLocallyIndependent G v S) := by
  unfold IsLocallyIndependent
  infer_instance

noncomputable def localIndependence {V : Type*} (G : SimpleGraph V) (v : V) : ℕ :=
  sSup {n | ∃ S : Finset V, IsLocallyIndependent G v S ∧ S.card = n}

theorem exists_total_domination_of_connected {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) (hn : 1 < Fintype.card V) : ∃ D, IsTotalDominating G D := by
  refine ⟨univ, fun v => ?_⟩
  obtain ⟨w, hne⟩ := Fintype.exists_ne_of_one_lt_card hn v
  obtain ⟨p⟩ := hc.preconnected v w
  exact ⟨p.snd, mem_univ _, p.adj_snd (Walk.not_nil_of_ne hne.symm)⟩

private theorem independent_bounded {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    BddAbove {k : ℕ | ∃ S : Finset V, IsLocallyIndependent G v S ∧ S.card = k} := by
  refine ⟨Fintype.card V, ?_⟩
  rintro _ ⟨S, _, rfl⟩
  exact card_le_univ S

private theorem independent_nonempty {V : Type*} (G : SimpleGraph V) (v : V) :
    {k : ℕ | ∃ S : Finset V, IsLocallyIndependent G v S ∧ S.card = k}.Nonempty :=
  ⟨0, ∅, by simp [IsLocallyIndependent], rfl⟩

private theorem localIndependence_ge_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    {v : V} {S : Finset V} (h : IsLocallyIndependent G v S) :
    S.card ≤ localIndependence G v :=
  le_csSup (independent_bounded G v) ⟨S, h, rfl⟩

noncomputable def evenSet {V : Type*} [Fintype V] (G : SimpleGraph V) (r : V) : Finset V :=
  univ.filter fun v => G.dist r v % 2 = 0

noncomputable def minEven {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf (Set.range fun r => (evenSet G r).card)

noncomputable def localMaxVertices {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => ∀ w, localIndependence G w ≤ localIndependence G v

noncomputable def localMaxFrequency {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (localMaxVertices G).card

def Conjecture302 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (hc : G.Connected)
    (hn : 2 < Fintype.card V),
    totalDominationNumber G (exists_total_domination_of_connected hc (by omega)) ≤
      minEven G + localMaxFrequency Gᶜ

/-- Edge differences give a lower bound on distance. Parents with label one
smaller supply walks attaining the bound and also certify connectivity. -/
private theorem certified_distances {V : Type*} {G : SimpleGraph V} (r : V) (label : V → ℕ)
    (root_zero : label r = 0)
    (step : ∀ u v, G.Adj u v → label v ≤ label u + 1)
    (parent : ∀ v, v ≠ r → ∃ w, G.Adj w v ∧ label w + 1 = label v) :
    G.Connected ∧ ∀ v, G.dist r v = label v := by
  have routes (v : V) : ∃ p : G.Walk r v, p.length = label v := by
    generalize h : label v = n
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = r
      · subst v
        exact ⟨.nil, by simpa [root_zero] using h⟩
      · obtain ⟨w, hAdj, hw⟩ := parent v hv
        obtain ⟨p, hp⟩ := ih (label w) (by omega) w rfl
        exact ⟨p.append hAdj.toWalk, by simpa [Adj.toWalk, hp] using hw.trans h⟩
  have hconn : G.Connected := (connected_iff_exists_forall_reachable G).mpr
    ⟨r, fun v => by obtain ⟨p, _⟩ := routes v; exact p.reachable⟩
  have label_bound {u v : V} (p : G.Walk u v) : label v ≤ label u + p.length := by
    induction p with
    | nil => simp
    | @cons a b c h p ih =>
      have hs := step a b h
      simp only [Walk.length_cons]
      omega
  refine ⟨hconn, fun v => ?_⟩
  obtain ⟨p, hp⟩ := routes v
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist r v
  have hl := G.dist_le p
  have hr := label_bound q
  omega

set_option maxRecDepth 8192
set_option maxHeartbeats 15000000

abbrev Vertex := Fin 22

/-- The central clique is {1,4,6,9,11,14,16,19,21}.
For each five-vertex group (y,b,x,z,s), the extra edges are
0-y, y-1, y-b, b-x, b-z, and z-s. -/
private def row (v : Vertex) : ℕ :=
  #[135300, 2841300, 11, 52, 2705994, 72, 2705970, 259, 1664, 2705746, 2304, 2704978, 8195, 53248, 2697810, 73728, 2673234, 262147, 1703936, 2443858, 2359296, 1657426][v.val]!

private def edge (u v : Vertex) : Prop := (row u).testBit v.val = true

private instance : DecidableRel edge := fun _ _ =>
  inferInstanceAs (Decidable (_ = (true : Bool)))

def graph : SimpleGraph Vertex where
  Adj := edge
  symm := by
    change ∀ u v, edge u v → edge v u
    decide
  loopless := by
    change ∀ u, ¬edge u u
    decide

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel edge)

instance : DecidableRel graphᶜ.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ ¬graph.Adj u v))

private def distanceLabel (r v : Vertex) : ℕ :=
  let labels : Array ℕ := #[
    #[0, 2, 1, 2, 3, 3, 3, 1, 2, 3, 3, 3, 1, 2, 3, 3, 3, 1, 2, 3, 3, 3],
    #[2, 0, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1],
    #[1, 1, 0, 1, 2, 2, 2, 2, 3, 2, 3, 2, 2, 3, 2, 3, 2, 2, 3, 2, 3, 2],
    #[2, 2, 1, 0, 1, 1, 2, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2],
    #[3, 1, 2, 1, 0, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1],
    #[3, 2, 2, 1, 2, 0, 1, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2],
    #[3, 1, 2, 2, 1, 1, 0, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1],
    #[1, 1, 2, 3, 2, 3, 2, 0, 1, 2, 2, 2, 2, 3, 2, 3, 2, 2, 3, 2, 3, 2],
    #[2, 2, 3, 3, 2, 3, 2, 1, 0, 1, 1, 2, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2],
    #[3, 1, 2, 2, 1, 2, 1, 2, 1, 0, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1],
    #[3, 2, 3, 3, 2, 3, 2, 2, 1, 2, 0, 1, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2],
    #[3, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 0, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1],
    #[1, 1, 2, 3, 2, 3, 2, 2, 3, 2, 3, 2, 0, 1, 2, 2, 2, 2, 3, 2, 3, 2],
    #[2, 2, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2, 1, 0, 1, 1, 2, 3, 3, 2, 3, 2],
    #[3, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 0, 2, 1, 2, 2, 1, 2, 1],
    #[3, 2, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2, 2, 1, 2, 0, 1, 3, 3, 2, 3, 2],
    #[3, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 0, 2, 2, 1, 2, 1],
    #[1, 1, 2, 3, 2, 3, 2, 2, 3, 2, 3, 2, 2, 3, 2, 3, 2, 0, 1, 2, 2, 2],
    #[2, 2, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2, 1, 0, 1, 1, 2],
    #[3, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 0, 2, 1],
    #[3, 2, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2, 2, 1, 2, 0, 1],
    #[3, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 0]][r.val]!
  labels[v.val]!

private theorem label_zero : ∀ r : Vertex, distanceLabel r r = 0 := by
  decide

private theorem label_step : ∀ r u v : Vertex,
    graph.Adj u v → distanceLabel r v ≤ distanceLabel r u + 1 := by
  decide

private theorem label_parent : ∀ r v : Vertex, v ≠ r →
    ∃ w : Vertex, graph.Adj w v ∧ distanceLabel r w + 1 = distanceLabel r v := by
  decide

private theorem distance_cert (r : Vertex) :
    graph.Connected ∧ ∀ v, graph.dist r v = distanceLabel r v :=
  certified_distances r (distanceLabel r) (label_zero r) (label_step r) (label_parent r)

theorem connected : graph.Connected := (distance_cert 0).1

private def evenLabels (r : Vertex) : Finset Vertex :=
  univ.filter fun v => distanceLabel r v % 2 = 0

private theorem evenSet_eq (r : Vertex) : evenSet graph r = evenLabels r := by
  ext v
  simp [evenSet, evenLabels, (distance_cert r).2 v]

theorem root_even_set : evenSet graph 0 = {0,1,3,8,13,18} := by
  rw [evenSet_eq]
  decide

theorem minEven_eq_six : minEven graph = 6 := by
  apply le_antisymm
  · have hcard : (evenSet graph 0).card = 6 := by rw [root_even_set]; decide
    exact Nat.sInf_le ⟨0, hcard⟩
  · have hlower : ∀ r : Vertex, 6 ≤ (evenLabels r).card := by decide
    have hnonempty : (Set.range fun r => (evenSet graph r).card).Nonempty :=
      ⟨_, 0, rfl⟩
    obtain ⟨r, hr⟩ := Nat.sInf_mem hnonempty
    change (evenSet graph r).card = minEven graph at hr
    rw [← hr, evenSet_eq]
    exact hlower r

private def centralClique : Finset Vertex := {1,4,6,9,11,14,16,19,21}

private theorem centralClique_card : centralClique.card = 9 := by decide

private theorem outside_degree : ∀ v : Vertex, v ∉ centralClique → graph.degree v ≤ 4 := by
  decide

private theorem clique_covers : ∀ v : Vertex, v ≠ 0 →
    ∃ w ∈ centralClique, graph.Adj v w := by
  decide

private theorem adjacent_of_locallyIndependent {v : Vertex} {S : Finset Vertex}
    (hS : IsLocallyIndependent graphᶜ v S) {a b : Vertex}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) : graph.Adj a b := by
  by_contra hnot
  exact hS.2 a ha b hb hab ((compl_adj graph a b).mpr ⟨hab, hnot⟩)

private theorem small_if_outside {v : Vertex} {S : Finset Vertex}
    (hS : IsLocallyIndependent graphᶜ v S) {a : Vertex} (ha : a ∈ S)
    (haout : a ∉ centralClique) : S.card ≤ 5 := by
  have hsub : S.erase a ⊆ graph.neighborFinset a := by
    intro b hb
    obtain ⟨hne, hmem⟩ := mem_erase.mp hb
    exact (mem_neighborFinset graph a b).mpr
      (adjacent_of_locallyIndependent hS ha hmem hne.symm)
  have hb := card_le_card hsub
  rw [card_neighborFinset_eq_degree] at hb
  have hn := outside_degree a haout
  have hcard := card_erase_add_one ha
  omega

private theorem localIndependence_root : localIndependence graphᶜ 0 = 9 := by
  apply le_antisymm
  · apply csSup_le (independent_nonempty graphᶜ 0)
    rintro _ ⟨S, hS, rfl⟩
    by_cases hsub : S ⊆ centralClique
    · simpa only [centralClique_card] using card_le_card hsub
    · obtain ⟨a, ha, hout⟩ := Finset.not_subset.mp hsub
      exact (small_if_outside hS ha hout).trans (by decide)
  · have hclique : IsLocallyIndependent graphᶜ 0 centralClique := by decide
    simpa only [centralClique_card] using localIndependence_ge_card hclique

private theorem localIndependence_nonroot (v : Vertex) (hv : v ≠ 0) :
    localIndependence graphᶜ v ≤ 8 := by
  apply csSup_le (independent_nonempty graphᶜ v)
  rintro _ ⟨S, hS, rfl⟩
  by_cases hsub : S ⊆ centralClique
  · obtain ⟨w, hw, hadj⟩ := clique_covers v hv
    have hnot : w ∉ S := fun h => ((compl_adj graph v w).mp (hS.1 w h)).2 hadj
    have hsubset : S ⊆ centralClique.erase w := by
      intro a ha
      exact mem_erase.mpr ⟨fun h => hnot (h ▸ ha), hsub ha⟩
    have hcard := card_erase_add_one hw
    have hC := centralClique_card
    have hle := card_le_card hsubset
    omega
  · obtain ⟨a, ha, hout⟩ := Finset.not_subset.mp hsub
    exact (small_if_outside hS ha hout).trans (by decide)

theorem localMaxVertices_eq : localMaxVertices graphᶜ = {0} := by
  classical
  ext v
  simp only [localMaxVertices, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h
    by_contra hn
    have hlow := h 0
    rw [localIndependence_root] at hlow
    have hhigh := localIndependence_nonroot v hn
    omega
  · rintro rfl w
    by_cases hw : w = 0
    · subst w
      exact le_rfl
    · rw [localIndependence_root]
      exact (localIndependence_nonroot w hw).trans (by decide)

theorem localMaxFrequency_eq_one : localMaxFrequency graphᶜ = 1 := by
  rw [localMaxFrequency, localMaxVertices_eq, card_singleton]

def dominatingSet : Finset Vertex := {3,4,7,8,12,13,17,18}

private theorem dominatingSet_total : IsTotalDominating graph dominatingSet := by
  unfold IsTotalDominating
  decide

theorem totalDomination_exists : ∃ D, IsTotalDominating graph D :=
  ⟨dominatingSet, dominatingSet_total⟩

private def packing (i : Fin 8) : Vertex := #[3,5,8,10,13,15,18,20][i.val]!

private theorem packing_disjoint :
    ∀ i j, i ≠ j → ∀ u, ¬ (graph.Adj (packing i) u ∧ graph.Adj (packing j) u) := by
  decide

theorem totalDomination_eq_eight : totalDominationNumber graph totalDomination_exists = 8 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨dominatingSet, dominatingSet_total, by decide⟩
  · change 8 ≤ sInf {k : ℕ | ∃ D, IsTotalDominating graph D ∧ D.card = k}
    have he : {k : ℕ | ∃ D, IsTotalDominating graph D ∧ D.card = k}.Nonempty :=
      ⟨8, dominatingSet, dominatingSet_total, by decide⟩
    obtain ⟨D, hD, hcard⟩ := Nat.sInf_mem he
    rw [← hcard]
    choose f hf hAdj using fun i => hD (packing i)
    let toDom (i : Fin 8) : ↥D := ⟨f i, hf i⟩
    have hinj : Function.Injective toDom := by
      intro i j hij
      by_contra hne
      have heq : f i = f j := congrArg Subtype.val hij
      exact packing_disjoint i j hne (f i) ⟨hAdj i, heq.symm ▸ hAdj j⟩
    simpa using Fintype.card_le_of_injective toDom hinj

theorem disprove302 : ¬Conjecture302 := by
  intro h
  have hbound := h Vertex graph connected (by decide)
  rw [totalDomination_eq_eight, minEven_eq_six, localMaxFrequency_eq_one] at hbound
  omega

#print axioms root_even_set
#print axioms minEven_eq_six
#print axioms localIndependence_root
#print axioms localMaxFrequency_eq_one
#print axioms totalDomination_eq_eight
#print axioms disprove302

end Graffiti302
