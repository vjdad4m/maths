import SparseBlocks180
import TriangleDefect180
import TriangleCut180

set_option warningAsError true
namespace Minimal180.PrivateCore
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A single shortest-path tree contains every edge whose deletion fails to
increase the largest induced bipartite order of the rooted-sparse graph. -/
theorem noncritical_tree (G : SimpleGraph V) (gc : G.Connected) (r : V) (sp : SparseAt G r) :
    ∃ T≤G, T.IsTree ∧ ∀ a b, G.Adj a b →
      bipartiteNum (G.deleteEdges {s(a,b)})≠bipartiteNum G+1 → T.Adj a b := by
  classical
  let f (a : V) := if h : a=r then r else (Graffiti169.exists_predecessor G gc r a h).choose
  have pred (a : V) (ne : a≠r) : G.Adj a (f a) ∧ G.dist a r=G.dist (f a) r+1 := by
    simpa [f,ne] using (Graffiti169.exists_predecessor G gc r a ne).choose_spec
  obtain ⟨T,tg,tr,_,take,_⟩ := predecessor_tree G gc r false f pred
  have forced (a b : V) (arc : Arc G r a b) : T.Adj a b := by
    have br : b≠r := by
      intro e
      have d := arc.2.1
      rw [e,dist_self] at d
      omega
    have eq := arc.2.2 (f b) (pred b br).1.symm (pred b br).2
    exact eq ▸ (take b br).symm
  refine ⟨T,tg,tr,?_⟩
  intro a b edge nc
  by_cases arc : Arc G r a b
  · exact forced a b arc
  by_cases rev : Arc G r b a
  · exact (forced b a rev).symm
  exact (nc (sp a b edge arc rev)).elim

/-- Removing every edge of any cyclic subgraph strictly increases bipartite
order. Extra edges may also be removed. The lower bound applies to each
same-vertex subgraph H edge-disjoint from the indicated cyclic subgraph. -/
theorem cyclic_deletion_gain (G H K : SimpleGraph V) (gc : G.Connected) (r : V) (sp : SparseAt G r)
    (hg : H≤G) (kg : K≤G) (apart : ∀ {a b},K.Adj a b → ¬H.Adj a b) (cycle : ¬K.IsAcyclic) :
    bipartiteNum G < bipartiteNum H := by
  classical
  obtain ⟨T,_,tr,all⟩ := noncritical_tree G gc r sp
  by_contra! small
  have kt : K≤T := by
    intro a b e
    apply all a b (kg e)
    have sub : H≤G.deleteEdges {s(a,b)} := by
      intro i j edge
      apply deleteEdges_adj.mpr
      refine ⟨hg edge,?_⟩
      intro eq
      rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp eq) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact apart e edge
      · exact apart e edge.symm
    have bound := rank_antitone (G.deleteEdges {s(a,b)}) sub
    omega
  apply cycle
  intro v walk simple
  exact tr.IsAcyclic (walk.mapLe kt) (simple.mapLe kt)

/-- In a rooted-sparse triangle transition, a cyclic old core forces at
least two vertices to be missing from every upper induced bipartite set.
In fact removing its internal edges strictly increases bipartite order and
still leaves the chord triangle. -/
theorem cyclic_core_rank_gap (J : SimpleGraph V) (jc : J.Connected) (C : Finset V)
    (x y w r : V) (xy : x≠y) (xw : J.Adj x w) (wy : J.Adj w y)
    (tip : NeedsTip J C (univ\C) x y) (sp : SparseAt (J⊔SimpleGraph.edge x y) r)
    (cycle : ¬(within J (univ\C)).IsAcyclic) :
    let G := J⊔SimpleGraph.edge x y
    let H := G.deleteEdges (within J (univ\C)).edgeSet
    bipartiteNum G<bipartiteNum H ∧ bipartiteNum H<Fintype.card V := by
  classical
  let S := univ\C
  let K := within J S
  let G := J⊔SimpleGraph.edge x y
  let H := G.deleteEdges K.edgeSet
  have xs : x∉S := fun h => (mem_sdiff.mp h).2 tip.1
  have ws : w∉S := fun h => tip.2.2.2.1 ⟨w,h,xw⟩
  have keep (a b : V) (e : G.Adj a b) (out : a∉S) : H.Adj a b :=
    deleteEdges_adj.mpr ⟨e,fun h => out ((show K.Adj a b from h).2.1)⟩
  have chord : G.Adj x y := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,xy⟩)
  have up := cyclic_deletion_gain G H K (jc.mono le_sup_left) r sp (G.deleteEdges_le _)
    (fun _ _ e => Or.inl e.1) (fun e h => (deleteEdges_adj.mp h).2 e) cycle
  obtain ⟨B,col,size⟩ := optB H
  obtain ⟨i,_,out⟩ := Finset.not_subset.mp (triangle_excluded H B col x y w
    (keep x y chord xs) (keep w y (Or.inl wy) ws).symm (keep x w (Or.inl xw) xs).symm)
  have sub : B⊂univ := Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,fun h => out (h ▸ mem_univ i)⟩
  have bound := card_lt_card sub
  rw [card_univ] at bound
  exact ⟨up,size ▸ bound⟩

/-- A cyclic subgraph costs one additional bipartization deletion beyond
any packing of vertex-disjoint nonbipartite sets in an edge-disjoint
subgraph. The two subgraphs are allowed to share vertices. -/
theorem cyclic_obstruction_packing (G H K : SimpleGraph V) (gc : G.Connected) (r : V) (sp : SparseAt G r)
    (hg : H≤G) (kg : K≤G) (apart : ∀ {a b},K.Adj a b → ¬H.Adj a b) (cycle : ¬K.IsAcyclic)
    (sets : Finset (Finset V)) (dis : (sets:Set (Finset V)).PairwiseDisjoint id)
    (bad : ∀ D∈sets, ¬TwoColor H D) :
    bipartiteNum G+sets.card+1≤Fintype.card V := by
  classical
  have up := cyclic_deletion_gain G H K gc r sp hg kg apart cycle
  obtain ⟨B,col,top⟩ := optB H
  obtain ⟨c,proper⟩ := (color_function H B).mp col
  have miss (D : Finset V) (hd : D∈sets) : ∃ a∈D,a∉B := by
    apply Finset.not_subset.mp
    intro sub
    apply bad D hd
    exact (color_function H D).mpr ⟨c,fun i hi j hj e => proper i (sub hi) j (sub hj) e⟩
  let f (D : Finset V) := if h : D∈sets then (miss D h).choose else r
  have spec (D : Finset V) (hd : D∈sets) : f D∈D ∧ f D∉B := by
    simpa [f,hd] using (miss D hd).choose_spec
  have card : sets.card≤(univ\B).card := by
    apply card_le_card_of_injOn f (fun D hd => mem_sdiff.mpr ⟨mem_univ _,(spec D hd).2⟩)
    intro D hd E he eq
    by_contra ne
    exact (disjoint_left.mp (dis hd he ne)) (spec D hd).1 (eq ▸ (spec E he).1)
  have sum := card_sdiff_add_card_eq_card (subset_univ B)
  rw [card_univ] at sum
  omega

#print axioms cyclic_obstruction_packing

#print axioms noncritical_tree
#print axioms cyclic_deletion_gain
#print axioms cyclic_core_rank_gap
end Minimal180.PrivateCore
