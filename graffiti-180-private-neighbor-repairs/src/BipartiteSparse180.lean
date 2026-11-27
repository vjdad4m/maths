import CyclicRank180

set_option warningAsError true
namespace Minimal180.PrivateCore
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem full_color (G : SimpleGraph V) (h : bipartiteNum G=Fintype.card V) : TwoColor G univ := by
  obtain ⟨B,col,sz⟩ := optB G
  exact (B.card_eq_iff_eq_univ.mp (sz.trans h)) ▸ col

/-- In a sparse rank-one transition with a bipartite lower graph and a
common chord neighbor, the whole lower graph is a tree. -/
theorem bipartite_lower_tree (J : SimpleGraph V) (jc : J.Connected) (x y w r : V)
    (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (sp : SparseAt (J⊔SimpleGraph.edge x y) r) (full : bipartiteNum J=Fintype.card V)
    (drop : bipartiteNum J=bipartiteNum (J⊔SimpleGraph.edge x y)+1) : J.IsTree := by
  classical
  let G := J⊔SimpleGraph.edge x y
  obtain ⟨c,proper⟩ := (color_function J univ).mp (full_color J full)
  have diff1 := proper x (mem_univ _) w (mem_univ _) xw
  have diff2 := proper w (mem_univ _) y (mem_univ _) wy
  have same : c x=c y := by cases cx : c x <;> cases cw : c w <;> cases cy : c y <;> simp_all
  obtain ⟨T,_,tr,forced⟩ := noncritical_tree G (jc.mono le_sup_left) r sp
  refine ⟨jc,?_⟩
  intro v walk cycle
  have keep : ∀ e∈walk.edges,e∈T.edgeSet := by
    intro e eh
    induction e using Sym2.ind with
    | _ a b =>
      have ab : J.Adj a b := walk.edges_subset_edgeSet eh
      apply forced a b (Or.inl ab)
      intro crit
      let K := J.deleteEdges {s(a,b)}
      let H := G.deleteEdges {s(a,b)}
      have nb : ¬J.IsBridge s(a,b) := fun h => (isBridge_iff_mem_and_forall_cycle_not_mem.mp h).2 walk cycle eh
      have kc : K.Connected := jc.connected_delete_edge_of_not_isBridge nb
      have inc : K⊔SimpleGraph.edge x y≤H := by
        intro i j edge
        rcases edge with kept|chord
        · obtain ⟨ij,ne⟩ := deleteEdges_adj.mp kept
          exact deleteEdges_adj.mpr ⟨Or.inl ij,ne⟩
        · apply deleteEdges_adj.mpr
          refine ⟨Or.inr chord,?_⟩
          intro eq
          have ij : J.Adj i j := (show s(i,j)∈J.edgeSet from (Set.mem_singleton_iff.mp eq) ▸ ab)
          rcases ((edge_adj ..).mp chord).1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          · exact old ij
          · exact old ij.symm
      have rank : bipartiteNum H=Fintype.card V := crit.trans (drop.symm.trans full)
      obtain ⟨d,hd⟩ := (color_function H univ).mp (full_color H rank)
      have color : TwoColor (K⊔SimpleGraph.edge x y) univ := (color_function _ _).mpr
        ⟨d,fun i hi j hj edge => hd i hi j hj (inc edge)⟩
      have cp : ProperOn K univ c := fun i hi j hj edge => proper i hi j hj (J.deleteEdges_le _ edge)
      have no := (anchored_iff_cut K univ x y xy (mem_univ _) (mem_univ _) c cp same).mp color
      have reach : (within K univ).Reachable x y := (kc x y).mono
        (fun i j edge => ⟨edge,mem_univ i,mem_univ j⟩)
      exact no reach
  exact tr.IsAcyclic (walk.transfer T keep) (cycle.transfer keep)

/-- With no upper cut vertex, the bipartite-lower sparse triangle
transition is the three-vertex triangle. No equality on the leaf score and
no choice of old certificate are needed. -/
theorem bipartite_lower_triangle_order (J : SimpleGraph V) (jc : J.Connected) (hn : 2<Fintype.card V)
    (x y w r : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (block : NoCut (J⊔SimpleGraph.edge x y)) (sp : SparseAt (J⊔SimpleGraph.edge x y) r)
    (full : bipartiteNum J=Fintype.card V) (drop : bipartiteNum J=bipartiteNum (J⊔SimpleGraph.edge x y)+1) :
    ({x,y,w}:Finset V)=univ ∧ Fintype.card V=3 := by
  classical
  let G := J⊔SimpleGraph.edge x y
  let D : Finset V := {x,y,w}
  have gc : G.Connected := jc.mono le_sup_left
  have tr := bipartite_lower_tree J jc x y w r xy old xw wy sp full drop
  have edges : G.edgeFinset.card=Fintype.card V := (J.card_edgeFinset_sup_edge old xy).trans tr.card_edgeFinset
  have low (z : V) : 2≤G.degree z := by
    obtain ⟨a,b,za,zb,ne⟩ := block_neighbors G gc hn block z
    rw [←card_neighborFinset_eq_degree]
    exact one_lt_card_iff.mpr ⟨a,b,(G.mem_neighborFinset ..).mpr za,(G.mem_neighborFinset ..).mpr zb,ne⟩
  have two (z : V) : G.degree z=2 := by
    have sum : (∑ i ∈ (univ:Finset V),G.degree i)=2*Fintype.card V := by
      rw [←edges]
      simpa only [show G.fintypeEdgeSet=J.fintypeEdgeSetSup (edge x y) from Subsingleton.elim _ _] using G.sum_degrees_eq_twice_card_edges
    apply Classical.byContradiction
    intro diff
    have strict : (∑ _i ∈ (univ:Finset V), (2:ℕ)) < ∑ i ∈ univ,G.degree i :=
      sum_lt_sum (fun i _ => low i) ⟨z,mem_univ _,lt_of_le_of_ne (low z) (Ne.symm diff)⟩
    simp only [sum_const,card_univ,smul_eq_mul] at strict
    omega
  have only {i a b j : V} (ia : G.Adj i a) (ib : G.Adj i b) (ne : a≠b) (ij : G.Adj i j) : j=a ∨ j=b := by
    have inc : ({a,b}:Finset V)⊆G.neighborFinset i := insert_subset ((G.mem_neighborFinset ..).mpr ia)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr ib))
    have eq := eq_of_subset_of_card_le inc (by rw [card_neighborFinset_eq_degree,two,card_pair ne])
    have mem := (G.mem_neighborFinset ..).mpr ij
    simpa only [←eq,mem_insert,mem_singleton] using mem
  have chord : G.Adj x y := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,xy⟩)
  have a : G.Adj x w := Or.inl xw
  have b : G.Adj w y := Or.inl wy
  have closed {i j : V} (hi : i∈D) (ij : G.Adj i j) : j∈D := by
    simp only [D,mem_insert,mem_singleton] at hi ⊢
    rcases hi with rfl|rfl|rfl
    · exact Or.inr (only chord a wy.ne.symm ij)
    · rcases only chord.symm b.symm xw.ne ij with h|h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rcases only a.symm b xy ij with h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have walk {i j : V} (p : G.Walk i j) : i∈D → j∈D := by
    induction p with
    | nil => exact id
    | cons edge _ ih => exact fun hi => ih (closed hi edge)
  have all : D=univ := eq_univ_iff_forall.mpr (fun v => walk (Classical.choice (gc x v)) (mem_insert_self ..))
  have size : D.card=3 := by
    rw [show D=insert x {y,w} from rfl,card_insert_of_not_mem (by simp [xy,xw.ne]),card_pair wy.ne.symm]
  exact ⟨all,by simpa only [all,card_univ] using size⟩

#print axioms bipartite_lower_tree
#print axioms bipartite_lower_triangle_order
end Minimal180.PrivateCore
