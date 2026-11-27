import PatchRank180

set_option warningAsError true
namespace Minimal180.OddBlock
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 PrivateCore
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A connected bipartite patch with two adjacent ports is a tree in any
rooted-sparse graph. Every edge of an internal cycle would be noncritical. -/
theorem sparse_patch_tree (G : SimpleGraph V) (gc : G.Connected) (r : V) (sp : SparseAt G r)
    (S : Finset V) (x w : V) (xs : x∈S) (ws : w∈S) (xw : G.Adj x w)
    (ports : Ports G S x w) (bip : TwoColor G S) (con : (side G S).Connected) :
    (side G S).IsTree := by
  classical
  obtain ⟨T,_,tr,forced⟩ := noncritical_tree G gc r sp
  let K := side G S
  refine ⟨con,?_⟩
  intro v p cyc
  have keep : ∀ e∈p.edges, e∈(side T S).edgeSet := by
    intro e eh
    induction e using Sym2.ind with
    | _ a b =>
      have ab : K.Adj a b := p.edges_subset_edgeSet eh
      have nb : ¬K.IsBridge s(a,b) :=
        fun h => (isBridge_iff_mem_and_forall_cycle_not_mem.mp h).2 p cyc eh
      let H := G.deleteEdges {s(a.val,b.val)}
      have inc : K.deleteEdges {s(a,b)} ≤ side H S := by
        intro i j e
        obtain ⟨ij,ne⟩ := deleteEdges_adj.mp e
        apply deleteEdges_adj.mpr
        refine ⟨ij,?_⟩
        intro h
        apply ne
        apply Set.mem_singleton_iff.mpr
        apply Sym2.eq_iff.mpr
        exact (Sym2.eq_iff.mp (Set.mem_singleton_iff.mp h)).imp
          (fun k => ⟨Subtype.ext k.1,Subtype.ext k.2⟩)
          (fun k => ⟨Subtype.ext k.1,Subtype.ext k.2⟩)
      have hc : (side H S).Connected := (con.connected_delete_edge_of_not_isBridge nb).mono inc
      have eq := patch_rank G H S x w xs ws xw ports bip (G.deleteEdges_le _) (by
        intro i j e off
        apply deleteEdges_adj.mpr
        refine ⟨e,?_⟩
        intro h
        rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp h) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact off ⟨a.property,b.property⟩
        · exact off ⟨b.property,a.property⟩) (hc _ _)
      apply forced a b ab
      change bipartiteNum H≠_
      omega
  let f : side T S ↪g T := Embedding.induce _
  exact tr.IsAcyclic ((p.transfer (side T S) keep).map f.toHom) ((cyc.transfer keep).map f.injective)

omit [Fintype V] in
/-- Retraction through either surviving port shows that a patch with
adjacent ports inherits absence of cut vertices from the ambient graph. -/
theorem nocut_patch (G : SimpleGraph V) (block : NoCut G) (S : Finset V)
    (x w : V) (xs : x∈S) (ws : w∈S) (xw : G.Adj x w) (ports : Ports G S x w) :
    NoCut (side G S) := by
  classical
  intro d
  let W := ↥({d.val}ᶜ : Set V)
  let Z := ↥({d}ᶜ : Set ↥S)
  let H := G.induce ({d.val}ᶜ : Set V)
  let K := (side G S).induce ({d}ᶜ : Set ↥S)
  let t : Z := if h : w=d.val then ⟨⟨x,xs⟩,fun k => xw.ne ((congrArg Subtype.val k).trans h.symm)⟩
               else ⟨⟨w,ws⟩,fun k => h (congrArg Subtype.val k)⟩
  have terminal : t.val.val=x ∨ t.val.val=w := by
    by_cases h : w=d.val <;> simp [t,h]
  let lift (v : Z) : W := ⟨v.val.val,fun h => v.property (Subtype.ext h)⟩
  let proj (v : W) : Z := if h : v.val∈S then ⟨⟨v.val,h⟩,fun k => v.property (congrArg Subtype.val k)⟩ else t
  have inside (v : W) (h : v.val∈S) : (proj v).val.val=v.val := by simp [proj,h]
  have outside (v : W) (h : v.val∉S) : proj v=t := by simp [proj,h]
  have fixed (v : Z) : proj (lift v)=v := Subtype.ext (Subtype.ext (inside _ v.val.property))
  have atPort (a b : Z) (ha : a.val.val=x ∨ a.val.val=w) (hb : b.val.val=x ∨ b.val.val=w) :
      K.Reachable a b := by
    rcases ha with ha|ha <;> rcases hb with hb|hb
    · exact (Subtype.ext (Subtype.ext (ha.trans hb.symm)) : a=b) ▸ Reachable.refl _
    · apply Adj.reachable
      change G.Adj a.val.val b.val.val
      rw [ha,hb]
      exact xw
    · apply Adj.reachable
      change G.Adj a.val.val b.val.val
      rw [ha,hb]
      exact xw.symm
    · exact (Subtype.ext (Subtype.ext (ha.trans hb.symm)) : a=b) ▸ Reachable.refl _
  have step (i j : W) (e : H.Adj i j) : K.Reachable (proj i) (proj j) := by
    by_cases hi : i.val∈S <;> by_cases hj : j.val∈S
    · apply Adj.reachable
      change G.Adj (proj i).val.val (proj j).val.val
      rwa [inside i hi,inside j hj]
    · rw [outside j hj]
      apply atPort _ _ _ terminal
      rw [inside i hi]
      exact ports i hi j hj e
    · rw [outside i hi]
      apply atPort _ _ terminal
      rw [inside j hj]
      exact ports j hj i hi e.symm
    · rw [outside i hi,outside j hj]
  have go {i j : W} (p : H.Walk i j) : K.Reachable (proj i) (proj j) := by
    induction p with
    | nil => exact Reachable.refl _
    | cons e _ ih => exact (step _ _ e).trans ih
  intro a b
  simpa only [fixed] using go (block d.val (lift a) (lift b)).some

private theorem tree_block_small (K : SimpleGraph V) (tr : K.IsTree) (noc : NoCut K) : Fintype.card V≤2 := by
  classical
  by_contra! hn
  have low (a : V) : 2≤K.degree a := by
    obtain ⟨i,j,ai,aj,ne⟩ := block_neighbors K tr.isConnected hn noc a
    rw [←card_neighborFinset_eq_degree]
    exact one_lt_card_iff.mpr ⟨i,j,(K.mem_neighborFinset ..).mpr ai,(K.mem_neighborFinset ..).mpr aj,ne⟩
  have sum := sum_le_sum (s:=(univ:Finset V)) (fun i _ => low i)
  rw [sum_const,card_univ,smul_eq_mul,K.sum_degrees_eq_twice_card_edges] at sum
  have edges := tr.card_edgeFinset
  omega

/-- In a biconnected rooted-sparse graph a connected piece with two
adjacent ports has exactly those two vertices or is nonbipartite. -/
theorem sparse_block_odd_patch (G : SimpleGraph V) (gc : G.Connected) (block : NoCut G)
    (r : V) (sp : SparseAt G r) (S : Finset V) (x w : V) (xs : x∈S) (ws : w∈S)
    (xw : G.Adj x w) (ports : Ports G S x w) (con : (side G S).Connected) :
    S={x,w} ∨ ¬TwoColor G S := by
  classical
  by_cases bip : TwoColor G S
  · left
    symm
    apply eq_of_subset_of_card_le (insert_subset xs (singleton_subset_iff.mpr ws))
    rw [card_pair xw.ne]
    by_contra! large
    let K := side G S
    have tr := sparse_patch_tree G gc r sp S x w xs ws xw ports bip con
    have hn : 2<Fintype.card ↥S := by simpa only [Fintype.card_coe] using large
    have noc := nocut_patch G block S x w xs ws xw ports
    exact (Nat.not_lt_of_ge (tree_block_small K tr noc)) hn
  · exact Or.inr bip

#print axioms sparse_patch_tree
#print axioms nocut_patch
#print axioms sparse_block_odd_patch
end Minimal180.OddBlock
