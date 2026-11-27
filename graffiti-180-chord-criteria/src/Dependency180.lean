import MinimalVertex180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

def Arc (r a b : V) : Prop :=
  G.Adj a b ∧ G.dist b r=G.dist a r+1 ∧ ∀ x, G.Adj x b → G.dist b r=G.dist x r+1 → x=a

omit [Fintype V] [DecidableEq V] in
theorem remove_edge_distances (hc : G.Connected) (r a b : V)
    (ab : ¬Arc G r a b) (ba : ¬Arc G r b a) :
    let J := G.deleteEdges {s(a,b)}
    J.Connected ∧ ∀ v, J.dist v r=G.dist v r := by
  classical
  let J := G.deleteEdges {s(a,b)}
  have other (s t : V) (no : ¬Arc G r s t) (edge : G.Adj s t)
      (d : G.dist t r=G.dist s r+1) : ∃ w, G.Adj w t ∧ G.dist t r=G.dist w r+1 ∧ w≠s := by
    by_contra! h
    exact no ⟨edge,d,h⟩
  apply layers
  · exact G.dist_self
  · intro v w e
    have t := hc.dist_triangle (u:=v) (v:=w) (w:=r)
    rw [dist_eq_one_iff_adj.mpr ((G.deleteEdges_le _) e)] at t
    omega
  · intro v ne
    obtain ⟨w,e,d⟩ := Graffiti169.exists_predecessor G hc r v ne
    by_cases removed : s(v,w)=s(a,b)
    · rcases Sym2.eq_iff.mp removed with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · obtain ⟨j,je,jd,jn⟩ := other _ _ ba e.symm d
        exact ⟨j,deleteEdges_adj.mpr ⟨je.symm,by simp [Sym2.eq_iff,jn,e.ne]⟩,jd⟩
      · obtain ⟨j,je,jd,jn⟩ := other _ _ ab e.symm d
        exact ⟨j,deleteEdges_adj.mpr ⟨je.symm,by simp [Sym2.eq_iff,jn,e.ne]⟩,jd⟩
    · exact ⟨w,deleteEdges_adj.mpr ⟨e,removed⟩,d⟩

noncomputable def MaxSet (S : Finset V) : Prop := TwoColor G S ∧ S.card=bipartiteNum G

theorem optB : ∃ X, MaxSet G X := by
  classical
  obtain ⟨A,mem,eq⟩ := exists_mem_eq_sup (s:=univ.filter (TwoColor G)) (f:=card)
    ⟨∅,mem_filter.mpr ⟨mem_univ _,∅,∅,by simp,by simp,by simp [Indep],by simp [Indep]⟩⟩
  exact ⟨A,(mem_filter.mp mem).2,eq.symm⟩

theorem size_bip {X : Finset V} (h : TwoColor G X) : X.card ≤ bipartiteNum G := by
  classical exact le_sup (f:=card) (mem_filter.mpr ⟨mem_univ _,h⟩)

omit [Fintype V] [DecidableEq V] in
private theorem away {a b : V} {S : Finset V} (ok : Indep (G.deleteEdges {s(a,b)}) S)
    (miss : a∉S ∨ b∉S) : Indep G S := by
  intro v hv w hw ne e
  apply ok _ hv _ hw ne
  refine deleteEdges_adj.mpr ⟨e,?_⟩
  intro cut
  rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp cut) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact miss.elim (fun h => h hv) (fun h => h hw)
  · exact miss.elim (fun h => h hw) (fun h => h hv)

omit [Fintype V] in
private theorem trim_color (a b : V) (S : Finset V) (ok : TwoColor (G.deleteEdges {s(a,b)}) S) :
    TwoColor G (S.erase a) := by
  obtain ⟨C,D,dis,rfl,ic,id⟩ := ok
  refine ⟨C.erase a,D.erase a,dis.mono (erase_subset _ _) (erase_subset _ _),?_,?_,?_⟩
  · ext v; simp only [mem_union,mem_erase]; tauto
  · exact away G (fun x hx y hy => ic x (mem_of_mem_erase hx) y (mem_of_mem_erase hy))
      (Or.inl (not_mem_erase _ _))
  · exact away G (fun x hx y hy => id x (mem_of_mem_erase hx) y (mem_of_mem_erase hy))
      (Or.inl (not_mem_erase _ _))

/-- Each dispensable edge in an edge-minimal failed state admits a largest
two-color set upstairs excluding either chosen endpoint and including the
other. The graph with the edge removed has one more bipartite vertex. -/
theorem edge_witness (a b : V) (ab : G.Adj a b)
    (up : bipartiteNum G<bipartiteNum (G.deleteEdges {s(a,b)})) :
    bipartiteNum (G.deleteEdges {s(a,b)})=bipartiteNum G+1 ∧
      ∃ X Y, MaxSet G X ∧ MaxSet G Y ∧ a∈X ∧ b∉X ∧ a∉Y ∧ b∈Y := by
  classical
  obtain ⟨S,col,eq⟩ := optB (G.deleteEdges {s(a,b)})
  have c1 := trim_color G a b S col
  have c2 := trim_color G b a S (by rw [Sym2.eq_swap]; exact col)
  have n1 := size_bip G c1
  have n2 := size_bip G c2
  have am : a∈S := by
    by_contra no
    rw [erase_eq_of_not_mem no,eq] at n1
    omega
  have bm : b∈S := by
    by_contra no
    rw [erase_eq_of_not_mem no,eq] at n2
    omega
  have u := card_erase_add_one am
  have v := card_erase_add_one bm
  exact ⟨by omega,S.erase b,S.erase a,⟨c2,by omega⟩,⟨c1,by omega⟩,
    mem_erase.mpr ⟨ab.ne,am⟩,not_mem_erase _ _,not_mem_erase _ _,mem_erase.mpr ⟨ab.ne.symm,bm⟩⟩

theorem leaf_mono {J : SimpleGraph V} (sub : J ≤ G) (U : Finset V) :
    weightedLeaves J U≤weightedLeaves G U := by
  classical
  apply Finset.sup_le
  intro T ht
  obtain ⟨le,kt⟩ := (mem_filter.mp ht).2
  exact le_sup (f:=fun K => (U ∩ leaves K).card) (mem_filter.mpr ⟨mem_univ _,le.trans sub,kt⟩)

/-- A hypothesis on proper spanning subgraphs is supplied by minimizing
the number of edges among failed rooted states, after order minimization. -/
theorem fragile_edges (hc : G.Connected) (r : V) (odd : Bool) (A : Finset V)
    (bad : let P := parity G r odd
           weightedLeaves G (eligible A P r)+bipartiteNum G<1+A.card+P.card)
    (smaller : ∀ a b, G.Adj a b → let J := G.deleteEdges {s(a,b)}
       J.Connected → let P := parity J r odd
       1+A.card+P.card≤weightedLeaves J (eligible A P r)+bipartiteNum J)
    (a b : V) (e : G.Adj a b) (ab : ¬Arc G r a b) (ba : ¬Arc G r b a) :
    bipartiteNum (G.deleteEdges {s(a,b)})=bipartiteNum G+1 ∧
      ∃ X Y, MaxSet G X ∧ MaxSet G Y ∧ a∈X ∧ b∉X ∧ a∉Y ∧ b∈Y := by
  classical
  obtain ⟨jc,dist⟩ := remove_edge_distances G hc r a b ab ba
  have eq : parity (G.deleteEdges {s(a,b)}) r odd=parity G r odd := by
    ext v; simp only [mem_parity,dist v]
  have good := smaller a b e jc
  dsimp only at good bad
  rw [eq] at good
  have mono := leaf_mono G (G.deleteEdges_le {s(a,b)}) (eligible A (parity G r odd) r)
  exact edge_witness G a b e (by omega)

def MandatoryB (v : V) : Prop := ∀ X, MaxSet G X → v∈X

/-- A mandatory bipartite vertex with two neighbors has an outgoing
private-successor edge whenever dispensable edges admit endpoint swaps. -/
theorem next_of_mandatory (r : V) (swaps : ∀ a b, G.Adj a b → ¬Arc G r a b → ¬Arc G r b a →
      ∃ X, MaxSet G X ∧ a∉X) (v : V) (must : MandatoryB G v)
    (two : ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a≠b) : ∃ w, Arc G r v w := by
  obtain ⟨a,b,va,vb,ne⟩ := two
  have step (w : V) (e : G.Adj v w) : Arc G r v w ∨ Arc G r w v := by
    by_contra! h
    obtain ⟨X,ok,no⟩ := swaps v w e h.1 h.2
    exact no (must X ok)
  rcases step a va with h|h
  · exact ⟨a,h⟩
  rcases step b vb with k|k
  · exact ⟨b,k⟩
  exact (ne (k.2.2 a va.symm h.2.1)).elim

/-- Follow private successors until reaching a nonmandatory vertex. Every
maximum bipartite witness contains the whole prefix. A witness contains
the complete chain exactly when its last vertex can occur in an optimum. -/
theorem witness_chain (r : V) (degree : ∀ v : V, ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a≠b)
    (swaps : ∀ a b, G.Adj a b → ¬Arc G r a b → ¬Arc G r b a →
      ∃ X, MaxSet G X ∧ a∉X)
    (start : V) (must : MandatoryB G start) :
    ∃ t, ∃ p : (SimpleGraph.fromRel (fun u v => Arc G r u v)).Walk start t,
      ¬MandatoryB G t ∧ (∀ v∈p.support, v≠t → MandatoryB G v) ∧
      G.dist t r=G.dist start r+p.length ∧
      (∀ X, MaxSet G X → (t∈X ↔ ∀ v∈p.support, v∈X)) := by
  classical
  let bound := univ.sup (fun v : V => G.dist v r)
  induction n : bound-G.dist start r using Nat.strong_induction_on generalizing start with
  | h n ih =>
    obtain ⟨w,arc⟩ := next_of_mandatory G r swaps start must (degree start)
    have vw : (SimpleGraph.fromRel (fun u z => Arc G r u z)).Adj start w := ⟨arc.1.ne,Or.inl arc⟩
    have cap : G.dist w r ≤ bound := le_sup (f:=fun z => G.dist z r) (mem_univ w)
    have dw := arc.2.1
    by_cases hw : MandatoryB G w
    · obtain ⟨t,p,no,ms,len,all⟩ := ih _ (by omega) w hw rfl
      refine ⟨t,p.cons vw,no,?_,by simp only [Walk.length_cons]; omega,?_⟩
      · intro u hu ne
        rcases List.mem_cons.mp hu with e|h
        · exact e ▸ must
        · exact ms u h ne
      · intro X ok
        rw [all X ok]
        exact ⟨fun h u m => (List.mem_cons.mp m).elim (fun e => e ▸ must X ok) (h u),
          fun h u m => h u (List.mem_cons_of_mem _ m)⟩
    · refine ⟨w,Walk.cons vw Walk.nil,hw,?_,by simpa using dw,?_⟩
      · intro u hu ne
        rcases List.mem_cons.mp hu with e|h
        · exact e ▸ must
        · exact (ne (List.mem_singleton.mp h)).elim
      · intro X ok
        constructor
        · intro yes u hu
          rcases List.mem_cons.mp hu with e|h
          · exact e ▸ must X ok
          · exact (List.mem_singleton.mp h) ▸ yes
        · intro h
          exact h w (by simp)

/-- Every private-successor chain can be extended to a sink. At a sink all
remaining nonroot vertices retain a predecessor on deletion. The sink is
optional for maximum bipartite witnesses in an edge-minimal failed block. -/
theorem sink_chain (r start : V) (degree : ∀ v : V, ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a≠b)
    (swaps : ∀ a b, G.Adj a b → ¬Arc G r a b → ¬Arc G r b a →
      ∃ X Y, MaxSet G X ∧ MaxSet G Y ∧ a∈X ∧ b∉X ∧ a∉Y ∧ b∈Y) :
    ∃ t, ∃ p : (SimpleGraph.fromRel (fun u v => Arc G r u v)).Walk start t,
      (∀ w, ¬Arc G r t w) ∧ G.dist t r=G.dist start r+p.length ∧
      ∃ X Y, MaxSet G X ∧ MaxSet G Y ∧ t∈X ∧ t∉Y := by
  classical
  let bound := univ.sup (fun v : V => G.dist v r)
  induction n : bound-G.dist start r using Nat.strong_induction_on generalizing start with
  | h n ih =>
    by_cases next : ∃ w, Arc G r start w
    · obtain ⟨w,arc⟩ := next
      have vw : (SimpleGraph.fromRel (fun u z => Arc G r u z)).Adj start w := ⟨arc.1.ne,Or.inl arc⟩
      have cap : G.dist w r ≤ bound := le_sup (f:=fun z => G.dist z r) (mem_univ w)
      have dw := arc.2.1
      obtain ⟨t,p,sink,len,flex⟩ := ih _ (by omega) w rfl
      exact ⟨t,p.cons vw,sink,by simp only [Walk.length_cons]; omega,flex⟩
    · have stop : ∀ w, ¬Arc G r start w := fun w h => next ⟨w,h⟩
      obtain ⟨a,b,va,vb,ne⟩ := degree start
      have inc : ∃ u, G.Adj start u ∧ ¬Arc G r u start := by
        by_cases inA : Arc G r a start
        · exact ⟨b,vb,fun inB => ne (inB.2.2 a va.symm inA.2.1)⟩
        · exact ⟨a,va,inA⟩
      obtain ⟨u,e,no⟩ := inc
      obtain ⟨X,Y,xm,ym,xs,_,ys,_⟩ := swaps start u e (stop _) no
      exact ⟨start,Walk.nil,stop,by simp,X,Y,xm,ym,xs,ys⟩

#print axioms remove_edge_distances
#print axioms edge_witness
#print axioms fragile_edges
#print axioms next_of_mandatory
#print axioms witness_chain
#print axioms sink_chain
end Minimal180
