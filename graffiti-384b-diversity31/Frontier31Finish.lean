import FrontierPivot31

namespace Graffiti384b.Frontier31
open Finset SimpleGraph HighEar
open private Repair.triangles_le_choose from Repair384b
open private ThreeChoice.pair_turan from ThreeGeometry33
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem local_clique {v : V} (d : G.degree v≤9)
    (big : RankTable.cap (G.degree v) 3<trianglesAt G v) :
    ∃ C : Finset V,G.IsNClique 5 C ∧ v∈C := by
  classical
  by_contra! no
  let N := G.neighborFinset v
  have free (Q : Finset V) (sub : Q⊆N) (cl : G.IsNClique (3+1) Q) : False :=
    no (insert v Q) (cl.insert (fun y ym => (G.mem_neighborFinset ..).mp (sub ym))) (mem_insert_self ..)
  have up := ThreeChoice.pair_turan G N (by decide : 0<3) free
  change trianglesAt G v≤(turanGraph N.card 3).edgeFinset.card at up
  have sz : N.card=G.degree v := card_neighborFinset_eq_degree ..
  rw [sz] at up
  have ar := RankTable.cap_table ⟨G.degree v,by omega⟩ ⟨3,by decide⟩ (by decide)
  exact (not_lt_of_ge (up.trans_eq ar)) big

/-- The center exceeding its triangle bound belongs to the forced K5. -/
theorem clique_center (t : (types G).card=31) (n : 31≤(nonleaves G).card) (bad : bound G<gamma G) :
    ∃ v,4≤G.degree v ∧ G.degree v≤8 ∧ RankTable.cap (G.degree v) 3<trianglesAt G v ∧
      ∃ C : Finset V,G.IsNClique 5 C ∧ v∈C := by
  obtain ⟨v,l,d,big⟩ := dense_center G t n bad
  exact ⟨v,l,d,big,local_clique G (by omega) big⟩

private theorem clique_edges {C : Finset V} (cl : G.IsNClique 5 C) : (pairs G C).card=10 := by
  have eq : pairs G C=C.powersetCard 2 := filter_true_of_mem (fun D dm x xm y ym xy =>
    cl.1 ((mem_powersetCard.mp dm).1 xm) ((mem_powersetCard.mp dm).1 ym) xy)
  rw [eq,card_powersetCard,cl.2]; decide

/-- At every order a failure of diversity 31 contains five vertices
spanning at least nine edges, including a vertex of degree at most nine. -/
theorem near_five (t : (types G).card=31) (bad : bound G<gamma G) :
    ∃ C : Finset V,C.card=5 ∧ 9≤(pairs G C).card ∧ ∃ v∈C,4≤G.degree v ∧ G.degree v≤9 := by
  classical
  by_cases localCap : ∀ v,G.degree v≤9 → trianglesAt G v≤RankTable.cap (G.degree v) 3
  · obtain ⟨_,_,x,dx,s⟩ := profile G t localCap bad
    let N := G.neighborFinset x
    have xn : x∉N := G.not_mem_neighborFinset_self _
    have sz : N.card=4 := (card_neighborFinset_eq_degree ..).trans dx
    have all : N.filter (G.Adj x)=N := filter_true_of_mem (fun _ m => (G.mem_neighborFinset ..).mp m)
    have b : nbr G x N=4 := (congrArg card all).trans sz
    have e := pairs_insert G xn
    change (pairs G (insert x N)).card=trianglesAt G x+nbr G x N at e
    exact ⟨insert x N,by rw [card_insert_of_not_mem xn,sz],by omega,x,mem_insert_self ..,by omega,by omega⟩
  · push_neg at localCap
    obtain ⟨v,d,big⟩ := localCap
    obtain ⟨C,cl,vm⟩ := local_clique G d big
    have nv : 4≤G.degree v := by
      by_contra! sm
      have eq := (show ∀ a : Fin 4,a.val.choose 2=RankTable.cap a.val 3 by decide) ⟨_,sm⟩
      have cap := Repair.triangles_le_choose G v
      exact (not_lt_of_ge (cap.trans_eq eq)) big
    exact ⟨C,cl.2,(clique_edges G cl).symm ▸ (by decide : 9≤10),v,vm,nv,d⟩

/-- In particular the catalogue inequality holds for all graphs of
diversity 31 that avoid the graph K5 minus an edge as a subgraph. -/
theorem exact_of_no_near_five (t : (types G).card=31)
    (avoid : ∀ C : Finset V,C.card=5 → (pairs G C).card≤8) : gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro bad
  obtain ⟨C,sz,edges,_⟩ := near_five G t bad
  have := avoid C sz; omega

/-- Exact obstruction in the positive core of a five-clique-free failure. -/
theorem five_free_core (hc : G.Connected) (t : (types G).card=31) (free : G.CliqueFree 5)
    (bad : bound G<gamma G) :
    let P := nonleaves G
    let H := G.induce (P:Set V)
    Fintype.card P=30 ∧ H.Connected ∧ Function.Injective (trianglesAt H) ∧
      (∀ v,0<trianglesAt H v) ∧ gamma H=15 ∧
      ∃ u x e : P,H.degree u=3 ∧ trianglesAt H u=2 ∧ H.degree x=4 ∧ trianglesAt H x=5 ∧
        H.degree e=2 ∧ trianglesAt H e=1 ∧ (∀ v,v≠e → 3≤H.degree v) ∧
        ∀ A B : Finset P,EarFrame33.Frame H A B → e∈A∪B → 2≤((A∪B)∩H.neighborFinset x).card := by
  let P := nonleaves G
  let H := G.induce (P:Set V)
  obtain ⟨sz,con,_,fi,pos,g,⟨u,du,su⟩,x,dx,sx⟩ := core G hc t (free_cap G free) bad
  have half : Fintype.card P≤2*gamma H := by rw [sz,show gamma H=15 from g]
  obtain ⟨e,de,se,lo,bar⟩ := ear_barrier H dx sx half pos fi
  exact ⟨sz,con,fi,pos,g,u,x,e,du,su,dx,sx,de,se,lo,bar⟩

end Graffiti384b.Frontier31
#print axioms Graffiti384b.Frontier31.clique_center
#print axioms Graffiti384b.Frontier31.near_five
#print axioms Graffiti384b.Frontier31.exact_of_no_near_five
#print axioms Graffiti384b.Frontier31.five_free_core
