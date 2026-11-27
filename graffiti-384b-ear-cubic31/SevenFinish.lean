import SevenEmbedding

namespace Graffiti384b.Seven
open Finset SimpleGraph
open private third from SevenContact
open private OneEar.deg2 from OneEarFinish384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In a five-clique-free failure of diversity 31 the unique degree-two
vertex of the positive core has both its neighbors of degree at least four. -/
theorem core_neighbors (hc : G.Connected) (t : (types G).card=31) (free : G.CliqueFree 5)
    (bad : bound G<gamma G) :
    let P := nonleaves G
    let H := G.induce (P:Set V)
    ∃ e : P,H.degree e=2 ∧ trianglesAt H e=1 ∧ (∀ v,v≠e → 3≤H.degree v) ∧
      ∀ u,H.Adj e u → 4≤H.degree u := by
  let P := nonleaves G
  let H := G.induce (P:Set V)
  obtain ⟨n,_,fi,pos,g,u,x,e,_,_,dx,sx,de,se,rest,_⟩ := Frontier31.five_free_core G hc t free bad
  have hf : H.CliqueFree 5 := free.comap (Embedding.induce (P:Set V))
  refine ⟨e,de,se,rest,?_⟩
  intro v ev
  have low := rest v ev.ne.symm
  change 3≤H.degree v at low
  change 4≤H.degree v
  change gamma H=15 at g
  by_contra! small
  have up := adjacent_bound H n hf pos fi de (show H.degree v=3 by omega) dx sx ev rest
  omega

/-- This criterion is stated directly in the original graph. The vertex e
is triangular, has degree two, and has a neighbor of degree at most three. -/
theorem exact_of_adjacent (hc : G.Connected) (t : (types G).card=31) (free : G.CliqueFree 5)
    {e u : V} (de : G.degree e=2) (ep : 0<trianglesAt G e) (eu : G.Adj e u)
    (du : G.degree u≤3) : gamma G≤bound G := by
  classical
  by_contra! bad
  let P := nonleaves G
  let H := G.induce (P:Set V)
  obtain ⟨a,_,_,rest,high⟩ := core_neighbors G hc t free bad
  obtain ⟨r,er,ur⟩ := third G de eu ep
  have em : e∈P := mem_filter.mpr ⟨mem_univ _,de.ge⟩
  have um : u∈P := mem_filter.mpr ⟨mem_univ _,OneEar.deg2 G er.ne eu.symm ur⟩
  let E : P := ⟨e,em⟩
  let U : P := ⟨u,um⟩
  have deg (v : P) : H.degree v≤G.degree v.val := by
    rw [EarAnchor.induced_degree]
    change (P.filter (G.Adj v.val)).card≤G.degree v.val
    rw [←card_neighborFinset_eq_degree]
    exact card_le_card (fun w wm => (G.mem_neighborFinset ..).mpr (mem_filter.mp wm).2)
  have le : H.degree E≤2 := (deg E).trans_eq de
  have same : E=a := Classical.byContradiction (fun ne => by have big : 3≤H.degree E := rest E ne; omega)
  have edge : H.Adj E U := eu
  have hi : 4≤H.degree U := high U (same ▸ edge)
  have up : H.degree U≤3 := (deg U).trans du
  omega

end Graffiti384b.Seven
#print axioms Graffiti384b.Seven.core_neighbors
#print axioms Graffiti384b.Seven.exact_of_adjacent
