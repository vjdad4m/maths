import Boundary180

set_option warningAsError true
namespace Assembly180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

private theorem erase_cost (U : Finset V) (w : V) :
    weightedLeaves G U ≤ weightedLeaves G (U.erase w)+1 := by
  classical
  have sub : U \ U.erase w ⊆ {w} := by
    intro v h
    obtain ⟨vu,no⟩ := mem_sdiff.mp h
    apply mem_singleton.mpr
    exact Classical.byContradiction (fun ne => no (mem_erase.mpr ⟨ne,vu⟩))
  have size := card_le_card sub
  rw [card_singleton] at size
  exact (restrict_leaves G U (U.erase w)).trans (Nat.add_le_add_left size _)

/-- Failure to gain bipartite order at the next triangle forces either a
strictly smaller failed rooted witness with the restricted independent set,
or equality downstairs, no leaf gain, a one-unit increase in bipartite
order at the deleted vertex, and mandatory eligibility of *every* neighbor.
All graph, distance, tree, and induced-set invariants are actual maxima. -/
theorem equality_descent (hc : G.Connected) (hn : 2<Fintype.card V) (N : Finset V)
    (r : V) (odd : Bool) (A : Finset (V ⊕ Unit)) (ai : Indep (ear G N) A)
    (par : pull Sum.inl (parity (ear G N) (.inl r) odd)=parity G r odd)
    (once : let P := parity (ear G N) (.inl r) odd
            (.inr ()∈A ∨ .inr ()∈P) ∧ ¬(.inr ()∈A ∧ .inr ()∈P))
    (tight : let P := parity (ear G N) (.inl r) odd
             weightedLeaves (ear G N) (eligible A P (.inl r))+bipartiteNum (ear G N)=1+A.card+P.card)
    (w : V) (wn : w∈N)
    (stuck : let H := ear G N
             bipartiteNum (ear H {Sum.inl w,Sum.inr ()}) ≠ bipartiteNum H+1) :
    let H := ear G N
    let B := pull Sum.inl A
    let Q := parity G r odd
    let U := eligible B Q r
    let E := eligible A (parity H (.inl r) odd) (.inl r)
    (weightedLeaves G U+bipartiteNum G<1+B.card+Q.card ∧
        counterexampleAtMost.{u} (4*Fintype.card V-1)) ∨
    (weightedLeaves G U+bipartiteNum G=1+B.card+Q.card ∧
     weightedLeaves H E=weightedLeaves G U ∧ bipartiteNum H=bipartiteNum G+1 ∧
     ∀ v∈N, v∈U ∧ ∀ T ≤ G, T.IsTree → (U ∩ leaves T).card=weightedLeaves G U → v∈leaves T) := by
  classical
  let H := ear G N
  let B := pull Sum.inl A
  let Q := parity G r odd
  let U := eligible B Q r
  let P := parity H (.inl r) odd
  let E := eligible A P (.inl r)
  dsimp only
  obtain ⟨selection,count⟩ := new_vertex_counts G N r odd A par once
  change E=U.disjSum univ at selection
  change A.card+P.card=B.card+Q.card+1 at count
  change weightedLeaves H E+bipartiteNum H=1+A.card+P.card at tight
  have rank := without_new G N
  change bipartiteNum G ≤ without H (.inr ()) at rank
  have le (a) : without H a ≤ bipartiteNum H := by
    apply Finset.sup_le
    intro X hx
    exact le_sup (f:=card) (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩)
  have zle := le (.inr ())
  have wle := le (.inl w)
  have step := triangle_rank_exchange H (.inl w) (.inr ()) wn
  change bipartiteNum (ear H {Sum.inl w,Sum.inr ()})≠bipartiteNum H+1 at stuck
  have jump : bipartiteNum G+1 ≤ bipartiteNum H := by omega
  have gain (v : V) (vn : v∈N) : weightedLeaves G (U.erase v)+1 ≤ weightedLeaves H E := by
    rw [selection]
    exact gain_at G hc hn N U v vn
  have g := gain w wn
  have e := erase_cost G U w
  by_cases bad : weightedLeaves G U+bipartiteNum G<1+B.card+Q.card
  · left
    have ib : Indep G B := fun v hv a ha ne e => ai _ (mem_pull.mp hv) _ (mem_pull.mp ha)
      (fun eq => ne (Sum.inl.inj eq)) e
    exact ⟨bad,realize G hc (by omega) r odd B ib bad⟩
  · right
    have eq : weightedLeaves G U+bipartiteNum G=1+B.card+Q.card := by omega
    have leaf : weightedLeaves H E=weightedLeaves G U := by omega
    have rankeq : bipartiteNum H=bipartiteNum G+1 := by omega
    refine ⟨eq,leaf,rankeq,fun v vn => (mandatory_iff G hc U v).mp ?_⟩
    have := gain v vn
    omega


/-- Even when the old attachment neighbor itself is a leaf, its eligibility
can be dropped before hanging the new leaf from it. If it is mandatory in
the enlarged graph, there is a strict net gain over the old optimum. -/
theorem mandatory_neighbor_gain (hc : G.Connected) (hn : 2<Fintype.card V)
    (N U : Finset V) (w : V) (wn : w∈N)
    (must : weightedLeaves (ear G N) ((U.disjSum (univ : Finset Unit)).erase (.inl w)) <
      weightedLeaves (ear G N) (U.disjSum univ)) :
    weightedLeaves G U+1 ≤ weightedLeaves (ear G N) (U.disjSum univ) := by
  classical
  have sel : (U.disjSum (univ : Finset Unit)).erase (.inl w)=(U.erase w).disjSum univ := by
    ext v; cases v <;> simp
  rw [sel] at must
  have hang := gain_at G hc hn N (U.erase w) w wn
  rw [erase_idem] at hang
  have b := erase_cost G U w
  omega

/-- If an endpoint is counted exactly once and deleting it preserves the
old distance parity, local equality plus a mandatory neighbor rules out a
stalled bipartite rank at their edge unless the restricted independent set
on the smaller graph already gives a counterexample. -/
theorem critical_stable_deletion (hc : G.Connected) (hn : 2<Fintype.card V) (N : Finset V)
    (r : V) (odd : Bool) (A : Finset (V ⊕ Unit)) (ai : Indep (ear G N) A)
    (par : pull Sum.inl (parity (ear G N) (.inl r) odd)=parity G r odd)
    (once : let P := parity (ear G N) (.inl r) odd
            (.inr ()∈A ∨ .inr ()∈P) ∧ ¬(.inr ()∈A ∧ .inr ()∈P))
    (tight : let P := parity (ear G N) (.inl r) odd
             weightedLeaves (ear G N) (eligible A P (.inl r))+bipartiteNum (ear G N)=1+A.card+P.card)
    (w : V) (wn : w∈N)
    (stuck : let H := ear G N
             bipartiteNum (ear H {Sum.inl w,Sum.inr ()}) ≠ bipartiteNum H+1)
    (must : let H := ear G N
            let E := eligible A (parity H (.inl r) odd) (.inl r)
            weightedLeaves H (E.erase (.inl w))<weightedLeaves H E) :
    let B := pull Sum.inl A
    let Q := parity G r odd
    weightedLeaves G (eligible B Q r)+bipartiteNum G<1+B.card+Q.card ∧
      counterexampleAtMost.{u} (4*Fintype.card V-1) := by
  classical
  rcases equality_descent G hc hn N r odd A ai par once tight w wn stuck with bad | eq
  · exact bad
  · let H := ear G N
    let Q := parity G r odd
    let U := eligible (pull Sum.inl A) Q r
    let E := eligible A (parity H (.inl r) odd) (.inl r)
    have sel := (new_vertex_counts G N r odd A par once).1
    change E=U.disjSum univ at sel
    change weightedLeaves H (E.erase (.inl w))<weightedLeaves H E at must
    rw [sel] at must
    have gain := mandatory_neighbor_gain G hc hn N U w wn must
    have h := eq.2.1
    change weightedLeaves H E=weightedLeaves G U at h
    rw [sel] at h
    change _ ≤ weightedLeaves H (U.disjSum univ) at gain
    omega

omit [Fintype V] [DecidableEq V] in
/-- If all surviving nonroot vertices admit an old predecessor, deletion
preserves their full distances, and hence each distance parity. -/
theorem kept_predecessors (hc : G.Connected) (N : Finset V) (nz : N.Nonempty) (r : V)
    (keep : ∀ v≠r, ∃ a, G.Adj v a ∧
      (ear G N).dist (.inl v) (.inl r)=(ear G N).dist (.inl a) (.inl r)+1) :
    ∀ v, (ear G N).dist (.inl v) (.inl r)=G.dist v r := by
  let H := ear G N
  have con := ear_connected G hc N nz
  let d (v : V) := H.dist (.inl v) (.inl r)
  obtain ⟨_,dist⟩ := layers G r d H.dist_self (fun {v a} va => by
    have tri := con.dist_triangle (u:=Sum.inl v) (v:=Sum.inl a) (w:=Sum.inl r)
    rw [dist_eq_one_iff_adj.mpr (show H.Adj (.inl v) (.inl a) from va)] at tri
    change H.dist (.inl v) (.inl r) ≤ 1+H.dist (.inl a) (.inl r) at tri
    change H.dist (.inl v) (.inl r) ≤ H.dist (.inl a) (.inl r)+1
    omega) keep
  exact fun v => (dist v).symm

/-- For a sharp obstruction with no smaller witness, some surviving
vertex has the deleted endpoint as its only predecessor. -/
theorem private_successor (hc : G.Connected) (hn : 2<Fintype.card V) (N : Finset V)
    (r : V) (odd : Bool) (A : Finset (V ⊕ Unit)) (ai : Indep (ear G N) A)
    (once : let P := parity (ear G N) (.inl r) odd
            (.inr ()∈A ∨ .inr ()∈P) ∧ ¬(.inr ()∈A ∧ .inr ()∈P))
    (tight : let P := parity (ear G N) (.inl r) odd
             weightedLeaves (ear G N) (eligible A P (.inl r))+bipartiteNum (ear G N)=1+A.card+P.card)
    (w : V) (wn : w∈N)
    (stuck : let H := ear G N
             bipartiteNum (ear H {Sum.inl w,Sum.inr ()}) ≠ bipartiteNum H+1)
    (must : let H := ear G N
            let E := eligible A (parity H (.inl r) odd) (.inl r)
            weightedLeaves H (E.erase (.inl w))<weightedLeaves H E) :
    let H := ear G N
    (∃ v : V, v≠r ∧ H.Adj (.inl v) (.inr ()) ∧
      H.dist (.inl v) (.inl r)=H.dist (.inr ()) (.inl r)+1 ∧
      ∀ a : V, G.Adj v a → H.dist (.inl v) (.inl r) ≠ H.dist (.inl a) (.inl r)+1) ∨
    counterexampleAtMost.{u} (4*Fintype.card V-1) := by
  classical
  let H := ear G N
  let nz : N.Nonempty := ⟨w,wn⟩
  let d (v : V) := H.dist (.inl v) (.inl r)
  by_cases keep : ∀ v≠r, ∃ a, G.Adj v a ∧ d v=d a+1
  · right
    have eq := kept_predecessors G hc N nz r keep
    have par : pull Sum.inl (parity H (.inl r) odd)=parity G r odd := by
      ext v; simp only [mem_pull,mem_parity]; rw [eq]
    exact (critical_stable_deletion G hc hn N r odd A ai par once tight w wn stuck must).2
  · left
    push_neg at keep
    obtain ⟨v,vr,no⟩ := keep
    obtain ⟨a,e,down⟩ := Graffiti169.exists_predecessor H (ear_connected G hc N nz) (.inl r) (.inl v)
      (fun eq => vr (Sum.inl.inj eq))
    rcases a with a|a
    · exact (no a e down).elim
    · cases a
      exact ⟨v,vr,e,down,no⟩

#print axioms mandatory_neighbor_gain
#print axioms critical_stable_deletion
#print axioms kept_predecessors
#print axioms private_successor

#print axioms equality_descent
end Assembly180
