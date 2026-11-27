import EarRank180

set_option warningAsError true
namespace Converse180
open Finset SimpleGraph Graffiti177 Rooted180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def earDepth (x y r : V) : V ⊕ Unit → ℕ :=
  Sum.elim (fun v => G.dist v r) (fun _ => min (G.dist x r) (G.dist y r)+1)

omit [Fintype V] in
theorem triangle_distances (hc : G.Connected) (x y r : V) (xy : G.Adj x y) :
    (ear G {x,y}).Connected ∧ ∀ v, (ear G {x,y}).dist v (.inl r) = earDepth G x y r v := by
  have lip {a b : V} (e : G.Adj a b) : G.dist a r ≤ G.dist b r + 1 := by
    have z := hc.dist_triangle (u:=a) (v:=b) (w:=r)
    rw [dist_eq_one_iff_adj.mpr e] at z
    omega
  have a := lip xy
  have b := lip xy.symm
  apply layers
  · exact G.dist_self
  · rintro (v|v) (w|w) e
    · exact lip e
    · have vw : v=x ∨ v=y := by simpa [ear] using e
      change G.dist v r ≤ min (G.dist x r) (G.dist y r)+1+1
      rcases vw with rfl|rfl <;> omega
    · have vw : w=x ∨ w=y := by simpa [ear] using e
      change min (G.dist x r) (G.dist y r)+1 ≤ G.dist w r+1
      rcases vw with rfl|rfl <;> omega
    · exact e.elim
  · rintro (v|v) ne
    · obtain ⟨w,e,d⟩ := Graffiti169.exists_predecessor G hc r v (fun eq => ne (congrArg Sum.inl eq))
      exact ⟨.inl w,e,d⟩
    · by_cases le : G.dist x r ≤ G.dist y r
      · exact ⟨.inl x,mem_insert_self _ _,by simp [earDepth,min_eq_left le]⟩
      · exact ⟨.inl y,mem_insert_of_mem (mem_singleton_self _),by simp [earDepth,min_eq_right (by omega : G.dist y r ≤ G.dist x r)]⟩

/-- A block meeting both mandatory-endpoint conditions at equality gives a
counterexample to 180. The added vertex is one beyond the nearer endpoint
and outside the chosen parity. All distances are for the actual graphs. -/
theorem of_critical_edge (hc : G.Connected) (hn : 2 < Fintype.card V) (r x y : V)
    (xy : G.Adj x y) (odd : Bool) (A : Finset V) (ai : Indep G A)
    (outside : (min (G.dist x r) (G.dist y r)+1)%2 ≠ odd.toNat) :
    let P := parity G r odd
    let U := eligible A P r
    weightedLeaves G U+bipartiteNum G=1+A.card+P.card →
    weightedLeaves G (U.erase x)<weightedLeaves G U →
    weightedLeaves G (U.erase y)<weightedLeaves G U →
    without G x<bipartiteNum G → without G y<bipartiteNum G →
    counterexampleAtMost.{u} (4*(Fintype.card V+1)-1) := by
  classical
  dsimp only
  let P := parity G r odd
  let U := eligible A P r
  let H := ear G {x,y}
  let I := A.disjSum (∅ : Finset Unit)
  intro tight lx ly bx by'
  change weightedLeaves G U+bipartiteNum G=1+A.card+P.card at tight
  change weightedLeaves G (U.erase x)<weightedLeaves G U at lx
  change weightedLeaves G (U.erase y)<weightedLeaves G U at ly
  obtain ⟨con,dist⟩ := triangle_distances G hc x y r xy
  have pp : parity H (.inl r) odd = P.disjSum (∅ : Finset Unit) := by
    ext v
    rcases v with v|v
    · simp only [mem_parity,inl_mem_disjSum,P]
      exact congrArg (fun d => d%2=odd.toNat) (dist (.inl v)) |>.to_iff
    · rw [mem_parity,show H.dist (.inr v) (.inl r) = earDepth G x y r (.inr v) from dist _]
      simp [earDepth,outside]
  have uu : eligible I (parity H (.inl r) odd) (.inl r) = U.disjSum (∅ : Finset Unit) := by
    rw [pp]
    ext v
    by_cases both : r∈A ∧ r∈P
    · rcases v with v|v <;> simp [eligible,I,U,both]
    · rcases v with v|v <;> simp [eligible,I,U,both]
  have ii : Indep H I := by
    rintro (v|v) hv (w|w) hw ne e
    · exact ai _ (inl_mem_disjSum.mp hv) _ (inl_mem_disjSum.mp hw) (fun h => ne (congrArg Sum.inl h)) e
    · simp [I] at hw
    · simp [I] at hv
    · simp [I] at hv
  have leaf := triangle_leaf_exchange G hn x y xy U
  have col := triangle_rank_exchange G x y xy
  have fail : weightedLeaves H (eligible I (parity H (.inl r) odd) (.inl r)) + bipartiteNum H <
      1+I.card+(parity H (.inl r) odd).card := by
    rw [uu,pp]
    simp only [I,card_disjSum,card_empty,Nat.add_zero]
    change weightedLeaves H _ = _ at leaf
    change bipartiteNum H = _ at col
    omega
  have h := realize H con (by simp only [Fintype.card_sum,Fintype.card_unit]; omega) (.inl r) odd I ii fail
  simpa only [Fintype.card_sum,Fintype.card_unit] using h

#print axioms triangle_distances
#print axioms of_critical_edge
end Converse180
