import EJOrderTwoClose189

open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
namespace Graffiti189LongestPath.BipartiteTraceability
variable {V : Type*} {G : SimpleGraph V}

private theorem len_mod {a b : V} (p : G.Walk a b) (f : V→Bool)
    (proper : ∀ i j,G.Adj i j → f i≠f j) :
    p.length%2=if f a=f b then 0 else 1 := by
  induction p with
  | nil => simp
  | @cons a c b h p ih =>
    have ac := proper a c h
    simp only [length_cons]
    cases ea : f a <;> cases ec : f c <;> cases eb : f b <;>
      simp [ea,ec,eb] at ac ih ⊢ <;> omega

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The original #189 claim for a connected bipartite graph.
A proper Boolean 2-coloring expresses its bipartition. -/
theorem traceable_of_bipartite (hc : G.Connected) (d : ℕ)
    (cap : ∀ u,(EvenFrom G u).card≤d+1)
    (degree : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v)
    (f : V→Bool) (proper : ∀ u v,G.Adj u v → f u≠f v) :
    Graffiti189Ore.Traceable G := by
  classical
  let S (c : Bool) : Finset V := univ.filter (fun v => f v=c)
  have bound (c : Bool) : (S c).card≤d+1 := by
    by_cases empty : S c=∅
    · simp [empty]
    · obtain ⟨x,xs⟩ := nonempty_of_ne_empty empty
      have xcolor : f x=c := (mem_filter.mp xs).2
      apply (card_le_card (t:=EvenFrom G x) ?_).trans (cap x)
      intro y ys
      have same : f x=f y := xcolor.trans (mem_filter.mp ys).2.symm
      obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist x y
      have even := len_mod p f proper
      rw [pl,if_pos same] at even
      simp only [EvenFrom,mem_filter,mem_univ,true_and]
      exact Nat.even_iff.mpr even
  have all : (univ:Finset V)=S false∪S true := by
    ext v
    cases h : f v <;> simp [S,h]
  have dis : Disjoint (S false) (S true) := by
    apply disjoint_left.mpr
    intro v hv hv'
    exact Bool.false_ne_true ((mem_filter.mp hv).2.symm.trans (mem_filter.mp hv').2)
  have n := congrArg Finset.card all
  rw [card_univ,card_union_of_disjoint dis] at n
  have x := bound false
  have y := bound true
  apply Graffiti189LongestPath.SmallOrder.traceable_at_order_le_two_d_add_two hc d cap degree
  omega

#print axioms traceable_of_bipartite
end Graffiti189LongestPath.BipartiteTraceability
