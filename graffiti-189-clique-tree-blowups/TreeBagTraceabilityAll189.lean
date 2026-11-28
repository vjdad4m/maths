import TreeBagTraceability189
import AllTightTreeBag189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open scoped BigOperators
open private Graffiti189LongestPath.TreeBagTraceability.model_system from TreeBagTraceability189
namespace Graffiti189LongestPath.TreeBagTraceability
open BagQuotient TreeParity TreeBagCharges TreeBagCapacity TreeBagTight TreeTightSpine
open BagSpineCriterion BagWalkLift

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  {B : SimpleGraph U} {G : SimpleGraph V} [DecidableRel B.Adj] [DecidableRel G.Adj]

/-- #189 for graphs built from a tree by replacing each vertex by a nonempty
clique and each edge by a complete join, in the range d≥5. -/
theorem traceable_of_clique_tree_blowup_of_degree_ge_five {f : V→U}
    (M : Model B G f) (tree : B.IsTree) (hc : G.Connected)
    (d : ℕ) (d5 : 5≤d)
    (even : ∀ v,(EvenFrom G v).card≤d+1)
    (deg : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v) :
    ∃ (a b : V) (p : G.Walk a b),p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  letI : Nonempty V := hc.nonempty
  obtain ⟨v⟩ := hc.nonempty
  let r := f v
  let F (i : U) := bag f i
  have clique (i : U) (u : V) (ui : u∈F i) (v : V) (vi : v∈F i) (uv : u≠v) :
      G.Adj u v := (M.exact_edge u v).mpr (Or.inl
        ⟨((mem_bag _ _ _).mp ui).trans ((mem_bag _ _ _).mp vi).symm,uv⟩)
  have join (i j : U) (ij : B.Adj i j) (u : V) (ui : u∈F i) (v : V) (vj : v∈F j) :
      G.Adj u v := (M.exact_edge u v).mpr (Or.inr (by
        rwa [(mem_bag _ _ _).mp ui,(mem_bag _ _ _).mp vj]))
  have covers (u : V) : ∃ i,u∈F i := ⟨f u,(mem_bag _ _ _).mpr rfl⟩
  by_cases cut : ∃ u : V,¬(G.induce {z : V | z≠u}).Connected
  · obtain ⟨u,hu⟩ := cut
    exact Graffiti189LongestPath.CrossSaturation.traceable_at_articulation_general hc d
      (by omega) even deg u hu
  have robust (u : V) : (G.induce {z : V | z≠u}).Connected :=
    Classical.byContradiction (fun z => cut ⟨u,z⟩)
  by_cases edge : ∃ a b,B.Adj a b
  · have A := Graffiti189LongestPath.TreeBagTraceability.model_system M tree hc d r even deg robust
    let T := univ.filter (fun i => (F i).card<B.degree i)
    obtain ⟨a,b,ne,p,hp,interior⟩ := exists_spine_through_two_nonleaves tree edge T (card_tight_degree_ge_five A d5)
      (fun i it => (show 3≤B.degree i from tight_degree_three A i (mem_filter.mp it).2).trans' (by omega))
    exact traceable_of_bag_capacity_spine tree.isConnected ne p hp F (bag_pairwise f) clique join
      (degree_le_capacity_add_one A) (fun i hi => interior i (mem_filter.mpr ⟨mem_univ _,hi⟩)) covers
  · have only (i : U) : i=r := by
      obtain ⟨p⟩ := tree.isConnected i r
      cases p with
      | nil => rfl
      | cons h p => exact (edge ⟨_,_,h⟩).elim
    apply traceable_of_base_walk (.nil : B.Walk r r) F (bag_pairwise f) clique join
    · intro i
      rw [only i, support_nil]
      simp only [List.count_cons_self,List.count_nil,Nat.zero_add]
      exact card_pos.mpr (M.bag_nonempty r)
    · intro i ne
      have e := only i
      exact (ne (by simp [e])).elim
    · exact covers

#print axioms traceable_of_clique_tree_blowup_of_degree_ge_five
end Graffiti189LongestPath.TreeBagTraceability
