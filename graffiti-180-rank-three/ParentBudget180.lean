import CutEntry180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def Pred (G : SimpleGraph V) (r x y : V) : Prop := G.Adj x y ∧ G.dist x r=G.dist y r+1

/-- Any prescribed selection of shortest-path parents satisfies an exact
component and branching budget in a failed rooted marking. -/
theorem parent_budget (G : SimpleGraph V) (hc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (odd : Bool) (two : ∃ s t, G.Adj r s ∧ G.Adj r t ∧ s≠t)
    (A : Finset V) (ai : Indep G A) (p : V→V) (hp : ∀ x≠r, Pred G r x (p x)) :
    let P := parity G r odd
    let X := A∪P
    let D := X\(A∩P)
    let leavesBound := weightedLeaves G (eligible A P r)+bipartiteNum G
    leavesBound<1+A.card+P.card →
    ∃ T≤G, T.IsTree ∧ (∀ x≠r, T.Adj x (p x)) ∧ (∀ x, G.Adj r x → T.Adj r x) ∧
      (if r∈D then 1 else 0) + ((D.erase r).filter (fun x => p x∉D)).card +
        (∑ v∈X, (T.degree v-2)) + bipartiteNum G < Fintype.card V := by
  classical
  intro P X D leavesBound fail
  obtain ⟨T,sub,tr,cross,take,star⟩ := predecessor_tree G hc r odd p hp
  obtain ⟨s,t,rs,rt,ne⟩ := two
  have internal : r∉leaves T := fun lf => ne (leaf_unique T lf (star s rs) (star t rt))
  have id := tree_defect T tr hn r internal A P (fun x hx y hy diff e => ai x hx y hy diff (sub e)) cross
  change Fintype.card V+((eligible A P r)∩leaves T).card+(T.edgeFinset∩D.sym2).card =
    1+A.card+P.card+D.card+∑ v∈X,(T.degree v-2) at id
  rw [chosen_parent_count T tr r D p (fun x => G.dist x r) (fun x xr => (hp x xr).2) take] at id
  have bd : ((eligible A P r)∩leaves T).card≤weightedLeaves G (eligible A P r) :=
    le_sup (f:=fun K => ((eligible A P r)∩leaves K).card)
      (mem_filter.mpr ⟨mem_univ _,sub,tr⟩)
  have opp := filter_card_add_filter_neg_card_eq_card (s:=D.erase r) (p:=fun x => p x∈D)
  change weightedLeaves G (eligible A P r)+bipartiteNum G<1+A.card+P.card at fail
  refine ⟨T,sub,tr,take,star,?_⟩
  by_cases rd : r∈D
  · rw [if_pos rd]
    have := card_erase_add_one rd
    omega
  · rw [if_neg rd]
    have : (D.erase r).card=D.card := by simp [rd]
    omega

#print axioms parent_budget
end Minimal180.HigherRank
