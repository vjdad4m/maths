import LayerScore180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem parent_properties (G : SimpleGraph V) (hc : G.Connected) (r : V) (odd : Bool)
    (p : V→V) (hp : ∀ x≠r, Pred G r x (p x)) (T : SimpleGraph V) (tr : T.IsTree)
    (take : ∀ x≠r,T.Adj x (p x)) :
    T≤G ∧ (∀ {x y}, T.Adj x y → (x∈parity G r odd ↔ y∉parity G r odd)) ∧
      (∀ x,G.Adj r x → T.Adj r x) ∧ (∀ x,T.dist x r=G.dist x r) := by
  classical
  obtain ⟨K,kg,kt,cross,keep,star⟩ := predecessor_tree G hc r odd p hp
  have down (x : V) (xr : x≠r) : G.dist (p x) r<G.dist x r := by rw [(hp x xr).2]; omega
  have same : T=K := edgeFinset_inj.mp ((parent_image T tr r p (fun x => G.dist x r) down take).symm.trans
    (parent_image K kt r p (fun x => G.dist x r) down keep))
  subst K
  refine ⟨kg,fun e => cross e,star,(layers T r (fun v => G.dist v r) G.dist_self ?_ ?_).2⟩
  · intro v w e
    have h := hc.dist_triangle (u:=v) (v:=w) (w:=r)
    rw [dist_eq_one_iff_adj.mpr (kg e)] at h
    change G.dist v r≤G.dist w r+1
    omega
  · exact fun v vr => ⟨p v,take v vr,(hp v vr).2⟩

/-- Separate the root contribution, the parent entries, and all remaining
branching in the exact eligible-leaf count of a shortest-path tree. -/
theorem breadth_identity (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 1<Fintype.card V) (r : V) (odd : Bool) (two : ∃ s t, G.Adj r s ∧ G.Adj r t ∧ s≠t)
    (A : Finset V) (ai : Indep G A) (p : V→V) (hp : ∀ x≠r, Pred G r x (p x))
    (T : SimpleGraph V) [DecidableRel T.Adj] (tr : T.IsTree) (take : ∀ x≠r,T.Adj x (p x)) :
    let P := parity G r odd
    let X := A∪P
    let D := X\(A∩P)
    Fintype.card V+(eligible A P r∩leaves T).card =
      1+A.card+P.card+(if r∈D then 1 else 0)+((D.erase r).filter (fun x => p x∉D)).card+
      (if r∈X then G.degree r-2 else 0)+(∑ v∈X.erase r,(T.degree v-2)) := by
  classical
  intro P X D
  obtain ⟨sub,cross,star,_⟩ := parent_properties G hc r odd p hp T tr take
  obtain ⟨s,t,rs,rt,st⟩ := two
  have internal : r∉leaves T := fun lf => st (leaf_unique T lf (star s rs) (star t rt))
  have id := tree_defect T tr hn r internal A P (fun x hx y hy diff e => ai x hx y hy diff (sub e)) cross
  change Fintype.card V+((eligible A P r)∩leaves T).card+(T.edgeFinset∩D.sym2).card =
    1+A.card+P.card+D.card+∑ v∈X,(T.degree v-2) at id
  rw [chosen_parent_count T tr r D p (fun x => G.dist x r) (fun x xr => (hp x xr).2) take] at id
  have cnt := filter_card_add_filter_neg_card_eq_card (s:=D.erase r) (p:=fun x => p x∈D)
  have rd : D.card=(D.erase r).card+(if r∈D then 1 else 0) := by
    split_ifs with h
    · exact (card_erase_add_one h).symm
    · simp [h]
  have deg : T.degree r=G.degree r := by
    have eq : T.neighborFinset r=G.neighborFinset r := by
      ext x; simp only [mem_neighborFinset]; exact ⟨fun e => sub e,star x⟩
    simpa only [card_neighborFinset_eq_degree] using congrArg Finset.card eq
  have sum : (∑ v∈X,(T.degree v-2)) =
      (if r∈X then G.degree r-2 else 0)+∑ v∈X.erase r,(T.degree v-2) := by
    split_ifs with h
    · rw [←deg]; exact (add_sum_erase X (fun v => T.degree v-2) h).symm
    · simp [h]
  omega

#print axioms parent_properties
#print axioms breadth_identity
end Minimal180.HigherRank
