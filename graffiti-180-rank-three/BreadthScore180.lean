import BreadthIdentity180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A test using only predecessor neighborhoods in the original graph.
For a fixed branch set B the summands each evaluate to zero, one or two. -/
noncomputable def LayerTest (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (A P : Finset V) : Prop :=
  let X := A∪P
  let D := X\(A∩P)
  ∃ B⊆X.erase r, Fintype.card V+B.card≤bipartiteNum G+
    (if r∈D then 1 else 0)+(if r∈X then G.degree r-2 else 0)+score G r D B

/-- The test is exact for all spanning trees preserving distances to r.
The degree assumption allows the root to be internal in every such tree. -/
theorem breadth_iff (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 1<Fintype.card V) (r : V) (two : ∃ s t, G.Adj r s ∧ G.Adj r t ∧ s≠t)
    (odd : Bool) (A : Finset V) (ai : Indep G A) :
    let P := parity G r odd
    (∃ T≤G, T.IsTree ∧ (∀ x,T.dist x r=G.dist x r) ∧
      1+A.card+P.card≤(eligible A P r∩leaves T).card+bipartiteNum G) ↔ LayerTest G r A P := by
  classical
  intro P
  let X := A∪P
  let D := X\(A∩P)
  let Y := X.erase r
  have nr : r∉Y := by simp [Y] 
  constructor
  · rintro ⟨T,sub,tr,dist,pay⟩
    let p (x : V) := if h : x=r then r else (Graffiti169.exists_predecessor T tr.isConnected r x h).choose
    have std (x : V) (xr : x≠r) : T.Adj x (p x) ∧ T.dist x r=T.dist (p x) r+1 := by
      simpa only [p,dif_neg xr] using (Graffiti169.exists_predecessor T tr.isConnected r x xr).choose_spec
    have hp (x : V) (xr : x≠r) : Pred G r x (p x) :=
      ⟨sub (std x xr).1,by simpa only [dist] using (std x xr).2⟩
    have down (x : V) (xr : x≠r) : G.dist (p x) r<G.dist x r := by rw [(hp x xr).2]; omega
    have ident := breadth_identity G hc hn r odd two A ai p hp T tr (fun x xr => (std x xr).1)
    change Fintype.card V+(eligible A P r∩leaves T).card=1+A.card+P.card+
      (if r∈D then 1 else 0)+((D.erase r).filter (fun x => p x∉D)).card+
      (if r∈X then G.degree r-2 else 0)+∑ v∈Y,(T.degree v-2) at ident
    obtain ⟨B,inc,hit⟩ := (branch_linearization T tr r p (fun x => G.dist x r) down
      (fun x xr => (std x xr).1) Y nr).2
    have sum := reward_sum r D B p
    have bound : (∑ x∈univ.erase r,reward D B x (p x))≤score G r D B := by
      apply sum_le_sum
      intro x hx
      exact le_sup (f:=reward D B x) (mem_filter.mpr ⟨mem_univ _,hp x (mem_erase.mp hx).1⟩)
    refine ⟨B,inc,?_⟩
    change Fintype.card V+B.card≤bipartiteNum G+
      (if r∈D then 1 else 0)+(if r∈X then G.degree r-2 else 0)+score G r D B
    omega
  · rintro ⟨B,inc,paid⟩
    change B⊆Y at inc
    change Fintype.card V+B.card≤bipartiteNum G+
      (if r∈D then 1 else 0)+(if r∈X then G.degree r-2 else 0)+score G r D B at paid
    obtain ⟨p,hp,best⟩ := realizing_parents G hc r D B
    obtain ⟨T,sub,tr,_,take,_⟩ := predecessor_tree G hc r odd p hp
    have down (x : V) (xr : x≠r) : G.dist (p x) r<G.dist x r := by rw [(hp x xr).2]; omega
    have ident := breadth_identity G hc hn r odd two A ai p hp T tr take
    change Fintype.card V+(eligible A P r∩leaves T).card=1+A.card+P.card+
      (if r∈D then 1 else 0)+((D.erase r).filter (fun x => p x∉D)).card+
      (if r∈X then G.degree r-2 else 0)+∑ v∈Y,(T.degree v-2) at ident
    have ub := (branch_linearization T tr r p (fun x => G.dist x r) down take Y nr).1 B inc
    have val : score G r D B=∑ x∈univ.erase r,reward D B x (p x) :=
      sum_congr rfl (fun x hx => best x (mem_erase.mp hx).1)
    have sum := reward_sum r D B p
    exact ⟨T,sub,tr,(parent_properties G hc r odd p hp T tr take).2.2.2,by omega⟩

theorem rooted_of_layer_test (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 1<Fintype.card V) (r : V) (two : ∃ s t, G.Adj r s ∧ G.Adj r t ∧ s≠t)
    (odd : Bool) (A : Finset V) (ai : Indep G A) (test : LayerTest G r A (parity G r odd)) :
    let P := parity G r odd
    1+A.card+P.card≤weightedLeaves G (eligible A P r)+bipartiteNum G := by
  classical
  intro P
  obtain ⟨T,sub,tr,_,pay⟩ := (breadth_iff G hc hn r two odd A ai).mpr test
  have le : (eligible A P r∩leaves T).card≤weightedLeaves G (eligible A P r) :=
    le_sup (f:=fun K => (eligible A P r∩leaves K).card) (mem_filter.mpr ⟨mem_univ _,sub,tr⟩)
  exact pay.trans (Nat.add_le_add_right le _)

#print axioms breadth_iff
#print axioms rooted_of_layer_test
end Minimal180.HigherRank
