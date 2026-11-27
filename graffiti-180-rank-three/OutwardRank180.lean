import AdmissibleLayers180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All outward neighbors, with no entry-priority restriction. -/
noncomputable def outward (G : SimpleGraph V) (r : V) (B : Finset V) : Finset V :=
  (univ.erase r).filter (fun x => ∃ y∈B,Pred G r x y)

theorem outward_score (G : SimpleGraph V) (r : V) (B : Finset V) :
    score G r ∅ B=(outward G r B).card := by
  classical
  rw [score_formula]
  have nil : entries G r ∅=∅ := by ext x; simp [entries,Entry]
  rw [nil,card_empty,zero_add]
  congr 1
  ext x
  simp [children,outward,Entry,Allowed]

theorem failed_difference (G : SimpleGraph V) (hc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (odd : Bool) (A : Finset V) (ai : Indep G A) :
    let P := parity G r odd
    weightedLeaves G (eligible A P r)+bipartiteNum G<1+A.card+P.card →
    ((A∪P)\(A∩P)).Nonempty := by
  classical
  intro P fail
  by_contra! no
  have sub : A⊆P := by
    intro v va
    by_contra out
    exact no ⟨v,mem_sdiff.mpr ⟨mem_union_left _ va,fun h => out (mem_inter.mp h).2⟩⟩
  have cap : markedBip G (A∩P)≤bipartiteNum G := by
    apply Finset.sup_le
    exact fun _ h => size_bip G (mem_filter.mp h).2.2
  have bound := confined_parity G hc hn r odd.toNat A ai sub
  change 1+A.card+P.card≤weightedLeaves G (eligible A P r)+markedBip G (A∩P) at bound
  omega

/-- At any failed rooted marking, every group of nonroot marked centers is
limited by the actual number of distinct outward neighbors, even if
shortest-path entries elsewhere are not optimized. -/
theorem outward_budget (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 1<Fintype.card V) (r : V) (two : ∃ s t, G.Adj r s ∧ G.Adj r t ∧ s≠t)
    (odd : Bool) (A : Finset V) (ai : Indep G A) :
    let P := parity G r odd
    let X := A∪P
    weightedLeaves G (eligible A P r)+bipartiteNum G<1+A.card+P.card →
    ∀ B⊆X.erase r,1+(if r∈X then G.degree r-2 else 0)+(outward G r B).card+
      bipartiteNum G<Fintype.card V+B.card := by
  classical
  intro P X bad B inc
  let D := X\(A∩P)
  let Y := X.erase r
  obtain ⟨p,hp,best⟩ := realizing_parents G hc r ∅ B
  obtain ⟨T,sub,tr,cross,take,star⟩ := predecessor_tree G hc r odd p hp
  obtain ⟨s,t,rs,rt,st⟩ := two
  have nr : r∉leaves T := fun leaf => st (leaf_unique T leaf (star s rs) (star t rt))
  have id := tree_defect T tr hn r nr A P (fun x hx y hy diff e => ai x hx y hy diff (sub e)) cross
  change Fintype.card V+(eligible A P r∩leaves T).card+(T.edgeFinset∩D.sym2).card=
    1+A.card+P.card+D.card+∑ v∈X,(T.degree v-2) at id
  have nz := failed_difference G hc hn r odd A ai bad
  have forest := forest_strict T tr D nz
  have lf : (eligible A P r∩leaves T).card≤weightedLeaves G (eligible A P r) :=
    le_sup (f:=fun K => (eligible A P r∩leaves K).card) (mem_filter.mpr ⟨mem_univ _,sub,tr⟩)
  have down (x : V) (xr : x≠r) : G.dist (p x) r<G.dist x r := by rw [(hp x xr).2]; omega
  have ub := (branch_linearization T tr r p (fun x => G.dist x r) down take Y (by simp [Y])).1 B inc
  have val : score G r ∅ B=∑ x∈univ.erase r,reward ∅ B x (p x) :=
    sum_congr rfl (fun x hx => best x (mem_erase.mp hx).1)
  rw [outward_score,reward_sum] at val
  simp only [erase_empty,filter_empty,card_empty,zero_add] at val
  have de : T.degree r=G.degree r := by
    have eq : T.neighborFinset r=G.neighborFinset r := by ext x; simp only [mem_neighborFinset]; exact ⟨fun e => sub e,star x⟩
    simpa only [card_neighborFinset_eq_degree] using congrArg Finset.card eq
  have se : (∑ v∈X,(T.degree v-2))=(if r∈X then G.degree r-2 else 0)+∑ v∈Y,(T.degree v-2) := by
    by_cases rx : r∈X
    · rw [if_pos rx,←de]; exact (add_sum_erase X (fun v => T.degree v-2) rx).symm
    · simp [rx,Y]
  omega

#print axioms failed_difference
#print axioms outward_score
#print axioms outward_budget
end Minimal180.HigherRank
