import PrimeObstruction180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A root in the symmetric difference of the independent and parity
marks pays for its degree minus one in missing witness vertices. -/
theorem root_reserve (G : SimpleGraph V) (hc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A)
    (singly : r∈(A∪parity G r p)\(A∩parity G r p)) :
    1+A.card+(parity G r p).card+(G.degree r-1)≤
      weightedLeaves G (eligible A (parity G r p) r)+Fintype.card V := by
  classical
  let P := parity G r p
  let X := A∪P
  let D := X\(A∩P)
  by_cases high : 1<G.degree r
  · let H := alternating G P
    obtain ⟨con,star⟩ := alternating_parity G hc r p
    obtain ⟨T,ts,tt⟩ := con.exists_isTree_le
    obtain ⟨K,kh,kt,keep,_⟩ := full_star_exchange H T ts tt hn r
    have kg : K≤G := fun _ _ e => (kh e).1
    have eq : K.neighborFinset r=G.neighborFinset r := by
      ext x; simp only [mem_neighborFinset]
      exact ⟨fun e => kg e,fun e => keep _ (star _ e)⟩
    have deg : K.degree r=G.degree r := by simpa only [card_neighborFinset_eq_degree] using congrArg card eq
    have internal : r∉leaves K := by
      intro m
      have one : K.degree r=1 := (mem_filter.mp m).2
      omega
    have id := tree_defect K kt hn r internal A P (fun x xm y ym ne e => ai x xm y ym ne (kg e))
      (fun e => (kh e).2)
    change Fintype.card V+(eligible A P r∩leaves K).card+(K.edgeFinset∩D.sym2).card=
      1+A.card+P.card+D.card+∑ v∈X,(K.degree v-2) at id
    have forest := forest_strict K kt D ⟨r,singly⟩
    have branch := single_le_sum (f:=fun v => K.degree v-2) (fun v _ => Nat.zero_le _) (mem_sdiff.mp singly).1
    change K.degree r-2≤∑ v∈X,(K.degree v-2) at branch
    have pay : (eligible A P r∩leaves K).card≤weightedLeaves G (eligible A P r) := le_sup
      (f:=fun T => (eligible A P r∩leaves T).card) (mem_filter.mpr ⟨mem_univ _,kg,kt⟩)
    change 1+A.card+P.card+(G.degree r-1)≤weightedLeaves G (eligible A P r)+Fintype.card V
    omega
  · have ok := weighted_order G hc hn r p.toNat A ai
    change A.card+P.card+1≤Fintype.card V+weightedLeaves G (eligible A P r) at ok
    change 1+A.card+P.card+(G.degree r-1)≤weightedLeaves G (eligible A P r)+Fintype.card V
    omega

theorem odd_reserve (G : SimpleGraph V) (hc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (I : Finset V) (ii : Indep G I) (ir : r∈I) :
    1+I.card+(parity G r true).card+(G.degree r-1)≤
      weightedLeaves G (eligible I (parity G r true) r)+Fintype.card V := by
  apply root_reserve G hc hn r true I ii
  simp [ir,mem_parity,dist_self]

/-- Isolating the root spends all its neighbors and earns the adjacent
true-twin credit. The remaining vertices need only induce a bipartite graph. -/
theorem odd_isolate (G : SimpleGraph V) (hc : G.Connected) (hn : 1<Fintype.card V) (r : V)
    (bi : TwoColor G (univ\G.neighborFinset r)) (I : Finset V) (ii : Indep G I) (ir : r∈I) :
    OddRootTest G r I := by
  classical
  let Z := univ\G.neighborFinset r
  have cover : I⊆Z := by
    intro x xi
    apply mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro m; have ed := (G.mem_neighborFinset r x).mp m
    exact ii r ir x xi ed.ne ed
  have isolated (x : V) (xm : x∈Z) (ed : G.Adj r x) := (mem_sdiff.mp xm).2 ((G.mem_neighborFinset _ _).mpr ed)
  have cost := card_sdiff_add_card_eq_card (subset_univ (G.neighborFinset r))
  change Z.card+(G.neighborFinset r).card=(univ : Finset V).card at cost
  rw [card_neighborFinset_eq_degree,card_univ] at cost
  have ok := odd_reserve G hc hn r I ii ir
  refine ⟨Z,bi,insert_subset (cover ir) (inter_subset_left.trans cover),?_⟩
  rw [bonus,if_pos isolated];omega

#print axioms root_reserve
#print axioms odd_reserve
#print axioms odd_isolate
end Minimal180.Transversals
