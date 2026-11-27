import LayerPayment180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem double_root (G : SimpleGraph V) (hc : G.Connected) (hn : 1<Fintype.card V) (r : V)
    (p : Bool) (A : Finset V) (ai : Indep G A) (ar : r∈A) :
    1+A.card+(parity G r p).card+(G.degree r-2)≤weightedLeaves G (eligible A (parity G r p) r)+Fintype.card V := by
  classical
  let P := parity G r p
  let X := A∪P
  let D := X\(A∩P)
  by_cases high : 1<G.degree r
  · let H := alternating G P
    obtain ⟨con,star⟩ := alternating_parity G hc r p
    obtain ⟨T,sub,tree⟩ := con.exists_isTree_le
    obtain ⟨K,kh,kt,keep,_⟩ := full_star_exchange H T sub tree hn r
    have kg : K≤G := fun _ _ e => (kh e).1
    have eq : K.neighborFinset r=G.neighborFinset r := by
      ext x; simp only [mem_neighborFinset];exact ⟨fun e => kg e,fun e => keep _ (star _ e)⟩
    have deg : K.degree r=G.degree r := by simpa only [card_neighborFinset_eq_degree] using congrArg card eq
    have internal : r∉leaves K := by intro m;have one : K.degree r=1 := (mem_filter.mp m).2;omega
    have id := tree_defect K kt hn r internal A P (fun x xm y ym ne e => ai x xm y ym ne (kg e)) (fun e => (kh e).2)
    change Fintype.card V+(eligible A P r∩leaves K).card+(K.edgeFinset∩D.sym2).card=
      1+A.card+P.card+D.card+∑ v∈X,(K.degree v-2) at id
    have forest : (K.edgeFinset∩D.sym2).card≤D.card := by
      rcases D.eq_empty_or_nonempty with nil|nz
      · simp [nil]
      · exact (forest_strict K kt D nz).le
    have branch := single_le_sum (f:=fun v => K.degree v-2) (fun v _ => Nat.zero_le _) (mem_union_left P ar)
    change K.degree r-2≤∑ v∈X,(K.degree v-2) at branch
    have pay : (eligible A P r∩leaves K).card≤weightedLeaves G (eligible A P r) :=
      le_sup (f:=fun T => (eligible A P r∩leaves T).card) (mem_filter.mpr ⟨mem_univ _,kg,kt⟩)
    change 1+A.card+P.card+(G.degree r-2)≤weightedLeaves G (eligible A P r)+Fintype.card V
    omega
  · have ok := weighted_order G hc hn r p.toNat A ai
    change A.card+P.card+1≤Fintype.card V+weightedLeaves G (eligible A P r) at ok
    change 1+A.card+P.card+(G.degree r-2)≤weightedLeaves G (eligible A P r)+Fintype.card V
    omega

/-- Every doubly marked vertex, at any distance, contributes its full
graph degree minus two to the order bound. -/
theorem double_degree (G : SimpleGraph V) (hc : G.Connected) (hn : 2<Fintype.card V) (r t : V)
    (p : Bool) (A : Finset V) (ai : Indep G A) (at' : t∈A) (pt : t∈parity G r p) :
    1+A.card+(parity G r p).card+(G.degree t-2)≤weightedLeaves G (eligible A (parity G r p) r)+Fintype.card V := by
  classical
  by_cases tr : t=r
  · subst t;exact double_root G hc (by omega) r p A ai at'
  let H := alternating G (parity G r p)
  have incl : H.neighborFinset t⊆G.neighborFinset t := fun y ym =>
    (G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp ym).1
  have sum := card_sdiff_add_card_eq_card incl
  rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at sum
  have score := layer_payment G hc hn r t p A ai tr at' pt
  change 1+A.card+(parity G r p).card+(G.neighborFinset t\H.neighborFinset t).card+(H.degree t-2)≤
    weightedLeaves G (eligible A (parity G r p) r)+Fintype.card V at score
  omega

#print axioms double_root
#print axioms double_degree
end Minimal180.Transversals
