import PairColors180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The additional unit at the root only requires a nonempty symmetric
difference somewhere and a root in the union of the marks. -/
theorem marked_root_reserve (G : SimpleGraph V) (hc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A)
    (marked : r∈A∪parity G r p) (diff : ((A∪parity G r p)\(A∩parity G r p)).Nonempty) :
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
    have forest := forest_strict K kt D diff
    have branch := single_le_sum (f:=fun v => K.degree v-2) (fun v _ => Nat.zero_le _) marked
    change K.degree r-2≤∑ v∈X,(K.degree v-2) at branch
    have pay : (eligible A P r∩leaves K).card≤weightedLeaves G (eligible A P r) := le_sup
      (f:=fun T => (eligible A P r∩leaves T).card) (mem_filter.mpr ⟨mem_univ _,kg,kt⟩)
    change 1+A.card+P.card+(G.degree r-1)≤weightedLeaves G (eligible A P r)+Fintype.card V
    omega
  · have ok := weighted_order G hc hn r p.toNat A ai
    change A.card+P.card+1≤Fintype.card V+weightedLeaves G (eligible A P r) at ok
    change 1+A.card+P.card+(G.degree r-1)≤weightedLeaves G (eligible A P r)+Fintype.card V
    omega

theorem solo_root (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V) (r : V) (p : Bool)
    (A : Finset V) (ai : Indep G A) (bad : ¬Protected G r p A) (b : V) (rb : r≠b)
    (bi : TwoColor G (univ\{r,b})) (rk : r∈A∩insert r (parity G r p))
    (bk : b∉A∩insert r (parity G r p)) : p=false ∧ A=parity G r false := by
  classical
  let P := parity G r p
  have rig := solo_rigidity G gc hn r p A ai bad r b rb bi rk bk
  have pay := allowance_eq G gc hn r p A ai
  change 1+A.card+P.card+allowance G r p A=weightedLeaves G (eligible A P r)+Fintype.card V at pay
  have same : A=P := by
    by_contra ne
    have diff : ((A∪P)\(A∩P)).Nonempty := by
      by_contra empty
      apply ne
      ext x
      have off : x∉(A∪P)\(A∩P) := fun xm => empty ⟨x,xm⟩
      simp only [mem_sdiff,mem_union,mem_inter] at off
      tauto
    have hit := marked_root_reserve G gc hn r p A ai (mem_union_left _ (mem_inter.mp rk).1) diff
    change 1+A.card+P.card+(G.degree r-1)≤weightedLeaves G (eligible A P r)+Fintype.card V at hit
    obtain ⟨four,two,_⟩ := rig
    omega
  have rp : r∈P := same ▸ (mem_inter.mp rk).1
  cases p
  · exact ⟨rfl,same⟩
  · simp [P,mem_parity,dist_self] at rp

#print axioms marked_root_reserve
#print axioms solo_root
end Minimal180.PairRepair
