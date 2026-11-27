import OneBypass180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Graffiti318 Graffiti180 Rooted180 Converse180 Assembly180 HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At arbitrary deficit a connected spanning subgraph with independent
odd vertices pays one unit per deleted odd vertex or even degree excess.
Even-even edges used by the subgraph offset these costs. -/
theorem general_star_budget (G F : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel F.Adj]
    (fg : F≤G) (fc : F.Connected) (hn : 1<Fintype.card V) (r : V)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (oi : Indep F (univ\parity G r false))
    (S : Finset V) (odd : Disjoint S (parity G r false)) (con : Con F (univ\S))
    (a : V) (ae : a∈parity G r false) :
    bipartiteNum G+secondDegree G+1+S.card+(F.degree a-2)≤
      Fintype.card V+(F.edgeFinset∩(parity G r false).sym2).card := by
  classical
  let P := parity G r false
  have dom (v : V) (vs : v∈S) : Dominates F (univ\S) v := by
    obtain ⟨w,e⟩ := exists_adj F fc hn v
    have outside {z : V} (zs : z∈S) : z∈univ\P := mem_sdiff.mpr ⟨mem_univ _,disjoint_left.mp odd zs⟩
    exact ⟨w,mem_sdiff.mpr ⟨mem_univ _,fun ws => oi _ (outside vs) _ (outside ws) e.ne e⟩,e⟩
  obtain ⟨T,sub,tr,ls,star⟩ := leaves_and_star F fc hn S con dom a (fun h => disjoint_left.mp odd h ae)
  have lower := (support_obstruction G (fc.mono fg) hn r bad ∅).1
  have id := horizontal_identity T tr hn P (fun x hx y hy ne e => oi x hx y hy ne (sub e))
  have obj : (leaves T).card≤maxLeaves G := by
    simpa only [univ_inter,weighted_all] using score_of_tree G T (sub.trans fg) tr univ
  have lf := card_le_card (show S⊆leaves T\P from fun _ vs => mem_sdiff.mpr ⟨ls vs,disjoint_left.mp odd vs⟩)
  have inc : F.neighborFinset a⊆T.neighborFinset a := fun x hx => (T.mem_neighborFinset ..).mpr (star x ((F.mem_neighborFinset ..).mp hx))
  have deg := card_le_card inc
  rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at deg
  have edges := card_le_card (inter_subset_inter (edgeFinset_mono sub) (Subset.rfl : P.sym2⊆P.sym2))
  have exc : T.degree a-2≤∑ v∈P,(T.degree v-2) := single_le_sum (f:=fun v => T.degree v-2) (fun _ _ => Nat.zero_le _) ae
  rw [even_equiv] at bad lower
  change independence G+secondDegree G≤P.card at lower
  change maxLeaves G+bipartiteNum G<1+independence G+P.card at bad
  change _≤Fintype.card V+(F.edgeFinset∩P.sym2).card
  omega

/-- Odd pendant vertices of the crossing graph are forced in every one
of its spanning trees. Their count can be added to the excess degree
of any even star chosen in that graph. -/
theorem pendant_star (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r) (a : V) (ae : a∈parity G r false) :
    let P := parity G r false
    let H := alternating G P
    let S := leaves H\P
    bipartiteNum G+secondDegree G+1+S.card+(H.degree a-2)≤Fintype.card V := by
  classical
  intro P H S
  have hc := (alternating_parity G gc r false).1
  obtain ⟨K,sub,kt⟩ := hc.exists_isTree_le
  obtain ⟨T,th,tr,star,_⟩ := full_star_exchange H K sub kt hn a
  have lf (v : V) (m : v∈S) : v∈leaves T := leaf_of_unique T tr.isConnected hn v
    (fun e f => leaf_unique H (mem_sdiff.mp m).1 (th e) (th f))
  have cap := card_le_card (show S⊆leaves T\P from fun v m => mem_sdiff.mpr ⟨lf v m,(mem_sdiff.mp m).2⟩)
  have nb : H.neighborFinset a⊆T.neighborFinset a := fun x h => (T.mem_neighborFinset ..).mpr (star x ((H.mem_neighborFinset ..).mp h))
  have deg := card_le_card nb
  rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at deg
  have bill := parity_tree_budget G gc hn r bad T tr th
  change bipartiteNum G+secondDegree G+1+(leaves T\P).card+(∑ v∈P,(T.degree v-2))≤Fintype.card V at bill
  have exc : T.degree a-2≤∑ v∈P,(T.degree v-2) := single_le_sum (f:=fun v => T.degree v-2) (fun _ _ => Nat.zero_le _) ae
  omega

/-- In particular, two odd leaves of the crossing graph at a maximizing
root settle the entire deficit-three branch, including second degree one. -/
theorem conjecture180_two_odd_pendants (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (rk : Fintype.card V≤bipartiteNum G+3) (r : V) (mx : evenCount G r=maxEven G)
    (two : 2≤(leaves (alternating G (parity G r false))\parity G r false).card) :
    1+independence G+maxEven G≤maxLeaves G+bipartiteNum G := by
  classical
  rw [←mx]; by_contra! bad
  have lower := (secondDegree_properties G gc hn).1
  have bill := pendant_star G gc hn r bad r (by simp [dist_self])
  omega

#print axioms general_star_budget
#print axioms pendant_star
#print axioms conjecture180_two_odd_pendants
end Minimal180.PortParity
