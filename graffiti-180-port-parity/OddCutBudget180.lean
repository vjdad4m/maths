import SaturatedParity180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Graffiti318 Graffiti180 Rooted180 Converse180 Assembly180 HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At any failed root, the number of odd leaves plus all excess degrees
on even vertices of any parity-crossing spanning tree falls strictly
below the deficit minus the second-smallest degree. -/
theorem parity_tree_budget (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (T : SimpleGraph V) [DecidableRel T.Adj] (tr : T.IsTree) (sub : T≤alternating G (parity G r false)) :
    bipartiteNum G+secondDegree G+1+((leaves T)\parity G r false).card+
      (∑ v∈parity G r false,(T.degree v-2))≤Fintype.card V := by
  classical
  let P := parity G r false
  have small := (support_obstruction G gc hn r bad ∅).1
  have independent : Short177.Indep T P := fun _ x _ y _ e => ((sub e).2.mp x) y
  have count := @Graffiti169.tree_budget_excess V _ _ T ‹DecidableRel T.Adj› tr hn P independent
  change 2*P.card+1+(∑ v∈P,(T.degree v-2))≤Fintype.card V+(P∩leaves T).card at count
  have cap : (leaves T).card≤maxLeaves G := by
    simpa only [univ_inter,weighted_all] using score_of_tree G T (fun _ _ e => (sub e).1) tr univ
  have split := card_sdiff_add_card_inter (leaves T) P
  rw [inter_comm (leaves T) P] at split
  rw [even_equiv] at small bad
  change independence G+secondDegree G≤P.card at small
  change maxLeaves G+bipartiteNum G<1+independence G+P.card at bad
  change bipartiteNum G+secondDegree G+1+(leaves T\P).card+(∑ v∈P,(T.degree v-2))≤_
  omega

/-- For any set of odd vertices whose simultaneous removal leaves the
parity-crossing graph connected, a failed ordinary root pays one unit
of deficit per removed vertex. This includes cut vertices in G. -/
theorem removable_odds_budget (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (S : Finset V) (outside : Disjoint S (parity G r false))
    (keep : Con (alternating G (parity G r false)) (univ\S)) :
    bipartiteNum G+secondDegree G+1+S.card≤Fintype.card V := by
  classical
  let P := parity G r false
  let H := alternating G P
  let D : Finset V := univ\S
  have hc := (alternating_parity G gc r false).1
  have dom : ∀ x∉D,Dominates H D x := by
    intro x out
    have xs : x∈S := by simpa [D] using out
    obtain ⟨y,xy⟩ := exists_adj H hc hn x
    have yp : y∈P := by
      by_contra no
      exact disjoint_left.mp outside xs (xy.2.mpr no)
    exact ⟨y,mem_sdiff.mpr ⟨mem_univ _,fun ys => disjoint_left.mp outside ys yp⟩,xy⟩
  have bound := weightedCore H D S keep dom
  have diff : S\D=S := by ext x; simp [D]
  rw [diff] at bound
  obtain ⟨T,sub,tree,opt⟩ := tree_opt H hc S
  rw [←opt] at bound
  have inc : S∩leaves T⊆leaves T\P := fun _ h =>
    mem_sdiff.mpr ⟨(mem_inter.mp h).2,disjoint_left.mp outside (mem_inter.mp h).1⟩
  have cap := card_le_card inc
  have bud := parity_tree_budget G gc hn r bad T tree sub
  change bipartiteNum G+secondDegree G+1+(leaves T\P).card+_≤_ at bud
  omega

/-- In particular every odd vertex must disconnect the vertical graph
upon deletion when the deficit is at most one above the degree bound. -/
theorem odd_is_cut (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (rank : Fintype.card V≤bipartiteNum G+secondDegree G+1)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (v : V) (odd : v∉parity G r false) :
    ¬Con (alternating G (parity G r false)) (univ.erase v) := by
  classical
  intro conn
  have budget := removable_odds_budget G gc hn r bad {v} (by simpa using odd)
    (by simpa only [sdiff_singleton_eq_erase] using conn)
  rw [card_singleton] at budget
  omega

#print axioms parity_tree_budget
#print axioms removable_odds_budget
#print axioms odd_is_cut
end Minimal180.PortParity
