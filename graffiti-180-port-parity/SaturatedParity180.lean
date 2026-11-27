import SupportRank180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Graffiti318 Graffiti180 Rooted180 Converse180 Assembly180 HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At the first deficit above the degree bound a failed ordinary
marking forces equality in both underlying leaf inequalities. -/
theorem saturated_counts (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (rank : Fintype.card V≤bipartiteNum G+secondDegree G+1)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r) :
    Fintype.card V=bipartiteNum G+secondDegree G+1 ∧
    evenCount G r=independence G+secondDegree G ∧
    maxLeaves G+Fintype.card V=2*evenCount G r+1 ∧
    Indep G (oddSet G r) := by
  classical
  have ⟨small,comp⟩ := support_obstruction G gc hn r bad ∅
  rw [union_empty,card_empty,add_zero] at comp
  obtain ⟨M,sub,ind,mass⟩ := independentReps G (oddSet G r)
  have part := odd_partition G r
  have sup := card_le_card sub
  have lb := (Graffiti169.parity_bounds G gc hn r).1
  change 2*evenCount G r+1≤Fintype.card V+maxLeaves G at lb
  have eq : M=oddSet G r := eq_of_subset_of_card_le sub (by omega)
  exact ⟨by omega,by omega,by omega,eq ▸ ind⟩

/-- Every spanning tree of the parity-crossing graph is globally optimal.
All of its leaves are even, and each even vertex has degree at most two. -/
theorem saturated_tree (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (rank : Fintype.card V≤bipartiteNum G+secondDegree G+1)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (T : SimpleGraph V) [DecidableRel T.Adj] (tr : T.IsTree) (sub : T≤alternating G (parity G r false)) :
    (leaves T).card=maxLeaves G ∧ leaves T⊆parity G r false ∧
      ∀ x∈parity G r false,T.degree x≤2 := by
  classical
  let P := parity G r false
  have eq := (saturated_counts G gc hn r rank bad).2.2.1
  rw [even_equiv] at eq
  have cap : (leaves T).card≤maxLeaves G := by
    simpa only [univ_inter,weighted_all] using
      score_of_tree G T (fun _ _ e => (sub e).1) tr univ
  have independent : Short177.Indep T P := fun _ x _ y _ e => ((sub e).2.mp x) y
  have count := @Graffiti169.tree_budget_excess V _ _ T ‹DecidableRel T.Adj› tr hn P independent
  change 2*P.card+1+(∑ x∈P,(T.degree x-2))≤Fintype.card V+(P∩leaves T).card at count
  change maxLeaves G+Fintype.card V=2*P.card+1 at eq
  have inc : P∩leaves T⊆leaves T := inter_subset_right
  have sm := card_le_card inc
  have all : P∩leaves T=leaves T := eq_of_subset_of_card_le inc (by omega)
  refine ⟨by omega,fun v h => (mem_inter.mp (all.symm ▸ h)).1,?_⟩
  intro x hx
  have single := single_le_sum (s:=P) (f:=fun v => T.degree v-2) (fun _ _ => Nat.zero_le _) hx
  change T.degree x-2≤∑ v∈P,(T.degree v-2) at single
  have zero : (∑ v∈P,(T.degree v-2))=0 := by omega
  rw [zero] at single
  exact Nat.le_of_sub_eq_zero (Nat.eq_zero_of_le_zero single)

#print axioms saturated_counts
#print axioms saturated_tree
end Minimal180.PortParity
