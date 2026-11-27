import CutEntry180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Graffiti318 Graffiti180 Rooted180 Converse180 Assembly180
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem odd_partition (G : SimpleGraph V) (r : V) :
    evenCount G r+(oddSet G r).card=Fintype.card V := by
  classical
  simpa only [evenCount,oddSet,dist_comm (u:=r),card_univ] using
    (filter_card_add_filter_neg_card_eq_card (s:=(univ : Finset V)) (p:=fun x => G.dist x r%2=0))

/-- At any failing root, every augmentation of the odd layers must have
many induced components. The deficit is unrestricted. -/
theorem support_obstruction (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (fail : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (C : Finset V) :
    independence G+secondDegree G≤evenCount G r ∧
    bipartiteNum G+secondDegree G<evenCount G r+C.card+compCount G (oddSet G r∪C) := by
  classical
  let Q := oddSet G r
  let S := Q∪C
  have lo := Graffiti177.conjecture177 G hc hn
  obtain ⟨y,ry⟩ := exists_adj G hc hn r
  have ys : y∈S := mem_union_left _ (show y∈Q by simp [Q,oddSet,dist_eq_one_iff_adj.mpr ry.symm])
  have conn : (incidentGraph G S).Connected := by
    apply (alternating_parity G hc r false).1.mono
    intro a b e
    refine ⟨e.1,?_⟩
    have h := e.2
    simp only [mem_parity,Bool.toNat_false] at h
    have oq (z : V) : z∈Q ↔ G.dist z r%2≠0 := by simp [Q,oddSet]
    by_cases az : G.dist a r%2=0
    · exact Or.inr (mem_union_left _ ((oq b).mpr (h.mp az)))
    · exact Or.inl (mem_union_left _ ((oq a).mpr az))
  have leaf := incident_leaf G S ⟨y,ys⟩ hn conn
  have un : S.card≤Q.card+C.card := card_union_le .. 
  have part := odd_partition G r
  change evenCount G r+Q.card=Fintype.card V at part
  change _ ∧ bipartiteNum G+secondDegree G<evenCount G r+C.card+compCount G S
  constructor <;> omega

/-- Ordinary #180 throughout the class in which the odd-cycle transversal
number is at most the second smallest degree. -/
theorem conjecture180_of_second_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hn : 1<Fintype.card V)
    (rk : Fintype.card V≤bipartiteNum G+secondDegree G) :
    1+independence G+maxEven G≤maxLeaves G+bipartiteNum G := by
  classical
  haveI : Nonempty V := hc.nonempty
  obtain ⟨r,_,mx⟩ := exists_mem_eq_sup (s:=univ) (f:=evenCount G) univ_nonempty
  change maxEven G=evenCount G r at mx
  rw [mx]
  by_contra! fail
  have bad := (support_obstruction G hc hn r fail ∅).2
  rw [union_empty,card_empty,add_zero] at bad
  obtain ⟨M,sub,_,q⟩ := independentReps G (oddSet G r)
  have bd := card_le_card sub
  have part := odd_partition G r
  omega

#print axioms support_obstruction
#print axioms conjecture180_of_second_degree
end Minimal180.HigherRank
