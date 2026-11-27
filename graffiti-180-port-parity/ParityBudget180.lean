import NearestPort180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem lost_marks (A P Q : Finset V) (x : V) (same : x∈Q → x∈P) :
    ((eligible A Q x)\((A∪P).erase x)).card=
      ((Q\P)\A).card+(if x∈A∩Q then 1 else 0) := by
  classical
  by_cases mark : x∈A∩Q
  · have eq : eligible A Q x\((A∪P).erase x)=insert x ((Q\P)\A) := by
      ext v
      simp only [mem_sdiff,eligible_iff,mem_erase,mem_union,mem_insert]
      by_cases h : v=x
      · subst v; obtain ⟨l,r⟩ := mem_inter.mp mark; tauto
      · tauto
    have no : x∉(Q\P)\A := fun h => (mem_sdiff.mp h).2 (mem_inter.mp mark).1
    rw [eq,card_insert_of_not_mem no,if_pos mark]
  · have eq : eligible A Q x\((A∪P).erase x)=(Q\P)\A := by
      ext v
      simp only [mem_sdiff,eligible_iff,mem_erase,mem_union]
      by_cases h : v=x
      · subst v; simp only [mem_inter,not_and] at mark; tauto
      · tauto
    rw [eq,if_neg mark,add_zero]

omit [Fintype V] [DecidableEq V] in
theorem near_zero (G : SimpleGraph V) (N : Finset V) (nz : N.Nonempty) {x : V} (xn : x∈N) :
    near G N nz x=0 := by
  have low : near G N nz x≤G.dist x x := inf'_le _ xn
  simpa only [dist_self,Nat.le_zero] using low

/-- The old rooted inequality at one attachment neighbor suffices when
the independent set pays for the signed change of parity classes and
the bipartite-order change pays the remaining endpoint costs. -/
theorem transfer_at_port (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N : Finset V) (nz : N.Nonempty) (A : Finset V) (a p : Bool) (x : V) (xn : x∈N) :
    let H := ear G N
    let P := nearParity G N nz (!p)
    let Q := parity G x (!p)
    let B := lift A a
    let C := parity H (.inr ()) p
    1+A.card+Q.card≤weightedLeaves G (eligible A Q x)+bipartiteNum G →
    bipartiteNum G+(P\Q).card+(a || !p).toNat+(if x∈A∩Q then 1 else 0)
        ≤bipartiteNum H+((Q\P)∩A).card →
    1+B.card+C.card≤weightedLeaves H (eligible B C (.inr ()) )+bipartiteNum H := by
  classical
  intro H P Q B C lower budget
  have agree : x∈Q → x∈P := by
    intro h
    change x∈parity G x (!p) at h
    simpa only [P,nearParity,mem_filter,mem_univ,true_and,near_zero G N nz xn,Nat.zero_mod] using
      (show 0=(!p).toNat by simpa only [mem_parity,dist_self,Nat.zero_mod] using h)
  have loss := restrict_leaves G (eligible A Q x) ((A∪P).erase x)
  rw [lost_marks A P Q x agree] at loss
  have attachBound := attach G gc hn N (A∪P) (a && !p) x xn
  have cdef : C=lift P (!p) := apex_parity G gc N nz p
  rw [cdef,apex_eligible,card_lift,card_lift]
  have cp := card_sdiff_add_card_inter P Q
  have cq := card_sdiff_add_card_inter Q P
  rw [inter_comm Q P] at cq
  have uncovered := card_sdiff_add_card_inter (Q\P) A
  have bools : (a && !p).toNat+(a || !p).toNat=a.toNat+(!p).toNat := by
    cases a <;> cases p <;> decide
  change 1+(A.card+a.toNat)+(P.card+(!p).toNat)≤
    weightedLeaves (ear G N) (lift (A∪P) (a && !p))+bipartiteNum H
  change weightedLeaves G ((A∪P).erase x)+(a && !p).toNat≤weightedLeaves H _ at attachBound
  change 1+(A.card+a.toNat)+(P.card+(!p).toNat)≤weightedLeaves H _+bipartiteNum H
  omega

#print axioms lost_marks
#print axioms near_zero
#print axioms transfer_at_port
end Minimal180.PortParity
