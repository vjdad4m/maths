import BicycleTaggedPortCounts133

namespace Graffiti133Bicycle
open SimpleGraph Finset
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {B : Finset V}

noncomputable def TaggedFamily.loopsAt (F : TaggedFamily G B) (z : V) :
    Finset {S // S∈F.sets} :=
  F.sets.attach.filter (fun S => F.head S=z ∧ (F.channel S).b=z)

noncomputable def TaggedFamily.crosses (F : TaggedFamily G B) :
    Finset {S // S∈F.sets} :=
  F.sets.attach.filter (fun S => F.head S≠(F.channel S).b)

private theorem degree_split_two_hubs [DecidableRel G.Adj] (u v : V) :
    ((G.neighborFinset u)\({u,v} : Finset V)).card +
      (if G.Adj u v then 1 else 0) = G.degree u := by
  classical
  have X : (G.neighborFinset u)\({u,v} : Finset V) = (G.neighborFinset u).erase v := by
    ext w
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,Finset.mem_erase]
    constructor
    · rintro ⟨h,n⟩
      exact ⟨fun eq=>n (Or.inr eq),h⟩
    · rintro ⟨n,e⟩
      refine ⟨e,fun hh=>?_⟩
      rcases hh with h|h
      · exact ((G.mem_neighborFinset u w).mp e).ne h.symm
      · exact n h
  rw [X,←G.card_neighborFinset_eq_degree]
  by_cases e : G.Adj u v
  · rw [if_pos e]
    exact Finset.card_erase_add_one ((G.mem_neighborFinset u v).mpr e)
  · rw [if_neg e,Finset.erase_eq_of_not_mem (fun h=>e ((G.mem_neighborFinset u v).mp h)),Nat.add_zero]

private theorem weight_two_hubs {u v : V} (ne : u≠v)
    (F : TaggedFamily G ({u,v} : Finset V)) (S : {S // S∈F.sets}) :
    (if u=F.head S then (1:Nat) else 0)+(if u=(F.channel S).b then 1 else 0) =
      2*(if F.head S=u ∧ (F.channel S).b=u then 1 else 0)
        +(if F.head S≠(F.channel S).b then 1 else 0) := by
  have a : F.head S=u ∨ F.head S=v := by simpa using F.head_mem S
  have b : (F.channel S).b=u ∨ (F.channel S).b=v := by simpa using (F.channel S).bIn
  rcases a with p|p <;> rcases b with q|q <;> simp [p,q,ne,ne.symm]

theorem TaggedFamily.hub_incidence_count [DecidableRel G.Adj] {u v : V} (ne : u≠v)
    (F : TaggedFamily G ({u,v} : Finset V)) :
    2*(F.loopsAt u).card+F.crosses.card+(if G.Adj u v then 1 else 0) = G.degree u := by
  classical
  have h := F.outside_neighbor_count u (by simp)
  have pp := degree_split_two_hubs (G:=G) u v
  rw [h] at pp
  rw [Finset.sum_congr rfl (fun S _=>weight_two_hubs ne F S),Finset.sum_add_distrib,←Finset.mul_sum] at pp
  unfold TaggedFamily.loopsAt TaggedFamily.crosses
  rw [Finset.card_filter,Finset.card_filter]
  exact pp

theorem TaggedFamily.two_degree_three_partition [DecidableRel G.Adj] {u v : V} (ne : u≠v)
    (F : TaggedFamily G ({u,v} : Finset V)) (du : G.degree u=3) (dv : G.degree v=3) :
    let delta : Nat := if G.Adj u v then 1 else 0
    ((F.loopsAt u).card=0 ∧ (F.loopsAt v).card=0 ∧ F.crosses.card+delta=3) ∨
      ((F.loopsAt u).card=1 ∧ (F.loopsAt v).card=1 ∧ F.crosses.card+delta=1) := by
  classical
  let delta : Nat := if G.Adj u v then 1 else 0
  change ((F.loopsAt u).card=0 ∧ (F.loopsAt v).card=0 ∧ F.crosses.card+delta=3) ∨
    ((F.loopsAt u).card=1 ∧ (F.loopsAt v).card=1 ∧ F.crosses.card+delta=1)
  let FF : TaggedFamily G ({v,u} : Finset V) := (show ({u,v} : Finset V)={v,u} by
    ext x; simp [or_comm]) ▸ F
  have a := F.hub_incidence_count ne
  have b := FF.hub_incidence_count ne.symm
  have b' : 2*(F.loopsAt v).card+F.crosses.card+delta=G.degree v := by
    have hr : ∀ (D E : Finset V) (h : D=E) (P : TaggedFamily G D),
        ((h ▸ P : TaggedFamily G E).loopsAt v).card=(P.loopsAt v).card ∧
        (h ▸ P : TaggedFamily G E).crosses.card=P.crosses.card := by
      intro D E h P
      subst E
      exact ⟨rfl,rfl⟩
    obtain ⟨bb,cc⟩ := hr _ _ (show ({u,v}:Finset V)={v,u} by ext x; simp [or_comm]) F
    change (FF.loopsAt v).card=(F.loopsAt v).card at bb
    change FF.crosses.card=F.crosses.card at cc
    have ss : (if G.Adj v u then (1:Nat) else 0)=(if G.Adj u v then 1 else 0) :=
      if_congr (G.adj_comm v u) rfl rfl
    rw [bb,cc,ss] at b
    exact b
  change 2*(F.loopsAt u).card+F.crosses.card+delta=G.degree u at a
  omega

#print axioms TaggedFamily.hub_incidence_count
#print axioms TaggedFamily.two_degree_three_partition
end Graffiti133Bicycle
