import SaturatedPair180
import ReturnBudget180
import Example180
set_option warningAsError true
namespace Minimal180.Controlled
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem all_neighbors_iff_degree (J : SimpleGraph V) [DecidableRel J.Adj] (C : Finset V)
    (x y : V) (k : ℕ) (ct : C.card=k+1) (tip : NeedsTip J C (univ\C) x y) :
    (∀ b∈C.erase x,J.Adj x b) ↔ J.degree x=k := by
  classical
  obtain ⟨sub,_,eq⟩ := second_neighborhood J C x y k ct tip
  rw [←eq]
  constructor
  · intro sat
    apply Subset.antisymm _ sub
    intro a ha
    by_cases ax : a=x
    · exact mem_insert.mpr (Or.inl ax)
    · exact mem_insert_of_mem ((J.mem_neighborFinset x a).mpr (sat a (mem_erase.mpr ⟨ax,ha⟩)))
  · intro e b h
    obtain ⟨bx,bc⟩ := mem_erase.mp h
    rw [e] at bc
    exact (J.mem_neighborFinset x b).mp ((mem_insert.mp bc).resolve_left bx)

end Minimal180.Controlled

namespace Minimal180.Case12
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Controlled
private noncomputable abbrev Z : Finset V := {3,11}
private noncomputable abbrev H : Finset V := {4,6,9,10}
private noncomputable abbrev R : Finset V := (univ\C)\Z

/-- Both possible failed tips have insufficient old degree to saturate any
second certificate. The general return-set test still certifies the repair. -/
theorem controlled_without_saturation :
    (∀ K:Finset V,K.card=weightedLeaves J U+1 →
      (NeedsTip J K (univ\K) 7 8 → ¬(∀ b∈K.erase 7,J.Adj 7 b)) ∧
      (NeedsTip J K (univ\K) 8 7 → ¬(∀ b∈K.erase 8,J.Adj 8 b))) ∧
    FirstForm J U 7 8 1 ∧
    (let L' := (C.erase 7\{2})∪Z
     L'=L ∧ Con G (univ\L') ∧ ∀ q∈L',Dominates G (univ\L') q) := by
  have two : remote J R 8={H} := by
    apply remote_eq_singleton J R {8} H 8 4 (by decide) (by decide) (by decide) (by decide)
    · exact con 8 (fun _ => 0) (by decide) (by decide)
    · exact con 4 (fun i => [88,88,88,88,0,88,2,88,88,1,1,88][i.val]!) (by decide) (by decide)
    · decide
  have join (P:Finset V) (h:P∈remote J R 8) : ∃ b∈({2}:Finset V),Dominates J P b := by
    have eq := mem_singleton.mp (two ▸ h)
    subst P
    exact ⟨2,by decide,10,by decide,by decide⟩
  have serve (q:V) (h:q∈demand J R C Z 7) : q∈({2}:Finset V) ∨ Dominates J {2} q := by
    obtain ⟨place,nr,nx⟩ := (mem_demand ..).mp h
    rcases (show ∀ i∈C.erase 7∪Z,Dominates J R i ∨ J.Adj i 7 by unfold Dominates; decide) q place with dom|adj
    · exact (nr dom).elim
    · exact (nx adj).elim
  have top : C.card=weightedLeaves J U+1 := by rw [old_score]; decide
  have tip := specified_exchange.1
  have cert := return_certificate J C {2} Z 7 8 (by decide) tip (by decide) (by decide)
    (by decide) join serve
  dsimp only at cert
  rw [add_eq] at cert
  refine ⟨?_,first_of_return_set J jc (by decide) 7 8 1 (by decide) (by decide) (by decide)
    (by decide) U C {2} Z (by decide) top tip (by decide) (by decide) (by decide) (by decide) join serve,
    by decide,cert⟩
  intro K size
  rw [old_score] at size
  constructor
  · intro k all
    exact (show J.degree 7≠4 by decide) ((all_neighbors_iff_degree J K 7 8 4 size k).mp all)
  · intro k all
    exact (show J.degree 8≠4 by decide) ((all_neighbors_iff_degree J K 8 7 4 size k).mp all)

#print axioms controlled_without_saturation
end Minimal180.Case12
