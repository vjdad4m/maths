import PairColors180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def ClosedIn (G : SimpleGraph V) (R C : Finset V) := ∀ x∈R,∀ y∈R,G.Adj x y → (x∈C ↔ y∈C)
noncomputable def toggled (C : Finset V) (c : V→Bool) (x : V) := if x∈C then !(c x) else c x

omit [Fintype V] in
theorem toggle_proper (G : SimpleGraph V) (R C : Finset V) (c : V→Bool)
    (cp : ProperOn G R c) (closed : ClosedIn G R C) : ProperOn G R (toggled C c) := by
  intro x xm y ym ed
  have same := closed x xm y ym ed
  by_cases xc : x∈C
  · simpa [toggled,xc,same.mp xc] using cp x xm y ym ed
  · simpa [toggled,xc,mt same.mpr xc] using cp x xm y ym ed

/-- Every closed part of the bipartite remainder contains the same
number of neighbors of the protected degree-four tip of each color. -/
theorem component_balance (G : SimpleGraph V) (a b : V) (solo : G.degree a=4 ∧
    ∀ c : V→Bool,ProperOn G (univ\{a,b}) c → ∀ s,(sideNeighbors G a c s).card=2)
    (C : Finset V) (cut : ClosedIn G (univ\{a,b}) C) (c : V→Bool) (cp : ProperOn G (univ\{a,b}) c) :
    (sideNeighbors G a c false∩C).card=(sideNeighbors G a c true∩C).card ∧
      (G.neighborFinset a∩C).card=2*(sideNeighbors G a c true∩C).card := by
  classical
  let L := sideNeighbors G a c false
  let H := sideNeighbors G a c true
  have orig : L.card=2 := solo.2 c cp false
  have changed := solo.2 (toggled C c) (toggle_proper G _ C c cp cut) false
  have eq : sideNeighbors G a (toggled C c) false=(L\C)∪(H∩C) := by
    ext x
    by_cases m : x∈C <;> cases val : c x <;> simp [L,H,sideNeighbors,toggled,m,val]
  have sep : Disjoint (L\C) (H∩C) := disjoint_left.mpr (fun _ xm ym => (mem_sdiff.mp xm).2 (mem_inter.mp ym).2)
  rw [eq,card_union_of_disjoint sep] at changed
  have count := card_sdiff_add_card_inter L C
  have balanced : (L∩C).card=(H∩C).card := by omega
  have split : G.neighborFinset a∩C=(L∩C)∪(H∩C) := by
    ext x;cases val : c x <;> simp [L,H,sideNeighbors,val]
  have d : Disjoint (L∩C) (H∩C) := disjoint_left.mpr (fun x xm ym => Bool.noConfusion
    (((mem_filter.mp (mem_inter.mp xm).1).2).symm.trans ((mem_filter.mp (mem_inter.mp ym).1).2)))
  rw [split,card_union_of_disjoint d]
  exact ⟨balanced,by change (L∩C).card+(H∩C).card=2*(H∩C).card;omega⟩

#print axioms toggle_proper
#print axioms component_balance
end Minimal180.PairRepair
