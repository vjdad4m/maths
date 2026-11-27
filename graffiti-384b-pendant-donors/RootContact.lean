import PendantDonor

namespace Graffiti384b.Donor
open Finset SimpleGraph
open private Repair.support_sub Repair.support_pos Repair.link_sum Repair.full_nbr from Repair384b
open private Remaining29.account from Remaining29
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- If no neighbor of the root has degree at least three, every triangle
through it uses two degree-two vertices, each in exactly one such triangle. -/
theorem low_neighbors (w : V) (none : ∀ x∈high G, ¬G.Adj w x) :
    2 * trianglesAt G w ≤ (LowSample.twos G).card := by
  classical
  let T := Repair.linkSupport G w
  have out : w∉T := fun wm => G.irrefl ((G.mem_neighborFinset ..).mp (Repair.support_sub G w wm))
  have counts (x : V) (xm : x∈T) : x∈LowSample.twos G ∧ nbr G x T≤1 := by
    have adj := (G.mem_neighborFinset ..).mp (Repair.support_sub G w xm)
    have nx : x∉high G := fun hh => none x hh adj
    have deg : G.degree x<3 := by simpa [high] using nx
    have off : 0<nbr G x Tᶜ := card_pos.mpr ⟨w,mem_filter.mpr ⟨mem_compl.mpr out,adj.symm⟩⟩
    have on := Repair.support_pos G xm
    change 1≤nbr G x T at on
    have total := Repair.full_nbr G x T
    exact ⟨mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,nx⟩,by omega⟩
  have cost := sum_le_sum (s:=T) (g:=fun _ => 1) (fun x xm => (counts x xm).2)
  have link := Repair.link_sum G w
  change ∑ x∈T,nbr G x T=2*trianglesAt G w at link
  simpa only [link,sum_const,nsmul_eq_mul,mul_one] using
    cost.trans (show (∑ _x∈T,1) ≤ (LowSample.twos G).card by
      simpa using card_le_card (fun x (xm : x∈T) => (counts x xm).1))

/-- In the two remaining nonleaf quotas the last exposure in the degree-five
regime is automatic: otherwise the two triangles at the root need four ears. -/
theorem pendant_at_floor_five (t : (types G).card=29) (h : (high G).card=27)
    (q : (nonleaves G).card≤30) {u v w : V} (uv : u≠v) (uw : u≠w) (vw : v≠w)
    (nu : G.neighborFinset u={v,w}) (nv : G.neighborFinset v={u,w}) (wh : w∈high G)
    (degree : ∀x∈(high G).erase w,5≤G.degree x) :
    ∃s : Finset V,u∈deficient G s ∧ v∈deficient G s ∧ nbr G u s=1 ∧
      s.card+(deficient G s).card+14≤Fintype.card V ∧ gamma G≤Fintype.card V-15 := by
  apply pendant_sample G t h uv uw vw nu nv wh
  refine Or.inr (Or.inr ⟨?_,degree⟩)
  have score := (Repair.maximal_diversity G (show (types G).card=(high G).card+2 by omega)).2.1 w wh
  have acc := Remaining29.account G
  obtain ⟨x,xh,adj⟩ : ∃x∈high G,G.Adj w x := by
    by_contra! none
    have := low_neighbors G w none
    omega
  exact card_pos.mpr ⟨x,mem_filter.mpr ⟨mem_erase.mpr ⟨adj.ne.symm,xh⟩,w,not_mem_erase w _,adj.symm⟩⟩

end Graffiti384b.Donor
#print axioms Graffiti384b.Donor.low_neighbors
#print axioms Graffiti384b.Donor.pendant_at_floor_five
