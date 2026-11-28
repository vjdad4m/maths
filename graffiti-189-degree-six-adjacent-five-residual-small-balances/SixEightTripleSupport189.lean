import SixEightTripleCoreClosure189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem eight_triple_support (D C : Finset V) (cd : C⊆D) (d8 : D.card=8) (c5 : C.card=5)
    (core : ∀ u∈C,5≤(inside G D u).card) (minimum : ∀ u∈D,3≤(inside G D u).card)
    {a z h : V} (ad : a∈D) (zd : z∈D) (hd : h∈D) (az : a≠z) (zh : z≠h)
    (zc : z∉C) (hc : h∉C) (backup : 4≤(inside G D h).card ∨ ¬G.Adj z h) :
    RouteOn G D a z := by
  classical
  let U := ↑(↑D : Set V)
  let J := G.induce (↑D : Set V)
  let M := univ.filter (fun u : U=>u.val∈C)
  have n8 : Fintype.card U=8 := (Fintype.card_coe D).trans d8
  have exactC : M.card=C.card := by
    apply card_bij (fun (j : U) _=>j.val)
    · intro j m
      exact (mem_filter.mp m).2
    · intro j _ k _ e
      exact Subtype.ext e
    · intro z zm
      exact ⟨⟨z,cd zm⟩,mem_filter.mpr ⟨mem_univ _,zm⟩,rfl⟩
  have C5 (u : U) (um : u∈M) : 5≤J.degree u := by
    rw [←inside_card_eq_degree_induce]
    exact core _ (mem_filter.mp um).2
  have base (u : U) : 3≤J.degree u := by
    rw [←inside_card_eq_degree_induce]
    exact minimum _ u.property
  let a' : U := ⟨a,ad⟩
  let z' : U := ⟨z,zd⟩
  let h' : U := ⟨h,hd⟩
  have az' : a'≠z' := fun e=>az (congrArg Subtype.val e)
  have zh' : z'≠h' := fun e=>zh (congrArg Subtype.val e)
  have zb : z'∉M := fun e=>zc (mem_filter.mp e).2
  have hb : h'∉M := fun e=>hc (mem_filter.mp e).2
  have back : 4≤J.degree h' ∨ ¬J.Adj z' h' := by
    rcases backup with d|no
    · left
      rw [←inside_card_eq_degree_induce]
      exact d
    exact .inr no
  obtain ⟨p,pp,ps⟩ := eight_triple_core_closure (G:=J) n8 M (exactC.trans c5) C5 base az' zh' zb hb back
  exact lift_side_path D p pp ps

#print axioms eight_triple_support
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
