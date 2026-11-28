import SixSevenHighCoreRoute189
import SixSingletonDarkOre189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private erase_internal_deg from SixSingletonDarkOre189
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem erase_avoids_nonneighbor (D : Finset V) {z w : V} (no : ¬G.Adj w z) :
    inside G (D.erase z) w=inside G D w := by
  ext u
  simp only [inside,mem_filter,mem_erase]
  exact ⟨fun h=>⟨h.1.2,h.2⟩,fun h=>⟨⟨fun e=>no (e ▸ h.2),h.1⟩,h.2⟩⟩

/-- A degree-one or degree-two vertex can be appended to a terminal path
through the other seven, when those seven contain a five-vertex high
core and have no other vertex below dark degree four. -/
theorem eight_remove_one_low_route (D C L : Finset V) (lC : L⊆C) (cd : C⊆D)
    (d8 : D.card=8) (c5 : 5≤C.card) (l2 : 2≤L.card)
    {z : V} (zd : z∈D) (zc : z∉C) (low : (inside G D z).card≤2)
    (pos : ∃ w∈D,G.Adj w z)
    (high : ∀ w∈C,5≤(inside G D w).card)
    (rest : ∀ w∈D,w≠z → 4≤(inside G D w).card) :
    ∃ l∈L,RouteOn G D l z := by
  classical
  let E := D.erase z
  have e7 : E.card=7 := by change (D.erase z).card=7; rw [card_erase_of_mem zd,d8]
  have cE : C⊆E := fun w wm=>mem_erase.mpr ⟨fun e=>zc (e ▸ wm),cd wm⟩
  have three (w : V) (wm : w∈E) : 3≤(inside G E w).card := by
    have ⟨wz,wd⟩ := mem_erase.mp wm
    have h := rest w wd wz
    have r := erase_internal_deg (G:=G) D z w
    change (inside G D w).card≤(inside G E w).card+1 at r
    omega
  have on (w : V) (wm : w∈E) (slow : (inside G E w).card≤3) : G.Adj w z := by
    by_contra no
    have eq := erase_avoids_nonneighbor (G:=G) D no
    change inside G E w=inside G D w at eq
    have ⟨wz,wd⟩ := mem_erase.mp wm
    have g := rest w wd wz
    rw [eq] at slow
    omega
  have fill {w : V} (wm : w∈E) (wz : G.Adj w z)
      (exit : ∀ l∈L,l≠w → RouteOn G E l w) : ∃ l∈L,RouteOn G D l z := by
    obtain ⟨l,lm,lw⟩ := exists_ne_of_one_lt_card (s:=L) (by omega) w
    have r := (exit l lm lw).suffix wz (by simp [E])
    change RouteOn G (insert z (D.erase z)) l z at r
    rw [insert_erase zd] at r
    exact ⟨l,lm,r⟩
  by_cases two : ∃ x∈E,∃ y∈E,x≠y ∧ (inside G E x).card≤3 ∧ (inside G E y).card≤3
  · obtain ⟨x,xE,y,yE,xy,xlow,ylow⟩ := two
    have xz := on x xE xlow
    have yz := on y yE ylow
    have xf : x∈inside G D z := mem_filter.mpr ⟨(mem_erase.mp xE).2,xz.symm⟩
    have yf : y∈inside G D z := mem_filter.mpr ⟨(mem_erase.mp yE).2,yz.symm⟩
    have eq : inside G D z=({x,y}:Finset V) := by
      have sub : ({x,y}:Finset V)⊆inside G D z := insert_subset xf (singleton_subset_iff.mpr yf)
      apply (eq_of_subset_of_card_le sub ?_).symm
      rw [card_insert_of_not_mem (by simpa using xy),card_singleton]
      exact low
    have xC : x∉C := by
      intro m
      have j := high x m
      have k := erase_internal_deg (G:=G) D z x
      change (inside G D x).card≤(inside G E x).card+1 at k
      omega
    have yC : y∉C := by
      intro m
      have j := high y m
      have k := erase_internal_deg (G:=G) D z y
      change (inside G D y).card≤(inside G E y).card+1 at k
      omega
    have highE (w : V) (wC : w∈C) : 5≤(inside G E w).card := by
      have no : ¬G.Adj w z := by
        intro wz
        have q : w∈inside G D z := mem_filter.mpr ⟨cd wC,wz.symm⟩
        rw [eq,mem_insert,mem_singleton] at q
        exact q.elim (fun h=>xC (h ▸ wC)) (fun h=>yC (h ▸ wC))
      change 5≤(inside G (D.erase z) w).card
      rw [erase_avoids_nonneighbor (G:=G) D no]
      exact high w wC
    exact fill xE xz (fun l lm lx=>seven_high_core_route E C cE e7 c5 three highE (cE (lC lm)) xE lx)
  by_cases one : ∃ w∈E,(inside G E w).card≤3
  · obtain ⟨w,wm,wl⟩ := one
    have wz := on w wm wl
    apply fill wm wz
    intro l lm lw
    apply weighted_side_route E (cE (lC lm)) wm lw
    have highE {v : V} (vm : v∈E) (no : v≠w) : 4≤(inside G E v).card := by
      by_contra p
      exact two ⟨v,vm,w,wm,no,by omega,wl⟩
    intro u um v vm uv _
    rw [e7]
    by_cases uw : u=w
    · subst u
      rw [if_pos (.inl rfl)]
      have h := three w wm
      have b := highE vm uv.symm
      omega
    by_cases vw : v=w
    · subst v
      rw [if_pos (.inr rfl)]
      have h := three w wm
      have b := highE um uv
      omega
    have u4 := highE um uw
    have v4 := highE vm vw
    omega
  obtain ⟨w,wd,wz⟩ := pos
  have wm : w∈E := mem_erase.mpr ⟨wz.ne,wd⟩
  apply fill wm wz
  intro l lm lw
  apply terminal_route_on_of_local_ore E (cE (lC lm)) wm lw
  have h (v : V) (vm : v∈E) : 4≤(inside G E v).card := by
    by_contra p
    exact one ⟨v,vm,by omega⟩
  intro u um v vm _ _
  have u4 := h u um
  have v4 := h v vm
  omega

#print axioms eight_remove_one_low_route
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
