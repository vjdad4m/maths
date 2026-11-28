import DegreeFiveFourPort189
import DegreeFiveAlternatingRoute189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 foreign_subset from CrossSaturation189
open private not_common from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem singleton_local_distance_two_at_opposite_four (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤6) (four : S.foreignA.card=4)
    {p u v : V} (pL : p∈S.L) (ap : G.Adj a p)
    (uL : u∈S.L) (vL : v∈S.L)
    (u2 : u∈DistanceTwo G p) (v2 : v∈DistanceTwo G p) : u=v := by
  classical
  by_contra ne
  have unf : u∉S.foreignA := fun h=>disjoint_left.mp S.dis uL (mem_filter.mp h).1
  have vnf : v∉S.foreignA := fun h=>disjoint_left.mp S.dis vL (mem_filter.mp h).1
  have no : u∉insert v S.foreignA := by simp [ne,unf]
  have sub : insert u (insert v S.foreignA)⊆DistanceTwo G p := by
    intro z hz
    rcases mem_insert.mp hz with rfl|h
    · exact u2
    rcases mem_insert.mp h with rfl|h
    · exact v2
    exact foreign_subset S hc pL ap h
  have h := (card_le_card sub).trans (distanceTwo_le_of_even 5 p (even p))
  rw [card_insert_of_not_mem no,card_insert_of_not_mem vnf,four] at h
  omega

theorem bridge_route_at_four_four (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6) (localFour : S.localA.card=4)
    (foreignFour : S.foreignA.card=4)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (bridge : portBridge S) :
    ∃ p,∃ q,G.Adj a p ∧ G.Adj b q ∧ RouteOn G S.L p q := by
  classical
  let A := S.localA
  let E := S.L\A
  obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
  have xA : x∈A := mem_filter.mpr ⟨xl,ax⟩
  have yA : y∉A := fun h=>not_common far (mem_filter.mp h).2 by'
  have yE : y∈E := mem_sdiff.mpr ⟨yl,yA⟩
  have aSub : A⊆S.L := filter_subset _ _
  have sep : Disjoint A E := disjoint_left.mpr (fun z za ze=>(mem_sdiff.mp ze).2 za)
  have univ := bridge_four_forces_universal S hc far even foreignFour xl ax xy by'
  have adj (p : V) (pA : p∈A) (z : V) (zl : z∈S.L) (pz : p≠z) (zy : z≠y) :
      G.Adj p z := by
    have pL := aSub pA
    have ap := (mem_filter.mp pA).2
    by_cases px : p=x
    · subst p
      exact (univ z zl).resolve_left (fun e=>pz e.symm)
    have xp := (univ p pL).resolve_left px
    by_cases hit : ∃ w∈S.L,G.Adj b w ∧ G.Adj p w
    · obtain ⟨w,_,bw,pw⟩ := hit
      exact (bridge_four_forces_universal S hc far even foreignFour pL ap pw bw z zl).resolve_left
        (fun e=>pz e.symm)
    have py : p≠y := fun h=>yA (h ▸ pA)
    have pyn : ¬G.Adj p y := fun h=>hit ⟨y,yl,by',h⟩
    have y2 := d2 hc py pyn xp.symm xy
    apply Classical.byContradiction
    intro pzn
    have zx : z≠x := fun e=>pzn (e.symm ▸ xp.symm)
    have xz := (univ z zl).resolve_left zx
    have z2 := d2 hc pz pzn xp.symm xz
    exact zy (singleton_local_distance_two_at_opposite_four S hc even foreignFour pL ap zl yl z2 y2)
  have cl : CompleteOn G A := by
    intro p pA z zA ne
    exact adj p pA z (aSub zA) ne (fun e=>yA (e ▸ zA))
  have cap : E.card≤A.card := by
    have h := bound_bridge_side_of_opposite_four S hc far even rightConnected rightA rightB
      foreignFour ⟨x,xl,y,yl,ax,xy,by'⟩
    have q : E.card+A.card=S.L.card := card_sdiff_add_card_eq_card aSub
    change A.card=4 at localFour
    change S.L.card≤A.card+4 at h
    omega
  obtain ⟨p,pp,route⟩ := route_clique_join_end_leaf sep cl
    (fun p pp z zz=>adj p pp z (mem_sdiff.mp (mem_erase.mp zz).2).1
      (fun e=>(mem_sdiff.mp (mem_erase.mp zz).2).2 (e ▸ pp)) (mem_erase.mp zz).1)
    cap xA yE xy
  have key : A∪E=S.L := union_sdiff_of_subset aSub
  exact ⟨p,y,(mem_filter.mp pp).2,by',key ▸ route⟩

#print axioms singleton_local_distance_two_at_opposite_four
#print axioms bridge_route_at_four_four
end Graffiti189LongestPath.CrossSaturation.Split.Five
