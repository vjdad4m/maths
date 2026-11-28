import DegreeFiveSevenMixedOneGeometry189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private not_common from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem four_a_bridge_one_inner_free (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (a4 : S.localA.card=4) (b4 : (S.L.filter (G.Adj b)).card=4)
    (i1 : (farNonports S.L a b G).card=1)
    (w2 : (visibleBPorts S.L a b G).card≤2) (foreign : S.foreignA.card=3)
    (showI : farNonports S.L a b G⊆secondA G S.L a) (bridge : portBridge S) :
    (∃ u v,G.Adj a u ∧ RouteOn G S.L u v) ∨
      (∃ u v,G.Adj b u ∧ RouteOn G S.L u v) := by
  classical
  let A := S.localA
  let B := S.L.filter (G.Adj b)
  let I := farNonports S.L a b G
  let U := A∪I
  obtain ⟨complete,v,w,h,l,vw,vh,vl,wh,wl,hl,BQ,vH,wH,hL,opts⟩ :=
    four_a_bridge_one_inner_geometry S hc far even degree a4 b4 i1 w2 foreign showI bridge
  change CompleteOn G U at complete
  change B={v,w,h,l} at BQ
  change A.card=4 at a4
  have dis : Disjoint U B := by
    apply disjoint_union_left.mpr
    exact ⟨disjoint_left.mpr (fun q qa qb=>not_common far (mem_filter.mp qa).2 (mem_filter.mp qb).2),
      disjoint_left.mpr (fun q qi qb=>(mem_filter.mp qi).2.2 (mem_filter.mp qb).2)⟩
  have total : U∪B=S.L := by
    change (A∪I)∪B=S.L
    rw [union_right_comm]
    exact left_port_partition S far
  rcases opts with ⟨vw',x,xa,xv⟩|⟨x,xa,y,ya,xy,vx,yw⟩
  · left
    have ex : ∃ p∈A,p≠x := by
      apply Classical.byContradiction
      intro no
      have sub : A⊆{x} := fun p pa=>mem_singleton.mpr
        (Classical.byContradiction (fun h=>no ⟨p,pa,h⟩))
      have n := card_le_card sub
      rw [a4,card_singleton] at n
      omega
    obtain ⟨p,pa,px⟩ := ex
    obtain ⟨q,hq,sq⟩ := path_between_in_clique U complete (mem_union_left _ pa)
      (mem_union_left _ xa) px
    have path : RouteOn G U p x := ⟨q,hq,sq⟩
    have step := (RouteOn.edge vw').suffix wH (by simp [vh.symm,wh.symm])
    have pB := step.suffix hL (by simp [vl.symm,wl.symm,hl.symm])
    have e : insert l (insert h ({v,w} : Finset V))=B := by
      rw [BQ]
      ext q
      simp [or_comm,or_left_comm,or_assoc]
    have tail : RouteOn G B v l := e ▸ pB
    exact ⟨p,l,(mem_filter.mp pa).2,total ▸ path.join tail dis xv⟩
  right
  obtain ⟨q,hq,sq⟩ := path_between_in_clique U complete (mem_union_left _ xa)
    (mem_union_left _ ya) xy
  have pU : RouteOn G U x y := ⟨q,hq,sq⟩
  let V₃ := ({l,h,v} : Finset V)
  have pB : RouteOn G V₃ l v := RouteOn.three hL.symm vH.symm vl.symm
  have sub : V₃⊆B := by
    intro z zz
    rw [BQ]
    have e : z=l ∨ z=h ∨ z=v := by simpa [V₃] using zz
    rcases e with e|e|e <;> simp [e]
  have d := dis.symm.mono sub (Subset.refl U)
  have p := pB.join pU d vx
  have wOff : w∉V₃∪U := by
    intro e
    rcases mem_union.mp e with h|h
    · simp [V₃,wl,wh,vw.symm] at h
    exact disjoint_left.mp dis h (by simp [BQ])
  have b := p.suffix yw wOff
  have e : insert w (V₃∪U)=S.L := by
    rw [←total,BQ]
    ext q
    simp [V₃,or_comm,or_left_comm,or_assoc]
  have lb : l∈B := by simp [BQ]
  exact ⟨l,w,(mem_filter.mp lb).2,e ▸ b⟩

#print axioms four_a_bridge_one_inner_free
end Graffiti189LongestPath.CrossSaturation.Split.Five
