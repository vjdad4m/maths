import DegreeFiveDarkGatewayRoute189
import DegreeFiveAlternatingExtraBlock189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private left_boundary from AdjacentCut189
open private not_common left_secondA_positive secondA_right_and_left_le_five from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem no_bridge_terminal_three_four (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (localThree : S.localA.card=3) (foreignFour : S.foreignA.card=4)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (noBridge : ¬portBridge S) :
    ∃ p q,G.Adj a p ∧ G.Adj b q ∧ RouteOn G S.L p q := by
  classical
  obtain ⟨z,zL,bz,⟨r,rY,rz⟩,cl,see,link,bound⟩ :=
    saturated_gateway_shape S hc far even foreignFour noBridge
  let A := S.localA
  let Y := gatewayVisible S
  let T := gatewayDark S z
  have za : z∉A := fun h=>not_common far (mem_filter.mp h).2 bz
  have zy : z∉Y := fun h=>(mem_filter.mp h).2.2.1 bz
  have aSub : A⊆S.L := filter_subset _ _
  have ySub : Y⊆S.L := by
    intro v vv
    exact (mem_filter.mp vv).1
  have yCap : Y.card≤A.card+1 := by
    have ys := card_le_card (visible_gateway_subset_second S hc)
    have tail := left_secondA_positive (switch S rightConnected rightA rightB) hc far
    change 1≤(secondA G S.R a).card at tail
    have sum := secondA_right_and_left_le_five S even
    change A.card=3 at localThree
    change Y.card≤(secondA G S.L a).card at ys
    omega
  have both (y : V) (yy : y∈Y) (v : V) (yv : G.Adj y v) :
      v=z ∨ v∈A ∨ v∈Y := by
    obtain ⟨yl,ay,by',_,_,_⟩ := mem_filter.mp yy
    rcases left_boundary S y yl v yv with va|vb|vl
    · exact (ay (va ▸ yv.symm)).elim
    · exact (by' (vb ▸ yv.symm)).elim
    by_cases vz : v=z
    · exact .inl vz
    by_cases vv : v∈A∪Y
    · exact .inr (mem_union.mp vv)
    have vt : v∈T := mem_sdiff.mpr ⟨vl,fun m=>(mem_insert.mp m).elim vz vv⟩
    rcases bound v vt y yv.symm with yz|yb|yt
    · exact (zy (yz ▸ yy)).elim
    · exact (S.leftOff.2 (yb ▸ yl)).elim
    exact ((mem_sdiff.mp yt).2 (mem_insert_of_mem (mem_union_right _ yy))).elim
  have pair : A.card<Y.card → ∃ u∈Y,∃ v∈Y,G.Adj u v := by
    intro gt
    apply Classical.byContradiction
    intro no
    have low (y : V) (yy : y∈Y) : ¬5≤G.degree y := by
      have sub : G.neighborFinset y⊆insert z A := by
        intro v vn
        have yv := (mem_neighborFinset G y v).mp vn
        rcases both y yy v yv with e|e|e
        · exact mem_insert.mpr (.inl e)
        · exact mem_insert_of_mem e
        exact (no ⟨y,yy,v,e,yv⟩).elim
      have n := (card_le_card sub).trans (card_insert_le z A)
      rw [card_neighborFinset_eq_degree] at n
      change A.card=3 at localThree
      omega
    change A.card=3 at localThree
    obtain ⟨u,uy,v,vy,uv⟩ := one_lt_card.mp (show 1<Y.card by omega)
    exact (degree u v uv).elim (low u uy) (low v vy)
  obtain ⟨x,xl,ax⟩ := S.leftA
  have xa : x∈A := mem_filter.mpr ⟨xl,ax⟩
  have sep : Disjoint A Y := disjoint_left.mpr (fun v va vy=>(mem_filter.mp vy).2.1 (mem_filter.mp va).2)
  obtain ⟨p,pa,pth⟩ := route_clique_join_end_leaf_with_extra_block sep cl see yCap xa rY pair
  have zoff : z∉A∪Y := fun h=>(mem_union.mp h).elim za zy
  have qth := pth.suffix rz zoff
  have uSub : insert z (A∪Y)⊆S.L := insert_subset_iff.mpr ⟨zL,union_subset aSub ySub⟩
  have cover : insert z (A∪Y)∪T=S.L := union_sdiff_of_subset uSub
  have pa' : G.Adj a p := (mem_filter.mp pa).2
  by_cases e : T.Nonempty
  · have far' : 3≤G.dist b a := by rwa [dist_comm]
    have b4 : (S.L.filter (G.Adj b)).card≤4 :=
      foreign_a_ports_le_four (switch S rightConnected rightA rightB).flip hc far' even
    obtain ⟨cap,bc,hit⟩ := dark_gateway_bounds S hc conn even zL bz rY rz link bound b4
    obtain ⟨r,t,bt,p⟩ := route_through_dark_gateway_block cap bc (hit e) bound degree
    have rt : r∈T := by
      obtain ⟨p,p',sup⟩ := p
      exact (sup r).mp p.start_mem_support
    have dis : Disjoint (insert z (A∪Y)) T :=
      disjoint_left.mpr (fun v vl vt=>(mem_sdiff.mp vt).2 vl)
    exact ⟨_,t,pa',bt,cover ▸ qth.join p dis (link r rt)⟩
  have e' : T=∅ := Finset.eq_empty_iff_forall_not_mem.mpr (fun v m=>e ⟨v,m⟩)
  have cover' : insert z (A∪Y)=S.L := by simpa [e'] using cover
  exact ⟨p,z,pa',bz,cover' ▸ qth⟩

#print axioms no_bridge_terminal_three_four
end Graffiti189LongestPath.CrossSaturation.Split.Five
