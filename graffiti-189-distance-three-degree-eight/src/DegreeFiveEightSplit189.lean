import DegreeFiveEightNoBridgeRoute189
import DegreeFiveSurplus189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private left_boundary from AdjacentCut189
open private two_walk_middle from DistanceTwoCut189
open private cut_not_adj not_common secondA_right_and_left_le_five left_secondA_positive
  from DegreeFiveFourPort189
open private distance_three_has_bridge from DegreeFiveBalancedUniform189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem traceable_four_a_ports_each_shore_distance_three (hc : G.Connected)
    (three : G.dist a b=3) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (leftFour : S.localA.card=4) (rightFour : S.foreignA.card=4)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x) :
    ∃ r t,∃ p : G.Walk r t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have far : 3≤G.dist a b := by omega
  have ab : a≠b := by intro h; rw [h,dist_self] at three; omega
  have stage (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
      (l4 : S.localA.card=4) (r4 : S.foreignA.card=4)
      (rc : (G.induce (↑S.R : Set V)).Connected)
      (ra : ∃ x∈S.R,G.Adj a x) (rb : ∃ x∈S.R,G.Adj b x) (bridge : portBridge S) :
      ∃ r t,∃ p : G.Walk r t,p.IsPath ∧ ∀ z,z∈p.support := by
    let T := switch S rc ra rb
    have t4 : T.localA.card=4 := r4
    have tf4 : T.foreignA.card=4 := l4
    obtain ⟨p,q,ap,bq,l⟩ := bridge_route_at_four_four S hc far even l4 r4 rc ra rb bridge
    have wing : ∃ u v,G.Adj a u ∧ G.Adj b v ∧ RouteOn G S.R u v := by
      by_cases bridges : portBridge T
      · exact bridge_route_at_four_four T hc far even t4 tf4 S.leftConnected S.leftA S.leftB bridges
      let I := S.R.filter (fun u=>¬G.Adj a u ∧ ¬G.Adj b u)
      have cover := right_cover_of_mixed_opposite_four S hc far even r4 bridge
      have isub : I⊆secondA G S.R a := by
        intro x xx
        obtain ⟨xr,ax,bx⟩ := mem_filter.mp xx
        rcases mem_union.mp (cover xr) with e|s
        · rcases mem_union.mp e with xp|xb
          · exact (ax (mem_filter.mp xp).2).elim
          exact (bx (mem_filter.mp xb).2).elim
        exact s
      have i4 : I.card≤4 := by
        have hi := card_le_card isub
        have l1 := left_secondA_positive S hc far
        have c := secondA_right_and_left_le_five S even
        omega
      have bFar : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
      have b4 : (S.R.filter (G.Adj b)).card≤4 := foreign_a_ports_le_four S.flip hc bFar even
      have seen (u : V) (uR : u∈T.L) (au : ¬G.Adj a u) (bu : ¬G.Adj b u) :
          ∃ x∈T.localA,G.Adj x u := by
        have m := isub (mem_filter.mpr ⟨uR,au,bu⟩)
        have d : G.dist a u=2 := by simpa [DistanceTwo] using (mem_inter.mp m).2
        obtain ⟨w,wl⟩ := hc.exists_walk_length_eq_dist a u
        obtain ⟨x,ax,xu⟩ := two_walk_middle w (wl.trans d)
        rcases left_boundary T u uR x xu.symm with xa|xb|xR
        · exact (G.loopless a (xa ▸ ax)).elim
        · exact (cut_not_adj far (xb ▸ ax)).elim
        exact ⟨x,mem_filter.mpr ⟨xR,ax⟩,xu⟩
      exact no_bridge_route_at_four_four T hc far even degree t4 tf4 b4 i4 bridges seen
    obtain ⟨u,v,au,_,r⟩ := wing
    have l' := l.reverse.suffix ap.symm S.leftOff.1
    have dis : Disjoint (insert a S.L) S.R :=
      disjoint_left.mpr (fun z zL zR=>(mem_insert.mp zL).elim
        (fun e=>S.rightOff.1 (e ▸ zR)) (fun l=>disjoint_left.mp S.dis l zR))
    have path := l'.join r dis au
    have bOff : b∉insert a S.L∪S.R := by
      intro n
      rcases mem_union.mp n with m|m
      · exact (mem_insert.mp m).elim ab.symm S.leftOff.2
      exact S.rightOff.2 m
    obtain ⟨walk,wp,ws⟩ := path.prefix bq bOff
    refine ⟨b,v,walk,wp,fun z=>(ws z).mpr ?_⟩
    rcases S.cover z with e|e|zl|zr
    · exact mem_insert_of_mem (mem_union_left _ (mem_insert.mpr (.inl e)))
    · exact mem_insert.mpr (.inl e)
    · exact mem_insert_of_mem (mem_union_left _ (mem_insert_of_mem zl))
    exact mem_insert_of_mem (mem_union_right _ zr)
  rcases distance_three_has_bridge S hc three rightConnected rightA rightB with bL|bR
  · exact stage S leftFour rightFour rightConnected rightA rightB bL
  exact stage (switch S rightConnected rightA rightB) rightFour leftFour S.leftConnected S.leftA S.leftB bR

#print axioms traceable_four_a_ports_each_shore_distance_three
end Graffiti189LongestPath.CrossSaturation.Split.Five
