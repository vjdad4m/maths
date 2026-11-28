import DegreeFiveSevenNoBridgeClose189
import DegreeFiveSevenThreeInnerRoute189
import DegreeFiveSevenMixedTwoRoute189
import DegreeFiveSevenMixedOneRoute189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem traceable_three_four_far_split (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (left3 : S.localA.card=3) (right4 : S.foreignA.card=4)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ v,v∈p.support := by
  classical
  by_cases bridge : portBridge S
  · have term := bridge_route_at_three_four S hc far even degree left3 right4
      rightConnected rightA rightB bridge
    let T := switch S rightConnected rightA rightB
    have a4 : T.localA.card=4 := right4
    have foreign : T.foreignA.card=3 := left3
    have fre : (∃ u v,G.Adj a u ∧ RouteOn G S.R u v) ∨
        (∃ u v,G.Adj b u ∧ RouteOn G S.R u v) := by
      by_cases small : T.L.card≤8
      · exact .inl (free_route_small_far_shore T far degree small (by omega : 2≤T.localA.card))
      have big : 9≤T.L.card := by omega
      obtain ⟨vis,cap,budget⟩ := bridge_three_opposite_shell_cap S hc far even degree left3 right4 bridge
      let B := T.L.filter (G.Adj b)
      let I := farNonports T.L a b G
      let W := visibleBPorts T.L a b G
      have sum : T.localA.card+B.card+I.card=T.L.card := left_port_count T far
      have fd : 3≤G.dist b a := by rwa [dist_comm]
      have b4 : B.card≤4 := foreign_a_ports_le_four S.flip hc fd even
      change I.card+W.card≤3 at cap
      by_cases no : ¬portBridge T
      · by_cases smallI : I.card≤2
        · exact .inl (four_a_no_bridge_small_inner_free T hc far even degree a4 foreign b4 smallI
            big no vis)
        have size : I.card=3 := by omega
        have bp := (budget size).2
        exact .inl (four_a_no_bridge_three_inner_free T hc far even degree a4 foreign b4 size
          big no vis bp)
      have bridgeT : portBridge T := Classical.byContradiction no
      have w1 : 1≤W.card := by
        obtain ⟨r,rl,z,zl,ar,rz,bz⟩ := bridgeT
        exact card_pos.mpr ⟨z,mem_filter.mpr ⟨zl,bz,r,rl,ar,rz⟩⟩
      by_cases smallI : I.card=1
      · have bb : B.card=4 := by omega
        have ww : W.card≤2 := by omega
        exact four_a_bridge_one_inner_free T hc far even degree a4 bb smallI ww foreign vis bridgeT
      have i2 : I.card=2 := by omega
      have wEq : W.card=1 := by omega
      by_cases four : B.card=4
      · exact (no_four_b_with_bridge_two_inner T hc far even degree a4 four i2 wEq foreign vis bridgeT).elim
      have b3 : B.card=3 := by omega
      exact .inl (four_a_bridge_two_inner_free T hc far even degree a4 b3 i2 wEq foreign vis bridgeT)
    exact traceable_from_far_terminal_and_free S far term fre
  exact traceable_seven_split_without_bridge_on_three S hc far even conn degree left3 right4
    rightConnected rightA rightB bridge

#print axioms traceable_three_four_far_split
end Graffiti189LongestPath.CrossSaturation.Split.Five
