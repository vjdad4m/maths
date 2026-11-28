import SixThree20FourteenTriple189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeEighteen (Omit mem_Omit LM RM high_filter_card)
open Graffiti189LongestPath.SixThreeNineteen (SeesPort pin_indices_not_consecutive)
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.mem_distanceTwo from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.dist_two from Rigidity189
open private Graffiti189LongestPath.OneSlack.mem_omittedStar Graffiti189LongestPath.OneSlack.mem_external
  Graffiti189LongestPath.OneSlack.boundary_lower Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem
  Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem omitted_adj_of_high_pairs {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (sz : (Omit p).card=5)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (pair : ∀ x∈HighOmit p,(Pins p x).card=2) :
    ∀ x∉p.support,∀ y∉p.support,x≠y → G.Adj x y := by
  intro x xo y yo ne
  rcases degree x y ne with dx|dy
  · have xm : x∈HighOmit p := mem_filter.mpr ⟨mem_Omit.mpr xo,dx⟩
    exact high_omitted_universal_when_exact_degree_room hp xm
      (by rw [pair x xm,sz]) y yo ne
  have ym : y∈HighOmit p := mem_filter.mpr ⟨mem_Omit.mpr yo,dy⟩
  exact (high_omitted_universal_when_exact_degree_room hp ym
    (by rw [pair y ym,sz]) x xo ne.symm).symm

theorem all_sites_separated_of_omitted_adj {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (adj : ∀ x∉p.support,∀ y∉p.support,x≠y → G.Adj x y) :
    ∀ i∈Sites p (Omit p),i+1∉Sites p (Omit p) := by
  intro i im jm
  obtain ⟨ir,x,xm,xe⟩ := mem_filter.mp im
  obtain ⟨jr,y,ym,ye⟩ := mem_filter.mp jm
  have xo := mem_Omit.mp xm
  have yo := mem_Omit.mp ym
  have xp : i∈Pins p x := mem_filter.mpr ⟨ir,xe⟩
  have yp : i+1∈Pins p y := mem_filter.mpr ⟨jr,ye⟩
  by_cases eq : x=y
  · subst y
    exact pin_indices_not_consecutive hp xo xp yp
  have xy := adj x xo y yo eq
  have off : ∀ v∈xy.toWalk.support,v∉p.support := by
    intro v vm vp
    have e : v=x ∨ v=y := by simpa using vm
    rcases e with rfl|rfl
    · exact xo vp
    exact yo vp
  have n := gap_three_of_linked_pins hp xp yp (by omega) xy.toWalk (by simpa using eq) (by simp) off
  omega

theorem port_set_ge_three_of_omitted_adj (conn : ConnThree G) {a b : V} {p : G.Walk a b}
    (hp : IsLongest p) (non : (Omit p).Nonempty)
    (adj : ∀ x∉p.support,∀ y∉p.support,x≠y → G.Adj x y) :
    3≤(PortSet p (Omit p)).card := by
  obtain ⟨x,xm⟩ := non
  have xo := mem_Omit.mp xm
  have sub : External G (OmittedStar p x) ⊆ PortSet p (Omit p) := by
    intro z zm
    obtain ⟨zOut,y,ym,yz⟩ := Graffiti189LongestPath.OneSlack.mem_external.mp zm
    have yo := (Graffiti189LongestPath.OneSlack.mem_omittedStar.mp ym).1
    have on : z∈p.support := by
      by_contra zo
      by_cases eq : z=x
      · exact zOut (Graffiti189LongestPath.OneSlack.mem_omittedStar.mpr ⟨zo,.inl eq⟩)
      exact zOut (Graffiti189LongestPath.OneSlack.mem_omittedStar.mpr ⟨zo,.inr (adj x xo z zo (fun h=>eq h.symm))⟩)
    exact (mem_portSet hp (fun v vm=>mem_Omit.mp vm)).mpr ⟨on,y,mem_Omit.mpr yo,yz⟩
  exact (Graffiti189LongestPath.OneSlack.boundary_lower 3 hp xo conn).trans (card_le_card sub)

open scoped Classical in
theorem pair_port_candidate_hit_cap (hc : G.Connected)
    (cap : ∀ v,(EvenFrom G v).card≤7) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (adj : ∀ x∉p.support,∀ y∉p.support,x≠y → G.Adj x y)
    (three : 3≤(PortSet p (Omit p)).card)
    {x : V} (xo : x∉p.support) (pair : (Pins p x).card=2) :
    ((CandHigh p).filter (fun v=>SeesPort p x v)).card≤5 := by
  classical
  let U := PortSet p (Omit p)
  let T := PinVertices p x
  have sub : T⊆U := pin_vertices_sub_ports (mem_Omit.mpr xo)
  have tc : T.card=2 := (Graffiti189LongestPath.OneSlack.card_pinVertices hp).trans pair
  have diff := card_sdiff_add_card_eq_card sub
  obtain ⟨z,zm⟩ : (U\T).Nonempty := card_pos.mp (by change 3≤U.card at three; omega)
  obtain ⟨zU,zT⟩ := mem_sdiff.mp zm
  obtain ⟨zp,y,ym,yz⟩ := (mem_portSet hp (fun v vm=>mem_Omit.mp vm)).mp zU
  have no : ¬G.Adj x z := by
    intro h
    obtain ⟨i,ip,ie⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp xo zp h
    exact zT (mem_image.mpr ⟨i,ip,ie⟩)
  have xy : x≠y := fun e=>no (e.symm ▸ yz)
  have zd : z ∈ DistanceTwo G x := Graffiti189LongestPath.mem_distanceTwo.mpr
    (Graffiti189LongestPath.Rigidity.dist_two hc (fun e=>xo (e.symm ▸ zp)) no (adj x xo y (mem_Omit.mp ym) xy) yz)
  let H := (CandHigh p).filter (fun v=>SeesPort p x v)
  have zoff : z∉H := by
    intro h
    exact cand_no_omitted_edge hp (mem_filter.mp (mem_filter.mp h).1).1 (mem_Omit.mp ym) yz
  have hit : H⊆DistanceTwo G x := by
    intro v vm
    obtain ⟨hv,w,wp,xw,vw⟩ := mem_filter.mp vm
    have vm' := (mem_filter.mp hv).1
    obtain ⟨t,q,hq,same,_,_⟩ := cand_rotated_path hp vm'
    have vs := (same v).mpr q.start_mem_support
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.Rigidity.dist_two hc (fun e=>xo (e.symm ▸ vs))
        (cand_no_omitted_edge hp vm' xo) xw vw.symm)
  have bounds := (card_le_card (show insert z H⊆DistanceTwo G x from
    fun v m=>(mem_insert.mp m).elim (fun e=>e.symm ▸ zd) (fun h=>hit h))).trans (distanceTwo_le_of_even 6 x (cap x))
  rw [card_insert_of_not_mem zoff] at bounds
  change H.card≤5
  omega

#print axioms omitted_adj_of_high_pairs
#print axioms pair_port_candidate_hit_cap
end Graffiti189LongestPath.SixThreeTwenty
