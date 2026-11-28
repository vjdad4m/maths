import SixThree18NoHigh189

namespace Graffiti189LongestPath.SixThreeEighteen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints
  Graffiti189LongestPath.boundary_card_of_connectivity Graffiti189LongestPath.splice_gap_two
  from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem
  Graffiti189LongestPath.OneSlack.card_pinVertices
  Graffiti189LongestPath.OneSlack.cardinal_flankVertices from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem no_gap_two (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤18) {a b : V} {p : G.Walk a b} (hp : IsLongest p) (long : 13≤p.length)
    {x : V} (hx : x∉p.support) {i : ℕ} (hi : i∈Pins p x) :
    i+2∉Pins p x := by
  intro hi'
  have h := (Graffiti189LongestPath.pin_data hi').1
  obtain ⟨q,hq,len,support⟩ := Graffiti189LongestPath.splice_gap_two p hp.1
    (Walk.nil : G.Walk x x) (by simp)
    (fun w m=>by have e:=mem_support_nil_iff.mp m; simpa [e] using hx)
    i (by omega) (Graffiti189LongestPath.pin_data hi).2.symm (Graffiti189LongestPath.pin_data hi').2
  have eq : q.length=p.length := by simpa using len
  have maxq : IsLongest q := ⟨hq,fun u v r rp=>eq.symm ▸ hp.2 u v r rp⟩
  have out : p.getVert (i+1)∉q.support := by
    intro hit
    rcases (support _).mp hit with m|m
    · exact hx ((mem_support_nil_iff.mp m) ▸ p.getVert_mem_support (i+1))
    exact m.2 rfl
  have one := all_omitted_low_long hc conn cap degree ord hp long hx
  have lq : 13≤q.length := by rw [eq]; exact long
  have two := all_omitted_low_long hc conn cap degree ord maxq lq out
  have ne : x≠p.getVert (i+1) := fun h=>hx (h ▸ p.getVert_mem_support (i+1))
  rcases degree x (p.getVert (i+1)) ne with d|d <;> omega

theorem saturated_flanks (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤18) {a b : V} {p : G.Walk a b} (hp : IsLongest p) (long : 13≤p.length)
    {x : V} (hx : x∉p.support) :
    (Pins p x).card=3 ∧ DistanceTwo G x=FlankVertices p x := by
  classical
  have low := all_omitted_low_long hc conn cap degree ord hp long hx
  have all (y : V) (xy : G.Adj x y) : y∈p.support := by
    by_contra yo
    have other := all_omitted_low_long hc conn cap degree ord hp long yo
    rcases degree x y xy.ne with h|h <;> omega
  have mind : 3≤G.degree x := by
    rw [←card_neighborFinset_eq_degree]
    apply Graffiti189LongestPath.boundary_card_of_connectivity 3 conn (x:=x) (a:=a) (A:={x})
    · exact mem_singleton_self _
    · exact fun e=>hx ((mem_singleton.mp e) ▸ p.start_mem_support)
    · exact fun e=>(Graffiti189LongestPath.no_endpoints hp hx).1 ((mem_neighborFinset _ _ _).mp e)
    · apply disjoint_left.mpr
      intro v vm vn
      exact ((mem_neighborFinset _ _ _).mp vn).ne (mem_singleton.mp vm).symm
    · intro v vm w _ e
      exact (mem_neighborFinset _ _ _).mpr ((mem_singleton.mp vm) ▸ e)
  have sub : G.neighborFinset x⊆PinVertices p x := by
    intro y m
    have xy := (mem_neighborFinset _ _ _).mp m
    obtain ⟨i,hi,he⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hx (all y xy) xy
    exact mem_image.mpr ⟨i,hi,he⟩
  have lower := card_le_card sub
  rw [card_neighborFinset_eq_degree,Graffiti189LongestPath.OneSlack.card_pinVertices hp] at lower
  have first : FirstPins p x=Pins p x := by
    apply Subset.antisymm (filter_subset ..)
    intro i hi
    exact mem_filter.mpr ⟨hi,fun j hj e=>no_gap_two hc conn cap degree ord hp long hx hj (e.symm ▸ hi)⟩
  have cardf := Graffiti189LongestPath.OneSlack.cardinal_flankVertices (x:=x) hp
  rw [flank_count_exact hp hx,first] at cardf
  have sf : FlankVertices p x⊆DistanceTwo G x := fun y ym=>
    (mem_sdiff.mp (flanks_outside_boundary hc hp hx ym)).1
  have f := card_le_card sf
  have upper := distanceTwo_le_of_even 6 x (cap x)
  refine ⟨by omega,(eq_of_subset_of_card_le sf (by omega)).symm⟩

#print axioms saturated_flanks
end Graffiti189LongestPath.SixThreeEighteen