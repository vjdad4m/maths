import SixThree19Slots189

namespace Graffiti189LongestPath.SixThreeNineteen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem all_omitted_low_long (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤19) {a b : V} {p : G.Walk a b} (hp : IsLongest p) (long : 14≤p.length)
    {x : V} (hx : x∉p.support) : G.degree x<6 := by
  classical
  by_contra! dx
  obtain ⟨u,v,q,hq,same,du,dv⟩ :=
    OneSlack.MultiRotation.rotate_to_two_high_endpoints_general hc 3 (by decide) 6 conn degree hp hx
  have xq : x∉q.support := fun h=>hx ((same x).mpr h)
  have longq := long.trans (hq.2 a b p hp.1)
  obtain ⟨len,_,pc,_⟩ := high_pin_shape_long hc conn cap degree ord hq longq xq dx
  have non : (Pins q x).Nonempty := card_pos.mp (by omega)
  have bnd := (saturated_mark_slots hq xq non
    (fun hi h=>high_pin_no_start_chord hc conn cap degree ord hq longq xq dx hi h)
    (fun hi h=>high_pin_no_end_chord hc conn cap degree ord hq longq xq dx hi h)).1
  omega

#print axioms all_omitted_low_long
end Graffiti189LongestPath.SixThreeNineteen
