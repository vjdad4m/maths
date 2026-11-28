import EJOrdinaryCompletion189
import ArticulationThree189

namespace Graffiti189LongestPath.SmallOrder
open Finset SimpleGraph SimpleGraph.Walk Graffiti189Ore Graffiti189LongestPath
open private Graffiti189Ore.degree_increasing from OreClosure189
open private Graffiti189LongestPath.CrossSaturation.ThreeShores.d2 from ArticulationThree189
variable {V : Type*} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
set_option linter.unusedSectionVars false

theorem neighbors_unchanged_of_degree_unchanged (sub : G≤H) {x : V}
    (eq : G.degree x=H.degree x) :
    ∀ y,H.Adj x y → G.Adj x y := by
  have s : G.neighborFinset x⊆H.neighborFinset x := fun y hy=>
    (mem_neighborFinset H x y).mpr (sub ((mem_neighborFinset G x y).mp hy))
  have e := eq_of_subset_of_card_le s (by rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,eq])
  exact fun y h=>(mem_neighborFinset G x y).mp (e.symm ▸ (mem_neighborFinset H x y).mpr h)

theorem connected_of_supergraph (sub : G≤H) (hc : G.Connected) : H.Connected := by
  exact SimpleGraph.Connected.mono sub hc

/-- The finite terminal-graph argument in Easwar–Johari, §4.1.
There must be a high unchanged vertex at degree d if H is nontraceable;
a direct even-shell charge then rules out terminality. -/
theorem traceable_terminal_order_two_add
    (hc : G.Connected) (d : ℕ) (size : Fintype.card V=2*d+2)
    (sub : G≤H) (cap : ∀ v,(EvenFrom G v).card≤d+1)
    (degree : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v)
    (terminal : ∀ u v : V,u≠v → d≤G.degree u → d≤G.degree v → ¬H.Adj u v →
       H.degree u+H.degree v+1<Fintype.card V ∧
       ∃ w,H.Adj u w ∧ H.Adj w v) :
    Graffiti189Ore.Traceable H := by
  classical
  apply Classical.byContradiction
  intro fail
  have exists' : ∃ u,d≤G.degree u ∧ H.degree u=d := by
    apply Classical.byContradiction
    intro none
    have boosted (u : V) (hi : d≤G.degree u) : d+1≤H.degree u := by
      have ge := hi.trans (Graffiti189Ore.degree_increasing sub u)
      have ne : H.degree u≠d := fun e=>none ⟨u,hi,e⟩
      omega
    exact fail (traceable_all_but_one_by_order (connected_of_supergraph sub hc) (d+1)
      (fun u v ne=>(degree u v ne).imp (boosted u) (boosted v)) (by omega))
  obtain ⟨u,uhi,ud⟩ := exists'
  have uEq : G.degree u=H.degree u := by have n := Graffiti189Ore.degree_increasing sub u; omega
  have um := neighbors_unchanged_of_degree_unchanged sub uEq
  have nonlow_far {v : V} (uv : u≠v) (vh : d≤G.degree v) (no : ¬H.Adj u v) :
      v∈DistanceTwo G u := by
    obtain ⟨dg,w,uw,wv⟩ := terminal u v uv uhi vh no
    have m := Graffiti189Ore.degree_increasing sub v
    have vd : G.degree v=H.degree v := by omega
    exact Graffiti189LongestPath.CrossSaturation.ThreeShores.d2 hc uv (fun h=>no (sub h)) (um w uw)
      (neighbors_unchanged_of_degree_unchanged sub vd w wv.symm).symm
  have low_far {v : V} (uv : u≠v) (vlow : ¬d≤G.degree v) (no : ¬H.Adj u v) :
      v∈DistanceTwo G u := by
    obtain ⟨p⟩ := hc.preconnected v u
    have hit : ∃ w,G.Adj v w := by
      cases p with
      | nil => exact (uv rfl).elim
      | cons e p => exact ⟨_,e⟩
    obtain ⟨w,vw⟩ := hit
    have wh := (degree v w vw.ne).resolve_left vlow
    have wu : u≠w := fun e=>no (sub (e.symm ▸ vw.symm))
    have strict : d+1≤H.degree w := by
      have ge := wh.trans (Graffiti189Ore.degree_increasing sub w)
      have ne : H.degree w≠d := by
        intro e
        have eq : G.degree w=H.degree w := by
          have inc := Graffiti189Ore.degree_increasing sub w
          omega
        have next := neighbors_unchanged_of_degree_unchanged sub eq
        -- If w were unchanged, its adjacency to the sole low vertex
        -- already forces d+1 charged *high* nonneighbors.
        let S := (univ : Finset V)\insert w (H.neighborFinset w)
        have sSub : S⊆DistanceTwo G w := by
          intro z zz
          have out := (mem_sdiff.mp zz).2
          have wz : w≠z := fun h=>out (mem_insert.mpr (.inl h.symm))
          have notz : ¬H.Adj w z := fun f=>out (mem_insert_of_mem ((mem_neighborFinset H w z).mpr f))
          have zv : z≠v := fun h=>notz (h.symm ▸ sub vw.symm)
          have zh := (degree z v zv).resolve_right vlow
          obtain ⟨sum,r,wr,rz⟩ := terminal w z wz wh zh notz
          have md := Graffiti189Ore.degree_increasing sub z
          have ze : G.degree z=H.degree z := by omega
          exact Graffiti189LongestPath.CrossSaturation.ThreeShores.d2 hc wz (fun h=>notz (sub h)) (next r wr)
            (neighbors_unchanged_of_degree_unchanged sub ze r rz.symm).symm
        have cardS : S.card=d+1 := by
          change ((univ : Finset V)\insert w (H.neighborFinset w)).card=d+1
          rw [card_sdiff (subset_univ _),card_univ,card_insert_of_not_mem,
            card_neighborFinset_eq_degree,size,e]
          · omega
          exact fun h=>H.loopless w ((mem_neighborFinset H w w).mp h)
        have n := (card_le_card sSub).trans (distanceTwo_le_of_even d w (cap w))
        omega
      omega
    have uw : H.Adj u w := Classical.byContradiction (fun n=>by
      have hit := (terminal u w wu uhi wh n).1
      omega)
    exact Graffiti189LongestPath.CrossSaturation.ThreeShores.d2 hc uv (fun h=>no (sub h)) (um w uw) vw.symm
  let S := (univ : Finset V)\insert u (H.neighborFinset u)
  have sSub : S⊆DistanceTwo G u := by
    intro v hv
    have out := (mem_sdiff.mp hv).2
    have uv : u≠v := fun e=>out (mem_insert.mpr (.inl e.symm))
    have no : ¬H.Adj u v := fun h=>out (mem_insert_of_mem ((mem_neighborFinset H u v).mpr h))
    by_cases h : d≤G.degree v
    · exact nonlow_far uv h no
    exact low_far uv h no
  have sc : S.card=d+1 := by
    change ((univ : Finset V)\insert u (H.neighborFinset u)).card=d+1
    rw [card_sdiff (subset_univ _),card_univ,card_insert_of_not_mem,
      card_neighborFinset_eq_degree,size,ud]
    · omega
    exact fun e=>H.loopless u ((mem_neighborFinset H u u).mp e)
  have n := (card_le_card sSub).trans (distanceTwo_le_of_even d u (cap u))
  omega

#print axioms traceable_terminal_order_two_add
end Graffiti189LongestPath.SmallOrder
