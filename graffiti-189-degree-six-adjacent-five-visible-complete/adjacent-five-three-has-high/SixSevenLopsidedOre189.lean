import SixEightTripleCoreClosure189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private starClose star_mono star_degree_of_marked star_degree_of_unmarked local_degree_mono from SixTenOre189
open private cliqueFill cliqueFill_mono cliqueFill_degree from SixEightTripleCoreClosure189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem four_heavy_seven (n : Fintype.card V=7)
    (C : Finset V) (c4 : 4≤C.card) (h5 : ∀ u∈C,5≤G.degree u)
    {a b : V} (ab : a≠b) (b2 : 2≤G.degree b)
    (min3 : ∀ u,u≠b → 3≤G.degree u) :
    ∃ p : G.Walk a b,p.IsPath ∧ ∀ u,u∈p.support := by
  classical
  let H := starClose G C
  have min4 (u : V) : 4≤H.degree u := by
    change 4≤(starClose G C).degree u
    by_cases cu : u∈C
    · have k := star_degree_of_marked (G:=G) C cu
      rw [n] at k
      omega
    exact c4.trans (star_degree_of_unmarked (G:=G) C cu)
  obtain ⟨p,pp,ps⟩ := hamilton_connected_of_ore (G:=H)
    (fun u v _ _=>by rw [n]; have i := min4 u; have j := min4 v; omega) ab
  apply weighted_terminal_ore_closure (star_mono G C) _ p pp ps
  intro u v yes no
  rw [n]
  rcases yes with e|⟨_,uc|vc⟩
  · exact (no e).elim
  · have i := h5 u uc
    by_cases e : v=b
    · subst v; rw [if_pos (.inr rfl)]; omega
    have j := min3 v e
    omega
  · have j := h5 v vc
    by_cases e : u=b
    · subst u; rw [if_pos (.inl rfl)]; omega
    have i := min3 u e
    omega

/-- A seven-vertex support has a Hamilton path between the marked ends if
four vertices already have degree five, or if a six-vertex degree-four
part can first be made a clique. Degree two is tolerated at the last end. -/
theorem seven_lopsided_ore (n : Fintype.card V=7)
    {a b : V} (ab : a≠b) (b2 : 2≤G.degree b) (min3 : ∀ u,u≠b → 3≤G.degree u)
    (profile : (∃ C : Finset V,4≤C.card ∧ ∀ u∈C,5≤G.degree u) ∨
      (∃ C : Finset V,C.card=6 ∧ ∀ u∈C,4≤G.degree u)) :
    ∃ p : G.Walk a b,p.IsPath ∧ ∀ u,u∈p.support := by
  classical
  rcases profile with ⟨C,c4,h5⟩|⟨C,c6,h4⟩
  · exact four_heavy_seven n C c4 h5 ab b2 min3
  let H := cliqueFill G C
  have sub : G≤H := cliqueFill_mono G C
  have hi (u : V) (um : u∈C) : 5≤H.degree u := by
    have e := cliqueFill_degree (G:=G) C um
    rw [c6] at e
    exact e
  obtain ⟨p,pp,ps⟩ := four_heavy_seven (G:=H) n C (by omega) hi ab
    (b2.trans (local_degree_mono sub b)) (fun u h=>(min3 u h).trans (local_degree_mono sub u))
  apply weighted_terminal_ore_closure sub _ p pp ps
  intro u v yes no
  rw [n]
  rcases yes with e|⟨_,um,vm⟩
  · exact (no e).elim
  have h := h4 u um
  have j := h4 v vm
  omega

#print axioms seven_lopsided_ore
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
