import SixSingletonFiveThreeDarkThree189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 p5 from SixSingletonFiveShallowRoute189
open private dark_core_five from SixSingletonFiveThreeBase189
open private split_dark_degree from SixSingletonFiveThreeDarkThree189
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem all_low_cross_counts {L R S : Finset V} {T : V} (_F : ProfileThree G L R S T) :
    (∑ u∈S,(inside G (D\S) u).card) = ∑ v∈D\S,(inside G S v).card := by
  have cast (v : V) : S.bipartiteBelow G.Adj v=inside G S v := by
    ext u
    simp only [mem_bipartiteBelow,inside,mem_filter]
    exact and_congr_right (fun _=>⟨Adj.symm,Adj.symm⟩)
  have count := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj (s:=S) (t:=D\S)
  simp_rw [cast] at count
  exact count

private theorem each_core_inside_four {L R S : Finset V} {T : V} (F : ProfileThree G L R S T)
    (u : V) (us : u∈S) : (inside G S u).card≤4 := by
  have k : inside G S u⊆S.erase u := fun v vm=>mem_erase.mpr
    ⟨(mem_filter.mp vm).2.ne.symm,(mem_filter.mp vm).1⟩
  have f := card_le_card k
  rw [card_erase_of_mem us,dark_core_five F] at f
  exact f

private theorem core_dark_sum {L R S : Finset V} {T : V} (F : ProfileThree G L R S T) :
    26≤∑ u∈S,(inside G D u).card := by
  have min : (∑ _u∈S.erase T,(5:ℕ))≤∑ u∈S.erase T,(inside G D u).card :=
    sum_le_sum (fun u m=>F.dark5 u (mem_erase.mp m).2)
  rw [sum_const,nsmul_eq_mul,card_erase_of_mem F.deepS,dark_core_five F] at min
  rw [←sum_erase_add S (fun u=>(inside G D u).card) F.deepS]
  have k := F.deep6
  omega

private theorem core_cross_exists_six {L R S : Finset V} {T : V} (F : ProfileThree G L R S T) :
    6≤∑ z∈D\S,(inside G S z).card := by
  have h := core_dark_sum F
  have k : (∑ u∈S,(inside G S u).card)≤∑ _u∈S,(4:ℕ) := sum_le_sum (each_core_inside_four F)
  rw [sum_const,nsmul_eq_mul,dark_core_five F] at k
  simp_rw [split_dark_degree F] at h
  rw [sum_add_distrib,all_low_cross_counts F] at h
  omega

theorem all_low_core_route {L R S : Finset V} {T z : V} (F : ProfileThree G L R S T)
    (low : ∀ w∈D\S,(inside G D w).card≤3) (zm : z∈D\S) (tiny : (inside G D z).card≤2) :
    ∀ u∈S,∀ v∈S,u≠v → RouteOn G S u v := by
  have core := core_dark_sum F
  simp_rw [split_dark_degree F] at core
  rw [sum_add_distrib,all_low_cross_counts F] at core
  let W := D\S
  have w3 : W.card=3 := F.balance
  have rem : (∑ w∈W.erase z,(inside G S w).card)≤∑ _w∈W.erase z,(3:ℕ) := by
    apply sum_le_sum
    intro w wm
    have h := low w (mem_erase.mp wm).2
    rw [split_dark_degree F] at h
    omega
  rw [sum_const,nsmul_eq_mul,card_erase_of_mem zm,w3] at rem
  have zs : (inside G S z).card≤2 := by
    have q := split_dark_degree F z
    omega
  have cross8 : (∑ w∈W,(inside G S w).card)≤8 := by
    rw [←sum_erase_add W (fun w=>(inside G S w).card) zm]
    omega
  change 26≤(∑ u∈S,(inside G S u).card)+(∑ v∈W,(inside G S v).card) at core
  have internal : 18≤∑ u∈S,(inside G S u).card := by omega
  intro u um v vm uv
  apply terminal_route_on_of_local_ore S um vm uv
  intro i im j jm ij _
  rw [dark_core_five F]
  have je : j∈S.erase i := mem_erase.mpr ⟨ij.symm,jm⟩
  have r : (∑ u∈(S.erase i).erase j,(inside G S u).card)≤
      ∑ _u∈(S.erase i).erase j,(4:ℕ) :=
    sum_le_sum (fun u h=>each_core_inside_four F u (mem_erase.mp (mem_erase.mp h).2).2)
  rw [sum_const,nsmul_eq_mul,card_erase_of_mem je,card_erase_of_mem im,dark_core_five F] at r
  rw [←sum_erase_add S (fun u=>(inside G S u).card) im,
    ←sum_erase_add (S.erase i) (fun u=>(inside G S u).card) je] at internal
  omega

theorem all_low_every_balance_hits_core {L R S : Finset V} {T z : V} (F : ProfileThree G L R S T)
    (low : ∀ w∈D\S,(inside G D w).card≤3) (zm : z∈D\S) :
    ∃ u∈S,G.Adj u z := by
  classical
  by_contra no
  have z0 : (inside G S z).card=0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_not_mem.mpr
    intro u um
    exact no ⟨u,(mem_filter.mp um).1,(mem_filter.mp um).2.symm⟩
  have cross := core_cross_exists_six F
  let W := D\S
  have w3 : W.card=3 := F.balance
  have zd := (mem_sdiff.mp zm).1
  have hit : ∃ w∈W,G.Adj z w := by
    by_contra none
    have sub : G.neighborFinset z⊆P := by
      intro u um
      have e := (mem_neighborFinset _ _ _).mp um
      exact (mem_union.mp (F.darkBounds z zd u e)).resolve_left
        (fun ud=>by
          by_cases us : u∈S
          · exact no ⟨u,us,e.symm⟩
          exact none ⟨u,mem_sdiff.mpr ⟨ud,us⟩,e⟩)
    have h := card_le_card sub
    rw [card_neighborFinset_eq_degree,p5] at h
    have k := F.darkHigh z zd
    omega
  obtain ⟨w,wm,zw⟩ := hit
  have we : w∈W.erase z := mem_erase.mpr ⟨zw.ne.symm,wm⟩
  have atLeast : 1≤(inside G W w).card := card_pos.mpr ⟨z,mem_filter.mpr ⟨zm,zw.symm⟩⟩
  have w2 : (inside G S w).card≤2 := by
    have h := low w wm
    rw [split_dark_degree F] at h
    change (inside G S w).card+(inside G W w).card≤3 at h
    omega
  have rem : (∑ u∈(W.erase z).erase w,(inside G S u).card)≤∑ _u∈(W.erase z).erase w,(3:ℕ) := by
    apply sum_le_sum
    intro u um
    have h := low u (mem_erase.mp (mem_erase.mp um).2).2
    rw [split_dark_degree F] at h
    omega
  rw [sum_const,nsmul_eq_mul,card_erase_of_mem we,card_erase_of_mem zm,w3] at rem
  change 6≤∑ u∈W,(inside G S u).card at cross
  rw [←sum_erase_add W (fun u=>(inside G S u).card) zm,
    ←sum_erase_add (W.erase z) (fun u=>(inside G S u).card) we,z0] at cross
  omega

#print axioms all_low_core_route
#print axioms all_low_every_balance_hits_core
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
