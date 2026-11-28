import SixTripleCutTerminalRank189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

def dark (G : SimpleGraph V) [DecidableRel G.Adj] (S A : Finset V) :=
  A \ visible G S A

private theorem no_adj_dark {S A : Finset V} {z : V} (zz : z∈dark G S A)
    {a : V} (az : a∈S) : ¬G.Adj z a := by
  intro za
  exact (mem_sdiff.mp zz).2 (mem_filter.mpr ⟨(mem_sdiff.mp zz).1,a,az,za⟩)

private theorem visible_distance_two_of_singleton (hc : G.Connected)
    {S A : Finset V} {s : V}
    (one : Shore G S ({s}:Finset V)) (sh : Shore G S A)
    (sep : Disjoint ({s}:Finset V) A)
    (touch : ∀ t∈S,G.Adj s t) : visible G S A⊆DistanceTwo G s := by
  intro z zm
  obtain ⟨za,t,ts,zt⟩ := mem_filter.mp zm
  have ss : s∈({s}:Finset V) := mem_singleton_self _
  have ne : s≠z := fun e => disjoint_left.mp sep ss (e ▸ za)
  have no : ¬G.Adj s z := fun h=>
    (one.closed s ss z h).elim (fun z' => disjoint_left.mp sep z' za)
      (fun z' => disjoint_left.mp sh.disjoint za z')
  exact two_of_common hc ne no (touch t ts) zt.symm

/-- Three shores with a singleton pin rigidify the parity shells of the pin.
Both other shores have exactly three visible vertices and at least four
dark vertices. Every dark vertex has a neighbor visible to the cut. -/
theorem singleton_pin_dark_geometry (hc : G.Connected)
    (cap : ∀ v,(EvenFrom G v).card≤7) (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S A B : Finset V} (ss : S.card=3) {s : V}
    (one : Shore G S ({s}:Finset V)) (shA : Shore G S A) (shB : Shore G S B)
    (sA : Disjoint ({s}:Finset V) A) (sB : Disjoint ({s}:Finset V) B) (ab : Disjoint A B) :
    (visible G S A).card=3 ∧ (visible G S B).card=3 ∧
    (dark G S A).card≥4 ∧ (dark G S B).card≥4 ∧
    (∀ x∈dark G S A,∃ y∈visible G S A,G.Adj x y) ∧
    (∀ x∈dark G S B,∃ y∈visible G S B,G.Adj x y) := by
  classical
  have sa : s∈({s}:Finset V) := mem_singleton_self _
  have lo := one.degree_bound sa
  rw [card_singleton,ss] at lo
  have touch (t : V) (tm : t∈S) : G.Adj s t := by
    obtain ⟨z,zm,tz⟩ := one.hit ss conn tm
    rw [mem_singleton.mp zm] at tz
    exact tz.symm
  have high {W : Finset V} (sw : Disjoint ({s}:Finset V) W) {x : V} (xm : x∈W) :
      6≤G.degree x := by
    have ne : x≠s := fun e=>disjoint_left.mp sw sa (e ▸ xm)
    exact (degree x s ne).resolve_right (by omega)
  have lower {W : Finset V} (sh : Shore G S W) (sw : Disjoint ({s}:Finset V) W) :
      4≤W.card := by
    obtain ⟨x,xm⟩ := sh.nonempty
    have h := high sw xm
    have b := sh.degree_bound xm
    rw [ss] at b
    omega
  have visA := shA.visible_lower ss conn ((by decide : 3≤4).trans (lower shA sA))
  have visB := shB.visible_lower ss conn ((by decide : 3≤4).trans (lower shB sB))
  let C := visible G S A∪visible G S B
  have dis : Disjoint (visible G S A) (visible G S B) :=
    ab.mono (filter_subset _ _) (filter_subset _ _)
  have size : C.card=(visible G S A).card+(visible G S B).card := card_union_of_disjoint dis
  have csub : C⊆DistanceTwo G s := union_subset
    (visible_distance_two_of_singleton hc one shA sA touch)
    (visible_distance_two_of_singleton hc one shB sB touch)
  have h := (card_le_card csub).trans (distanceTwo_le_of_even 6 s (cap s))
  have va : (visible G S A).card=3 := by omega
  have vb : (visible G S B).card=3 := by omega
  have sized : C.card=6 := by omega
  have eq : C=DistanceTwo G s := eq_of_subset_of_card_le csub (by rw [sized]; exact distanceTwo_le_of_even 6 s (cap s))
  have rad (z : V) : G.dist s z≤3 := by
    by_contra! bad
    have p := distanceTwo_add_to_even_along_geodesic hc 1 (x:=s) (y:=z) (by omega)
    rw [←eq,sized] at p
    have d := cap s
    omega
  have dark_count {W : Finset V} (sh : Shore G S W) (sw : Disjoint ({s}:Finset V) W)
      (v3 : (visible G S W).card=3) : 4≤(dark G S W).card := by
    have n : 0<(dark G S W).card := by
      unfold dark
      have incl : visible G S W⊆W := filter_subset _ _
      rw [card_sdiff incl,v3]
      have l := lower sh sw
      omega
    obtain ⟨z,zd⟩ := card_pos.mp n
    have zm := (mem_sdiff.mp zd).1
    have nei : G.neighborFinset z⊆W.erase z := by
      intro t tm
      have zt := (G.mem_neighborFinset ..).mp tm
      rcases sh.closed z zm t zt with h|h
      · exact mem_erase.mpr ⟨zt.ne.symm,h⟩
      · exact (no_adj_dark zd h zt).elim
    have k := card_le_card nei
    rw [card_neighborFinset_eq_degree,card_erase_of_mem zm] at k
    have hh := high sw zm
    unfold dark
    have incl : visible G S W⊆W := filter_subset _ _
    rw [card_sdiff incl,v3]
    omega
  have has_neighbor {W : Finset V} (sh : Shore G S W) (sw : Disjoint ({s}:Finset V) W)
      (outside : ∀ z∈dark G S W,z∉C) :
      ∀ z∈dark G S W,∃ w∈visible G S W,G.Adj z w := by
    intro z zd
    have zm := (mem_sdiff.mp zd).1
    have ne : s≠z := fun e=>disjoint_left.mp sw sa (e ▸ zm)
    have no : ¬G.Adj s z := fun e=>
      (one.closed s sa z e).elim (fun q => disjoint_left.mp sw q zm)
        (fun q=>disjoint_left.mp sh.disjoint zm q)
    have p3 : G.dist s z=3 := by
      have lt := hc.one_lt_dist_of_ne_of_not_adj ne no
      have d2 : G.dist s z≠2 := by
        intro d
        exact outside z zd (eq.symm ▸ (show z∈DistanceTwo G s by simp [DistanceTwo,d]))
      have r := rad z
      omega
    obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist s z
    have len := pl.trans p3
    let u := p.getVert 1
    let w := p.getVert 2
    have su : G.Adj s u := by simpa [u] using p.adj_getVert_succ (i:=0) (by omega : 0<p.length)
    have uw : G.Adj u w := p.adj_getVert_succ (i:=1) (by omega)
    have wz : G.Adj w z := by
      have e := p.adj_getVert_succ (i:=2) (by omega)
      rwa [show p.getVert 3=z by rw [←len,getVert_length]] at e
    have uS : u∈S := (one.closed s sa u su).resolve_left
      (fun h => su.ne (mem_singleton.mp h).symm)
    have wW := (sh.closed z zm w wz.symm).resolve_right (fun h => no_adj_dark zd h wz.symm)
    exact ⟨w,mem_filter.mpr ⟨wW,u,uS,uw.symm⟩,wz.symm⟩
  refine ⟨va,vb,dark_count shA sA va,dark_count shB sB vb,has_neighbor shA sA ?_,has_neighbor shB sB ?_⟩
  · intro z zd zc
    rcases mem_union.mp zc with la|lb
    · exact (mem_sdiff.mp zd).2 la
    · exact disjoint_left.mp ab (mem_sdiff.mp zd).1 (mem_filter.mp lb).1
  · intro z zd zc
    rcases mem_union.mp zc with la|lb
    · exact disjoint_left.mp ab (mem_filter.mp la).1 (mem_sdiff.mp zd).1
    · exact (mem_sdiff.mp zd).2 lb

#print axioms singleton_pin_dark_geometry
end Graffiti189LongestPath.ThresholdSix.ThreeCut
