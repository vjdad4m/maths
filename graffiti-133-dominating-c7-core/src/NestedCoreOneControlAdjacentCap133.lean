import NestedCoreOneControlSaturatedLift133
import NestedCorePrivateWeightedGeometry133
import C7MultiP8AdjCharge133
import C7MultiWeightedGlobal133

namespace Graffiti133NestedOneControl
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133MultiWeighted
  Graffiti133MultiP8 Graffiti133PrivateGeneric Graffiti133NestedActive Graffiti133NestedWeightedCore
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem adjacent_site_cases :
    ∀ i : Fin 7,
    (∃ k : Fin 7,(k=i ∨ k=i+1) ∧ (k=0 ∨ k=3)) ∨ i=1 ∨ i=4 ∨ i=5 := by decide

theorem adj_sat_geometry_cap
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9→V,InducedPath G p) (r : 4≤radius G)
    (K : Finset V) (ck : ∀ i,H.c i∈K)
    (dom : ∀ y : (K : Set V),Outside (restrictedHole H K ck).c y →
      ∃ i,(G.induce (K : Set V)).Adj y ((restrictedHole H K ck).c i))
    (D : Finset V) (ddom : ∀ x : V,x∈D ∨ ∃ y∈D,G.Adj x y)
    (u : V) (un : Outside H.c u)
    (ue : ∀ j : Fin 7,G.Adj u (H.c j)↔j=0 ∨ j=3)
    (shape : ∀ x∈D,(∃ i,H.c i=x) ∨ x=u)
    (has : ∀ a : Fin 8,∃ z,PrivateFor G (core H u) a z)
    (cert : ∀ i : Fin 7,(i=1 ∨ i=4 ∨ i=5) → ∀ mask : Fin 8,
      ∃ t,checked (satSpec i mask) [] t=true ∧ usesOnly (satActive mask) t=true)
    (x : (K : Set V)) (xo : Outside (restrictedHole H K ck).c x)
    (two : (contactSet (restrictedHole H K ck) x).card=2)
    (adj : ∃ i∈contactSet (restrictedHole H K ck) x,∃ j∈contactSet (restrictedHole H K ck) x,Cyclic i j) :
    (exteriorNeighbors (restrictedHole H K ck) x).card≤2 := by
  classical
  let J := G.induce (K : Set V)
  let B := restrictedHole H K ck
  obtain ⟨i,tag⟩ := adjacent_pair_successor_form _ two adj
  have itag (j : Fin 7) : G.Adj x.val (H.c j)↔j=i ∨ j=i+1 :=
    (mem_contactSet B x j).symm.trans (tag j)
  have teq : contactSet B x={i,i+1} := by
    ext j
    simpa only [Finset.mem_insert,Finset.mem_singleton] using tag j
  change (exteriorNeighbors B x).card≤2
  by_contra! bad
  have full : (cleanSites (contactSet B x)).card≤(exteriorNeighbors B x).card := by
    rw [teq,adjacent_exact_clean_card]
    omega
  have got := saturated_exterior_has_singletons_at_all_clean_sites B (restricted_c4 h4 K) dom x xo full
  have chooseMe (d : Fin 3) := got (satSite i d) (by
    rw [teq,adjacent_exact_clean_sites]
    exact ⟨d,rfl⟩)
  choose z zoff xz zp using chooseMe
  change ∀ d,G.Adj x.val (z d).val at xz
  change ∀ d j,G.Adj (z d).val (H.c j)↔j=satSite i d at zp
  have distCycle := saturated_adjacent_cycle_dist_le_two H hc x.val i (fun d=>(z d).val) itag xz
    (fun d=>(zp d _).mpr rfl)
  rcases adjacent_site_cases i with ⟨a,ai,au⟩|notSafe
  · have twoD {x y z : V} (xy : G.Adj x y) (yz : G.Adj y z) : G.dist x z≤2 := by
      have h : G.dist x z≤G.dist x y+G.dist y z := hc.dist_triangle
      rw [dist_eq_one_iff_adj.mpr xy,dist_eq_one_iff_adj.mpr yz] at h
      exact h
    have small := radius_three_from_core_cover hc D ddom x.val (by
      intro w dw
      rcases shape w dw with ⟨j,rfl⟩|rfl
      · exact distCycle j
      · exact twoD ((itag a).mpr ai) ((ue a).mpr au).symm)
    omega
  have onOverlap :
      ∀ (w : V) (p : Fin 7), (∀ j : Fin 7,G.Adj w (H.c j)↔j=p ∨ j=p+1) → w≠u := by
    intro w p wp
    rintro rfl
    have bad : ∀ p : Fin 7,¬(∀ j : Fin 7,(j=0 ∨ j=3)↔j=p ∨ j=p+1) := by decide
    exact bad p (fun j=>(ue j).symm.trans (wp j))

  have onSingle :
      ∀ (w : V) (p : Fin 7), (∀ j : Fin 7,G.Adj w (H.c j)↔j=p) → w≠u := by
    intro w p wp
    rintro rfl
    have bad : ∀ p : Fin 7,¬(∀ j : Fin 7,(j=0 ∨ j=3)↔j=p) := by decide
    exact bad p (fun j=>(ue j).symm.trans (wp j))

  have outs (w : (K : Set V)) (wo : Outside B.c w) (wu : w.val≠u) :
      ∀ a : Fin 8,w.val≠core H u a := by
    intro a
    fin_cases a <;> simp [core] <;> first | exact wu | exact fun e=>wo _ (Subtype.ext e)
  have cv := core_at_site H u
  exact private_adjacent_multi_not_saturated h4 h9 i (cert i notSafe) _ (core_injective H u un)
    (core_fits H u ue) has x.val (outs x xo (onOverlap _ _ itag))
    (fun j=>by rw [cv]; exact itag j) (fun d=>(z d).val)
    (fun d=>outs (z d) (zoff d) (onSingle _ _ (zp d)))
    (fun d j=>by rw [cv]; exact zp d j) xz

#print axioms adj_sat_geometry_cap
end Graffiti133NestedOneControl
