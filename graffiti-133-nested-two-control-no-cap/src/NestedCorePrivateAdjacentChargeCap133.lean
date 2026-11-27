import C7MultiScoreHelpers133
import NestedCorePrivateAdjacentSatRealLift133
import NestedCorePrivateWeightedGeometry133
import C7MultiP8AdjCharge133

namespace Graffiti133NestedWeightedCore
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133MultiWeighted
  Graffiti133MultiP8 Graffiti133PrivateGeneric Graffiti133PrivateCross Graffiti133ExpandedPrivate Graffiti133NestedActive
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

def satSafeSites (m : Bool) (i : Fin 7) : Prop :=
  i=0 ∨ (if m then i=2 else i=3)

instance (m : Bool) (i : Fin 7) : Decidable (satSafeSites m i) := by unfold satSafeSites; infer_instance

theorem sat_safe_both_control_sites :
    ∀ (m : Bool) (i : Fin 7),satSafeSites m i →
    (∃ k : Fin 7,(k=i ∨ k=i+1) ∧ (k=0 ∨ k=3)) ∧
    (∃ l : Fin 7,(l=i ∨ l=i+1) ∧
      (if m then (l=1 ∨ l=2 ∨ l=5) else (l=1 ∨ l=4))) := by decide

theorem adj_sat_geometry_cap
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9→V,InducedPath G p) (r : 4≤radius G)
    (K : Finset V) (ck : ∀ i,H.c i∈K)
    (dom : ∀ y : (K : Set V),Outside (restrictedHole H K ck).c y →
      ∃ i,(G.induce (K : Set V)).Adj y ((restrictedHole H K ck).c i))
    (D : Finset V) (ddom : ∀ x : V,x∈D ∨ ∃ y∈D,G.Adj x y)
    (m : Bool) (u v : V) (un : Outside H.c u) (vn : Outside H.c v) (uv : u≠v)
    (ue : ∀ j : Fin 7,G.Adj u (H.c j)↔j=0 ∨ j=3)
    (ve : ∀ j : Fin 7,G.Adj v (H.c j)↔(if m then (j=1 ∨ j=2 ∨ j=5) else (j=1 ∨ j=4)))
    (noedge : ¬G.Adj u v)
    (shape : ∀ x∈D,(∃ i,H.c i=x) ∨ x=u ∨ x=v)
    (has : ∀ a : Fin 9,∃ z,PrivateFor G (canonCore H u v) a z)
    (cert : ∀ i : Fin 7,¬satSafeSites m i → ∀ mask : Fin 8,
      ∃ t,checked (satSpec m i mask) [] t=true ∧ usesOnly (satActive mask) t=true)
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
  by_cases safe : satSafeSites m i
  · obtain ⟨⟨a,ai,au⟩,⟨b,bi,bv⟩⟩ := sat_safe_both_control_sites m i safe
    have twoD {x y z : V} (xy : G.Adj x y) (yz : G.Adj y z) : G.dist x z≤2 := by
      have h : G.dist x z≤G.dist x y+G.dist y z := hc.dist_triangle
      rw [dist_eq_one_iff_adj.mpr xy,dist_eq_one_iff_adj.mpr yz] at h
      exact h
    have small := radius_three_from_core_cover hc D ddom x.val (by
      intro w dw
      rcases shape w dw with ⟨j,rfl⟩|rfl|rfl
      · exact distCycle j
      · exact twoD ((itag a).mpr ai) ((ue a).mpr au).symm
      · exact twoD ((itag b).mpr bi) ((ve b).mpr bv).symm)
    omega
  have onOverlap :
      ∀ (w : V) (p : Fin 7), (∀ j : Fin 7,G.Adj w (H.c j)↔j=p ∨ j=p+1) → w≠u ∧ w≠v := by
    intro w p wp
    constructor
    · rintro rfl
      have bad : ∀ p : Fin 7,¬(∀ j : Fin 7,(j=0 ∨ j=3)↔j=p ∨ j=p+1) := by decide
      exact bad p (fun j=>(ue j).symm.trans (wp j))
    · rintro rfl
      have bad : ∀ m : Bool,∀ p : Fin 7,¬(∀ j : Fin 7,
          (if m then (j=1 ∨ j=2 ∨ j=5) else (j=1 ∨ j=4))↔j=p ∨ j=p+1) := by decide
      exact bad m p (fun j=>(ve j).symm.trans (wp j))
  have onSingle :
      ∀ (w : V) (p : Fin 7), (∀ j : Fin 7,G.Adj w (H.c j)↔j=p) → w≠u ∧ w≠v := by
    intro w p wp
    constructor
    · rintro rfl
      have bad : ∀ p : Fin 7,¬(∀ j : Fin 7,(j=0 ∨ j=3)↔j=p) := by decide
      exact bad p (fun j=>(ue j).symm.trans (wp j))
    · rintro rfl
      have bad : ∀ m : Bool,∀ p : Fin 7,¬(∀ j : Fin 7,
          (if m then (j=1 ∨ j=2 ∨ j=5) else (j=1 ∨ j=4))↔j=p) := by decide
      exact bad m p (fun j=>(ve j).symm.trans (wp j))
  have outs (w : (K : Set V)) (wo : Outside B.c w) (wu : w.val≠u) (wv : w.val≠v) :
      ∀ a : Fin 9,w.val≠canonCore H u v a := by
    intro a
    fin_cases a <;> simp [canonCore] <;> first | exact wu | exact wv |
      exact fun e=>wo _ (Subtype.ext e)
  have cv (j : Fin 7) : canonCore H u v (sIndex j)=H.c j := by fin_cases j <;> rfl
  obtain ⟨xu,xv⟩ := onOverlap x.val i itag
  exact private_adjacent_multi_not_saturated h4 h9 m i (cert i safe) _ (canonCore_injective H u v un vn uv)
    (canonCore_fits H u v m noedge ue ve) has x.val (outs x xo xu xv)
    (fun j=>by rw [cv]; exact itag j) (fun d=>(z d).val)
    (fun d=>outs (z d) (zoff d) (onSingle _ _ (zp d)).1 (onSingle _ _ (zp d)).2)
    (fun d j=>by rw [cv]; exact zp d j) xz

#print axioms adj_sat_geometry_cap
end Graffiti133NestedWeightedCore
