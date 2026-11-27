import NestedCorePrivateNearSlack133
import NestedCorePrivateAdjacentChargeCap133
import NestedCorePrivateFarChargeCap133
import NestedCoreWeightedGlobalSlack133
import NestedCorePrivateAdjacentRows01133
import NestedCorePrivateAdjacentRows02133
import NestedCorePrivateAdjacentRows04133
import NestedCorePrivateAdjacentRows05133
import NestedCorePrivateAdjacentRows06133
import NestedCorePrivateAdjacentRows11133
import NestedCorePrivateAdjacentRows13133
import NestedCorePrivateAdjacentRows14133
import NestedCorePrivateAdjacentRows15133
import NestedCorePrivateAdjacentRows16133

namespace Graffiti133NestedWeightedCore
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133MultiWeighted
  Graffiti133PrivateGeneric Graffiti133NestedActive
open scoped Classical
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

theorem sat_all_unsafe_cases (m : Bool) (i : Fin 7) (notSafe : ¬satSafeSites m i) (mask : Fin 8) :
    ∃ t,checked (satSpec m i mask) [] t=true ∧ usesOnly (satActive mask) t=true := by
  cases m <;> fin_cases i
  all_goals first
    | exact (notSafe (by decide)).elim
    | exact satSuccess_0_1 mask
    | exact satSuccess_0_2 mask
    | exact satSuccess_0_4 mask
    | exact satSuccess_0_5 mask
    | exact satSuccess_0_6 mask
    | exact satSuccess_1_1 mask
    | exact satSuccess_1_3 mask
    | exact satSuccess_1_4 mask
    | exact satSuccess_1_5 mask
    | exact satSuccess_1_6 mask

end Graffiti133NestedWeightedCore

namespace Graffiti133NestedLongGates
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133CoreSeven
  Graffiti133MultiWeighted Graffiti133PrivateCross Graffiti133NestedSingleGate Graffiti133NestedWeightedCore
  Graffiti133PrivateGeneric Graffiti133NestedActive
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem radius_four_canonical_private_two_core_no_contact_cap
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (h9 : ¬∃ f : Fin 9→V,InducedPath G f) (hr : 4≤radius G)
    (D K : Finset V) (cd : ∀ i,H.c i∈D) (ck : ∀ i,H.c i∈K)
    (ddom : ∀ x : V,x∈D ∨ ∃ y∈D,G.Adj x y)
    (d7 : ¬∃ f : Fin 7→(D : Set V),InducedPath (G.induce (D : Set V)) f)
    (u v : V) (uv : u≠v) (ud : u∈D) (vd : v∈D) (uk : u∈K) (vk : v∈K)
    (shape : ∀ w∈D,(∃ i,H.c i=w) ∨ w=u ∨ w=v)
    (uoff : Outside H.c u) (voff : Outside H.c v) (noedge : ¬G.Adj u v)
    (m : Bool) (up : ∀ i : Fin 7,G.Adj u (H.c i)↔i=0 ∨ i=3)
    (vp : ∀ i : Fin 7,G.Adj v (H.c i)↔ (if m then (i=1 ∨ i=2 ∨ i=5) else (i=1 ∨ i=4)))
    (privateAll : ∀ i : Fin 9,∃ z,PrivateFor G (canonCore H u v) i z)
    (kdom : ∀ y : (K : Set V),Outside (restrictedHole H K ck).c y →
      ∃ i,(G.induce (K : Set V)).Adj y ((restrictedHole H K ck).c i))
    (remote : ∀ w∉K,Remote H w) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  classical
  have touch (w : V) (wk : w∈K) (wo : Outside H.c w) : (contactSet H w).Nonempty := by
    obtain ⟨i,hi⟩ := kdom (⟨w,wk⟩ : (K : Set V)) (fun i eq=>wo i (congrArg Subtype.val eq))
    exact ⟨i,(mem_contactSet H w i).mpr hi⟩
  let L := K.filter (fun x=>Outside H.c x ∧ x≠u ∧ x≠v ∧ ¬VeryShortGate H x)
  have lim : L.card≤1 := by
    apply Finset.card_le_one.mpr
    intro x xm y ym
    by_contra xy
    obtain ⟨xk,xo,xu,xv,xl⟩ := Finset.mem_filter.mp xm
    obtain ⟨yk,yo,yu,yv,yl⟩ := Finset.mem_filter.mp ym
    have small := radius_three_of_four_long_gates H hc h4 D cd ddom d7 u v x y ud vd shape
      uoff voff xo yo uv xu.symm yu.symm xv.symm yv.symm xy
      (touch _ uk uoff) (touch _ vk voff) (touch _ xk xo) (touch _ yk yo) xl yl
    omega
  let B := restrictedHole H K ck
  have range (y : (K : Set V)) (ym : y∈scoredFar B ⟨u,uk⟩ ⟨v,vk⟩) : y.val∈L := by
    have hh : y∈multiVertices B ∧ (contactSet B y).card=2 ∧
        (¬∃ i∈contactSet B y,∃ j∈contactSet B y,Cyclic i j) ∧ y≠⟨u,uk⟩ ∧ y≠⟨v,vk⟩ := by
      simpa only [scoredFar,Finset.mem_filter] using ym
    obtain ⟨mm,two,nadj,yu,yv⟩ := hh
    have yout : Outside H.c y.val :=
      fun i e=>(Finset.mem_filter.mp mm).2.1 i (Subtype.ext e)
    have eq : contactSet B y=contactSet H y.val := restricted_contacts H K ck y
    rw [eq] at two nadj
    have ns : ¬VeryShortGate H y.val := by
      rintro ⟨_,i,flag|flag⟩
      · have eq1 : contactSet H y.val={i} := by
          ext j
          exact (mem_contactSet H _ _).trans ((flag j).trans (by simp))
        rw [eq1] at two
        simp at two
      · apply nadj
        have c : Cyclic i (i+1) := by
          have r : ∀ i : Fin 7,Cyclic i (i+1) := by decide
          exact r i
        exact ⟨i,(mem_contactSet H _ _).mpr ((flag i).mpr (Or.inl rfl)),i+1,
          (mem_contactSet H _ _).mpr ((flag (i+1)).mpr (Or.inr rfl)),c⟩
    exact Finset.mem_filter.mpr ⟨y.property,yout,fun e=>yu (Subtype.ext e),fun e=>yv (Subtype.ext e),ns⟩
  have remain : (scoredFar B ⟨u,uk⟩ ⟨v,vk⟩).card≤1 :=
    (Finset.card_le_card_of_injOn Subtype.val range
      (by intro a _ b _ e; exact Subtype.ext e)).trans lim
  have short (y : (K : Set V)) (ym : y∈adjTwo B) : (exteriorNeighbors B y).card≤2 := by
    obtain ⟨ym,two,adj⟩ := Finset.mem_filter.mp ym
    exact adj_sat_geometry_cap H hc h4 h9 hr K ck kdom D ddom m u v uoff voff uv up vp noedge shape
      privateAll (sat_all_unsafe_cases m) y (Finset.mem_filter.mp ym).2.1 two adj
  have far (y : (K : Set V)) (high : y=⟨u,uk⟩ ∨ y=⟨v,vk⟩) (two : (contactSet B y).card=2)
      (_ : ¬∃ i∈contactSet B y,∃ j∈contactSet B y,Cyclic i j) :
      ((exteriorNeighbors B y) \ markedNeighbors B y).card=0 :=
    canonical_priority_far_clean_zero H h4 h9 K ck kdom m u v uoff voff uv up vp noedge privateAll y
      (high.imp (congrArg Subtype.val) (congrArg Subtype.val)) two
  have no9 : ¬∃ p : Fin 9→(K : Set V),InducedPath (G.induce (K : Set V)) p := by
    rintro ⟨p,hp⟩
    exact h9 ⟨Subtype.val ∘ p,Subtype.val_injective.comp hp.1,hp.2⟩
  have base := refined_near_base_slack B (restricted_c4 h4 K) no9 kdom _ _ remain short far
  have card : Fintype.card (K : Set V)=K.card := Fintype.card_coe K
  rw [card] at base
  have slack := (by omega : ∀ {l n : Nat},l+5≤4*n → l+2≤4*n) base
  exact radius_four_canonical_private_core_near_slack_mean_four H hc h4 h9 hr D K cd ck ddom d7 u v uv ud vd uk vk
    shape uoff voff noedge m up vp privateAll kdom slack remote

#print axioms radius_four_canonical_private_two_core_no_contact_cap
end Graffiti133NestedLongGates
