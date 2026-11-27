import NestedCorePrivateUnlimitedCross133
import NestedCorePrivateWitnesses133
import NestedCorePrivateOrbit133

namespace Graffiti133NestedLongGates
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7
  Graffiti133PrivateCross Graffiti133ExpandedPrivate Graffiti133NestedCore
  Graffiti133NestedSingleGate Graffiti133MultiWeighted
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

private theorem canonical_site_eq (H : Hole G 7) (u v : V) (i : Fin 7) :
    canonCore H u v (sIndex i)=H.c i := by fin_cases i <;> rfl

private theorem canonical_control_labels (H : Hole G 7) (u v : V) :
    canonCore H u v (7 : Fin 9)=u ∧ canonCore H u v (8 : Fin 9)=v := ⟨rfl,rfl⟩

theorem radius_four_canonical_private_core_near_slack_mean_four
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
    (nearSlack : (∑ y : (K : Set V),localIndependence (G.induce (K : Set V)) y)+2≤4*K.card)
    (remote : ∀ w∉K,Remote H w) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  classical
  have Dsub : D⊆K := by
    intro x xm
    rcases shape x xm with ⟨i,rfl⟩|rfl|rfl
    · exact ck i
    · exact uk
    · exact vk
  have sees (x : V) (xo : x∉K) : G.Adj x u ∨ G.Adj x v := by
    obtain dx|⟨y,ym,xy⟩ := ddom x
    · exact (xo (Dsub dx)).elim
    · rcases shape y ym with ⟨i,rfl⟩|rfl|rfl
      · exact ((remote x xo).2 i xy).elim
      · exact Or.inl xy
      · exact Or.inr xy
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
  obtain ⟨t,tk,tu,tv,cover⟩ : ∃ t∈K,t≠u ∧ t≠v ∧ ∀ x∈L,x=t := by
    by_cases ne : L.Nonempty
    · obtain ⟨t,tm⟩ := ne
      obtain ⟨tk,_,tu,tv,_⟩ := Finset.mem_filter.mp tm
      exact ⟨t,tk,tu,tv,fun x xm=>Finset.card_le_one.mp lim x xm t tm⟩
    · exact ⟨H.c 0,ck 0,(uoff 0).symm,(voff 0).symm,fun x xm=>(ne ⟨x,xm⟩).elim⟩
  let A : Finset V := {u,v,t}
  have ua : u∈A := by simp [A]
  have va : v∈A := by simp [A]
  have a3 : A.card=3 := by simp [A,uv,tu.symm,tv.symm]
  have ak : A⊆K := by
    intro x xm
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at xm
    rcases xm with rfl|rfl|rfl
    · exact uk
    · exact vk
    · exact tk
  have gate (r : V) (ro : r∉K) : ∃ a∈A,G.Adj r a :=
    (sees r ro).elim (fun p=>⟨u,ua,p⟩) (fun p=>⟨v,va,p⟩)
  have coreIn : ∀ a : Fin 9,canonCore H u v a∈K := by
    intro a
    fin_cases a <;> simp_all [canonCore]
  have paid (r : V) (ro : r∉K) (z : V) (zk : z∈K) (za : z∉A) (rz : G.Adj r z) :
      ∃ a∈A,G.Adj r a ∧ G.Adj z a := by
    have zoff : Outside H.c z := by
      intro i eq
      exact (remote r ro).2 i (eq ▸ rz)
    have zu : z≠u := fun eq=>za (eq.symm ▸ ua)
    have zv : z≠v := fun eq=>za (eq.symm ▸ va)
    have short : VeryShortGate H z := by
      by_contra bad
      have zl : z∈L := Finset.mem_filter.mpr ⟨zk,zoff,zu,zv,bad⟩
      exact za (by simp [A,cover z zl])
    have ao : ∀ a,r≠canonCore H u v a := fun a eq=>ro (eq.symm ▸ coreIn a)
    have zo : ∀ a,z≠canonCore H u v a := by
      intro a
      fin_cases a <;> simp [canonCore] <;> first | exact zoff _ | exact zu | exact zv
    have rNo (i : Fin 7) : ¬G.Adj r (canonCore H u v (sIndex i)) := by
      rw [canonical_site_eq]
      exact (remote r ro).2 i
    have rHit : G.Adj r (canonCore H u v 7) ∨ G.Adj r (canonCore H u v 8) := sees r ro
    obtain ⟨_,i,flag|flag⟩ := short
    · have zS (k : Fin 7) : G.Adj z (canonCore H u v (sIndex k))↔
        k=i ∨ (false=true ∧ k=i+1) := by rw [canonical_site_eq,flag]; simp
      obtain ⟨c,hit⟩ := very_short_crossing_has_common_control h4 h9 m (canonCore H u v)
        (canonCore_injective H u v uoff voff uv) (canonCore_fits H u v m noedge up vp)
        privateAll i false r z ao zo rNo rHit zS rz
      fin_cases c
      · exact ⟨u,ua,hit⟩
      · exact ⟨v,va,hit⟩
    · have zS (k : Fin 7) : G.Adj z (canonCore H u v (sIndex k))↔
        k=i ∨ (true=true ∧ k=i+1) := by rw [canonical_site_eq,flag]; simp
      obtain ⟨c,hit⟩ := very_short_crossing_has_common_control h4 h9 m (canonCore H u v)
        (canonCore_injective H u v uoff voff uv) (canonCore_fits H u v m noedge up vp)
        privateAll i true r z ao zo rNo rHit zS rz
      fin_cases c
      · exact ⟨u,ua,hit⟩
      · exact ⟨v,va,hit⟩
  exact three_retained_gates_with_paid_crossings_mean_four K A ak a3 h4 gate paid nearSlack

#print axioms radius_four_canonical_private_core_near_slack_mean_four
end Graffiti133NestedLongGates

namespace Graffiti133NestedLongGates
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133CoreSeven
  Graffiti133MultiWeighted Graffiti133NestedSingleGate Graffiti133PrivateCross Graffiti133Camby
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem radius_four_minimum_two_control_core_near_slack_mean_four
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (h9 : ¬∃ f : Fin 9→V,InducedPath G f) (hr : 4≤radius G)
    (D K : Finset V) (dmin : MinimalSize G D) (cd : ∀ i,H.c i∈D) (ck : ∀ i,H.c i∈K)
    (d7 : ¬∃ f : Fin 7→(D : Set V),InducedPath (G.induce (D : Set V)) f)
    (u v : V) (uv : u≠v) (ud : u∈D) (vd : v∈D) (uk : u∈K) (vk : v∈K)
    (shape : ∀ w∈D,(∃ i,H.c i=w) ∨ w=u ∨ w=v)
    (uoff : Outside H.c u) (voff : Outside H.c v)
    (uh : (contactSet H u).Nonempty) (vh : (contactSet H v).Nonempty)
    (kdom : ∀ y : (K : Set V),Outside (restrictedHole H K ck).c y →
      ∃ i,(G.induce (K : Set V)).Adj y ((restrictedHole H K ck).c i))
    (nearSlack : (∑ y : (K : Set V),localIndependence (G.induce (K : Set V)) y)+2≤4*K.card)
    (remote : ∀ w∉K,Remote H w) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  classical
  have ddom := dmin.1.2
  let J := G.induce (D : Set V)
  let HJ := restrictedHole H D cd
  have dj (w : (D : Set V)) (wo : Outside HJ.c w) : ∃ i,J.Adj w (HJ.c i) := by
    rcases shape w.val w.property with ⟨i,e⟩|e|e
    · exact (wo i (Subtype.ext e.symm)).elim
    · obtain ⟨i,im⟩ := uh
      exact ⟨i,show G.Adj w.val (H.c i) from e.symm ▸ (mem_contactSet H u i).mp im⟩
    · obtain ⟨i,im⟩ := vh
      exact ⟨i,show G.Adj w.val (H.c i) from e.symm ▸ (mem_contactSet H v i).mp im⟩
  have noedge : ¬G.Adj u v :=
    (outside_independent_and_core_order HJ (restricted_c4 h4 D) d7 dj).1 ⟨u,ud⟩ ⟨v,vd⟩
      (fun i e=>uoff i (congrArg Subtype.val e))
      (fun i e=>voff i (congrArg Subtype.val e))
  obtain ⟨p,q,pu,qv,canon⟩ := radius_four_two_control_core_archetypes H hc h4 hr D cd ddom d7
    u v ud vd shape uoff voff uv uh vh
  obtain ⟨t,rev,swap,triple,up,vp⟩ := orient_to_canonical_archetype H pu qv canon
  let H' := orientHole H t rev
  let U := if swap then v else u
  let W := if swap then u else v
  have Uoff : Outside H'.c U := (orient_hole_outside H t rev U).mpr (by cases swap <;> simp [U,uoff,voff])
  have Woff : Outside H'.c W := (orient_hole_outside H t rev W).mpr (by cases swap <;> simp [W,uoff,voff])
  have UW : U≠W := by cases swap <;> simp [U,W,uv,uv.symm]
  have noUW : ¬G.Adj U W := by
    cases swap
    · exact noedge
    · exact fun e=>noedge e.symm
  have Ud : U∈D := by cases swap <;> simp [U,ud,vd]
  have Wd : W∈D := by cases swap <;> simp [W,ud,vd]
  have Uk : U∈K := by cases swap <;> simp [U,uk,vk]
  have Wk : W∈K := by cases swap <;> simp [W,uk,vk]
  have cd' (i : Fin 7) : H'.c i∈D := cd _
  have ck' (i : Fin 7) : H'.c i∈K := ck _
  have shape' (x : V) (xd : x∈D) : (∃ i,H'.c i=x) ∨ x=U ∨ x=W := by
    rcases shape x xd with hx|hu|hv
    · have w : x∈Set.range H.c := hx
      rw [←orient_hole_range H t rev] at w
      exact Or.inl w
    · cases swap
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr hu)
    · cases swap
      · exact Or.inr (Or.inr hv)
      · exact Or.inr (Or.inl hv)
  let HK := restrictedHole H K ck
  let HK' := restrictedHole H' K ck'
  have hHK : HK'=orientHole HK t rev := rfl
  have kdom' (w : (K : Set V)) (wo : Outside HK'.c w) :
      ∃ i,(G.induce (K : Set V)).Adj w (HK'.c i) := by
    rw [hHK] at wo
    obtain ⟨j,ed⟩ := kdom w ((orient_hole_outside HK t rev w).mp wo)
    obtain ⟨i,eq⟩ := (orbitEquiv t rev).surjective j
    exact ⟨i,by
      change G.Adj w.val (H.c (orbitSite t rev i))
      change orbitSite t rev i=j at eq
      rw [eq]
      exact ed⟩
  have remote' (w : V) (wo : w∉K) : Remote H' w :=
    ⟨(orient_hole_outside H t rev w).mpr (remote w wo).1,fun i=>(remote w wo).2 (orbitSite t rev i)⟩
  have us : ∃ i j : Fin 7,i≠j ∧ G.Adj U (H'.c i) ∧ G.Adj U (H'.c j) :=
    ⟨0,3,by decide,(up 0).mpr (Or.inl rfl),(up 3).mpr (Or.inr rfl)⟩
  have vs : ∃ i j : Fin 7,i≠j ∧ G.Adj W (H'.c i) ∧ G.Adj W (H'.c j) := by
    cases triple
    · exact ⟨1,4,by decide,(vp 1).mpr (Or.inl rfl),(vp 4).mpr (Or.inr rfl)⟩
    · exact ⟨1,2,by decide,(vp 1).mpr (Or.inl rfl),(vp 2).mpr (Or.inr (Or.inl rfl))⟩
  have privateAll := minimum_core_has_canonical_private_witnesses H' D dmin cd' U W Uoff Woff UW
    Ud Wd shape' us vs
  exact radius_four_canonical_private_core_near_slack_mean_four H' hc h4 h9 hr D K cd' ck'
    ddom d7 U W UW Ud Wd Uk Wk shape' Uoff Woff noUW triple up vp privateAll kdom' nearSlack remote'

#print axioms radius_four_minimum_two_control_core_near_slack_mean_four
end Graffiti133NestedLongGates
