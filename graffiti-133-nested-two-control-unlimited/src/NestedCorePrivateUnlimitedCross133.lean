import NestedCorePrivateFullTriangle133
import NestedCorePrivatePaidTrim133
import NestedCoreLongGateRadius133

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

theorem radius_four_canonical_private_core_unlimited_crossings_mean_four
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
    (baseMultis : (multiVertices (restrictedHole H K ck)).card≤4)
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
  have base := C7_dominating_slack_depending_on_multis (restrictedHole H K ck)
    (restricted_c4 h4 K) (retained_no_path h9 K) kdom
  have card : Fintype.card (K : Set V)=K.card := Fintype.card_coe K
  rw [card] at base
  apply three_retained_gates_with_paid_crossings_mean_four K A ak a3 h4 gate paid
  have aux {l n m : Nat} (bd : l+14≤4*n+3*m) (m4 : m≤4) : l+2≤4*n := by omega
  exact aux base baseMultis

#print axioms radius_four_canonical_private_core_unlimited_crossings_mean_four
end Graffiti133NestedLongGates
