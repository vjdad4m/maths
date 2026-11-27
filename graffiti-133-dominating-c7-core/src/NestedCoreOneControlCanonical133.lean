import NestedCoreOneControlRows133
import NestedCoreOneControlFarCap133
import NestedCoreOneControlAdjacentCap133
import NestedCoreOneControlTrimLift133
import NestedCoreOneControlGlobalSlack133
import NestedCorePrivatePaidTrim133

namespace Graffiti133NestedOneControl
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133CoreSeven
  Graffiti133MultiWeighted Graffiti133NestedSingleGate Graffiti133NestedLongGates Graffiti133NestedCore
  Graffiti133NestedWeightedCore
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem canonical_minimum_one_control_mean_four
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9→V,InducedPath G p) (hr : 4≤radius G)
    (D : Finset V) (ddom : ∀ x : V,x∈D ∨ ∃ y∈D,G.Adj x y)
    (u : V) (uo : Outside H.c u) (shape : ∀ x∈D,(∃ i,H.c i=x) ∨ x=u)
    (up : ∀ j : Fin 7,G.Adj u (H.c j)↔j=0 ∨ j=3)
    (has : ∀ j : Fin 8,∃ w,PrivateFor G (core H u) j w) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  classical
  let K := Finset.univ.filter (fun w=>¬Remote H w)
  have ck (i : Fin 7) : H.c i∈K := Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun h=>h.1 i rfl⟩
  have uk : u∈K := Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun h=>h.2 0 ((up 0).mpr (Or.inl rfl))⟩
  let B := restrictedHole H K ck
  let U : (K : Set V) := ⟨u,uk⟩
  have kdom (y : (K : Set V)) (yo : Outside B.c y) :
      ∃ i,(G.induce (K : Set V)).Adj y (B.c i) := by
    by_contra! none
    have yr : Remote H y.val := ⟨fun i e=>yo i (Subtype.ext e),none⟩
    exact (Finset.mem_filter.mp y.property).2 yr
  have remote (w : V) (wo : w∉K) : Remote H w := by
    by_contra h
    exact wo (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have touch (w : V) (wk : w∈K) (wo : Outside H.c w) : (contactSet H w).Nonempty := by
    obtain ⟨i,hi⟩ := kdom (⟨w,wk⟩ : (K : Set V)) (fun i eq=>wo i (congrArg Subtype.val eq))
    exact ⟨i,(mem_contactSet H w i).mpr hi⟩
  have see (r : V) (ro : r∉K) : G.Adj r u := by
    obtain rd|⟨y,ym,ry⟩ := ddom r
    · rcases shape r rd with ⟨i,rfl⟩|rfl
      · exact (ro (ck i)).elim
      · exact (ro uk).elim
    · rcases shape y ym with ⟨i,rfl⟩|rfl
      · exact ((remote r ro).2 i ry).elim
      · exact ry
  let L := K.filter (fun w=>Outside H.c w ∧ w≠u ∧ ¬VeryShortGate H w)
  have two : L.card≤2 := by
    by_contra! high
    obtain ⟨a,am,b,bm,c,cm,ab,ac,bc⟩ := Finset.two_lt_card.mp high
    obtain ⟨ak,ao,au,al⟩ := Finset.mem_filter.mp am
    obtain ⟨bk,bo,bu,bl⟩ := Finset.mem_filter.mp bm
    obtain ⟨ck',co,cu,cl⟩ := Finset.mem_filter.mp cm
    have site_eq : ∀ i : Fin 7,(i=0 ∨ i=3)↔i∈profileContacts 0 := by decide
    have pu : Matches H u 0 := fun i=>(up i).trans (site_eq i)
    have rb := radius_three_of_three_additional_long_gates H hc h4 D ddom u a b c shape pu
      au.symm bu.symm cu.symm ab ac bc ao bo co
      (touch _ ak ao) (touch _ bk bo) (touch _ ck' co) al bl cl
    omega
  let Q := insert u L
  have qK : Q⊆K := by
    intro x xm
    rcases Finset.mem_insert.mp xm with rfl|xm
    · exact uk
    · exact (Finset.mem_filter.mp xm).1
  have q3 : Q.card≤3 := by
    change (insert u L).card≤3
    have hh := Finset.card_insert_le u L
    omega
  have k3 : 3≤K.card := by
    apply Nat.succ_le_iff.mpr
    exact Finset.two_lt_card.mpr ⟨H.c 0,ck 0,H.c 1,ck 1,H.c 2,ck 2,
      fun e=>(by decide : (0:Fin 7)≠1) (H.inj e),
      fun e=>(by decide : (0:Fin 7)≠2) (H.inj e),
      fun e=>(by decide : (1:Fin 7)≠2) (H.inj e)⟩
  obtain ⟨A,qa,aK,acard⟩ := Finset.exists_subsuperset_card_eq qK q3 k3
  have ua : u∈A := qa (Finset.mem_insert_self _ _)
  have short z (za : z∈K) (no : z∉A) (off : Outside H.c z) : VeryShortGate H z := by
    apply Classical.byContradiction
    intro f
    have zu : z≠u := fun e=>no (e.symm ▸ ua)
    have zl : z∈L := Finset.mem_filter.mpr ⟨za,off,zu,f⟩
    exact no (qa (Finset.mem_insert_of_mem zl))
  have gates (r : V) (ro : r∉K) : ∃ a∈A,G.Adj r a := ⟨u,ua,see r ro⟩
  have paid (r : V) (ro : r∉K) (z : V) (zk : z∈K) (za : z∉A) (rz : G.Adj r z) :
      ∃ a∈A,G.Adj r a ∧ G.Adj z a := by
    refine ⟨u,ua,see r ro,?_⟩
    apply Classical.byContradiction
    intro zu
    have zoff : Outside H.c z := fun i e=>(remote r ro).2 i (e ▸ rz)
    have zv : z≠u := fun e=>za (e.symm ▸ ua)
    have znew : ∀ a : Fin 8,z≠core H u a := by
      intro a
      fin_cases a <;> simp [core] <;> first | exact zoff _ | exact zv
    have rp : PrivateFor G (core H u) 7 r := by
      constructor
      · intro a e
        apply ro
        rw [e]
        fin_cases a <;> simp [core,ck,uk]
      · intro a
        fin_cases a <;> simp [core,(remote r ro).2,see r ro]
    obtain ⟨_,i,caseS|caseA⟩ := short z zk za zoff
    · have zspec (a : Fin 8) : G.Adj z (core H u a)↔
          a.val=i.val ∨ (false=true ∧ a.val=(i+1).val) := by
        by_cases q : a.val<7
        · let j : Fin 7 := ⟨a.val,q⟩
          have e : a=csite j := rfl
          rw [e,core_at_site,caseS j]
          simp only [Bool.false_eq_true,false_and,or_false,Fin.ext_iff]
          rfl
        · have e : a=7 := Fin.ext (by have := a.isLt; omega)
          subst a
          have ne : (7:Nat)≠i.val := Ne.symm (Nat.ne_of_lt i.isLt)
          simpa [core,zu,show (7:Fin 8).val=7 from rfl] using ne
      exact no_unpaid_short_crossing h4 h9 trim_rows _ (core_injective H u uo) (core_fits H u up)
        has i false r z rp znew zspec rz
    · have zspec (a : Fin 8) : G.Adj z (core H u a)↔
          a.val=i.val ∨ (true=true ∧ a.val=(i+1).val) := by
        by_cases q : a.val<7
        · let j : Fin 7 := ⟨a.val,q⟩
          have e : a=csite j := rfl
          rw [e,core_at_site,caseA j]
          simp only [true_and,Fin.ext_iff]
          rfl
        · have e : a=7 := Fin.ext (by have := a.isLt; omega)
          subst a
          have ne : (7:Nat)≠i.val := Ne.symm (Nat.ne_of_lt i.isLt)
          have nf : (7:Nat)≠(i+1).val := Ne.symm (Nat.ne_of_lt (i+1).isLt)
          simpa [core,zu,show (7:Fin 8).val=7 from rfl] using And.intro ne nf
      exact no_unpaid_short_crossing h4 h9 trim_rows _ (core_injective H u uo) (core_fits H u up)
        has i true r z rp znew zspec rz
  have remMap (y : (K : Set V)) (ym : y∈scoredFar B U U) : y.val∈L := by
    have h : y∈multiVertices B ∧ (contactSet B y).card=2 ∧
        (¬∃ i∈contactSet B y,∃ j∈contactSet B y,Cyclic i j) ∧ y≠U ∧ y≠U := by
      simpa only [scoredFar,Finset.mem_filter] using ym
    obtain ⟨mm,two',nadj,yu,_⟩ := h
    have yout : Outside H.c y.val :=
      fun i e=>(Finset.mem_filter.mp mm).2.1 i (Subtype.ext e)
    have eq : contactSet B y=contactSet H y.val := restricted_contacts H K ck y
    rw [eq] at two' nadj
    have ns : ¬VeryShortGate H y.val := by
      rintro ⟨_,i,flag|flag⟩
      · have eq1 : contactSet H y.val={i} := by
          ext j
          exact (mem_contactSet H _ _).trans ((flag j).trans (by simp))
        rw [eq1] at two'
        simp at two'
      · apply nadj
        have c : Cyclic i (i+1) := by
          have r : ∀ i : Fin 7,Cyclic i (i+1) := by decide
          exact r i
        exact ⟨i,(mem_contactSet H _ _).mpr ((flag i).mpr (Or.inl rfl)),i+1,
          (mem_contactSet H _ _).mpr ((flag (i+1)).mpr (Or.inr rfl)),c⟩
    exact Finset.mem_filter.mpr ⟨y.property,yout,fun e=>yu (Subtype.ext e),ns⟩
  have rem : (scoredFar B U U).card≤2 :=
    (Finset.card_le_card_of_injOn Subtype.val remMap (by intro a _ b _ e; exact Subtype.ext e)).trans two
  have sc (y : (K : Set V)) (ym : y∈adjTwo B) : (exteriorNeighbors B y).card≤2 := by
    obtain ⟨ym,two',adj⟩ := Finset.mem_filter.mp ym
    exact adj_sat_geometry_cap H hc h4 h9 hr K ck kdom D ddom u uo up shape has
      (fun i ok mask=>sat_rows i mask ok) y (Finset.mem_filter.mp ym).2.1 two' adj
  have fc (y : (K : Set V)) (hy : y=U ∨ y=U) (_ : (contactSet B y).card=2)
      (_ : ¬∃ i∈contactSet B y,∃ j∈contactSet B y,Cyclic i j) :
      ((exteriorNeighbors B y) \ markedNeighbors B y).card=0 := by
    have e : y=U := hy.elim id id
    rw [e]
    exact one_control_clean_zero H hc h4 hr D ddom u uo shape up K ck uk kdom
  have no9 : ¬∃ p : Fin 9→(K : Set V),InducedPath (G.induce (K : Set V)) p := by
    rintro ⟨p,hp⟩
    exact h9 ⟨Subtype.val ∘ p,Subtype.val_injective.comp hp.1,hp.2⟩
  have base := refined_near_base_slack_two B (restricted_c4 h4 K) no9 kdom U U rem sc fc
  have card : Fintype.card (K : Set V)=K.card := Fintype.card_coe K
  rw [card] at base
  have slack := (by omega : ∀ {l n : Nat},l+3≤4*n → l+2≤4*n) base
  exact three_retained_gates_with_paid_crossings_mean_four K A aK acard h4 gates paid slack

#print axioms canonical_minimum_one_control_mean_four
end Graffiti133NestedOneControl
