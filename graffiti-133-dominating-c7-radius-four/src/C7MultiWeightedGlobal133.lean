import C7MultiScoreHelpers133

namespace Graffiti133MultiWeighted
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133BicycleCharge
  Graffiti133ExteriorSlack Graffiti133ExactTriangleCharge Graffiti133Bicycle Graffiti133SingletonSlack
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem sum_local_plus_custom_slack (H : Hole G 7)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (penalty credit : V→Nat)
    (per : ∀ (U : Finset V) (x : (U : Set V)), (∀ i,H.c i∈U) → x.val∈multiVertices H →
      2*(G.induce (U : Set V)).degree x+penalty x.val ≤
        4+3*triangleIncidence (G.induce (U : Set V)) x+credit x.val) :
    (∑ v : V,localIndependence G v)+14+(∑ x∈multiVertices H,penalty x)≤
      4*Fintype.card V+(∑ x∈multiVertices H,credit x) := by
  classical
  let D := multiVertices H
  let K : Finset V := Finset.univ \ D
  have yesC (i : Fin 7) : H.c i∈K := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro dm
    exact (Finset.mem_filter.mp dm).2.1 i rfl
  have offD (x : V) (xm : x∈D) : Outside H.c x := (Finset.mem_filter.mp xm).2.1
  have singleK (x : (K : Set V)) (off : Outside (restrictedHole H K yesC).c x) :
      ∃ i,∀ j,(G.induce (K : Set V)).Adj x ((restrictedHole H K yesC).c j) ↔ j=i := by
    have offG : Outside H.c x.val := fun i e=>off i (Subtype.ext e)
    obtain ⟨i,edge⟩ := dom x.val offG
    have no := (Finset.mem_sdiff.mp x.property).2
    have le : (contactSet H x.val).card≤1 := by
      by_contra! high
      exact no (Finset.mem_filter.mpr ⟨Finset.mem_univ _,offG,high⟩)
    have im : i∈contactSet H x.val := (mem_contactSet H _ _).mpr edge
    refine ⟨i,fun j=>?_⟩
    constructor
    · intro e
      by_contra ne
      have je : G.Adj x.val (H.c j) := e
      have two : 1<(contactSet H x.val).card :=
        Finset.one_lt_card.mpr ⟨j,(mem_contactSet H _ _).mpr je,i,im,ne⟩
      omega
    · rintro rfl
      exact edge
  have no9K : ¬∃ p : Fin 9→(K : Set V),InducedPath (G.induce (K : Set V)) p := by
    rintro ⟨p,h⟩
    exact h9 ⟨Subtype.val ∘ p,Subtype.val_injective.comp h.1,h.2⟩
  let E (U : Finset V) := (G.induce (U : Set V)).edgeFinset.card
  let C (U : Finset V) := triangleCount (G.induce (U : Set V))
  have base : 2*E K+14≤4*K.card+3*C K := by
    have slack := singleton_seven_has_slack14 (restrictedHole H K yesC) (restricted_c4 h4 K) no9K singleK
    have charge := sum_degree_eq_local_add_triangles (restricted_c4 h4 K)
    have kc : Fintype.card (K : Set V)=K.card := Fintype.card_coe K
    change (∑ v : (K : Set V),localIndependence (G.induce (K : Set V)) v)+3*C K=2*E K at charge
    exact score_base slack charge kc
  have apart : Disjoint K D := by
    apply Finset.disjoint_left.mpr
    exact fun x xK xD=>(Finset.mem_sdiff.mp xK).2 xD
  have step (x : V) (xd : x∈D) (T : Finset V) (_ : T⊆D) (nt : x∉T) :
      2*E (K∪insert x T)+penalty x+3*C (K∪T) ≤
      2*E (K∪T)+4+3*C (K∪insert x T)+credit x := by
    let U := K∪insert x T
    let W := K∪T
    let nK : x∉K := fun xK=>(Finset.mem_sdiff.mp xK).2 xd
    have xU : x∈U := Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _))
    let y : (U : Set V) := ⟨x,xU⟩
    have neq : x∉W := by simp [W,nK,nt]
    have eq : U=insert x W := by ext z; simp [U,W,or_comm,or_left_comm]
    have erase : U.erase x=W := by rw [eq,Finset.erase_insert neq]
    have cyc (i : Fin 7) : H.c i∈U := Finset.mem_union.mpr (Or.inl (yesC i))
    have loc := per U y cyc xd
    have d := actual_induced_delta (G:=G) U y
    let degree := (G.induce (U : Set V)).degree y
    let inc := triangleIncidence (G.induce (U : Set V)) y
    have de : E (U.erase x)+degree=E U := d.1
    have dt : C (U.erase x)+inc=C U := d.2
    rw [erase] at de dt
    change 2*degree+penalty x≤4+3*inc+credit x at loc
    change 2*E U+penalty x+3*C W≤2*E W+4+3*C U+credit x
    have aux {a b t0 t1 dd tt p c : Nat} (ea : a+dd=b) (et : t0+tt=t1)
        (bound : 2*dd+p≤4+3*tt+c) : 2*b+p+3*t0≤2*a+4+3*t1+c := by omega
    exact aux de dt loc
  have total := score_add_sets K D E C penalty credit base step apart D Subset.rfl
  have eqAll : K∪D=(Finset.univ : Finset V) := by
    ext x
    simp [K]
  rw [eqAll,Finset.card_univ] at total
  dsimp only [E,C] at total
  rw [(full_induce_iso (G:=G)).card_edgeFinset_eq,
    triangle_count_iso (full_induce_iso (G:=G))] at total
  have main := sum_degree_eq_local_add_triangles h4
  exact score_finish main total


#print axioms sum_local_plus_custom_slack
end Graffiti133MultiWeighted
