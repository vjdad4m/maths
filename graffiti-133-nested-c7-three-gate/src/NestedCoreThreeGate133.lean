import NestedCoreGateScore133

namespace Graffiti133NestedCore
open SimpleGraph Finset Graffiti133 Graffiti133ExteriorSlack Graffiti133ExactTriangleCharge
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

noncomputable def gateTags (G : SimpleGraph V) (A : Finset V) (x : V) : Finset V :=
  A.filter (G.Adj x)

theorem gate_tag_rows_disjoint (h4 : FourCycleFree G) (A : Finset V) {x y z : V}
    (ox : x∉A) (yz : y≠z) (xy : G.Adj x y) (xz : G.Adj x z) :
    Disjoint (gateTags G A y) (gateTags G A z) := by
  apply Finset.disjoint_left.mpr
  intro a ay az
  obtain ⟨am,ya⟩ := Finset.mem_filter.mp ay
  have za := (Finset.mem_filter.mp az).2
  exact yz (h4 x a y z (fun e=>ox (e ▸ am)) xy ya.symm xz za.symm)

theorem disjoint_gate_slots_bound (h4 : FourCycleFree G) (A R : Finset V) (x : V)
    (ox : x∉A) (adj : ∀ y∈R,G.Adj x y)
    (dis : ∀ y∈R,Disjoint (gateTags G A x) (gateTags G A y)) :
    (gateTags G A x).card+(∑ y∈R,(gateTags G A y).card)≤A.card := by
  classical
  let T := R.biUnion (gateTags G A)
  have dj : (↑R : Set V).PairwiseDisjoint (gateTags G A) := by
    intro y ym z zm ynz
    exact gate_tag_rows_disjoint h4 A ox ynz (adj y ym) (adj z zm)
  have s : T.card=∑ y∈R,(gateTags G A y).card := Finset.card_biUnion dj
  have ap : Disjoint (gateTags G A x) T := by
    apply Finset.disjoint_left.mpr
    intro a ax at'
    obtain ⟨y,ym,ay⟩ := Finset.mem_biUnion.mp at'
    exact Finset.disjoint_left.mp (dis y ym) ax ay
  have sub : gateTags G A x ∪ T ⊆ A := by
    intro a am
    rcases Finset.mem_union.mp am with ax|at'
    · exact (Finset.mem_filter.mp ax).1
    · obtain ⟨y,_,ay⟩ := Finset.mem_biUnion.mp at'
      exact (Finset.mem_filter.mp ay).1
  rw [←s,←Finset.card_union_of_disjoint ap]
  exact Finset.card_le_card sub

theorem at_most_one_triple_gate_vertex (h4 : FourCycleFree G) (A R : Finset V)
    (asz : A.card=3) :
    (R.filter fun x=>(gateTags G A x).card=3).card≤1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x xm y ym
  have xt := (Finset.mem_filter.mp xm).2
  have yt := (Finset.mem_filter.mp ym).2
  have xa : gateTags G A x=A :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have ya : gateTags G A y=A :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have h : 1<A.card := by omega
  obtain ⟨a,am,b,bm,ab⟩ := Finset.one_lt_card.mp h
  have ax := (Finset.mem_filter.mp (xa.symm ▸ am)).2
  have bx := (Finset.mem_filter.mp (xa.symm ▸ bm)).2
  have ay := (Finset.mem_filter.mp (ya.symm ▸ am)).2
  have byy := (Finset.mem_filter.mp (ya.symm ▸ bm)).2
  exact h4 a b x y ab ax.symm bx.symm ay.symm byy.symm

def cleanEdge (G : SimpleGraph V) (A : Finset V) (x y : V) : Prop :=
  G.Adj x y ∧ Disjoint (gateTags G A x) (gateTags G A y)

noncomputable def cleanArcs (G : SimpleGraph V) (A R : Finset V) : Finset (V×V) :=
  (R ×ˢ R).filter (fun e=>cleanEdge G A e.1 e.2)

theorem clean_arc_card_le_two_singletons (h4 : FourCycleFree G) (A R : Finset V)
    (asz : A.card=3) (apart : Disjoint A R)
    (hasTag : ∀ x∈R,0<(gateTags G A x).card) :
    (cleanArcs G A R).card≤2*(R.filter fun x=>(gateTags G A x).card=1).card := by
  classical
  let W := R ×ˢ R
  let t (x : V) := (gateTags G A x).card
  let p (e : V×V) := if cleanEdge G A e.1 e.2 then if t e.1=1 then t e.2 else 0 else 0
  let I (e : V×V) := if cleanEdge G A e.1 e.2 then (1:Nat) else 0
  have sym (x y : V) : cleanEdge G A x y ↔ cleanEdge G A y x :=
    ⟨fun h=>⟨h.1.symm,h.2.symm⟩,fun h=>⟨h.1.symm,h.2.symm⟩⟩
  have swap : (∑ e∈W,p e.swap)=(∑ e∈W,p e) := by
    simp only [W,Finset.sum_product]
    exact Finset.sum_comm
  have step (e : V×V) (em : e∈W) : 2*I e≤p e+p e.swap := by
    rcases e with ⟨x,y⟩
    obtain ⟨xm,ym⟩ := Finset.mem_product.mp em
    by_cases c : cleanEdge G A x y
    · have cy : cleanEdge G A y x := (sym _ _).mp c
      have sub : gateTags G A x ∪ gateTags G A y ⊆ A :=
        Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      have ctot : t x+t y≤3 := by
        rw [←Finset.card_union_of_disjoint c.2,←asz]
        exact Finset.card_le_card sub
      have px := hasTag x xm
      have py := hasTag y ym
      have hx : 0<t x := px
      have hy : 0<t y := py
      simp only [I,p,Prod.swap_prod_mk,c,cy,if_true]
      by_cases ax : t x=1 <;> by_cases ay : t y=1 <;> simp [ax,ay] <;> omega
    · have cy : ¬cleanEdge G A y x := fun h=>c ((sym _ _).mpr h)
      simp [I,p,c,cy]
  have count : (cleanArcs G A R).card=∑ e∈W,I e := Finset.card_filter _ _
  have lhs : (∑ e∈W,2*I e) = 2*(cleanArcs G A R).card := by
    rw [←Finset.mul_sum, count]
  have rhs : (∑ e∈W,(p e+p e.swap))=2*(∑ e∈W,p e) := by
    rw [Finset.sum_add_distrib,swap,two_mul]
  have d : (cleanArcs G A R).card≤∑ e∈W,p e := by
    have a := Finset.sum_le_sum step
    rw [lhs,rhs] at a
    omega
  let S := R.filter (fun x=>t x=1)
  have row (x : V) (xm : x∈R) :
      (∑ y∈R,p (x,y))≤(if t x=1 then 2 else 0) := by
    by_cases one : t x=1
    · let Y := R.filter (cleanEdge G A x)
      have slots := disjoint_gate_slots_bound h4 A Y x
        (fun xA=>Finset.disjoint_left.mp apart xA xm)
        (fun y ym=>(Finset.mem_filter.mp ym).2.1)
        (fun y ym=>(Finset.mem_filter.mp ym).2.2)
      have c : t x+(∑ y∈Y,t y)≤3 := by simpa only [asz] using slots
      rw [if_pos one]
      have align : (∑ y∈R,p (x,y))=∑ y∈Y,t y := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro y _
        simp [p,one]
      rw [align]
      omega
    · simp [p,one]
  have score : (∑ e∈W,p e)≤2*S.card := by
    change (∑ e∈R ×ˢ R,p e)≤2*S.card
    rw [Finset.sum_product]
    calc
      _ ≤ ∑ x∈R,if t x=1 then (2:Nat) else 0 := Finset.sum_le_sum row
      _ = _ := by
        rw [←Finset.sum_filter]
        change (∑ x∈S,(2:Nat))=_
        simp [Nat.mul_comm]
  exact d.trans score

#print axioms clean_arc_card_le_two_singletons
#print axioms gate_tag_rows_disjoint
#print axioms disjoint_gate_slots_bound
#print axioms at_most_one_triple_gate_vertex
end Graffiti133NestedCore
namespace Graffiti133NestedCore
open SimpleGraph Finset Graffiti133 Graffiti133ExteriorSlack Graffiti133ExactTriangleCharge Graffiti133MultiWeighted
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

noncomputable def arcSet (p : V→V→Prop) (X Y : Finset V) : Finset (V×V) :=
  (X ×ˢ Y).filter (fun e=>p e.1 e.2)

theorem mem_arcSet {p : V→V→Prop} {X Y : Finset V} {e : V×V} :
    e∈arcSet p X Y ↔ e.1∈X ∧ e.2∈Y ∧ p e.1 e.2 := by
  simp only [arcSet,Finset.mem_filter,Finset.mem_product,and_assoc]

theorem card_arcSet_eq_rows (p : V→V→Prop) (X Y : Finset V) :
    (arcSet p X Y).card=∑ x∈X,(Y.filter (p x)).card := by
  classical
  unfold arcSet
  rw [Finset.card_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x _
  exact (Finset.card_filter _ _).symm

theorem sym_arc_card (p : V→V→Prop) (pr : Symmetric p) (X Y : Finset V) :
    (arcSet p X Y).card=(arcSet p Y X).card := by
  rw [card_arcSet_eq_rows,card_arcSet_eq_rows]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _=>Finset.sum_congr rfl fun y _=>by rw [show p y x ↔ p x y from ⟨fun h=>pr h,fun h=>pr h⟩]

theorem card_arcs_union_left (p : V→V→Prop) (X Y Z : Finset V) (d : Disjoint X Y) :
    (arcSet p (X∪Y) Z).card=(arcSet p X Z).card+(arcSet p Y Z).card := by
  rw [card_arcSet_eq_rows,card_arcSet_eq_rows,card_arcSet_eq_rows,Finset.sum_union d]

theorem card_arcs_core (K : Finset V) :
    (arcSet G.Adj K K).card=2*(G.induce (K : Set V)).edgeFinset.card := by
  classical
  rw [SimpleGraph.two_mul_card_edgeFinset]
  symm
  apply Finset.card_bij (fun e _=>(e.1.val,e.2.val))
  · intro x xm
    exact mem_arcSet.mpr ⟨x.1.property,x.2.property,(Finset.mem_filter.mp xm).2⟩
  · intro a _ b _ e
    exact Prod.ext (Subtype.ext (congrArg Prod.fst e)) (Subtype.ext (congrArg Prod.snd e))
  · intro e em
    obtain ⟨a,b,adj⟩ := mem_arcSet.mp em
    exact ⟨(⟨e.1,a⟩,⟨e.2,b⟩),Finset.mem_filter.mpr ⟨Finset.mem_univ _,adj⟩,rfl⟩

theorem degree_score_arcs_decomposition (K R : Finset V) (dis : Disjoint K R)
    (union : K∪R=Finset.univ) :
    2*G.edgeFinset.card=2*(G.induce (K : Set V)).edgeFinset.card+
      2*(arcSet G.Adj R K).card+(arcSet G.Adj R R).card := by
  classical
  have all : 2*G.edgeFinset.card = (arcSet G.Adj Finset.univ Finset.univ).card := by
    rw [SimpleGraph.two_mul_card_edgeFinset]
    simp [arcSet,Finset.univ_product_univ]
  rw [all,←union,card_arcs_union_left _ _ _ _ dis,sym_arc_card _ G.symm K (K∪R),
    sym_arc_card _ G.symm R (K∪R),card_arcs_union_left _ _ _ _ dis,card_arcs_union_left _ _ _ _ dis,
    sym_arc_card _ G.symm K R,card_arcs_core (G:=G) K]
  omega

noncomputable def noncoreTriangles (G : SimpleGraph V) (K : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun S=>¬S⊆K)

theorem triangle_core_partition (K : Finset V) :
    triangleCount (G.induce (K : Set V))+(noncoreTriangles G K).card=triangleCount G := by
  classical
  let C := (G.cliqueFinset 3).filter (fun S=>S⊆K)
  have hc : triangleCount (G.induce (K : Set V))=C.card := by
    unfold triangleCount
    let e : (K : Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    apply Finset.card_bij (fun T _=>T.map e)
    · intro T tm
      obtain ⟨cl,n⟩ := (SimpleGraph.isNClique_iff _).mp (SimpleGraph.mem_cliqueFinset_iff.mp tm)
      apply Finset.mem_filter.mpr
      refine ⟨SimpleGraph.mem_cliqueFinset_iff.mpr ((SimpleGraph.isNClique_iff _).mpr ⟨?_,by rw [Finset.card_map]; exact n⟩),?_⟩
      · intro x xm y ym hxy
        obtain ⟨a,am,rfl⟩ := Finset.mem_map.mp xm
        obtain ⟨b,bm,rfl⟩ := Finset.mem_map.mp ym
        exact cl am bm (fun eq=>hxy (congrArg e eq))
      · intro x xm
        obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp xm
        exact a.property
    · intro T _ S _ eq
      exact Finset.map_injective _ eq
    · intro S sm
      obtain ⟨cl,sub⟩ := Finset.mem_filter.mp sm
      obtain ⟨adj,n⟩ := (SimpleGraph.isNClique_iff _).mp (SimpleGraph.mem_cliqueFinset_iff.mp cl)
      let T : Finset (K : Set V) := Finset.univ.filter (fun x : (K : Set V)=>x.val∈S)
      have map : T.map e=S := by
        ext x
        constructor
        · intro xm
          obtain ⟨a,am,rfl⟩ := Finset.mem_map.mp xm
          exact (Finset.mem_filter.mp am).2
        · intro xm
          exact Finset.mem_map.mpr ⟨⟨x,sub xm⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,xm⟩,rfl⟩
      refine ⟨T,SimpleGraph.mem_cliqueFinset_iff.mpr ((SimpleGraph.isNClique_iff _).mpr ⟨?_,?_⟩),map⟩
      · intro a am b bm neq
        exact adj ((Finset.mem_filter.mp am).2) ((Finset.mem_filter.mp bm).2)
          (fun e=>neq (Subtype.ext e))
      · rw [←Finset.card_map e, map]
        exact n
  rw [hc]
  exact Finset.filter_card_add_filter_neg_card_eq_card (s:=G.cliqueFinset 3) (fun S=>S⊆K)

#print axioms card_arcs_core
#print axioms degree_score_arcs_decomposition
#print axioms triangle_core_partition
theorem shared_arc_card_le_twice_triangles (A K R : Finset V) (AK : A⊆K)
    (apart : Disjoint K R) :
    (arcSet (fun x y=>G.Adj x y ∧ ¬Disjoint (gateTags G A x) (gateTags G A y)) R R).card≤
      2*(noncoreTriangles G K).card := by
  classical
  let S := arcSet (fun x y=>G.Adj x y ∧ ¬Disjoint (gateTags G A x) (gateTags G A y)) R R
  let U := noncoreTriangles G K ×ˢ (Finset.univ : Finset Bool)
  let M (e : V×V) := gateTags G A e.1 ∩ gateTags G A e.2
  let pick (e : V×V) := if q : (M e).Nonempty then (M e).min' q else e.1
  let key (e : V×V) : Finset V×Bool := ({e.1,e.2,pick e},decide (e.1<e.2))
  have pick_mem (e : V×V) (em : e∈S) : pick e∈M e := by
    have ov := (mem_arcSet.mp em).2.2.2
    have ne : (M e).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp ov
    simp only [pick,dif_pos ne,Finset.min'_mem]
  have inner (e : V×V) (em : e∈S) : pick e∈K :=
    AK ((Finset.mem_filter.mp (Finset.mem_inter.mp (pick_mem e em)).1).1)
  have outside (e : V×V) (em : e∈S) : e.1∉K ∧ e.2∉K := by
    obtain ⟨a,b,_⟩ := mem_arcSet.mp em
    exact ⟨fun h=>Finset.disjoint_left.mp apart h a,fun h=>Finset.disjoint_left.mp apart h b⟩
  have endpoints (e : V×V) (em : e∈S) :
      (key e).1 \ K=({e.1,e.2} : Finset V) := by
    have k := inner e em
    have o := outside e em
    ext x
    simp only [key,Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨a|b|c,no⟩
      · exact Or.inl a
      · exact Or.inr b
      · exact (no (c.symm ▸ k)).elim
    · rintro (rfl|rfl)
      · exact ⟨Or.inl rfl,o.1⟩
      · exact ⟨Or.inr (Or.inl rfl),o.2⟩
  have bij : Set.InjOn key S := by
    intro a am b bm eq
    have ea := (mem_arcSet.mp am).2.2.1
    have eb := (mem_arcSet.mp bm).2.2.1
    have pars : ({a.1,a.2} : Finset V)=({b.1,b.2} : Finset V) := by
      rw [←endpoints a am,←endpoints b bm,eq]
    have order : (a.1<a.2) ↔ (b.1<b.2) := by
      have eqb := congrArg Prod.snd eq
      change decide (a.1<a.2)=decide (b.1<b.2) at eqb
      exact ⟨fun h=>of_decide_eq_true (eqb.symm.trans (decide_eq_true h)),
        fun h=>of_decide_eq_true (eqb.trans (decide_eq_true h))⟩
    have p1 : a.1=b.1 ∨ a.1=b.2 := by
      have h : a.1∈({a.1,a.2}:Finset V) := by simp
      rw [pars] at h
      simpa using h
    have p2 : a.2=b.1 ∨ a.2=b.2 := by
      have h : a.2∈({a.1,a.2}:Finset V) := by simp
      rw [pars] at h
      simpa using h
    rcases p1 with h1|h1 <;> rcases p2 with h2|h2
    · exact (ea.ne (h1.trans h2.symm)).elim
    · exact Prod.ext h1 h2
    · exfalso
      rw [h1,h2] at order
      rcases lt_or_gt_of_ne eb.ne with less|great
      · exact (not_lt_of_gt less) (order.mpr less)
      · exact (not_lt_of_gt great) (order.mp great)
    · exact (ea.ne (h1.trans h2.symm)).elim
  have cnt : S.card≤U.card := by
    apply Finset.card_le_card_of_injOn key _ bij
    intro e em
    have edge := (mem_arcSet.mp em).2.2.1
    obtain ⟨a,b⟩ := Finset.mem_inter.mp (pick_mem e em)
    have tri := SimpleGraph.is3Clique_triple_iff.mpr ⟨edge,
      (Finset.mem_filter.mp a).2,(Finset.mem_filter.mp b).2⟩
    have bad : ¬({e.1,e.2,pick e} : Finset V)⊆K :=
      fun sub=>(outside e em).1 (sub (by simp))
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨SimpleGraph.mem_cliqueFinset_iff.mpr tri,bad⟩,Finset.mem_univ _⟩
  have eq : U.card=2*(noncoreTriangles G K).card := by
    simp [U,Finset.card_product,Nat.mul_comm]
  exact cnt.trans_eq eq

#print axioms shared_arc_card_le_twice_triangles
theorem three_gate_preserves_score_up_to_triples (K A : Finset V) (ak : A⊆K)
    (a3 : A.card=3) (h4 : FourCycleFree G)
    (sees : ∀ x∉K,∃ a∈A,G.Adj x a)
    (gate : ∀ x∉K,∀ y∈K,G.Adj x y → y∈A) :
    (∑ w : V,localIndependence G w)+4*K.card ≤
      (∑ w : (K : Set V),localIndependence (G.induce (K : Set V)) w)+
        4*Fintype.card V+2*((Finset.univ \ K).filter fun x=>(gateTags G A x).card=3).card := by
  classical
  let R := (Finset.univ : Finset V) \ K
  let t (x : V) := (gateTags G A x).card
  let S := R.filter (fun x=>t x=1)
  let T := R.filter (fun x=>t x=3)
  have out (x : V) (xm : x∈R) : x∉K := (Finset.mem_sdiff.mp xm).2
  have dis : Disjoint K R :=
    Finset.disjoint_left.mpr (fun _ km rm=>out _ rm km)
  have apart : Disjoint A R :=
    Finset.disjoint_left.mpr (fun _ am rm=>out _ rm (ak am))
  have union : K∪R=Finset.univ := by ext x; simp [R,or_comm]
  have sizes : K.card+R.card=Fintype.card V := by
    rw [←Finset.card_union_of_disjoint dis,union,Finset.card_univ]
  have has (x : V) (xm : x∈R) : 0<t x := by
    obtain ⟨a,am,e⟩ := sees x (out x xm)
    exact Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨am,e⟩⟩
  have bound (x : V) : t x≤3 := by
    rw [←a3]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have cross : (arcSet G.Adj R K).card=∑ x∈R,t x := by
    rw [card_arcSet_eq_rows]
    apply Finset.sum_congr rfl
    intro x xm
    congr 1
    ext y
    simp only [gateTags,Finset.mem_filter]
    exact ⟨fun h=>⟨gate x (out x xm) y h.1 h.2,h.2⟩,fun h=>⟨ak h.1,h.2⟩⟩
  have cross_budget : 2*(arcSet G.Adj R K).card+2*S.card=4*R.card+2*T.card := by
    have row (x : V) (xm : x∈R) :
        2*t x+2*(if t x=1 then 1 else 0)=4+2*(if t x=3 then 1 else 0) := by
      have a := has x xm
      have b := bound x
      have c : t x=1 ∨ t x=2 ∨ t x=3 := by omega
      rcases c with e|e|e <;> simp [e]
    have ss : S.card=∑ x∈R,if t x=1 then (1:Nat) else 0 := Finset.card_filter _ _
    have tt : T.card=∑ x∈R,if t x=3 then (1:Nat) else 0 := Finset.card_filter _ _
    rw [cross,ss,tt,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,Finset.mul_sum]
    have cc : 4*R.card=∑ _ ∈ R, (4:Nat) := by simp [Nat.mul_comm]
    rw [cc,←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl row
  let Q := arcSet G.Adj R R
  let p (e : V×V) := Disjoint (gateTags G A e.1) (gateTags G A e.2)
  have qc : Q.filter p=cleanArcs G A R := by
    ext e
    simp only [Q,Finset.mem_filter,mem_arcSet,cleanArcs,Finset.mem_product,cleanEdge,p]
    tauto
  have qs : Q.filter (fun e=>¬p e)=arcSet (fun x y=>G.Adj x y ∧ ¬Disjoint (gateTags G A x) (gateTags G A y)) R R := by
    ext e
    simp only [Q,Finset.mem_filter,mem_arcSet,p]
    tauto
  have split := Finset.filter_card_add_filter_neg_card_eq_card (s:=Q) p
  rw [qc,qs] at split
  have cle : (cleanArcs G A R).card≤2*S.card := clean_arc_card_le_two_singletons h4 A R a3 apart has
  have she := shared_arc_card_le_twice_triangles (G:=G) A K R ak dis
  have d := degree_score_arcs_decomposition (G:=G) K R dis union
  have tr := triangle_core_partition (G:=G) K
  have cb := sum_degree_eq_local_add_triangles (restricted_c4 h4 K)
  have cg := sum_degree_eq_local_add_triangles h4
  have aux {d0 d1 tr0 tr1 trx q c s e r k n m l0 l1 lHost : Nat}
      (sizes : k+r=n) (db : 2*d1=2*d0+2*e+q) (tri : tr0+trx=tr1)
      (splt : c+s=q) (clean : c≤2*m) (share : s≤2*trx)
      (cross : 2*e+2*m=4*r+2*l0)
      (base : l1+3*tr0=2*d0) (host : lHost+3*tr1=2*d1) : lHost+4*k≤l1+4*n+2*l0 := by omega
  change (∑ w : V,localIndependence G w)+4*K.card ≤
    (∑ w : (K : Set V),localIndependence (G.induce (K : Set V)) w)+4*Fintype.card V+2*T.card
  exact aux sizes d tr split cle she cross_budget cb cg

#print axioms three_gate_preserves_score_up_to_triples
end Graffiti133NestedCore
