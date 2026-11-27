import BicycleOneExteriorTriangle133

namespace Graffiti133TwoExteriorTriangles
open SimpleGraph Finset Graffiti133 Graffiti133Bicycle Graffiti133ExpandedTriangle
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem erase_card (x : V) : Fintype.card {y : V // y≠x} + 1 = Fintype.card V := by
  rw [Fintype.card_subtype,Finset.filter_ne']
  exact (Finset.card_erase_add_one (Finset.mem_univ x)).trans Finset.card_univ

theorem critical_excess_four_impossible
    (over : Fintype.card V+4≤G.edgeFinset.card)
    (minimal : ∀ x : V,(G.induce {y : V | y≠x}).edgeFinset.card ≤ Fintype.card {y : V // y≠x}+3)
    (T : Finset V) (large : 5≤T.card)
    (triangleDeletion : ∀ x∈T,(G.induce {y : V | y≠x}).edgeFinset.card ≤ Fintype.card {y : V // y≠x}+1) :
    False := by
  let k := G.edgeFinset.card-Fintype.card V
  have k4 : 4≤k := by dsimp [k]; omega
  have e : G.edgeFinset.card=Fintype.card V+k := by dsimp [k]; omega
  have delta (x : V) : 2≤G.degree x := by
    have em := card_delete_add_degree G x
    have s := erase_card x
    have mini := minimal x
    omega
  have heavier (x : V) (hx : x∈T) : k≤G.degree x := by
    have em := card_delete_add_degree G x
    have s := erase_card x
    have h := triangleDeletion x hx
    omega
  have total : (∑ x : V,(G.degree x-2))+2*Fintype.card V=2*G.edgeFinset.card := by
    calc
      _ = ∑ x : V,((G.degree x-2)+2) := by rw [Finset.sum_add_distrib]; simp [Nat.mul_comm]
      _ = ∑ x : V,G.degree x := Finset.sum_congr rfl (fun x _=>Nat.sub_add_cancel (delta x))
      _ = _ := G.sum_degrees_eq_twice_card_edges
  have lb : T.card*(k-2)≤∑ x∈T,(G.degree x-2) := by
    simpa using (Finset.sum_le_sum (s:=T) (fun x hx=>Nat.sub_le_sub_right (heavier x hx) 2) :
      (∑ _∈T,(k-2))≤∑ x∈T,(G.degree x-2))
  have ub : (∑ x∈T,(G.degree x-2))≤∑ x : V,(G.degree x-2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (by simp)
  have lb' : 5*(k-2)≤T.card*(k-2) := Nat.mul_le_mul_right _ large
  omega

#print axioms critical_excess_four_impossible
end Graffiti133TwoExteriorTriangles


namespace Graffiti133TwoExteriorTriangles
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Bicycle Graffiti133ExpandedTriangle
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def TriangleIn (G : SimpleGraph V) (S T : Finset V) : Prop :=
  ∃ a b c, a∈S ∧ b∈S ∧ c∈S ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
    ({a,b,c}:Finset V)=T

def AtMostTwo (G : SimpleGraph V) (S T₁ T₂ : Finset V) : Prop :=
    ∀ a b c, a∈S → b∈S → c∈S → G.Adj a b → G.Adj b c → G.Adj c a →
      ({a,b,c}:Finset V)⊆T₁ ∨ ({a,b,c}:Finset V)⊆T₂

theorem triangle_card (a b c : V) (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) :
    ({a,b,c}:Finset V).card=3 := by simp [ab.ne,bc.ne,ca.ne.symm]

theorem tri_support_eq {T : Finset V} (T3 : T.card≤3)
    (a b c : V) (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a)
    (sub : ({a,b,c}:Finset V)⊆T) : ({a,b,c}:Finset V)=T :=
  Finset.eq_of_subset_of_card_le sub (by rwa [triangle_card a b c ab bc ca])

theorem TriangleIn.card {S T : Finset V} (h : TriangleIn G S T) : T.card=3 := by
  obtain ⟨a,b,c,_,_,_,ab,bc,ca,rfl⟩ := h
  exact triangle_card a b c ab bc ca

theorem TriangleIn.subset {S T : Finset V} (h : TriangleIn G S T) : T⊆S := by
  obtain ⟨a,b,c,as,bs,cs,_,_,_,rfl⟩ := h
  intro x xm
  simp only [Finset.mem_insert,Finset.mem_singleton] at xm
  rcases xm with e|e|e <;> subst x <;> assumption

theorem TriangleIn.clique {S T : Finset V} (h : TriangleIn G S T) (u v : V)
    (hu : u∈T) (hv : v∈T) (ne : u≠v) : G.Adj u v := by
  obtain ⟨a,b,c,_,_,_,ab,bc,ca,rfl⟩ := h
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with e|e|e <;> subst u <;> rcases hv with e|e|e <;> subst v
  all_goals first | contradiction | exact ab | exact ab.symm | exact bc | exact bc.symm | exact ca | exact ca.symm

theorem triangle_inter_card_le_one (h4 : FourCycleFree G) {S T₁ T₂ : Finset V}
    (tr₁ : TriangleIn G S T₁) (tr₂ : TriangleIn G S T₂) (ne : T₁≠T₂) :
    (T₁∩T₂).card≤1 := by
  classical
  by_contra! h
  obtain ⟨u,um,v,vm,uv⟩ := Finset.one_lt_card.mp h
  have pu : ¬T₁⊆T₂ := fun hh=>ne (Finset.eq_of_subset_of_card_le hh (by rw [tr₁.card,tr₂.card]))
  have qu : ¬T₂⊆T₁ := fun hh=>ne (Finset.eq_of_subset_of_card_le hh (by rw [tr₁.card,tr₂.card])).symm
  obtain ⟨p,p1,p2⟩ := Finset.not_subset.mp pu
  obtain ⟨q,q2,q1⟩ := Finset.not_subset.mp qu
  have u1 := (Finset.mem_inter.mp um).1
  have u2 := (Finset.mem_inter.mp um).2
  have v1 := (Finset.mem_inter.mp vm).1
  have v2 := (Finset.mem_inter.mp vm).2
  have eq := h4 u v p q uv
    (tr₁.clique u p u1 p1 (fun e=>p2 (e ▸ u2)))
    (tr₁.clique v p v1 p1 (fun e=>p2 (e ▸ v2)))
    (tr₂.clique u q u2 q2 (fun e=>q1 (e ▸ u1)))
    (tr₂.clique v q v2 q2 (fun e=>q1 (e ▸ v1)))
  exact p2 (eq.symm ▸ q2)

theorem union_triangle_card_ge_five (h4 : FourCycleFree G) {S T₁ T₂ : Finset V}
    (tr₁ : TriangleIn G S T₁) (tr₂ : TriangleIn G S T₂) (ne : T₁≠T₂) :
    5≤(T₁∪T₂).card := by
  classical
  have x := triangle_inter_card_le_one h4 tr₁ tr₂ ne
  have y := Finset.card_union_add_card_inter T₁ T₂
  rw [tr₁.card,tr₂.card] at y
  omega

#print axioms union_triangle_card_ge_five
end Graffiti133TwoExteriorTriangles


namespace Graffiti133TwoExteriorTriangles
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Bicycle Graffiti133ExpandedTriangle
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private def ambientEraseIso (S : Finset V) (x : (S : Set V)) :
    ((G.induce (S : Set V)).induce {y : (S : Set V) | y≠x}) ≃g G.induce (S.erase x.val : Set V) where
  toEquiv :=
    { toFun := fun y=>⟨y.val.val,Finset.mem_erase.mpr ⟨fun eq=>y.property (Subtype.ext eq),y.val.property⟩⟩
      invFun := fun y=>⟨⟨y.val,(Finset.mem_erase.mp y.property).2⟩,
        fun eq=>(Finset.mem_erase.mp y.property).1 (congrArg Subtype.val eq)⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  map_rel_iff' := Iff.rfl

private theorem choose_excess_four (O : Finset V)
    (big : O.card+4≤(G.induce (O : Set V)).edgeFinset.card) :
    ∃ S⊆O, S.card+4≤(G.induce (S : Set V)).edgeFinset.card ∧
      ∀ T⊆O,T.card<S.card → (G.induce (T : Set V)).edgeFinset.card≤T.card+3 := by
  classical
  let P (S : Finset V) := S.card+4≤(G.induce (S : Set V)).edgeFinset.card
  let C := O.powerset.filter P
  have mem (S : Finset V) : S∈C ↔ S⊆O ∧ P S := by simp [C]
  obtain ⟨S,sm,min⟩ := Finset.exists_min_image C Finset.card ⟨O,(mem O).mpr ⟨Subset.rfl,big⟩⟩
  refine ⟨S,((mem S).mp sm).1,((mem S).mp sm).2,?_⟩
  intro T TO small
  by_cases over : P T
  · exact ((Nat.not_le_of_gt small) (min T ((mem T).mpr ⟨TO,over⟩))).elim
  · change ¬ T.card+4≤(G.induce (T : Set V)).edgeFinset.card at over
    omega

theorem two_exterior_triangle_edge_bound (H : Hole G 7)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (site : ∀ x,Outside H.c x → ∃ i,∀ j,G.Adj x (H.c j) ↔ j=i)
    (O T₁ T₂ : Finset V) (out : ∀ x∈O,Outside H.c x)
    (t1 : T₁.card≤3) (t2 : T₂.card≤3)
    (two : AtMostTwo G O T₁ T₂) :
    (G.induce (O : Set V)).edgeFinset.card≤O.card+3 := by
  classical
  by_contra! big
  obtain ⟨S,SO,over,minor⟩ := choose_excess_four (G:=G) O (Nat.succ_le_of_lt big)
  have outS (x : V) (xs : x∈S) : Outside H.c x := out x (SO xs)
  have twoS : AtMostTwo G S T₁ T₂ :=
    fun a b c aS bS cS ab bc ca=>two a b c (SO aS) (SO bS) (SO cS) ab bc ca
  have notOne (T : Finset V) (T3 : T.card≤3)
      (all : ∀ a b c, a∈S → b∈S → c∈S → G.Adj a b → G.Adj b c → G.Adj c a → c∈T) : False := by
    have first := one_exterior_triangle_edge_bound H h4 h9 site S T outS T3 all
    omega
  have present1 : TriangleIn G S T₁ := by
    by_contra missing
    apply notOne T₂ t2
    intro a b c aS bS cS ab bc ca
    rcases twoS a b c aS bS cS ab bc ca with ha|hb
    · exact (missing ⟨a,b,c,aS,bS,cS,ab,bc,ca,tri_support_eq t1 a b c ab bc ca ha⟩).elim
    · exact hb (by simp)
  have present2 : TriangleIn G S T₂ := by
    by_contra missing
    apply notOne T₁ t1
    intro a b c aS bS cS ab bc ca
    rcases twoS a b c aS bS cS ab bc ca with ha|hb
    · exact ha (by simp)
    · exact (missing ⟨a,b,c,aS,bS,cS,ab,bc,ca,tri_support_eq t2 a b c ab bc ca hb⟩).elim
  have ne : T₁≠T₂ := by
    intro eq
    apply notOne T₂ t2
    intro a b c aS bS cS ab bc ca
    rcases twoS a b c aS bS cS ab bc ca with ha|hb
    · rw [eq] at ha
      exact ha (by simp)
    · exact hb (by simp)
  let U := (S : Set V)
  let J := G.induce U
  let val (x : U) := x.val
  let T := (T₁∪T₂).subtype (fun x=>x∈S)
  have large : 5≤T.card := by
    change 5≤((T₁∪T₂).subtype (fun x=>x∈S)).card
    rw [Finset.card_subtype]
    have f : ((T₁∪T₂).filter (fun x=>x∈S))=T₁∪T₂ := by
      apply Finset.filter_true_of_mem
      intro x xm
      rcases Finset.mem_union.mp xm with m|m
      · exact present1.subset m
      · exact present2.subset m
    rw [f]
    exact union_triangle_card_ge_five h4 present1 present2 ne
  have total : Fintype.card U+4≤J.edgeFinset.card := by
    rw [show Fintype.card U=S.card from Fintype.card_coe S]
    exact over
  have count (x : U) : Fintype.card {y : U // y≠x}=(S.erase x.val).card :=
    (Fintype.card_congr (ambientEraseIso (G:=G) S x).toEquiv).trans (Fintype.card_coe _)
  have allowed (x : U) : (S.erase x.val)⊆O := fun _ hx=>SO (Finset.mem_erase.mp hx).2
  have regular (x : U) : (J.induce {y : U | y≠x}).edgeFinset.card≤Fintype.card {y : U // y≠x}+3 := by
    rw [(ambientEraseIso (G:=G) S x).card_edgeFinset_eq,count]
    exact minor _ (allowed x) (Finset.card_erase_lt_of_mem x.property)
  have stronger (x : U) (xm : x∈T) :
      (J.induce {y : U | y≠x}).edgeFinset.card≤Fintype.card {y : U // y≠x}+1 := by
    rw [(ambientEraseIso (G:=G) S x).card_edgeFinset_eq,count]
    have xm' : x.val∈T₁∪T₂ := Finset.mem_subtype.mp xm
    have keep (B C : Finset V) (B3 : B.card≤3) (C3 : C.card≤3) (xB : x.val∈B)
        (cover : AtMostTwo G (S.erase x.val) B C) :
        (G.induce (S.erase x.val : Set V)).edgeFinset.card≤(S.erase x.val).card+1 := by
      apply one_exterior_triangle_edge_bound H h4 h9 site _ C
        (fun a h=>outS a (Finset.mem_erase.mp h).2) C3
      intro a b c aS bS cS ab bc ca
      rcases cover a b c aS bS cS ab bc ca with ha|hb
      · have eq := tri_support_eq B3 a b c ab bc ca ha
        rw [←eq] at xB
        simp only [Finset.mem_insert,Finset.mem_singleton] at xB
        rcases xB with e|e|e
        · exact ((Finset.mem_erase.mp aS).1 e.symm).elim
        · exact ((Finset.mem_erase.mp bS).1 e.symm).elim
        · exact ((Finset.mem_erase.mp cS).1 e.symm).elim
      · exact hb (by simp)
    rcases Finset.mem_union.mp xm' with xt|xt
    · exact keep T₁ T₂ t1 t2 xt (fun a b c aS bS cS ab bc ca =>
        twoS a b c (Finset.mem_erase.mp aS).2 (Finset.mem_erase.mp bS).2 (Finset.mem_erase.mp cS).2 ab bc ca)
    · exact keep T₂ T₁ t2 t1 xt (fun a b c aS bS cS ab bc ca =>
        (twoS a b c (Finset.mem_erase.mp aS).2 (Finset.mem_erase.mp bS).2
          (Finset.mem_erase.mp cS).2 ab bc ca).symm)
  exact critical_excess_four_impossible J total regular T large stronger

#print axioms two_exterior_triangle_edge_bound
end Graffiti133TwoExteriorTriangles


namespace Graffiti133TwoExteriorTriangles
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

open Graffiti133BicycleCharge Graffiti133Bicycle

private lemma row_card (v : V) (S : Finset V) :
    row G v S = (S.filter fun w => G.Adj v w).card := by
  classical
  exact (Finset.card_filter _ _).symm

private lemma local_bound (v : V) : localIndependence G v ≤ row G v Finset.univ := by
  classical
  obtain ⟨A,hA,eA⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
  rw [←eA,row_card]
  exact Finset.card_le_card (fun x hx => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,(Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1 x hx⟩)

private lemma row_symm (A B : Finset V) :
    (∑ x ∈ A, row G x B) = ∑ y ∈ B, row G y A := by
  classical
  unfold row
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [G.adj_comm y x]

private lemma cycle_row (H : Hole G 7) (i : Fin 7) :
    row G (H.c i) (Finset.univ.image H.c) = 2 := by
  classical
  change (∑ w ∈ Finset.univ.image H.c, (if G.Adj (H.c i) w then 1 else 0 : ℕ))=2
  rw [Finset.sum_image (fun _ _ _ _ eq => H.inj eq)]
  have aux : ∀ i : Fin 7, (Finset.univ.filter fun j => Cyclic i j).card = 2 := by decide
  rw [←aux i,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  exact if_congr (H.adj i j) rfl rfl


private theorem singleton_row (H : Hole G 7) (x : V) (i : Fin 7)
    (hit : ∀ j, G.Adj x (H.c j) ↔ j=i) :
    row G x (Finset.univ.image H.c) = 1 := by
  classical
  change (∑ w ∈ Finset.univ.image H.c, (if G.Adj x w then 1 else 0 : ℕ))=_
  rw [Finset.sum_image (fun _ _ _ _ eq => H.inj eq)]
  have h : (∑ j : Fin 7, (if j=i then 1 else 0 : ℕ)) = 1 := by simp
  have same : (∑ j : Fin 7, (if G.Adj x (H.c j) then 1 else 0 : ℕ)) =
      (∑ j : Fin 7, (if j=i then 1 else 0 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro j _
    exact if_congr (hit j) rfl rfl
  exact same.trans h


private theorem degree_induced_row (O : Finset V) (x : (O : Set V)) :
    (G.induce (O : Set V)).degree x = row G x.val O := by
  classical
  rw [SimpleGraph.degree,show row G x.val O=(O.filter fun y=>G.Adj x.val y).card
    from (Finset.card_filter _ _).symm]
  apply Finset.card_bij (fun y _=>y.val)
  · intro y hy
    exact Finset.mem_filter.mpr ⟨y.property,((G.induce (O : Set V)).mem_neighborFinset x y).mp hy⟩
  · exact fun y _ z _ e=>Subtype.ext e
  · intro y hy
    obtain ⟨mem,adj⟩ := Finset.mem_filter.mp hy
    exact ⟨⟨y,mem⟩,((G.induce (O : Set V)).mem_neighborFinset x ⟨y,mem⟩).mpr adj,rfl⟩


private theorem local_extra (v a b : V) (va : G.Adj v a) (vb : G.Adj v b)
    (ab : G.Adj a b) : localIndependence G v + 1 ≤ row G v Finset.univ := by
  classical
  obtain ⟨A,hA,eA⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
  have facts := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  obtain ⟨x,xn,xv⟩ : ∃ x, x∉A ∧ G.Adj v x := by
    by_cases aa : a∈A
    · exact ⟨b,fun bb=>facts.2 a aa b bb ab,vb⟩
    · exact ⟨a,aa,va⟩
  rw [←eA,row_card,←Finset.card_insert_of_not_mem xn]
  apply Finset.card_le_card
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl|ya
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,xv⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,facts.1 y ya⟩



private theorem vertex_triangle_neighbor_pair {S T : Finset V} (tr : TriangleIn G S T)
    (v : V) (vm : v∈T) :
    ∃ a b,a∈T ∧ b∈T ∧ G.Adj v a ∧ G.Adj v b ∧ G.Adj a b := by
  obtain ⟨a,b,c,_,_,_,ab,bc,ca,e⟩ := tr
  rw [←e] at vm ⊢
  simp only [Finset.mem_insert,Finset.mem_singleton] at vm
  rcases vm with r|r|r <;> subst v
  · exact ⟨b,c,by simp,by simp,ab,ca.symm,bc⟩
  · exact ⟨c,a,by simp,by simp,bc,ab.symm,ca⟩
  · exact ⟨a,b,by simp,by simp,ca,bc.symm,ab⟩

private theorem double_saving {S T₁ T₂ : Finset V}
    (h4 : FourCycleFree G) (tr₁ : TriangleIn G S T₁) (tr₂ : TriangleIn G S T₂)
    (ne : T₁≠T₂) (v : V) (v1 : v∈T₁) (v2 : v∈T₂) :
    localIndependence G v+2 ≤ row G v Finset.univ := by
  classical
  obtain ⟨A,hA,eA⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
  have facts := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  have select {T : Finset V} (tr : TriangleIn G S T) (vT : v∈T) :
      ∃ x∈T,x∉A ∧ G.Adj v x := by
    obtain ⟨a,b,am,bm,va,vb,ab⟩ := vertex_triangle_neighbor_pair tr v vT
    by_cases aa : a∈A
    · exact ⟨b,bm,fun bb=>facts.2 a aa b bb ab,vb⟩
    · exact ⟨a,am,aa,va⟩
  obtain ⟨a,a1,an,va⟩ := select tr₁ v1
  obtain ⟨b,b2,bn,vb⟩ := select tr₂ v2
  have apb : a≠b := by
    intro q
    have vI : v∈T₁∩T₂ := Finset.mem_inter.mpr ⟨v1,v2⟩
    have aI : a∈T₁∩T₂ := Finset.mem_inter.mpr ⟨a1,q.symm ▸ b2⟩
    have lb := Finset.one_lt_card.mpr ⟨v,vI,a,aI,va.ne⟩
    have ub := triangle_inter_card_le_one h4 tr₁ tr₂ ne
    omega
  have bad : a∉insert b A := by simp [apb,an]
  have num : (insert a (insert b A)).card=A.card+2 := by
    rw [Finset.card_insert_of_not_mem bad,Finset.card_insert_of_not_mem bn]
  rw [←eA,row_card,←num]
  apply Finset.card_le_card
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl|hz
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,va⟩
  · rcases Finset.mem_insert.mp hz with rfl|zm
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,vb⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,facts.1 z zm⟩

private theorem point_triangle_saving {S T₁ T₂ : Finset V}
    (h4 : FourCycleFree G) (tr₁ : TriangleIn G S T₁) (tr₂ : TriangleIn G S T₂)
    (ne : T₁≠T₂) (v : V) :
    localIndependence G v + ((if v∈T₁ then 1 else 0)+(if v∈T₂ then 1 else 0))
      ≤ row G v Finset.univ := by
  classical
  by_cases h1 : v∈T₁ <;> by_cases h2 : v∈T₂
  · simpa [h1,h2] using double_saving h4 tr₁ tr₂ ne v h1 h2
  · obtain ⟨a,b,_,_,va,vb,ab⟩ := vertex_triangle_neighbor_pair tr₁ v h1
    simpa [h1,h2] using local_extra v a b va vb ab
  · obtain ⟨a,b,_,_,va,vb,ab⟩ := vertex_triangle_neighbor_pair tr₂ v h2
    simpa [h1,h2] using local_extra v a b va vb ab
  · simpa [h1,h2] using local_bound (G:=G) v

private theorem particular_mean_four
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (site : ∀ x,Outside H.c x → ∃ i,∀ j,G.Adj x (H.c j) ↔ j=i)
    (T₁ T₂ : Finset V) (ne : T₁≠T₂)
    (tr₁ : TriangleIn G (Finset.univ \ Finset.univ.image H.c) T₁)
    (tr₂ : TriangleIn G (Finset.univ \ Finset.univ.image H.c) T₂)
    (two : AtMostTwo G (Finset.univ \ Finset.univ.image H.c) T₁ T₂) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let C : Finset V := Finset.univ.image H.c
  let O : Finset V := Finset.univ \ C
  have old : C.card=7 := by rw [Finset.card_image_of_injective _ H.inj]; simp
  have size : O.card+7=Fintype.card V := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
    rw [old,Finset.card_univ] at h
    exact h
  have out (x : V) (hx : x∈O) : Outside H.c x := by
    intro i e
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
  have edges := two_exterior_triangle_edge_bound H h4 h9 site O T₁ T₂ out
    (by rw [tr₁.card]) (by rw [tr₂.card]) two
  let J := G.induce (O : Set V)
  change J.edgeFinset.card≤O.card+3 at edges
  have arcsO : (∑ x∈O,row G x O)≤2*O.card+6 := by
    calc
      _ = ∑ x : (O : Set V),row G x.val O := (Finset.sum_attach O _).symm
      _ = ∑ x : (O : Set V),J.degree x := Finset.sum_congr rfl (fun x _=>(degree_induced_row O x).symm)
      _ = 2*J.edgeFinset.card := J.sum_degrees_eq_twice_card_edges
      _ ≤ _ := by omega
  have cSum : (∑ v∈C, row G v C)=14 := by
    change (∑ v ∈ Finset.univ.image H.c, row G v C)=14
    rw [Finset.sum_image (fun _ _ _ _ e => H.inj e)]
    have cRow (i : Fin 7) : row G (H.c i) C=2 := cycle_row H i
    simp_rw [cRow]
    simp
  have weight : (∑ v∈O, row G v C)=O.card := by
    have eq (v : V) (hv : v∈O) : row G v C=1 := by
      obtain ⟨i,hi⟩ := site v (out v hv)
      exact singleton_row H v i hi
    rw [Finset.sum_congr rfl eq]
    simp
  have split (f : V → ℕ) : (∑ v : V, f v) = (∑ v∈C,f v)+(∑ v∈O,f v) := by
    simpa [O,Nat.add_comm] using (Finset.sum_sdiff (f:=f) (Finset.subset_univ C)).symm
  have rows (v : V) : row G v Finset.univ = row G v C + row G v O :=
    split (fun w => @ite ℕ (G.Adj v w) (Classical.propDecidable _) 1 0)
  have budget : (∑ v : V,row G v Finset.univ)≤4*Fintype.card V+6 := by
    rw [split (fun v=>row G v Finset.univ)]
    simp_rw [rows,Finset.sum_add_distrib]
    rw [cSum,row_symm (G:=G) C O,weight]
    omega
  have points := Finset.sum_le_sum (s:=Finset.univ)
    (fun v _=>point_triangle_saving h4 tr₁ tr₂ ne v)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at points
  have totals (T : Finset V) : (∑ v : V,(if v∈T then (1:Nat) else 0))=T.card := by
    rw [←Finset.card_filter]
    simp
  rw [totals,totals,tr₁.card,tr₂.card] at points
  omega

theorem singleton_seven_at_most_two_exterior_triangles_mean_four
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (site : ∀ x,Outside H.c x → ∃ i,∀ j,G.Adj x (H.c j) ↔ j=i)
    (T₁ T₂ : Finset V) (t1 : T₁.card≤3) (t2 : T₂.card≤3)
    (two : AtMostTwo G (Finset.univ \ Finset.univ.image H.c) T₁ T₂) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let O : Finset V := Finset.univ \ Finset.univ.image H.c
  have inside (x : V) (off : Outside H.c x) : x∈O := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro m
    obtain ⟨i,_,eq⟩ := Finset.mem_image.mp m
    exact off i eq.symm
  by_cases eq : T₁=T₂
  · apply Graffiti133OneTriangle.singleton_seven_at_most_one_exterior_triangle_mean_four H h4 h9 site T₂ t2
    intro a b c ao bo co ab bc ca
    rcases two a b c (inside a ao) (inside b bo) (inside c co) ab bc ca with ha|hb
    · exact eq ▸ (ha (by simp) : c∈T₁)
    · exact hb (by simp)
  by_cases h1 : TriangleIn G O T₁
  · by_cases h2 : TriangleIn G O T₂
    · exact particular_mean_four H h4 h9 site T₁ T₂ eq h1 h2 two
    · apply Graffiti133OneTriangle.singleton_seven_at_most_one_exterior_triangle_mean_four H h4 h9 site T₁ t1
      intro a b c ao bo co ab bc ca
      have as := inside a ao
      have bs := inside b bo
      have cs := inside c co
      rcases two a b c as bs cs ab bc ca with ha|hb
      · exact ha (by simp)
      · exact (h2 ⟨a,b,c,as,bs,cs,ab,bc,ca,tri_support_eq t2 a b c ab bc ca hb⟩).elim
  · apply Graffiti133OneTriangle.singleton_seven_at_most_one_exterior_triangle_mean_four H h4 h9 site T₂ t2
    intro a b c ao bo co ab bc ca
    have as := inside a ao
    have bs := inside b bo
    have cs := inside c co
    rcases two a b c as bs cs ab bc ca with ha|hb
    · exact (h1 ⟨a,b,c,as,bs,cs,ab,bc,ca,tri_support_eq t1 a b c ab bc ca ha⟩).elim
    · exact hb (by simp)

#print axioms singleton_seven_at_most_two_exterior_triangles_mean_four
end Graffiti133TwoExteriorTriangles
