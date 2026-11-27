import BicycleSingletonSevenGeneral133

namespace Graffiti133MultiC7
open SimpleGraph Finset Graffiti133 Graffiti133NoFive
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def contactSet (H : Hole G 7) (x : V) : Finset (Fin 7) :=
  Finset.univ.filter (fun i => G.Adj x (H.c i))

@[simp] theorem mem_contactSet (H : Hole G 7) (x : V) (i : Fin 7) :
    i∈contactSet H x ↔ G.Adj x (H.c i) := by simp [contactSet]

def cleanSites (A : Finset (Fin 7)) : Finset (Fin 7) :=
  Finset.univ.filter (fun i => ∀ j∈A, ¬Cyclic i j)

def C4Allowed (A : Finset (Fin 7)) : Prop :=
  ∀ i∈A, ∀ j∈A, i≠j → ¬∃ k, Cyclic i k ∧ Cyclic j k

def farSites (i j : Fin 7) : Prop :=
  i≠j ∧ ¬Cyclic i j ∧ ¬∃ k, Cyclic i k ∧ Cyclic j k

instance (A : Finset (Fin 7)) : Decidable (C4Allowed A) := by unfold C4Allowed; infer_instance
instance (i j : Fin 7) : Decidable (farSites i j) := by unfold farSites; infer_instance

theorem geometry_cap : ∀ A : Finset (Fin 7), C4Allowed A → 2≤A.card →
    ((A.card=2 ∧ (cleanSites A).card=3) ∨ (A.card=3 ∧ (cleanSites A).card=1)) := by decide

theorem geometry_triple_center : ∀ A : Finset (Fin 7), C4Allowed A → A.card=3 →
    ∃ i∈A,∀ j,farSites i j→j∈A := by decide

theorem geometry_pair_types : ∀ A : Finset (Fin 7), C4Allowed A → A.card=2 →
    ∃ i j, i≠j ∧ A={i,j} ∧ (Cyclic i j ∨ farSites i j) := by decide

theorem geometry_profits : ∀ A : Finset (Fin 7), C4Allowed A → 2≤A.card →
    ((A.card=2 ∧ (∃ i∈A,∃ j∈A,Cyclic i j) ∧ ((cleanSites A)\A).card=3) ∨
     (A.card=2 ∧ (∀ i∈A,∀ j∈A,¬Cyclic i j) ∧ ((cleanSites A)\A).card=1) ∨
     (A.card=3 ∧ (∃ i∈A,∃ j∈A,Cyclic i j) ∧ ((cleanSites A)\A).card=0)) := by decide

theorem contacts_are_allowed (H : Hole G 7) (h4 : FourCycleFree G)
    (x : V) (hx : Outside H.c x) : C4Allowed (contactSet H x) := by
  intro i im j jm ne
  rintro ⟨k,ik,jk⟩
  have e := h4 (H.c i) (H.c j) x (H.c k) (H.inj.ne ne)
    ((mem_contactSet H x i).mp im).symm ((mem_contactSet H x j).mp jm).symm
    ((H.adj i k).mpr ik) ((H.adj j k).mpr jk)
  exact hx k e

theorem disjoint_contact_pairs (H : Hole G 7) (h4 : FourCycleFree G) {x y : V} (ne : x≠y) :
    (contactSet H x ∩ contactSet H y).card≤1 := by
  by_contra! wrong
  obtain ⟨i,im,j,jm,ij⟩ := Finset.one_lt_card.mp wrong
  have e := h4 x y (H.c i) (H.c j) ne
    ((mem_contactSet H x i).mp (Finset.mem_inter.mp im).1)
    ((mem_contactSet H y i).mp (Finset.mem_inter.mp im).2)
    ((mem_contactSet H x j).mp (Finset.mem_inter.mp jm).1)
    ((mem_contactSet H y j).mp (Finset.mem_inter.mp jm).2)
  exact ij (H.inj e)

noncomputable def exteriorNeighbors (H : Hole G 7) (x : V) : Finset V :=
  Finset.univ.filter (fun y => Outside H.c y ∧ G.Adj x y)

theorem neighbor_sites_clean (H : Hole G 7) (h4 : FourCycleFree G)
    {x y : V} (hx : Outside H.c x) (hy : Outside H.c y) (xy : G.Adj x y)
    (i : Fin 7) (yi : G.Adj y (H.c i)) : i∈cleanSites (contactSet H x) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro j jm e
  have eq := h4 x (H.c i) y (H.c j) (hx i) xy yi.symm
    ((mem_contactSet H x j).mp jm) ((H.adj i j).mpr e)
  exact hy j eq

theorem exterior_degree_capacity (H : Hole G 7) (h4 : FourCycleFree G)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i)) (x : V) (hx : Outside H.c x) :
    (exteriorNeighbors H x).card≤(cleanSites (contactSet H x)).card := by
  classical
  let X := exteriorNeighbors H x
  have prop (y : V) (hy : y∈X) : Outside H.c y ∧ G.Adj x y :=
    (Finset.mem_filter.mp hy).2
  choose label spec using fun y : {y // y∈X} => dom y.val (prop y.val y.property).1
  let lab (y : V) := if hy : y∈X then label ⟨y,hy⟩ else 0
  have eval (y : V) (hy : y∈X) : lab y=label ⟨y,hy⟩ := dif_pos hy
  change X.card≤_
  apply Finset.card_le_card_of_injOn lab
  · intro y hy
    change y∈X at hy
    rw [eval y hy]
    exact neighbor_sites_clean H h4 hx (prop y hy).1 (prop y hy).2 _ (spec ⟨y,hy⟩)
  · intro y hy z hz eq
    change y∈X at hy
    change z∈X at hz
    rw [eval y hy,eval z hz] at eq
    exact h4 x (H.c (label ⟨y,hy⟩)) y z (hx _)
      (prop _ hy).2 (spec ⟨y,hy⟩).symm (prop _ hz).2
      (by rw [eq]; exact (spec ⟨z,hz⟩).symm)

theorem multi_exterior_degree_le_three (H : Hole G 7) (h4 : FourCycleFree G)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i)) (x : V) (hx : Outside H.c x)
    (multi : 2≤(contactSet H x).card) : (exteriorNeighbors H x).card≤3 := by
  have profile := geometry_cap (contactSet H x) (contacts_are_allowed H h4 x hx) multi
  have cap := exterior_degree_capacity H h4 dom x hx
  rcases profile with ⟨_,h⟩|⟨_,h⟩ <;> omega

#print axioms geometry_cap
#print axioms geometry_triple_center
#print axioms exterior_degree_capacity
end Graffiti133MultiC7


namespace Graffiti133SingletonSlack
open Graffiti133TwoExteriorTriangles
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


private theorem charged_slack14 (H : Hole G 7)
    (site : ∀ x,Outside H.c x → ∃ i,∀ j,G.Adj x (H.c j) ↔ j=i)
    (k : Nat) (credit : V→Nat)
    (exterior : let O := (Finset.univ : Finset V) \ Finset.univ.image H.c;
      (G.induce (O : Set V)).edgeFinset.card≤O.card+k)
    (point : ∀ v,localIndependence G v+credit v≤row G v Finset.univ)
    (enough : 2*k≤∑ v : V,credit v) :
    (∑ v : V,localIndependence G v)+14≤4*Fintype.card V := by
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
  let J := G.induce (O : Set V)
  change J.edgeFinset.card≤O.card+k at exterior
  have arcsO : (∑ x∈O,row G x O)≤2*O.card + 2*k := by
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
  have budget : (∑ v : V,row G v Finset.univ) +14≤4*Fintype.card V+2*k := by
    rw [split (fun v=>row G v Finset.univ)]
    simp_rw [rows,Finset.sum_add_distrib]
    rw [cSum,row_symm (G:=G) C O,weight]
    omega

  have points := Finset.sum_le_sum (s:=Finset.univ) (fun v _=>point v)
  rw [Finset.sum_add_distrib] at points
  omega

private theorem exterior_outside (H : Hole G 7) (x : V)
    (hx : x∈((Finset.univ : Finset V) \ Finset.univ.image H.c)) : Outside H.c x := by
  intro i e
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)

private theorem indicator_sum (T : Finset V) : (∑ v : V,if v∈T then (1:Nat) else 0)=T.card := by
  rw [←Finset.card_filter]
  simp

private theorem one_ext_slack14 (H : Hole G 7)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (site : ∀ x,Outside H.c x → ∃ i,∀ j,G.Adj x (H.c j) ↔ j=i)
    (T : Finset V) (T3 : T.card≤3)
    (only : ∀ a b c, a∈((Finset.univ : Finset V) \ Finset.univ.image H.c) →
      b∈((Finset.univ : Finset V) \ Finset.univ.image H.c) →
      c∈((Finset.univ : Finset V) \ Finset.univ.image H.c) →
      G.Adj a b → G.Adj b c → G.Adj c a → ({a,b,c}:Finset V)⊆T) :
    (∑ v : V,localIndependence G v)+14≤4*Fintype.card V := by
  classical
  let O : Finset V := Finset.univ \ Finset.univ.image H.c
  by_cases ex : TriangleIn G O T
  · apply charged_slack14 H site 1 (fun v=>if v∈T then 1 else 0)
    · exact Graffiti133ExpandedTriangle.one_exterior_triangle_edge_bound H h4 h9 site O T
        (exterior_outside H) T3 (fun a b c am bm cm ab bc ca=>only a b c am bm cm ab bc ca (by simp))
    · intro v
      by_cases vm : v∈T
      · obtain ⟨a,b,_,_,va,vb,ab⟩ := vertex_triangle_neighbor_pair ex v vm
        simpa [vm] using local_extra v a b va vb ab
      · simpa [vm] using local_bound (G:=G) v
    · rw [indicator_sum,ex.card]
      decide
  · apply charged_slack14 H site 0 (fun _=>0)
    · have tris (a b c : V) (am : a∈O) (bm : b∈O) (cm : c∈O)
          (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) : False :=
        ex ⟨a,b,c,am,bm,cm,ab,bc,ca,tri_support_eq T3 a b c ab bc ca (only a b c am bm cm ab bc ca)⟩
      simpa only [Nat.add_zero] using
        Graffiti133TriangleDeletion.local_exterior_edges H h4 h9 site O (exterior_outside H) tris
    · intro v
      simpa using local_bound (G:=G) v
    · simp

theorem singleton_seven_has_slack14 (H : Hole G 7)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (site : ∀ x,Outside H.c x → ∃ i,∀ j,G.Adj x (H.c j) ↔ j=i) :
    (∑ v : V,localIndependence G v)+14≤4*Fintype.card V := by
  classical
  let O : Finset V := Finset.univ \ Finset.univ.image H.c
  obtain ⟨A,B,a3,b3,cover⟩ := Graffiti133ExteriorTriple.at_most_two_exterior_triangle_supports
    H h4 h9 site O (exterior_outside H)
  by_cases eq : A=B
  · apply one_ext_slack14 H h4 h9 site B b3
    intro a b c am bm cm ab bc ca
    rcases cover a b c am bm cm ab bc ca with h|h
    · exact eq ▸ h
    · exact h
  by_cases ea : TriangleIn G O A
  · by_cases eb : TriangleIn G O B
    · apply charged_slack14 H site 3 (fun v=>(if v∈A then 1 else 0)+(if v∈B then 1 else 0))
      · exact two_exterior_triangle_edge_bound H h4 h9 site O A B (exterior_outside H) a3 b3 cover
      · exact point_triangle_saving h4 ea eb eq
      · rw [Finset.sum_add_distrib,indicator_sum,indicator_sum,ea.card,eb.card]
    · apply one_ext_slack14 H h4 h9 site A a3
      intro a b c am bm cm ab bc ca
      rcases cover a b c am bm cm ab bc ca with h|h
      · exact h
      · exact (eb ⟨a,b,c,am,bm,cm,ab,bc,ca,tri_support_eq b3 a b c ab bc ca h⟩).elim
  · apply one_ext_slack14 H h4 h9 site B b3
    intro a b c am bm cm ab bc ca
    rcases cover a b c am bm cm ab bc ca with h|h
    · exact (ea ⟨a,b,c,am,bm,cm,ab,bc,ca,tri_support_eq a3 a b c ab bc ca h⟩).elim
    · exact h

#print axioms singleton_seven_has_slack14
end Graffiti133SingletonSlack


namespace Graffiti133MultiC7
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133BicycleCharge Graffiti133SingletonSlack
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

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


theorem split_degree_contacts (H : Hole G 7) (x : V) :
    row G x Finset.univ=(contactSet H x).card + (exteriorNeighbors H x).card := by
  classical
  let C : Finset V := Finset.univ.image H.c
  let O : Finset V := Finset.univ \ C
  have split := (Finset.sum_sdiff (f:=fun y=>if G.Adj x y then (1:Nat) else 0)
    (Finset.subset_univ C)).symm
  change row G x Finset.univ=row G x O+row G x C at split
  have c : row G x C=(contactSet H x).card := by
    change (∑ y∈Finset.univ.image H.c,(if G.Adj x y then (1:Nat) else 0))=_
    rw [Finset.sum_image (fun a _ b _ e=>H.inj e)]
    exact (Finset.card_filter _ _).symm
  have o : row G x O=(exteriorNeighbors H x).card := by
    rw [row_card]
    congr 1
    ext y
    simp only [Finset.mem_filter,exteriorNeighbors,Finset.mem_univ,true_and]
    have offtest : y∈O ↔ Outside H.c y := by
      constructor
      · intro h i e
        exact (Finset.mem_sdiff.mp h).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
      · intro h
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
        rintro m
        obtain ⟨i,_,e⟩ := Finset.mem_image.mp m
        exact h i e.symm
    rw [offtest]
  omega

theorem multi_degree_le_five (H : Hole G 7) (h4 : FourCycleFree G)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (x : V) (out : Outside H.c x) (multi : 2≤(contactSet H x).card) :
    row G x Finset.univ≤5 := by
  have ex := exterior_degree_capacity H h4 dom x out
  have eq := split_degree_contacts H x
  rcases geometry_cap _ (contacts_are_allowed H h4 x out) multi with ⟨a,b⟩|⟨a,b⟩ <;> omega

private theorem local_induced_loss (D : Finset V)
    (K : Finset V) (partition : K=Finset.univ \ D) (v : (K : Set V)) :
    localIndependence G v.val ≤ localIndependence (G.induce (K : Set V)) v+row G v.val D := by
  classical
  obtain ⟨A,hA,maxA⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v.val
  have facts := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let B := A.subtype (fun y=>y∈K)
  have valid : B∈localIndependentSets (G.induce (K : Set V)) v := by
    apply Graffiti133Pentagon.PentagonFrame.memLocalSet.mpr
    exact ⟨fun x hx=>facts.1 x.val (Finset.mem_subtype.mp hx),
      fun x hx y hy=>facts.2 x.val (Finset.mem_subtype.mp hx) y.val (Finset.mem_subtype.mp hy)⟩
  have maxB := Finset.le_sup (f:=Finset.card) valid
  change B.card≤localIndependence (G.induce (K : Set V)) v at maxB
  have split : B.card+(A.filter fun y=>y∉K).card=A.card := by
    rw [Finset.card_subtype]
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  have loss : (A.filter fun y=>y∉K).card≤row G v.val D := by
    rw [row_card]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨ay,nk⟩ := Finset.mem_filter.mp hy
    have yd : y∈D := by
      rw [partition] at nk
      simpa using nk
    exact Finset.mem_filter.mpr ⟨yd,facts.1 y ay⟩
  omega

theorem induced_removal_sum_bound (D K : Finset V) (partition : K=Finset.univ \ D) :
    (∑ v : V,localIndependence G v) ≤
      (∑ v : (K : Set V),localIndependence (G.induce (K : Set V)) v) +
        2*(∑ v∈D,row G v Finset.univ) := by
  classical
  have kept : (∑ v∈K,localIndependence G v)≤
      (∑ v : (K : Set V),localIndependence (G.induce (K : Set V)) v) +
        (∑ v∈K,row G v D) := by
    have cmp := Finset.sum_le_sum (s:=Finset.univ)
      (fun (v : (K : Set V)) _=>local_induced_loss (G:=G) D K partition v)
    rw [Finset.sum_add_distrib] at cmp
    rw [←Finset.sum_attach K (fun v=>localIndependence G v),
      ←Finset.sum_attach K (fun v=>row G v D)]
    exact cmp
  have rem : (∑ v∈D,localIndependence G v)≤∑ v∈D,row G v Finset.univ :=
    Finset.sum_le_sum (fun v _=>local_bound (G:=G) v)
  have cross : (∑ v∈K,row G v D) ≤ ∑ v∈D,row G v Finset.univ := by
    rw [row_symm K D]
    apply Finset.sum_le_sum
    intro v _
    rw [row_card,row_card]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ K))
  have all : (∑ v∈K,localIndependence G v)+(∑ v∈D,localIndependence G v)=
      ∑ v : V,localIndependence G v := by
    rw [partition]
    exact Finset.sum_sdiff (Finset.subset_univ D)
  omega

noncomputable def multiVertices (H : Hole G 7) : Finset V :=
  Finset.univ.filter (fun x=>Outside H.c x ∧ 2≤(contactSet H x).card)

theorem mean_four_of_multi_degree_budget (H : Hole G 7)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (budget : (∑ x∈multiVertices H,row G x Finset.univ) ≤ 2*(multiVertices H).card+7) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let D := multiVertices H
  let K : Finset V := Finset.univ \ D
  let J := G.induce (K : Set V)
  have preserved (i : Fin 7) : H.c i∈K := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro dm
    exact (Finset.mem_filter.mp dm).2.1 i rfl
  let c (i : Fin 7) : (K : Set V) := ⟨H.c i,preserved i⟩
  let HJ : Hole J 7 := ⟨c,fun i j e=>H.inj (congrArg Subtype.val e),H.adj⟩
  have fourJ : FourCycleFree J := by
    intro a b u v ne au bu av bv
    exact Subtype.ext (h4 _ _ _ _ (fun e=>ne (Subtype.ext e)) au bu av bv)
  have nineJ : ¬∃ p : Fin 9→(K : Set V),InducedPath J p := by
    rintro ⟨p,h⟩
    exact h9 ⟨Subtype.val ∘ p,Subtype.val_injective.comp h.1,h.2⟩
  have singleJ (v : (K : Set V)) (off : Outside HJ.c v) :
      ∃ i,∀ j,J.Adj v (HJ.c j) ↔ j=i := by
    have offG : Outside H.c v.val := fun i e=>off i (Subtype.ext e)
    obtain ⟨i,edge⟩ := dom v.val offG
    have no := (Finset.mem_sdiff.mp v.property).2
    have le : (contactSet H v.val).card≤1 := by
      by_contra! high
      exact no (Finset.mem_filter.mpr ⟨Finset.mem_univ _,offG,high⟩)
    have im : i∈contactSet H v.val := (mem_contactSet H _ _).mpr edge
    refine ⟨i,fun j=>?_⟩
    constructor
    · intro e
      by_contra ne
      have je : G.Adj v.val (H.c j) := e
      have two : 1<(contactSet H v.val).card :=
        Finset.one_lt_card.mpr ⟨j,(mem_contactSet H _ _).mpr je,i,im,ne⟩
      omega
    · rintro rfl
      exact edge
  have slack := singleton_seven_has_slack14 HJ fourJ nineJ singleJ
  change (∑ v : (K : Set V),localIndependence (G.induce (K : Set V)) v)+14≤
    4*Fintype.card (K : Set V) at slack
  have le := induced_removal_sum_bound (G:=G) D K rfl
  have size : Fintype.card (K : Set V)+D.card=Fintype.card V := by
    rw [show Fintype.card (K : Set V)=K.card from Fintype.card_coe K,←Finset.card_univ]
    exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  change (∑ x∈D,row G x Finset.univ)≤2*D.card+7 at budget
  omega

theorem at_most_two_multi_vertices_mean_four (H : Hole G 7)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (small : (multiVertices H).card≤2) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  apply mean_four_of_multi_degree_budget H h4 h9 dom
  let D := multiVertices H
  have degs : (∑ x∈D,row G x Finset.univ)≤5*D.card := by
    calc
      _ ≤ ∑ x∈D,(5:Nat) := by
        apply Finset.sum_le_sum
        intro x xm
        obtain ⟨off,multi⟩ := (Finset.mem_filter.mp xm).2
        exact multi_degree_le_five H h4 dom x off multi
      _ = _ := by simp [Nat.mul_comm]
  change D.card≤2 at small
  change (∑ x∈D,row G x Finset.univ)≤2*D.card+7
  omega

#print axioms split_degree_contacts
#print axioms induced_removal_sum_bound
#print axioms mean_four_of_multi_degree_budget
#print axioms at_most_two_multi_vertices_mean_four
end Graffiti133MultiC7


namespace Graffiti133MultiC7
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133BicycleCharge
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def farPairs (A : Finset (Fin 7)) : Finset (Finset (Fin 7)) :=
  (A.powersetCard 2).filter (fun P=>∀ i∈P,∀ j∈P,i≠j→farSites i j)

theorem farPairs_univ_card : (farPairs (Finset.univ : Finset (Fin 7))).card=7 := by decide

theorem triple_farPairs_card : ∀ A : Finset (Fin 7), C4Allowed A → A.card=3 → (farPairs A).card=2 := by
  decide

private theorem farPairs_mono {A B : Finset (Fin 7)} (ab : A⊆B) : farPairs A ⊆ farPairs B := by
  intro P pm
  obtain ⟨mem,cond⟩ := Finset.mem_filter.mp pm
  obtain ⟨sub,pc⟩ := Finset.mem_powersetCard.mp mem
  exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨sub.trans ab,pc⟩,cond⟩

theorem triple_contacts_at_most_three (H : Hole G 7) (h4 : FourCycleFree G)
    (D : Finset V) (off : ∀ x∈D,Outside H.c x)
    (three : ∀ x∈D,(contactSet H x).card=3) : D.card≤3 := by
  classical
  let F (x : V) := farPairs (contactSet H x)
  have each (x : V) (xm : x∈D) : (F x).card=2 :=
    triple_farPairs_card _ (contacts_are_allowed H h4 x (off x xm)) (three x xm)
  have dis : Set.PairwiseDisjoint (D : Set V) F := by
    intro x xm y ym ne
    apply Finset.disjoint_left.mpr
    intro P px py
    have p1 := Finset.mem_powersetCard.mp (Finset.mem_filter.mp px).1
    have p2 := Finset.mem_powersetCard.mp (Finset.mem_filter.mp py).1
    have le : P.card≤(contactSet H x ∩ contactSet H y).card :=
      Finset.card_le_card (fun j jm=>Finset.mem_inter.mpr ⟨p1.1 jm,p2.1 jm⟩)
    have ub := disjoint_contact_pairs H h4 ne
    omega
  have packed : (D.biUnion F).card=2*D.card := by
    rw [Finset.card_biUnion dis,Finset.sum_congr rfl each]
    simp [Nat.mul_comm]
  have sub : D.biUnion F ⊆ farPairs Finset.univ := by
    intro P pm
    obtain ⟨x,_,px⟩ := Finset.mem_biUnion.mp pm
    exact farPairs_mono (Finset.subset_univ _) px
  have max := Finset.card_le_card sub
  rw [packed,farPairs_univ_card] at max
  omega

theorem all_multis_triple_mean_four (H : Hole G 7) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (triple : ∀ x∈multiVertices H,(contactSet H x).card=3) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  apply mean_four_of_multi_degree_budget H h4 h9 dom
  let D := multiVertices H
  have out (x : V) (xm : x∈D) : Outside H.c x := (Finset.mem_filter.mp xm).2.1
  have max := triple_contacts_at_most_three H h4 D out triple
  have budget : (∑ x∈D,row G x Finset.univ)≤4*D.card := by
    calc
      _ ≤ ∑ x∈D,(4:Nat) := by
        apply Finset.sum_le_sum
        intro x xm
        have allowed := contacts_are_allowed H h4 x (out x xm)
        have hi := exterior_degree_capacity H h4 dom x (out x xm)
        have eq := split_degree_contacts H x
        have three := triple x xm
        obtain ⟨c2,cl⟩|⟨c3,cl⟩ := geometry_cap _ allowed (by omega)
        · omega
        · omega
      _ = _ := by simp [Nat.mul_comm]
  change (∑ x∈D,row G x Finset.univ)≤2*D.card+7
  omega

#print axioms triple_contacts_at_most_three
#print axioms all_multis_triple_mean_four
end Graffiti133MultiC7
