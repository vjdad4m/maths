import BicycleSingletonMean133

namespace Graffiti133TriangleDeletion
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


private theorem no_single_bicycle_embed
    {U : Type*} [Fintype U] (J : SimpleGraph U) [DecidableRel J.Adj]
    (f : U → V) (fi : Function.Injective f)
    (ind : ∀ x y,J.Adj x y ↔ G.Adj (f x) (f y))
    (H : Hole G 7) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9 → V, InducedPath G p)
    (outside : ∀ z,Outside H.c (f z))
    (single : ∀ z, ∃ k, ∀ j,G.Adj (f z) (H.c j) ↔ k=j)
    (tri : ∀ a b c, J.Adj a b → J.Adj b c → J.Adj c a → False)
    (u : U) (du : J.degree u=4) (d2 : ∀ x≠u,J.degree x=2) : False := by
  have four : FourCycleFree J := by
    intro a b c d ne ac bc ad bd
    exact fi (h4 _ _ _ _ (fi.ne ne) ((ind _ _).mp ac) ((ind _ _).mp bc) ((ind _ _).mp ad) ((ind _ _).mp bd))
  have nine : ¬∃ p : Fin 9 → U, InducedPath J p := by
    rintro ⟨p,hp⟩
    exact h9 ⟨f ∘ p,fi.comp hp.1,fun i j lt=>(ind _ _).symm.trans (hp.2 i j lt)⟩
  choose site contact using single
  rcases one_degree_four_yields_a_canonical_figure (G := J) u du d2 tri four nine with
    ⟨p,pi,edges⟩|⟨p,pi,edges⟩
  · exact h9 (hole_canonical_shape_has_nine (by decide) h4 H (f ∘ p) (fi.comp pi)
      (fun i=>outside (p i)) (site ∘ p) (fun i=>contact (p i))
      (dumbRelation 5 5 0) (fun i j=>(ind _ _).symm.trans (edges i j)) Dumb550.labeling
      (fun i j e=>Dumb550.canonical_rows.1 i j e) Dumb550.canonical_rows.2
      Dumb550.distanceTwo_checked Dumb550.checked)
  · exact h9 (hole_canonical_shape_has_nine (by decide) h4 H (f ∘ p) (fi.comp pi)
      (fun i=>outside (p i)) (site ∘ p) (fun i=>contact (p i))
      (dumbRelation 5 6 0) (fun i j=>(ind _ _).symm.trans (edges i j)) Dumb560.labeling
      (fun i j e=>Dumb560.canonical_rows.1 i j e) Dumb560.canonical_rows.2
      Dumb560.distanceTwo_checked Dumb560.checked)

theorem local_exterior_edges (H : Hole G 7) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9 → V, InducedPath G p)
    (site : ∀ x, Outside H.c x → ∃ i, ∀j, G.Adj x (H.c j) ↔ j=i)
    (O : Finset V) (out : ∀ x∈O,Outside H.c x)
    (tri : ∀ a b c, a∈O → b∈O → c∈O → G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (G.induce (O : Set V)).edgeFinset.card ≤ O.card := by
  classical
  let E := G.induce (O : Set V)
  by_contra! h
  have over : Fintype.card (O : Set V)<E.edgeFinset.card := by
    rw [show Fintype.card (O : Set V)=O.card from Fintype.card_coe O]
    exact h
  obtain ⟨S,plus,min,erase⟩ := choose_minimum_positive_excess E over
  let J := E.induce (S : Set (O : Set V))
  let f (x : (S : Set (O : Set V))) : V := x.val.val
  have fi : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have ind (x y : (S : Set (O : Set V))) : J.Adj x y ↔ G.Adj (f x) (f y) := Iff.rfl
  have outside (x : (S : Set (O : Set V))) : Outside H.c (f x) := out _ x.val.property
  have single (x : (S : Set (O : Set V))) :
      ∃ i, ∀ j, G.Adj (f x) (H.c j) ↔ i=j := by
    obtain ⟨i,hi⟩ := site _ (outside x)
    exact ⟨i,fun j=>(hi j).trans eq_comm⟩
  have h4J : FourCycleFree J := by
    intro a b c d ne ac bc ad bd
    exact fi (h4 _ _ _ _ (fi.ne ne) ((ind _ _).mp ac) ((ind _ _).mp bc) ((ind _ _).mp ad) ((ind _ _).mp bd))
  have triJ (a b c) : J.Adj a b → J.Adj b c → J.Adj c a → False :=
    tri _ _ _ a.val.property b.val.property c.val.property
  have hc : J.Connected := induced_minimal_excess_connected E S plus min
  have co : Fintype.card (S : Set (O : Set V))<J.edgeFinset.card := by
    rw [show Fintype.card (S : Set (O : Set V))=S.card from Fintype.card_coe S]
    exact plus
  rcases (vertex_minimal_profile J triJ h4J co erase).2 with ⟨u,du,d2⟩|⟨u,v,uv,du,dv,d2⟩
  · exact no_single_bicycle_embed J f fi ind H h4 h9 outside single triJ u du d2
  · exact no_two_branch_bicycle_of_singleton_seven J f fi ind H h4 h9 outside single triJ hc u v uv du dv d2

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

private theorem row_split (A B : Finset V) (sub : B⊆A) (x : V) :
    row G x A = row G x (A\B)+row G x B := by
  classical
  unfold row
  exact (Finset.sum_sdiff sub).symm

theorem triangle_transversal_mean_four (H : Hole G 7)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9 → V, InducedPath G p)
    (site : ∀ x, Outside H.c x → ∃ i, ∀j, G.Adj x (H.c j) ↔ j=i)
    (D T : Finset V)
    (dExt : ∀ x∈D,Outside H.c x)
    (dDeg : ∀ x∈D,row G x (Finset.univ \ Finset.univ.image H.c) ≤ 2)
    (remaining : ∀ a b c, Outside H.c a → Outside H.c b → Outside H.c c →
      a∉D → b∉D → c∉D → G.Adj a b → G.Adj b c → G.Adj c a → False)
    (tri : ∀ v∈T, ∃ a b,G.Adj v a ∧ G.Adj v b ∧ G.Adj a b)
    (balance : 2*D.card≤T.card) :
    (∑ v : V, localIndependence G v) ≤ 4*Fintype.card V := by
  classical
  let C : Finset V := Finset.univ.image H.c
  let O : Finset V := Finset.univ \ C
  let K : Finset V := O \ D
  have old : C.card=7 := by rw [Finset.card_image_of_injective _ H.inj]; simp
  have size : O.card+7=Fintype.card V := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
    rw [old,Finset.card_univ] at h
    exact h
  have out (v : V) (hv : v∈O) : Outside H.c v := by
    intro i e
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
  have do' : D⊆O := by
    intro x hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    rintro mem
    obtain ⟨i,_,eq⟩ := Finset.mem_image.mp mem
    exact dExt x hx i eq.symm
  have kSize : K.card+D.card=O.card := Finset.card_sdiff_add_card_eq_card do'
  have ko (v : V) (hv : v∈K) : Outside H.c v := out v (Finset.mem_sdiff.mp hv).1
  have noTri (a b c : V) (ha : a∈K) (hb : b∈K) (hc : c∈K) :
      G.Adj a b → G.Adj b c → G.Adj c a → False :=
    remaining _ _ _ (ko _ ha) (ko _ hb) (ko _ hc)
      (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).2 (Finset.mem_sdiff.mp hc).2
  have arcsK : (∑ x∈K,row G x K)≤2*K.card := by
    -- apply exterior sparsity to the induced graph on the kept vertices below.
    let J := G.induce (K : Set V)
    have edges : J.edgeFinset.card ≤ K.card := local_exterior_edges H h4 h9 site K ko noTri
    calc
      (∑ x∈K,row G x K) = ∑ x : (K : Set V), row G x.val K := (Finset.sum_attach K _).symm
      _ = ∑ x : (K : Set V), J.degree x := Finset.sum_congr rfl (fun x _=>(degree_induced_row K x).symm)
      _ = 2*J.edgeFinset.card := J.sum_degrees_eq_twice_card_edges
      _ ≤ 2*K.card := Nat.mul_le_mul_left 2 edges
  have arcsD : (∑ x∈D,row G x O)≤2*D.card := by
    calc
      _ ≤ ∑ x∈D,(2:Nat) := Finset.sum_le_sum dDeg
      _ = _ := by simp [Nat.mul_comm]
  have arcsO : (∑ x∈O,row G x O)≤2*O.card+2*D.card := by
    have part (f : V→Nat) : (∑ x∈O,f x)=(∑ x∈K,f x)+(∑ x∈D,f x) := (Finset.sum_sdiff do').symm
    have cut := row_symm (G:=G) K D
    have dSplit := Finset.sum_congr (s₁ := D) rfl (fun x _ => row_split (G:=G) O D do' x)
    change (∑ x∈D,row G x O)=(∑ x∈D,(row G x K+row G x D)) at dSplit
    rw [Finset.sum_add_distrib] at dSplit
    rw [part (fun x=>row G x O)]
    simp_rw [row_split (G:=G) O D do',Finset.sum_add_distrib]
    change ((∑ x∈K,row G x K)+(∑ x∈K,row G x D))+
      ((∑ x∈D,row G x K)+(∑ x∈D,row G x D))≤_
    omega
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
  have budget : (∑ v : V,row G v Finset.univ)≤4*Fintype.card V+2*D.card := by
    rw [split (fun v=>row G v Finset.univ)]
    simp_rw [rows,Finset.sum_add_distrib]
    rw [cSum,row_symm (G:=G) C O,weight]
    omega
  have point (v : V) : localIndependence G v+(if v∈T then 1 else 0)≤row G v Finset.univ := by
    by_cases inT : v∈T
    · obtain ⟨a,b,va,vb,ab⟩ := tri v inT
      simpa [inT] using local_extra v a b va vb ab
    · simpa [inT] using local_bound (G:=G) v
  have sb := Finset.sum_le_sum (s:=Finset.univ) (fun v _=>point v)
  rw [Finset.sum_add_distrib] at sb
  have cardT : (∑ v : V,(if v∈T then (1:Nat) else 0))=T.card := by
    rw [←Finset.card_filter]
    simp
  rw [cardT] at sb
  omega

#print axioms triangle_transversal_mean_four

theorem one_exterior_triangle_low_degree_mean_four (H : Hole G 7)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9 → V, InducedPath G p)
    (site : ∀ x, Outside H.c x → ∃ i, ∀j, G.Adj x (H.c j) ↔ j=i)
    (p a b : V) (hp : Outside H.c p)
    (pa : G.Adj p a) (ab : G.Adj a b) (bp : G.Adj b p)
    (degree : row G p (Finset.univ \ Finset.univ.image H.c) ≤ 2)
    (hitsAll : ∀ x y z, Outside H.c x → Outside H.c y → Outside H.c z →
       G.Adj x y → G.Adj y z → G.Adj z x → x=p ∨ y=p ∨ z=p) :
    (∑ v : V, localIndependence G v) ≤ 4*Fintype.card V := by
  classical
  apply triangle_transversal_mean_four H h4 h9 site {p} {p,a,b}
  · intro x hx
    rcases Finset.mem_singleton.mp hx with rfl
    exact hp
  · intro x hx
    rcases Finset.mem_singleton.mp hx with rfl
    exact degree
  · intro x y z hx hy hz nx ny nz xy yz zx
    rcases hitsAll x y z hx hy hz xy yz zx with rfl|rfl|rfl
    · exact nx (Finset.mem_singleton_self _)
    · exact ny (Finset.mem_singleton_self _)
    · exact nz (Finset.mem_singleton_self _)
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨a,b,pa,bp.symm,ab⟩
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨b,p,ab,pa.symm,bp⟩
      · rcases Finset.mem_singleton.mp hx with rfl
        exact ⟨p,a,bp,ab.symm,pa⟩
  · simp [pa.ne,ab.ne,bp.ne.symm]

#print axioms one_exterior_triangle_low_degree_mean_four
end Graffiti133TriangleDeletion
