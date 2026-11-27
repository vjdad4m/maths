import NestedCoreCleanArms133
namespace Graffiti133NestedFour
open SimpleGraph Finset Graffiti133 Graffiti133MultiWeighted
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem branch_from_induced_edge_excess (W : Finset V)
    (hi : W.card<(G.induce (W : Set V)).edgeFinset.card) : Nonempty (Branch G (W : Set V)) := by
  classical
  let E (T : Finset V) := (G.induce (T : Set V)).edgeFinset.card
  let S : Finset (Finset V) := Finset.univ.filter (fun T : Finset V=>T⊆W ∧ T.card<E T)
  have mem (T : Finset V) : T∈S↔T⊆W ∧ T.card<E T := by simp [S]
  obtain ⟨T,tm,min⟩ := Finset.exists_min_image S Finset.card ⟨W,(mem W).mpr ⟨Subset.rfl,hi⟩⟩
  obtain ⟨tw,ht⟩ := (mem T).mp tm
  let J := G.induce (T : Set V)
  have two (x : (T : Set V)) : 2≤J.degree x := by
    by_contra! small
    let U := T.erase x.val
    have ut : U⊆T := Finset.erase_subset _ _
    have su : U.card+1=T.card := Finset.card_erase_add_one x.property
    have eu : E U≤U.card := by
      by_contra! pu
      have hh := min U ((mem U).mpr ⟨ut.trans tw,pu⟩)
      omega
    have d := (actual_induced_delta (G:=G) T x).1
    change E U+J.degree x=E T at d
    omega
  have three : ∃ x : (T : Set V),2<J.degree x := by
    by_contra! no
    have b := Finset.sum_le_sum (s:=(Finset.univ : Finset (T : Set V))) (fun x _=>no x)
    have sum := SimpleGraph.sum_degrees_eq_twice_card_edges J
    have card : Fintype.card (T : Set V)=T.card := Fintype.card_coe T
    rw [Finset.sum_const,Finset.card_univ,card,smul_eq_mul] at b
    rw [sum] at b
    change 2*E T≤T.card*2 at b
    omega
  obtain ⟨v,vd⟩ := three
  rw [←J.card_neighborFinset_eq_degree] at vd
  obtain ⟨x,xm,y,ym,z,zm,xy,xz,yz⟩ := Finset.two_lt_card.mp vd
  have nx := (J.mem_neighborFinset _ _).mp xm
  have ny := (J.mem_neighborFinset _ _).mp ym
  have nz := (J.mem_neighborFinset _ _).mp zm
  have onward (x : (T : Set V)) (xv : J.Adj v x) :
      ∃ u : (T : Set V),u≠v ∧ J.Adj x u := by
    have xx := two x
    rw [←J.card_neighborFinset_eq_degree] at xx
    have vm : v∈J.neighborFinset x := (J.mem_neighborFinset _ _).mpr xv.symm
    have c := Finset.card_erase_add_one vm
    have pos : 0<((J.neighborFinset x).erase v).card := by omega
    obtain ⟨u,um⟩ := Finset.card_pos.mp pos
    exact ⟨u,(Finset.mem_erase.mp um).1,(J.mem_neighborFinset _ _).mp (Finset.mem_erase.mp um).2⟩
  refine ⟨⟨v.val,x.val,y.val,z.val,tw v.property,tw x.property,tw y.property,tw z.property,
    nx,ny,nz,(fun e=>xy (Subtype.ext e)),(fun e=>xz (Subtype.ext e)),(fun e=>yz (Subtype.ext e)),?_⟩⟩
  intro w hw
  have lift (q : (T : Set V)) (qa : J.Adj v q) :
      ∃ u∈(W : Set V),u≠v.val ∧ G.Adj q.val u := by
    obtain ⟨u,ne,adj⟩ := onward q qa
    exact ⟨u.val,tw u.property,fun e=>ne (Subtype.ext e),adj⟩
  rcases hw with rfl|rfl|rfl
  · exact lift x nx
  · exact lift y ny
  · exact lift z nz

theorem P9_of_two_outer_edge_excesses (X Y A : Finset V)
    (small : A.card≤5) (h4 : FourCycleFree G)
    (tag : V→V) (range : ∀ x∈X∪Y,tag x∈A) (off : ∀ x∈X∪Y,x∉A)
    (tri : ∀ a∈X∪Y,∀ b∈X∪Y,∀ c∈X∪Y,G.Adj a b→G.Adj b c→¬G.Adj a c)
    (proper : ∀ a∈X∪Y,∀ b∈X∪Y,G.Adj a b→tag a≠tag b)
    (gate : ∀ x∈X∪Y,∀ a∈A,G.Adj a x↔tag x=a)
    (dis : Disjoint X Y) (anti : ∀ x∈X,∀ y∈Y,¬G.Adj x y)
    (hx : X.card<(G.induce (X : Set V)).edgeFinset.card)
    (hy : Y.card<(G.induce (Y : Set V)).edgeFinset.card) :
    ∃ f : Fin 9→V,InducedPath G f := by
  have bound (x : V) : x∈((↑X : Set V) ∪ (↑Y : Set V)) → x∈X∪Y := by simp
  obtain ⟨BX⟩ := branch_from_induced_edge_excess X hx
  obtain ⟨BY⟩ := branch_from_induced_edge_excess Y hy
  refine P9_of_two_outer_branches A small h4 tag ?_ ?_ ?_ ?_ ?_ ?_ anti BX BY
  · intro x xm; exact range x (bound x xm)
  · intro x xm; exact off x (bound x xm)
  · intro a am b bm c cm; exact tri a (bound a am) b (bound b bm) c (bound c cm)
  · intro a am b bm; exact proper a (bound a am) b (bound b bm)
  · intro x xm; exact gate x (bound x xm)
  · exact Finset.disjoint_coe.mpr dis

#print axioms branch_from_induced_edge_excess
#print axioms P9_of_two_outer_edge_excesses
end Graffiti133NestedFour
