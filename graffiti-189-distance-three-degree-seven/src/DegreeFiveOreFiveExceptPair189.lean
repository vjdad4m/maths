import DegreeFiveSevenMixedDrop24189
import DegreeFiveAlternatingRoute189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Complete all missing pairs touching a three-set in an auxiliary induced
five-vertex graph. This is the small endpoint-preserving Ore residual needed
when the two other vertices might form an unfillable low-degree pair. -/
theorem rooted_route_a3_i2_from_induced_degrees {A I : Finset V}
    (a3 : A.card=3) (i2 : I.card=2) (dis : Disjoint A I)
    (dA : ∀ x∈A,3≤(inside G (A∪I) x).card)
    (dI : ∀ x∈I,2≤(inside G (A∪I) x).card) :
    ∃ u∈A,∃ v,RouteOn G (A∪I) u v := by
  classical
  let U := ↑(↑(A∪I) : Set V)
  let J := G.induce (↑(A∪I) : Set V)
  let A' := (univ : Finset U).filter (fun x=>x.val∈A)
  let I' := (univ : Finset U).filter (fun x=>x.val∈I)
  let H : SimpleGraph U :=
    ⟨fun x y=>J.Adj x y ∨ (x≠y ∧ (x∈A' ∨ y∈A')),
      by
        intro x y
        rintro (e|⟨ne,w⟩)
        · exact .inl e.symm
        exact .inr ⟨ne.symm,w.symm⟩,
      by intro x; rintro (e|⟨ne,_⟩); exact J.loopless x e; exact ne rfl⟩
  letI : DecidableRel H.Adj := Classical.decRel _
  have info (P : Finset V) (sub : P⊆A∪I) :
      ((univ : Finset U).filter (fun x=>x.val∈P)).card=P.card := by
    let f := Function.Embedding.subtype (fun x : V=>x∈↑(A∪I))
    have e : (((univ : Finset U).filter (fun x=>x.val∈P)).map f)=P := by
      ext x
      simp only [mem_map,mem_filter,mem_univ,true_and,f,Function.Embedding.subtype_apply]
      constructor
      · rintro ⟨u,um,rfl⟩
        exact um
      intro h
      exact ⟨⟨x,sub h⟩,h,rfl⟩
    have r := congrArg Finset.card e
    rwa [card_map] at r
  have anew : A'.card=3 := (info A (fun _ h=>mem_union_left _ h)).trans a3
  have inew : I'.card=2 := (info I (fun _ h=>mem_union_right _ h)).trans i2
  have sep : Disjoint A' I' := disjoint_left.mpr (fun x xa xi=>
    disjoint_left.mp dis (mem_filter.mp xa).2 (mem_filter.mp xi).2)
  obtain ⟨x,xa⟩ := card_pos.mp (show 0<A'.card by omega)
  obtain ⟨y,yi⟩ := card_pos.mp (show 0<I'.card by omega)
  have edge (u : U) (ua : u∈A') (v : U) (vi : v∈I') : H.Adj u v :=
    .inr ⟨fun e=>disjoint_left.mp sep (e ▸ ua) vi,.inl ua⟩
  have cl : CompleteOn H A' := fun x xa y _ ne=>.inr ⟨ne,.inl xa⟩
  obtain ⟨r,ra,path⟩ := route_clique_join_end_leaf sep cl
    (fun x xa y ym=>edge x xa y (mem_erase.mp ym).2) (show I'.card≤A'.card by omega)
    xa yi (edge x xa y yi)
  have cut : J≤H := fun x y h=>.inl h
  have ndegs (u : U) (ua : u∈A') : 3≤J.degree u := by
    have t := dA u.val (mem_filter.mp ua).2
    rwa [inside_card_eq_degree_induce (G:=G) (A∪I) u] at t
  have ld (u : U) : 2≤J.degree u := by
    rcases mem_union.mp u.property with ua|ui
    · exact (by decide : (2:ℕ)≤3).trans (ndegs u (mem_filter.mpr ⟨mem_univ _,ua⟩))
    have t := dI u.val ui
    rwa [inside_card_eq_degree_induce (G:=G) (A∪I) u] at t
  have ok (u v : U) (e : H.Adj u v) (no : ¬J.Adj u v) :
      Fintype.card U≤J.degree u+J.degree v := by
    have p : J.Adj u v ∨ (u≠v ∧ (u∈A' ∨ v∈A')) := e
    have m : Fintype.card U=5 := by
      have m0 : Fintype.card U = (A∪I).card := Fintype.card_coe (A∪I)
      rw [m0,card_union_of_disjoint dis,a3,i2]
    rcases (p.resolve_left no).2 with t|t
    · have h := ndegs u t
      have k := ld v
      omega
    have h := ndegs v t
    have k := ld u
    omega
  obtain ⟨p,hp,ps⟩ := path
  have cov (u : U) : u∈p.support := by
    apply (ps u).mpr
    rcases mem_union.mp u.property with ua|ui
    · exact mem_union_left _ (show u ∈ A' from mem_filter.mpr ⟨mem_univ _,ua⟩)
    exact mem_union_right _ (show u ∈ I' from mem_filter.mpr ⟨mem_univ _,ui⟩)
  obtain ⟨t,q,hq,qs⟩ := Graffiti189Ore.rooted_closure cut r ok ⟨y,p,hp,cov⟩
  exact ⟨r.val,(mem_filter.mp ra).2,t.val,lift_side_path (A∪I) q hq qs⟩

#print axioms rooted_route_a3_i2_from_induced_degrees
end Graffiti189LongestPath.CrossSaturation
