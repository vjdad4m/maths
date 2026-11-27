import BicycleTwoDegreeExclude133
import BicycleFigureCanonical133
import BicycleMinimalProfile133
import BicycleMinimumExcess133
import BicycleMinimumConnected133
import BicycleCharge133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Graffiti133NoFive Graffiti133BicycleCharge Finset
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

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

theorem singleton_seven_exterior_edges (H : Hole G 7) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9 → V, InducedPath G p)
    (site : ∀ x, Outside H.c x → ∃ i, ∀j, G.Adj x (H.c j) ↔ j=i)
    (tri : ∀ a b c, Outside H.c a → Outside H.c b → Outside H.c c →
      G.Adj a b → G.Adj b c → G.Adj c a → False)
    (O : Finset V) (out : ∀ x∈O,Outside H.c x) :
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
    tri _ _ _ (outside a) (outside b) (outside c)
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

theorem singleton_triangle_free_seven_mean_four (H : Hole G 7) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9 → V, InducedPath G p)
    (site : ∀ x, Outside H.c x → ∃ i, ∀j, G.Adj x (H.c j) ↔ j=i)
    (tri : ∀ a b c, Outside H.c a → Outside H.c b → Outside H.c c →
      G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (∑ v : V, localIndependence G v) ≤ 4*Fintype.card V := by
  classical
  apply singleton_contact_charge H site
  let O := ((Finset.univ : Finset V) \ Finset.univ.image H.c)
  change (∑ x∈O,row G x O)≤2*O.card
  have out (x : V) (hx : x∈O) : Outside H.c x := by
    intro i e
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
  have size := singleton_seven_exterior_edges H h4 h9 site tri O out
  let J := G.induce (O : Set V)
  calc
    (∑ x∈O,row G x O) = ∑ x : (O : Set V), row G x.val O := (Finset.sum_attach O _).symm
    _ = ∑ x : (O : Set V), J.degree x := Finset.sum_congr rfl (fun x _=>(degree_induced_row O x).symm)
    _ = 2*J.edgeFinset.card := J.sum_degrees_eq_twice_card_edges
    _ ≤ 2*O.card := Nat.mul_le_mul_left 2 size

#print axioms singleton_triangle_free_seven_mean_four
end Graffiti133Bicycle
