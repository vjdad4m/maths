import BicycleThetaCanonical133
import BicycleDumbCanonical133
import BicycleShapeCatalog133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Graffiti133NoFive
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem theta_motif_exclusion (H : Hole G 7) (h4 : FourCycleFree G)
    (a b c : Nat) (key : (a,b,c)∈thetaKeys)
    (f : Fin (2+(a-1)+(b-1)+(c-1)) → V) (inj : Function.Injective f)
    (outside : ∀ i,Outside H.c (f i))
    (single : ∀ i,∃ k,∀ j,G.Adj (f i) (H.c j) ↔ k=j)
    (edge : ∀ i j,G.Adj (f i) (f j) ↔ thetaRelation a b c i.val j.val=true) :
    ∃ p : Fin 9 → V, InducedPath G p := by
  choose site attach using single
  simp only [thetaKeys,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at key
  rcases key with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 1 4 4) edge Theta144.labeling
      (fun i j e=>Theta144.canonical_rows.1 i j e) Theta144.canonical_rows.2
      Theta144.distanceTwo_checked Theta144.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 1 4 5) edge Theta145.labeling
      (fun i j e=>Theta145.canonical_rows.1 i j e) Theta145.canonical_rows.2
      Theta145.distanceTwo_checked Theta145.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 2 3 3) edge Theta233.labeling
      (fun i j e=>Theta233.canonical_rows.1 i j e) Theta233.canonical_rows.2
      Theta233.distanceTwo_checked Theta233.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 2 3 4) edge Theta234.labeling
      (fun i j e=>Theta234.canonical_rows.1 i j e) Theta234.canonical_rows.2
      Theta234.distanceTwo_checked Theta234.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 2 3 5) edge Theta235.labeling
      (fun i j e=>Theta235.canonical_rows.1 i j e) Theta235.canonical_rows.2
      Theta235.distanceTwo_checked Theta235.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 2 3 6) edge Theta236.labeling
      (fun i j e=>Theta236.canonical_rows.1 i j e) Theta236.canonical_rows.2
      Theta236.distanceTwo_checked Theta236.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 2 4 4) edge Theta244.labeling
      (fun i j e=>Theta244.canonical_rows.1 i j e) Theta244.canonical_rows.2
      Theta244.distanceTwo_checked Theta244.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 2 4 5) edge Theta245.labeling
      (fun i j e=>Theta245.canonical_rows.1 i j e) Theta245.canonical_rows.2
      Theta245.distanceTwo_checked Theta245.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 3 3 3) edge Theta333.labeling
      (fun i j e=>Theta333.canonical_rows.1 i j e) Theta333.canonical_rows.2
      Theta333.distanceTwo_checked Theta333.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 3 3 4) edge Theta334.labeling
      (fun i j e=>Theta334.canonical_rows.1 i j e) Theta334.canonical_rows.2
      Theta334.distanceTwo_checked Theta334.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 3 3 5) edge Theta335.labeling
      (fun i j e=>Theta335.canonical_rows.1 i j e) Theta335.canonical_rows.2
      Theta335.distanceTwo_checked Theta335.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 3 3 6) edge Theta336.labeling
      (fun i j e=>Theta336.canonical_rows.1 i j e) Theta336.canonical_rows.2
      Theta336.distanceTwo_checked Theta336.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 3 4 4) edge Theta344.labeling
      (fun i j e=>Theta344.canonical_rows.1 i j e) Theta344.canonical_rows.2
      Theta344.distanceTwo_checked Theta344.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 3 4 5) edge Theta345.labeling
      (fun i j e=>Theta345.canonical_rows.1 i j e) Theta345.canonical_rows.2
      Theta345.distanceTwo_checked Theta345.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 4 4 4) edge Theta444.labeling
      (fun i j e=>Theta444.canonical_rows.1 i j e) Theta444.canonical_rows.2
      Theta444.distanceTwo_checked Theta444.checked
  · exact hole_canonical_shape_has_nine (by decide) h4 H f inj outside site attach
      (thetaRelation 4 4 5) edge Theta445.labeling
      (fun i j e=>Theta445.canonical_rows.1 i j e) Theta445.canonical_rows.2
      Theta445.distanceTwo_checked Theta445.checked

theorem no_two_branch_bicycle_of_singleton_seven
    {U : Type*} [Fintype U] (J : SimpleGraph U) [DecidableRel J.Adj]
    (embed : U → V) (ie : Function.Injective embed)
    (ind : ∀ x y,J.Adj x y ↔ G.Adj (embed x) (embed y))
    (H : Hole G 7) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9 → V, InducedPath G p)
    (outside : ∀ z,Outside H.c (embed z))
    (singleton : ∀ z, ∃ k, ∀ j,G.Adj (embed z) (H.c j) ↔ k=j)
    (noTri : ∀ a b c, J.Adj a b → J.Adj b c → J.Adj c a → False)
    (hc : J.Connected) (u v : U) (uv : u≠v)
    (du : J.degree u=3) (dv : J.degree v=3)
    (d2 : ∀ x, x≠u → x≠v → J.degree x=2) : False := by
  have four : FourCycleFree J := by
    intro a b c d ne ac bc ad bd
    exact ie (h4 _ _ _ _ (ie.ne ne) ((ind _ _).mp ac) ((ind _ _).mp bc) ((ind _ _).mp ad) ((ind _ _).mp bd))
  have nine : ¬∃ p : Fin 9 → U, InducedPath J p := by
    rintro ⟨p,hp⟩
    exact h9 ⟨embed ∘ p,ie.comp hp.1,fun i j lt=>(ind _ _).symm.trans (hp.2 i j lt)⟩
  rcases two_degree_three_has_relay_networks hc uv du dv d2 with l|r
  · obtain ⟨P⟩ := l
    obtain ⟨a,b,c,key,f,fi,edge⟩ := P.canonical_theta uv noTri four nine
    exact h9 (theta_motif_exclusion H h4 a b c key (embed ∘ f) (ie.comp fi)
      (fun i=>outside (f i)) (fun i=>singleton (f i)) (fun i j=>(ind _ _).symm.trans (edge i j)))
  · obtain ⟨P⟩ := r
    obtain ⟨f,fi,edge⟩ := P.canonical_dumb uv noTri four nine
    choose site contact using singleton
    exact h9 (hole_canonical_shape_has_nine (by decide) h4 H (embed ∘ f) (ie.comp fi)
      (fun i=>outside (f i)) (site ∘ f) (fun i=>contact (f i))
      (dumbRelation 5 5 1) (fun i j=>(ind _ _).symm.trans (edge i j)) Dumb551.labeling
      (fun i j e=>Dumb551.canonical_rows.1 i j e) Dumb551.canonical_rows.2
      Dumb551.distanceTwo_checked Dumb551.checked)

#print axioms no_two_branch_bicycle_of_singleton_seven
end Graffiti133Bicycle
