import ArticulationEight189
namespace Graffiti189LongestPath.CrossSaturation.ArticulationPair
open SimpleGraph SimpleGraph.Walk Finset
open private nonport_inside_left left_boundary' from ArticulationEight189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {c : V} (S : Graffiti189LongestPath.CrossSaturation.ArticulationPair G c)
set_option linter.unusedSectionVars false

theorem inside_card_eq_degree_induce (L : Finset V) (x : ↑(↑L : Set V)) :
    (inside G L x.val).card = (G.induce (↑L : Set V)).degree x := by
  classical
  rw [←card_neighborSet_eq_degree, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact {
    toFun := fun z => ⟨⟨z.val,(mem_filter.mp z.property).1⟩,(mem_filter.mp z.property).2⟩
    invFun := fun z => ⟨z.val.val,mem_filter.mpr ⟨z.val.property,z.property⟩⟩
    left_inv := fun z => by rfl
    right_inv := fun z => by rfl }

theorem eight_nonsingleton_high_internal_degree (hc : G.Connected)
    (even : ∀ v, (EvenFrom G v).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (eight : S.L.card=8) (rightTwo : 2≤S.R.card) :
    ∀ x∈S.L,4≤G.degree x → 4≤(inside G S.L x).card := by
  classical
  obtain ⟨n,allr,port⟩ := S.eight_nonsingleton_port_universal hc even degree eight rightTwo
  intro x xl high
  by_cases cx : G.Adj c x
  · have sub : S.L.erase x ⊆ inside G S.L x := by
      intro z zz
      obtain ⟨ne,zl⟩ := mem_erase.mp zz
      exact mem_filter.mpr ⟨zl,(port x xl cx z zl).resolve_left ne⟩
    have m := card_le_card sub
    rw [card_erase_of_mem xl,eight] at m
    omega
  exact nonport_inside_left S x xl high cx

theorem eight_nonsingleton_every_other_has_residual_neighbor (hc : G.Connected)
    (even : ∀ v, (EvenFrom G v).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (eight : S.L.card=8) (rightTwo : 2≤S.R.card)
    {x : V} (xl : x∈S.L) (cx : G.Adj c x) :
    ∀ z∈S.L.erase x, ∃ y∈S.L.erase x,G.Adj z y := by
  classical
  obtain ⟨n,allr,port⟩ := S.eight_nonsingleton_port_universal hc even degree eight rightTwo
  intro z zm
  obtain ⟨zx,zl⟩ := mem_erase.mp zm
  apply Classical.byContradiction
  intro bad
  have cz : ¬G.Adj c z := by
    intro cz
    have q : 0<(S.L.erase x |>.erase z).card := by
      rw [card_erase_of_mem zm,card_erase_of_mem xl,eight]
      decide
    obtain ⟨w,wm⟩ := card_pos.mp q
    obtain ⟨wz,we⟩ := mem_erase.mp wm
    exact bad ⟨w,we,(port z zl cz w (mem_of_mem_erase we)).resolve_left wz⟩
  have xz := (port x xl cx z zl).resolve_left zx
  let A := (univ : Finset V).erase z
  let B : Finset V := {z}
  have asub : x∈A := mem_erase.mpr ⟨zx.symm,mem_univ _⟩
  have bsub : z∈B := mem_singleton_self _
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro w wa wb
    have e : w=z := mem_singleton.mp wb
    exact (mem_erase.mp wa).1 e
  have cov (w : V) : w∈A ∨ w∈B := by
    by_cases wq : w=z <;> simp [A,B,wq]
  have single (u : V) (ua : u∈A) (v : V) (vb : v∈B) (uv : G.Adj u v) : u=x ∧ v=z := by
    have vz := mem_singleton.mp vb
    subst v
    rcases left_boundary' S zl uv.symm with h|ul
    · exact (cz (h ▸ uv)).elim
    refine ⟨?_,rfl⟩
    by_contra ux
    exact bad ⟨u,mem_erase.mpr ⟨ux,ul⟩,uv.symm⟩
  have m := order_le_twice_budget_plus_two_of_single_bridge hc 4 even A B dis cov asub bsub xz single
  omega

/-- A rooted spanning path of the induced side extends across the chosen
port to a path rooted at the articulation in the ambient graph. -/
theorem prefix_induced_side_path {x : V} (xl : x∈S.L) (cx : G.Adj c x)
    (rooted : ∃ y,∃ p : (G.induce (↑S.L : Set V)).Walk ⟨x,xl⟩ y,
      p.IsPath ∧ ∀ z,z∈p.support) :
    ∃ z,∃ q : G.Walk c z,q.IsPath ∧ ∀ u,u∈q.support ↔ u=c ∨ u∈S.L := by
  classical
  obtain ⟨z,p,pp,ps⟩ := rooted
  let f : (G.induce (↑S.L : Set V)) →g G := {toFun := Subtype.val, map_rel' := fun h=>h}
  let q := p.map f
  have qs (u : V) : u∈q.support ↔ u∈S.L := by
    change u∈(p.map f).support ↔ _
    rw [support_map,List.mem_map]
    constructor
    · rintro ⟨w,_,rfl⟩
      exact w.property
    · intro uL
      exact ⟨⟨u,uL⟩,ps _,rfl⟩
  have qp : q.IsPath := by
    rw [isPath_def]
    change (p.map f).support.Nodup
    rw [support_map]
    exact pp.support_nodup.map Subtype.val_injective
  exact ⟨z.val,Walk.cons cx q,qp.cons (fun e=>S.offL ((qs c).mp e)),
    fun u=>by simp only [support_cons,List.mem_cons,qs]⟩

#print axioms eight_nonsingleton_high_internal_degree
#print axioms eight_nonsingleton_every_other_has_residual_neighbor
#print axioms prefix_induced_side_path
end Graffiti189LongestPath.CrossSaturation.ArticulationPair
