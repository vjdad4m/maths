import ArticulationGeneralExtreme189
import ArticulationGeneralSmall189
import OreClosure189

universe u
namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
open private left_boundary' from ArticulationEight189
open private nonport_inside_left_general from ArticulationGeneralExtreme189
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

namespace ArticulationPair
variable {c : V} (S : ArticulationPair G c)

theorem extremal_nonsingleton_high_internal_degree (hc : G.Connected) (n : ℕ) (n2 : 2≤n)
    (even : ∀ v, (EvenFrom G v).card≤n+1)
    (degree : ∀ u v : V,u≠v → n≤G.degree u ∨ n≤G.degree v)
    (eight : S.L.card=2*n) (rightTwo : 2≤S.R.card) :
    ∀ x∈S.L,n≤G.degree x → n≤(inside G S.L x).card := by
  classical
  obtain ⟨order,allr,port⟩ := S.extremal_nonsingleton_port_universal hc n n2 even degree eight rightTwo
  intro x xl high
  by_cases cx : G.Adj c x
  · have sub : S.L.erase x ⊆ inside G S.L x := by
      intro z zz
      obtain ⟨ne,zl⟩ := mem_erase.mp zz
      exact mem_filter.mpr ⟨zl,(port x xl cx z zl).resolve_left ne⟩
    have m := card_le_card sub
    rw [card_erase_of_mem xl,eight] at m
    omega
  exact nonport_inside_left_general S n x xl high cx

theorem extremal_nonsingleton_every_other_has_residual_neighbor (hc : G.Connected) (n : ℕ) (n2 : 2≤n)
    (even : ∀ v, (EvenFrom G v).card≤n+1)
    (degree : ∀ u v : V,u≠v → n≤G.degree u ∨ n≤G.degree v)
    (eight : S.L.card=2*n) (rightTwo : 2≤S.R.card)
    {x : V} (xl : x∈S.L) (cx : G.Adj c x) :
    ∀ z∈S.L.erase x, ∃ y∈S.L.erase x,G.Adj z y := by
  classical
  obtain ⟨order,allr,port⟩ := S.extremal_nonsingleton_port_universal hc n n2 even degree eight rightTwo
  intro z zm
  obtain ⟨zx,zl⟩ := mem_erase.mp zm
  apply Classical.byContradiction
  intro bad
  have cz : ¬G.Adj c z := by
    intro cz
    have q : 0<(S.L.erase x |>.erase z).card := by
      rw [card_erase_of_mem zm,card_erase_of_mem xl,eight]
      omega
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
  have m := order_le_twice_budget_plus_two_of_single_bridge hc n even A B dis cov asub bsub xz single
  omega
private theorem large_left_rooted_general (ore : RootedClosureAPI.{u})
    (hc : G.Connected) (n : ℕ) (n2 : 2≤n) (even : ∀ x, (EvenFrom G x).card≤n+1)
    (degree : ∀ u v : V,u≠v → n≤G.degree u ∨ n≤G.degree v)
    (eight : S.L.card=2*n) :
    ∃ y,∃ p : G.Walk c y,p.IsPath ∧ ∀ z,z∈p.support ↔ z=c ∨ z∈S.L := by
  classical
  obtain ⟨x,xl,cx⟩ := S.hitL
  obtain ⟨y,yr,cy⟩ := S.hitR
  apply S.prefix_induced_side_path xl cx
  let U := ↑(↑S.L : Set V)
  let J := G.induce (↑S.L : Set V)
  let root : U := ⟨x,xl⟩
  change RootedSpan J root
  have U8 : Fintype.card U=2*n := by
    change Fintype.card {v : V // v∈S.L}=2*n
    rw [Fintype.card_coe,eight]
  have all_case (d : ∀ v : U, n≤J.degree v) : RootedSpan J root := by
    refine close_completed_class ore univ root ?_ ?_
    · intro v _ w _
      have h1 := d v
      have h2 := d w
      omega
    obtain ⟨e,p,pp,ps⟩ := rooted_path_in_clique univ (completeWith_of_mem J univ) (mem_univ root)
    exact ⟨e,p,pp,fun v=>(ps v).mpr (mem_univ _)⟩
  by_cases one : S.R.card≤1
  · have eq : S.R={y} :=
      (eq_of_subset_of_card_le (singleton_subset_iff.mpr yr) (by simpa)).symm
    have hi := S.extremal_singleton_internal_min_degree hc n n2 even degree eight eq
    exact all_case (fun v=>(inside_card_eq_degree_induce (G:=G) S.L v) ▸ hi _ v.property)
  have two : 2≤S.R.card := by omega
  have hi := S.extremal_nonsingleton_high_internal_degree hc n n2 even degree eight two
  have rootHigh : n≤G.degree x := by
    obtain ⟨order,_,port⟩ := S.extremal_nonsingleton_port_universal hc n n2 even degree eight two
    have sub : S.L.erase x ⊆ G.neighborFinset x := by
      intro v vm
      obtain ⟨vx,vl⟩ := mem_erase.mp vm
      exact (mem_neighborFinset _ _ _).mpr ((port x xl cx v vl).resolve_left vx)
    have b := card_le_card sub
    rw [card_neighborFinset_eq_degree,card_erase_of_mem xl,eight] at b
    omega
  by_cases low : ∃ z∈S.L, ¬n≤G.degree z
  · obtain ⟨z,zl,zlow⟩ := low
    have zx : z≠x := fun e=>zlow (e.symm ▸ rootHigh)
    let zz : U := ⟨z,zl⟩
    let A : Finset U := univ.erase zz
    have ha (v : U) (va : v∈A) : n≤J.degree v := by
      have vz : v.val≠z := fun e=>(mem_erase.mp va).1 (Subtype.ext e)
      have dh := (degree _ _ vz).resolve_right zlow
      exact (inside_card_eq_degree_induce (G:=G) S.L v) ▸ hi _ v.property dh
    refine close_completed_class ore A root ?_ ?_
    · intro v vm w wm
      have v4 := ha v vm
      have w4 := ha w wm
      omega
    obtain ⟨w,wm,zw⟩ := S.extremal_nonsingleton_every_other_has_residual_neighbor hc n n2 even degree eight two
      xl cx z (mem_erase.mpr ⟨zx,zl⟩)
    obtain ⟨wx,wl⟩ := mem_erase.mp wm
    let ww : U := ⟨w,wl⟩
    have rz : root≠zz := fun e=>zx.symm (congrArg Subtype.val e)
    have wz : ww≠zz := fun e=>zw.ne.symm (congrArg Subtype.val e)
    have rw' : root≠ww := fun e=>wx.symm (congrArg Subtype.val e)
    exact rooted_path_of_clique_and_outlier (completeWith J A) rz wz rw'
      (completeWith_mono J A (show J.Adj ww zz from zw.symm)) (completeWith_of_mem J A)
  apply all_case
  intro v
  have dh : n≤G.degree v.val := Classical.byContradiction (fun n=>low ⟨v.val,v.property,n⟩)
  exact (inside_card_eq_degree_induce (G:=G) S.L v) ▸ hi _ v.property dh

theorem left_rooted_at_articulation_general (ore : RootedClosureAPI.{u})
    (hc : G.Connected) (n : ℕ) (n2 : 2≤n) (even : ∀ x, (EvenFrom G x).card≤n+1)
    (degree : ∀ u v : V,u≠v → n≤G.degree u ∨ n≤G.degree v) :
    ∃ y,∃ p : G.Walk c y,p.IsPath ∧ ∀ z,z∈p.support ↔ z=c ∨ z∈S.L := by
  have bound := (S.sides_le_two_mul hc n even).1
  by_cases small : S.L.card+1≤2*n
  · exact small_left_rooted_general S ore hc n n2 even degree small
  exact large_left_rooted_general S ore hc n n2 even degree (by omega)

end ArticulationPair

theorem traceable_at_articulation_general_of_rooted_closure (ore : RootedClosureAPI.{u}) (hc : G.Connected) (n : ℕ) (n2 : 2≤n)
    (even : ∀ x, (EvenFrom G x).card≤n+1)
    (degree : ∀ u v : V,u≠v → n≤G.degree u ∨ n≤G.degree v)
    (c : V) (cut : ¬(G.induce {z : V | z≠c}).Connected) : ∃ a, RootedSpan G a := by
  classical
  by_cases small : Fintype.card V≤1
  · have ss := Fintype.card_le_one_iff_subsingleton.mp small
    exact ⟨c,c,Walk.nil,by simp,fun z=>by simp [ss.elim z c]⟩
  obtain ⟨S⟩ := articulation_pair_of_disconnected_general hc c n n2 even degree (by omega) cut
  exact S.splice_rooted (S.left_rooted_at_articulation_general ore hc n n2 even degree)
    (S.swapSides.left_rooted_at_articulation_general ore hc n n2 even degree)


/-- Graffiti.pc #189 for every degree threshold at least two when
deleting one vertex disconnects the graph. The parity bound includes self. -/
theorem traceable_at_articulation_general (hc : G.Connected) (n : ℕ) (n2 : 2≤n)
    (even : ∀ x,(EvenFrom G x).card≤n+1)
    (degree : ∀ u v : V,u≠v → n≤G.degree u ∨ n≤G.degree v)
    (c : V) (cut : ¬(G.induce {z : V | z≠c}).Connected) :
    ∃ a b,∃ p : G.Walk a b,p.IsPath ∧ ∀ z,z∈p.support := by
  let ore : RootedClosureAPI.{u} := by
    intro U _ _ J K _ _ sub root hdeg hp
    exact Graffiti189Ore.rooted_closure sub root hdeg hp
  exact traceable_at_articulation_general_of_rooted_closure ore hc n n2 even degree c cut

#print axioms traceable_at_articulation_general
end Graffiti189LongestPath.CrossSaturation
