import UnhitHandleCut

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.OddUncross
open HandleExtension FourRingCutAux
noncomputable section

private theorem acyclic_of_small_triangle_free
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (size : Fintype.card V≤3) (tri : TriangleFree G) : G.IsAcyclic := by
  intro root w c
  let F : Fin w.length→V := fun i=>w.getVert i.val
  have three := c.three_le_length
  have inj : Function.Injective F := by
    intro i j e
    have hi := i.isLt
    have hj := j.isLt
    exact Fin.ext (c.getVert_injOn' (show i.val≤w.length-1 by omega)
      (show j.val≤w.length-1 by omega) e)
  have l := Fintype.card_le_of_injective F inj
  rw [Fintype.card_fin] at l
  have eq : w.length=3 := by omega
  have ab := w.adj_getVert_succ (i:=0) (by omega)
  have bc := w.adj_getVert_succ (i:=1) (by omega)
  have ca := w.adj_getVert_succ (i:=2) (by omega)
  change G.Adj (w.getVert 2) (w.getVert 3) at ca
  have close : w.getVert 3=w.getVert 0 := by
    rw [←eq,Walk.getVert_length,Walk.getVert_zero]
  exact tri _ _ _ ab bc (close ▸ ca)

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable (E : Edges G)

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem singleton_old_acyclic (c : V⊕Bool→Bool)
    (small : ∀ x y, Edges.oldColor c x=true→Edges.oldColor c y=true→x=y) :
    (shoreGraph E.host c).IsAcyclic := by
  classical
  let f : Shore c→Option Bool := fun a=>
    match a.val with | Sum.inl _ => none | Sum.inr j => some j
  have inj : Function.Injective f := by
    rintro ⟨a,ha⟩ ⟨b,hb⟩ eq
    apply Subtype.ext
    cases a with
    | inl x =>
      cases b with
      | inl y => exact congrArg Sum.inl (small x y ha hb)
      | inr j => cases eq
    | inr i =>
      cases b with
      | inl y => cases eq
      | inr j => exact congrArg Sum.inr (Option.some.inj eq)
  have size := Fintype.card_le_of_injective f inj
  have card3 : Fintype.card (Option Bool)=3 := by decide
  rw [card3] at size
  apply acyclic_of_small_triangle_free size
  rintro ⟨a,ha⟩ ⟨b,hb⟩ ⟨d,hd⟩ ab bd da
  cases a <;> cases b <;> cases d
  · rename_i x y z
    have ne := (show E.host.Adj (Sum.inl x) (Sum.inl y) from ab).ne
    exact ne (congrArg Sum.inl (small _ _ ha hb))
  · rename_i x y z
    have ne := (show E.host.Adj (Sum.inl x) (Sum.inl y) from ab).ne
    exact ne (congrArg Sum.inl (small _ _ ha hb))
  · rename_i x y z
    have ne := (show E.host.Adj (Sum.inl z) (Sum.inl x) from da).ne
    exact ne (congrArg Sum.inl (small _ _ hd ha))
  · exact bd (E.separated ab da)
  · rename_i x y z
    have ne := (show E.host.Adj (Sum.inl y) (Sum.inl z) from bd).ne
    exact ne (congrArg Sum.inl (small _ _ hb hd))
  · exact da (E.separated bd ab)
  · exact ab (E.separated da bd)
  · rename_i p q r
    change p≠q at ab
    change q≠r at bd
    change r≠p at da
    exact da (by cases p <;> cases q <;> cases r <;> simp_all)

omit [DecidableEq V] in
private theorem if_acyclic_true_trivial (c : V⊕Bool→Bool)
    (cub : ∀v,E.host.degree v=3) (low : (boundary E.host c).card≤3)
    (acy : (shoreGraph E.host c).IsAcyclic) :
    ∀ u v,c u=true→c v=true→u=v := by
  classical
  intro u v hu hv
  refine Classical.byContradiction ?_
  intro ne
  have no := acyclic_shore_large_cut E.host c cub acy hu hv ne
  omega

/-- A nontrivial small cut of the handle extension projects to a
nontrivial small cut of the old graph. -/
theorem nontrivial_handle_cut_projects (c : V⊕Bool→Bool) (cub : ∀v,G.degree v=3)
    (low : (boundary E.host c).card≤3) (non : ¬TrivialCut c) :
    (boundary G (Edges.oldColor c)).card≤3 ∧ ¬TrivialCut (Edges.oldColor c) := by
  refine ⟨(E.boundary_mono c).trans low,?_⟩
  intro tr
  apply non
  have cube := E.cubic cub
  rcases tr with h|h
  · exact Or.inl (if_acyclic_true_trivial E c cube low (singleton_old_acyclic E c h))
  · right
    let d := fun z=> !(c z)
    have ld : (boundary E.host d).card≤3 := (boundary_flip_card E.host c).trans_le low
    have hs : ∀ x y,Edges.oldColor d x=true→Edges.oldColor d y=true→x=y := by
      intro u v hu hv
      apply h u v
      · change (!(c (Sum.inl u)))=true at hu
        cases e : c (Sum.inl u)
        · exact e
        · simp [e] at hu
      · change (!(c (Sum.inl v)))=true at hv
        cases e : c (Sum.inl v)
        · exact e
        · simp [e] at hv
    have t := if_acyclic_true_trivial E d cube ld (singleton_old_acyclic E d hs)
    exact fun u v hu hv=>t u v (by simp [d,hu]) (by simp [d,hv])

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem added_crossing_le (c : V⊕Bool→Bool)
    (mono : ∀s,Edges.oldColor c (E.a s)=Edges.oldColor c (E.b s))
    {p : (V⊕Bool)×(V⊕Bool)} (hp : p∈boundary E.host c)
    (fresh : ¬∃ a b : V,p=(Sum.inl a,Sum.inl b)) :
    (boundary G (Edges.oldColor c)).card+1≤(boundary E.host c).card := by
  classical
  let f : (V×V)→(V⊕Bool)×(V⊕Bool) := fun e=>(Sum.inl e.1,Sum.inl e.2)
  let D := (boundary G (Edges.oldColor c)).image f
  have inj : Function.Injective f := fun u v eq=>Prod.ext
    (Sum.inl.inj (congrArg Prod.fst eq)) (Sum.inl.inj (congrArg Prod.snd eq))
  have sub : D⊆boundary E.host c := by
    intro e mem
    obtain ⟨z,zm,rfl⟩ := mem_image.mp mem
    obtain ⟨z1,z2,adj⟩ := mem_boundary.mp zm
    have no : ¬E.Removed z.1 z.2 := by
      rintro ⟨s,pair⟩
      rcases pair with ⟨a,b⟩|⟨a,b⟩
      · have k := mono s
        rw [←a,←b,z1,z2] at k
        cases k
      · have k := mono s
        rw [←a,←b,z1,z2] at k
        cases k
    exact mem_boundary.mpr ⟨z1,z2,adj,no⟩
  have pn : p∉D := by
    intro m
    obtain ⟨q,_,eq⟩ := mem_image.mp m
    exact fresh ⟨q.1,q.2,eq.symm⟩
  have le := card_le_card (insert_subset hp sub)
  rw [card_insert_of_not_mem pn,card_image_of_injective _ inj] at le
  exact le

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- If each doubled old edge is wholly inside an old shore and the
handle cut costs only three, both new vertices have their edge's
color and the two edge colors must agree. -/
theorem no_new_crossing_in_tight_handle_cut (c : V⊕Bool→Bool)
    (low : (boundary E.host c).card≤3) (tight : (boundary G (Edges.oldColor c)).card=3)
    (mono : ∀s,Edges.oldColor c (E.a s)=Edges.oldColor c (E.b s)) :
    (∀s,c (Sum.inr s)=Edges.oldColor c (E.a s)) ∧
      Edges.oldColor c (E.a false)=Edges.oldColor c (E.a true) := by
  have new_same (s : Bool) : c (Sum.inr s)=Edges.oldColor c (E.a s) := by
    refine Classical.byContradiction ?_
    intro ne
    have adjacent : E.host.Adj (Sum.inr s) (Sum.inl (E.a s)) := Or.inl rfl
    have m := active_edge ne adjacent
    have new : ¬∃ a b : V,orientation c (Sum.inr s) (Sum.inl (E.a s))=(Sum.inl a,Sum.inl b) := by
      rintro ⟨a,b,e⟩
      rcases orientation_cases (x:=Sum.inr s) (y:=Sum.inl (E.a s)) (c:=c) with h|h
      · cases (congrArg Prod.fst (h.symm.trans e))
      · cases (congrArg Prod.snd (h.symm.trans e))
    have four := added_crossing_le E c mono m new
    omega
  refine ⟨new_same,?_⟩
  refine Classical.byContradiction ?_
  intro ne
  have e : c (Sum.inr false)≠c (Sum.inr true) := fun h=>ne ((new_same false).symm.trans (h.trans (new_same true)))
  have adjacent : E.host.Adj (Sum.inr false) (Sum.inr true) := Bool.false_ne_true
  have m := active_edge e adjacent
  have new : ¬∃ a b : V,orientation c (Sum.inr false) (Sum.inr true)=(Sum.inl a,Sum.inl b) := by
    rintro ⟨a,b,e⟩
    rcases orientation_cases (x:=Sum.inr false) (y:=Sum.inr true) (c:=c) with h|h <;>
      cases (congrArg Prod.fst (h.symm.trans e))
  have four := added_crossing_le E c mono m new
  omega

#print axioms nontrivial_handle_cut_projects
#print axioms no_new_crossing_in_tight_handle_cut
end
end KelmansCactus.AtomicBridge.OddUncross
