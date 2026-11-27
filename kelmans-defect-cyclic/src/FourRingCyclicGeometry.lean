import FourRingCapDomain
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Finset SimpleGraph
namespace KelmansCactus.FourRingCutAux
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
variable [DecidableRel G.Adj]

abbrev Shore (c : V→Bool) := {v : V // c v=true}
abbrev shoreGraph (c : V→Bool) : SimpleGraph (Shore c) := G.induce {v | c v=true}

omit [DecidableEq V] in
private theorem inside_eq (c : V→Bool) (x : Shore c) :
    ((shoreGraph G c).neighborFinset x).map (Function.Embedding.subtype (fun z : V=>c z=true)) =
      (G.neighborFinset x.val).filter (fun z=>c z=true) := by
  ext y
  simp only [Finset.mem_map,Function.Embedding.subtype_apply,mem_neighborFinset,mem_filter]
  constructor
  · rintro ⟨z,e,rfl⟩
    exact ⟨e,z.property⟩
  · rintro ⟨a,b⟩
    exact ⟨⟨y,b⟩,a,rfl⟩

private theorem inside_exit_sum (c : V→Bool) (x : Shore c) :
    (shoreGraph G c).degree x+(exitNeighbors G c x.val).card=G.degree x.val := by
  let N := G.neighborFinset x.val
  let I := N.filter (fun z=>c z=true)
  let O := N.filter (fun z=>c z=false)
  have union : I∪O=N := by
    ext y
    cases h : c y <;> simp [I,O,h]
  have dis : Disjoint I O := by
    apply disjoint_left.mpr
    intro y ay byy
    have a := (mem_filter.mp ay).2
    have b := (mem_filter.mp byy).2
    rw [a] at b
    contradiction
  have sum := card_union_of_disjoint dis
  rw [union] at sum
  have inside : I.card=(shoreGraph G c).degree x := by
    change ((G.neighborFinset x.val).filter (fun z=>c z=true)).card=(shoreGraph G c).degree x
    rw [←card_neighborFinset_eq_degree,←inside_eq G c x,card_map]
  change N.card=I.card+O.card at sum
  rw [inside] at sum
  exact sum.symm

/-- The boundary of an induced tree in a cubic graph has order n+2. -/
theorem tree_shore_boundary (c : V→Bool) (cub : ∀ v,G.degree v=3)
    (tree : (shoreGraph G c).IsTree) :
    (boundary G c).card=Fintype.card (Shore c)+2 := by
  classical
  have two (x : Shore c) : (shoreGraph G c).degree x+(exitNeighbors G c x.val).card=3 := by
    rw [inside_exit_sum G,cub]
  have total : (∑ x,(shoreGraph G c).degree x)+(∑ x : Shore c,(exitNeighbors G c x.val).card)=
      3*Fintype.card (Shore c) := by
    rw [←Finset.sum_add_distrib]
    simp [two,Nat.mul_comm]
  rw [(shoreGraph G c).sum_degrees_eq_twice_card_edges] at total
  have cut : (boundary G c).card=∑ x : Shore c,(exitNeighbors G c x.val).card := by
    rw [card_boundary_eq_exitSum G]
    exact sum_subtype _ (fun _=>mem_colour_class) _
  rw [←cut] at total
  have treeEq := tree.card_edgeFinset
  omega

private theorem induced_forest {W : Type*} {H : SimpleGraph W} (s : Set W)
    (acyc : H.IsAcyclic) : (H.induce s).IsAcyclic := by
  let e : H.induce s ↪g H := Embedding.induce s
  intro x w c
  exact acyc (w.map e.toHom) (c.map e.injective)

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem subshore_has_tree_of_edge (c : V→Bool) (acyc : (shoreGraph G c).IsAcyclic)
    {x y : Shore c} (edge : (shoreGraph G c).Adj x y) :
    ∃ q : V→Bool,
      (shoreGraph G q).IsTree ∧ q x.val=true ∧ q y.val=true ∧
      boundary G q⊆boundary G c := by
  classical
  let H := shoreGraph G c
  let C := H.connectedComponentMk x
  let q : V→Bool := fun v=>decide (∃ h : c v=true,(⟨v,h⟩ : Shore c)∈C.supp)
  have cert (v : V) : q v=true ↔ ∃ h : c v=true,(⟨v,h⟩ : Shore c)∈C.supp := by
    simp [q]
  have xx : x∈C.supp := by rw [ConnectedComponent.mem_supp_iff]
  have yy : y∈C.supp := by
    rw [ConnectedComponent.mem_supp_iff,ConnectedComponent.eq]
    exact edge.symm.reachable
  let f : H.induce C.supp →g shoreGraph G q :=
    ⟨fun v=>⟨v.val.val,(cert _).mpr ⟨v.val.property,v.property⟩⟩,fun h=>h⟩
  let g : shoreGraph G q →g H.induce C.supp :=
    ⟨fun v=>⟨⟨v.val,((cert _).mp v.property).choose⟩,((cert _).mp v.property).choose_spec⟩,
      fun h=>h⟩
  have inv (v : Shore q) : f (g v)=v := Subtype.ext rfl
  have ginj : Function.Injective g := fun _ _ e=>Subtype.ext
    (congrArg (fun v : C.supp=>v.val.val) e)
  refine ⟨q,⟨?_,?_⟩,(cert _).mpr ⟨x.property,xx⟩,(cert _).mpr ⟨y.property,yy⟩,?_⟩
  · have conn := C.connected_induce_supp
    haveI : Nonempty (Shore q) := ⟨f ⟨x,xx⟩⟩
    exact ⟨fun a b=>by
      have r := (conn (g a) (g b)).map f
      rwa [inv,inv] at r⟩
  · intro z w cyc
    exact (induced_forest C.supp acyc) (w.map g) (cyc.map ginj)
  · intro w inb
    obtain ⟨yes,no,e⟩ := mem_boundary.mp inb
    obtain ⟨hc,mem⟩ := (cert _).mp yes
    refine mem_boundary.mpr ⟨hc,?_,e⟩
    cases hb : c w.2
    · rfl
    · have a := (ConnectedComponent.mem_supp_iff C _).mp mem
      have r : H.Reachable (⟨w.2,hb⟩ : Shore c) ⟨w.1,hc⟩ := (show H.Adj ⟨w.2,hb⟩ ⟨w.1,hc⟩ from e.symm).reachable
      have b := (ConnectedComponent.eq.mpr r).trans a
      have contra := (cert _).mpr ⟨hb,(ConnectedComponent.mem_supp_iff C _).mpr b⟩
      rw [no] at contra
      contradiction

private theorem no_edge_shore_big (c : V→Bool) (cub : ∀ v,G.degree v=3)
    (none : ∀ x y,(shoreGraph G c).Adj x y→False) {x y : V}
    (a : c x=true) (b : c y=true) (ne : x≠y) :
    6≤(boundary G c).card := by
  classical
  have full (v : V) (hv : c v=true) : (exitNeighbors G c v).card=3 := by
    have e : exitNeighbors G c v=G.neighborFinset v := by
      ext w
      simp only [exitNeighbors,mem_filter,mem_neighborFinset,and_iff_left_iff_imp]
      intro adj
      cases ww : c w
      · rfl
      · exact (none ⟨v,hv⟩ ⟨w,ww⟩ adj).elim
    rw [e,card_neighborFinset_eq_degree,cub]
  have sub : ({x,y}:Finset V)⊆colourClass c true := by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl
    · exact mem_colour_class.mpr a
    · exact mem_colour_class.mpr b
  rw [card_boundary_eq_exitSum G]
  have sum := sum_le_sum_of_subset (f:=fun v=>(exitNeighbors G c v).card) sub
  rw [sum_insert (by simpa using ne),sum_singleton,full x a,full y b] at sum
  exact sum

/-- A cubic graph cannot have a small edge boundary around an acyclic shore of size at least two. -/
theorem acyclic_shore_large_cut (c : V→Bool) (cub : ∀ v,G.degree v=3)
    (acyc : (shoreGraph G c).IsAcyclic) {x y : V} (a : c x=true)
    (b : c y=true) (ne : x≠y) : 4≤(boundary G c).card := by
  classical
  by_cases existsEdge : ∃ u v,(shoreGraph G c).Adj u v
  · obtain ⟨u,v,e⟩ := existsEdge
    obtain ⟨q,tree,qu,qv,sub⟩ := subshore_has_tree_of_edge G c acyc e
    have ge : 2≤Fintype.card (Shore q) := by
      by_contra! low
      have h := (Fintype.card_le_one_iff_subsingleton.mp (by omega : Fintype.card (Shore q)≤1))
      have ee : (⟨u.val,qu⟩ : Shore q)=⟨v.val,qv⟩ := h.elim _ _
      exact e.ne (Subtype.ext (congrArg (fun z : Shore q=>z.val) ee))
    have eq := tree_shore_boundary G q cub tree
    have mono := card_le_card sub
    omega
  · push_neg at existsEdge
    exact (show 4≤6 by decide).trans (no_edge_shore_big G c cub existsEdge a b ne)

def NoCyclicCutBelowFour : Prop :=
  ∀ c : V→Bool,(boundary G c).card≤3 →
    (shoreGraph G c).IsAcyclic ∨ (shoreGraph G (fun v=> !(c v))).IsAcyclic

/-- The nontrivial-cut formulation is literally equivalent to the
usual condition that no cut of at most three edges has a cycle on
both shores. No connectivity assumption is needed for this bridge. -/
theorem small_trivial_iff_no_cyclic_cut (cub : ∀ v,G.degree v=3) :
    SmallTrivial G ↔ NoCyclicCutBelowFour G := by
  classical
  constructor
  · intro good c low
    have acy (q : V→Bool) (sub : ∀ a b,q a=true→q b=true→a=b) :
        (shoreGraph G q).IsAcyclic := by
      have eq : shoreGraph G q=⊥ := by
        ext x y
        have same : x=y := Subtype.ext (sub _ _ x.property y.property)
        subst y
        simp
      rw [eq]
      exact isAcyclic_bot
    rcases good c low with a|b
    · exact Or.inl (acy c a)
    · exact Or.inr (acy _ (fun x y a d=>b x y (by simpa using a) (by simpa using d)))
  · intro no c low
    rcases no c low with ac|ac
    · left
      intro x y a b
      by_contra ne
      have big := acyclic_shore_large_cut G c cub ac a b ne
      omega
    · right
      intro x y a b
      by_contra ne
      have big := acyclic_shore_large_cut G _ cub ac (by simpa using a) (by simpa using b) ne
      rw [boundary_flip_card] at big
      omega

#print axioms tree_shore_boundary
#print axioms acyclic_shore_large_cut
#print axioms small_trivial_iff_no_cyclic_cut
end
end KelmansCactus.FourRingCutAux
