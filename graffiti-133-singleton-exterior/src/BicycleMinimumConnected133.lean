import Partial133
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Operations

namespace Graffiti133Bicycle
open SimpleGraph Finset
open scoped BigOperators Classical
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private lemma toFinset_data (S : Finset V) (I : Fintype (↑S : Set V)) :
    @Set.toFinset _ (↑S : Set V) I=S := by
  ext v
  simp only [Set.mem_toFinset,Finset.mem_coe]

/-- The edge counts of two sides add exactly when no edge crosses the cut. -/
theorem edge_count_no_cross (S : Finset V)
    (closed : ∀ a b, G.Adj a b → (a∈S ↔ b∈S)) :
    (G.induce (↑S : Set V)).edgeFinset.card +
      (G.induce (↑(Finset.univ \ S) : Set V)).edgeFinset.card =
      G.edgeFinset.card := by
  classical
  let T := Finset.univ \ S
  let A := G.edgeFinset ∩ S.sym2
  let B := G.edgeFinset ∩ T.sym2
  have a : (G.induce (↑S : Set V)).edgeFinset.card = A.card := by
    have h := congrArg Finset.card (SimpleGraph.map_edgeFinset_induce (G:=G) (s:=(↑S : Set V)))
    rw [Finset.card_map,toFinset_data] at h
    convert h using 2
    ext e; simp only [SimpleGraph.mem_edgeFinset]
  have b : (G.induce (↑T : Set V)).edgeFinset.card = B.card := by
    have h := congrArg Finset.card (SimpleGraph.map_edgeFinset_induce (G:=G) (s:=(↑T : Set V)))
    rw [Finset.card_map,toFinset_data] at h
    convert h using 2
    ext e; simp only [SimpleGraph.mem_edgeFinset]
  have union : A ∪ B=G.edgeFinset := by
    ext e
    refine Sym2.inductionOn e ?_
    intro x y
    simp only [A,B,Finset.mem_union,Finset.mem_inter,Finset.mk_mem_sym2_iff,Finset.mem_sdiff,
      Finset.mem_univ,true_and,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,T]
    constructor
    · rintro (⟨h,_⟩ | ⟨h,_⟩) <;> exact h
    · intro h
      by_cases hs : x∈S
      · exact Or.inl ⟨h,hs,(closed _ _ h).mp hs⟩
      · exact Or.inr ⟨h,hs,fun hh => hs ((closed _ _ h).mpr hh)⟩
  have dis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e
    refine Sym2.inductionOn e ?_
    intro x y
    simp only [A,B,Finset.mem_inter,Finset.mk_mem_sym2_iff,Finset.mem_sdiff,Finset.mem_univ,true_and,T]
    exact fun h k => k.2.1 h.2.1
  change (G.induce (↑S : Set V)).edgeFinset.card + (G.induce (↑T : Set V)).edgeFinset.card = _
  rw [a,b,←Finset.card_union_of_disjoint dis,union]

/-- A positive-excess graph is connected if every smaller induced graph
has nonpositive excess. This uses full proper-induced minimality. -/
theorem minimal_excess_connected (over : Fintype.card V < G.edgeFinset.card)
    (small : ∀ S : Finset V, S.card < Fintype.card V →
      (G.induce (↑S : Set V)).edgeFinset.card ≤ S.card) : G.Connected := by
  classical
  have nonempty : Nonempty V := by
    rcases isEmpty_or_nonempty V with emp | ne
    · letI := emp
      have sum := G.sum_degrees_eq_twice_card_edges
      have zero : (∑ v : V, G.degree v)=0 := Finset.sum_eq_zero (fun v _ => isEmptyElim v)
      omega
    · exact ne
  obtain ⟨x⟩ := nonempty
  apply (G.connected_iff_exists_forall_reachable).mpr
  refine ⟨x,?_⟩
  intro y
  apply Classical.byContradiction
  intro no
  let S := Finset.univ.filter fun z => G.Reachable x z
  let T := Finset.univ \ S
  have ms (z) : z∈S ↔ G.Reachable x z := by simp [S]
  have sx : x∈S := (ms _).mpr SimpleGraph.Reachable.rfl
  have ny : y∉S := fun m => no ((ms _).mp m)
  have closed (a b) (ab : G.Adj a b) : a∈S ↔ b∈S := by
    rw [ms,ms]
    exact ⟨fun ha => ha.trans ab.reachable,fun hb => hb.trans ab.symm.reachable⟩
  have sSmall : S.card < Fintype.card V := by
    rw [←Finset.card_univ]
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _,fun eq => ny (eq.symm ▸ Finset.mem_univ y)⟩)
  have tSmall : T.card < Fintype.card V := by
    have size := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    have pos := Finset.card_pos.mpr ⟨x,sx⟩
    change T.card+S.card=(Finset.univ : Finset V).card at size
    rw [Finset.card_univ] at size
    omega
  have hS := small S sSmall
  have hT := small T tSmall
  have e := edge_count_no_cross G S closed
  have n := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  change (G.induce (↑S : Set V)).edgeFinset.card + (G.induce (↑T : Set V)).edgeFinset.card = _ at e
  change T.card+S.card=(Finset.univ : Finset V).card at n
  rw [Finset.card_univ] at n
  omega

private noncomputable def reinduceIso (S : Finset V) (T : Finset ((↑S : Set V))) :
    ((G.induce (↑S : Set V)).induce (↑T : Set ((↑S : Set V)))) ≃g
      G.induce (↑(T.image Subtype.val) : Set V) where
  toEquiv :=
    { toFun := fun x => ⟨x.val.val,Finset.mem_image.mpr ⟨x.val,x.property,rfl⟩⟩
      invFun := fun y => ⟨Classical.choose (Finset.mem_image.mp y.property),
        (Classical.choose_spec (Finset.mem_image.mp y.property)).1⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        exact (Classical.choose_spec (Finset.mem_image.mp
          (show x.val.val ∈ T.image Subtype.val from Finset.mem_image.mpr ⟨x.val,x.property,rfl⟩))).2
      right_inv := by
        intro y
        apply Subtype.ext
        exact (Classical.choose_spec (Finset.mem_image.mp y.property)).2 }
  map_rel_iff' := Iff.rfl

/-- Convenient ambient-subset form for the set chosen by minimum order. -/
theorem induced_minimal_excess_connected (S : Finset V)
    (over : S.card < (G.induce (↑S : Set V)).edgeFinset.card)
    (small : ∀ T : Finset V, T.card < S.card →
      (G.induce (↑T : Set V)).edgeFinset.card ≤ T.card) :
    (G.induce (↑S : Set V)).Connected := by
  classical
  let H := G.induce (↑S : Set V)
  have cs : Fintype.card ((↑S : Set V)) = S.card := Fintype.card_coe S
  apply minimal_excess_connected H (by simpa only [cs] using over)
  intro T hT
  let e := reinduceIso G S T
  have ce : (T.image Subtype.val).card = T.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  change (H.induce (↑T : Set ((↑S : Set V)))).edgeFinset.card ≤ T.card
  rw [e.card_edgeFinset_eq,←ce]
  exact small _ (by rwa [ce,←cs])

#print axioms edge_count_no_cross
#print axioms minimal_excess_connected
#print axioms induced_minimal_excess_connected
end Graffiti133Bicycle
