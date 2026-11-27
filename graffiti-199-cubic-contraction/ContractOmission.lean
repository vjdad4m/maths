import MinimumContraction

open private chain_away_from_contracted from ContractPath

namespace Graffiti199Depleted.ContractedEdge

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} (E : ContractedEdge G)
variable [DecidableEq V]

omit [DecidableEq V] in
/-- If both links of the contracted vertex attach to one end of the
original edge, restore that end. This gives a path omitting exactly
the other end. -/
theorem lift_single_side (p : PathOn E.graph Set.univ) {L R : List E.Vertex}
    (split : p.vertices = L ++ none :: R)
    {kept omitted : V}
    (sides : (kept = E.a ∧ omitted = E.b) ∨ (kept = E.b ∧ omitted = E.a))
    (left : ∀ x ∈ L.getLast?, G.Adj (E.representative x) kept)
    (right : ∀ y ∈ R.head?, G.Adj kept (E.representative y)) :
    Nonempty (PathOn G {v | v ≠ omitted}) := by
  have ne : kept ≠ omitted := by
    rcases sides with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact E.edge.ne
    · exact E.edge.ne.symm
  have other_ne (x : E.Other) : x.val ≠ kept ∧ x.val ≠ omitted := by
    rcases sides with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact x.property
    · exact ⟨x.property.2,x.property.1⟩
  let rep : E.Vertex ↪ V :=
    ⟨fun x => match x with | none => kept | some y => y.val,by
      intro x y eq
      rcases x with (_|x) <;> rcases y with (_|y)
      · rfl
      · exact ((other_ne y).1 eq.symm).elim
      · exact ((other_ne x).1 eq).elim
      · exact congrArg some (Subtype.ext eq)⟩
  have rep_surj (x : V) (off : x ≠ omitted) : ∃ y, rep y = x := by
    by_cases hit : x = kept
    · exact ⟨none,hit.symm⟩
    · have away : x ≠ E.a ∧ x ≠ E.b := by
        rcases sides with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact ⟨hit,off⟩
        · exact ⟨off,hit⟩
      exact ⟨some ⟨x,away⟩,rfl⟩
  have equalOn (A : List E.Vertex) (off : (none : E.Vertex) ∉ A) :
      A.map rep = A.map E.representative := by
    apply List.map_congr_left
    intro x h
    cases x with
    | none => exact (off h).elim
    | some x => rfl
  have ch := p.chain
  rw [split] at ch
  have nodup := p.nodup
  rw [split] at nodup
  obtain ⟨_,nR0,dis⟩ := List.nodup_append.mp nodup
  have offL : none ∉ L := fun h => (List.disjoint_left.mp dis) h (List.mem_cons_self ..)
  have offR := (List.nodup_cons.mp nR0).1
  have newCh : (p.vertices.map rep).Chain' G.Adj := by
    rw [split,List.map_append,List.map_cons,equalOn L offL,equalOn R offR]
    change (L.map E.representative ++ kept :: R.map E.representative).Chain' G.Adj
    have init := chain_away_from_contracted E offL ch.left_of_append
    have tail := chain_away_from_contracted E offR ch.right_of_append.tail
    have tail' : (kept :: R.map E.representative).Chain' G.Adj := by
      apply tail.cons'
      intro y hy
      obtain ⟨z,hz,rfl⟩ := Option.mem_map.mp (by rwa [List.head?_map] at hy)
      exact right z hz
    apply init.append tail'
    intro x hx y hy
    have yeq : kept = y := by simpa using hy
    subst y
    obtain ⟨z,hz,rfl⟩ := Option.mem_map.mp (by rwa [List.getLast?_map] at hx)
    exact left z hz
  refine ⟨⟨p.vertices.map rep,by simpa using p.nonempty,newCh,p.nodup.map rep.injective,?_⟩⟩
  intro x
  constructor
  · intro hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    cases y with
    | none => exact ne
    | some y => exact (other_ne y).2
  · intro hx
    obtain ⟨y,hy⟩ := rep_surj x hx
    exact List.mem_map.mpr ⟨y,(p.covers y).mpr (Set.mem_univ _),hy⟩

variable [Fintype V] [DecidableRel G.Adj]

/-- In the minimum-order cubic-edge case, deleting at least one end
of the edge leaves a traceable induced graph, expressed as an
ambient path visiting precisely the undeleted vertices. -/
theorem minimum_cubic_edge_one_omission
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card V))
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (cross : CrossingBetweenSurvivingEdges G)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 10 ≤ Fintype.card V)
    (da : G.degree E.a = 3) (db : G.degree E.b = 3)
    (noTrace : ¬ Catalogue.Traceable G) :
    Nonempty (PathOn G {x | x ≠ E.a}) ∨ Nonempty (PathOn G {x | x ≠ E.b}) := by
  obtain ⟨⟨p⟩,all⟩ := E.minimum_cubic_contraction_same_side smaller conn cross budget order da db noTrace
  obtain ⟨L,R,x,y,split,left,right,side⟩ := all p
  rcases side with ⟨xA,yA⟩|⟨xB,yB⟩
  · refine Or.inr (E.lift_single_side p split (Or.inl ⟨rfl,rfl⟩) ?_ ?_)
    · simpa [left] using xA.symm
    · simpa [right] using yA
  · refine Or.inl (E.lift_single_side p split (Or.inr ⟨rfl,rfl⟩) ?_ ?_)
    · simpa [left] using xB.symm
    · simpa [right] using yB

#print axioms lift_single_side
#print axioms minimum_cubic_edge_one_omission

end Graffiti199Depleted.ContractedEdge
