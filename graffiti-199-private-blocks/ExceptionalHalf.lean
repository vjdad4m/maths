import PrescribedPaths

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- In an exceptional shore, a clique of residual port neighbors, a
single contact, and its private clique make one path. Its endpoint in
the private clique can be prescribed arbitrarily. -/
theorem private_clique_half_traversal [Fintype V] {P C : Set V} {x t : V}
    (clP : P.Pairwise G.Adj) (clC : C.Pairwise G.Adj)
    (nonempty : P.Nonempty) (ht : t ∈ C)
    (apart : Disjoint P C) (xP : x ∉ P) (xC : x ∉ C)
    (xToP : ∀ u ∈ P, G.Adj x u) (xToC : ∀ u ∈ C, G.Adj x u) :
    ∃ z ∈ P, Traverses G ((P ∪ {x}) ∪ C) z t := by
  classical
  obtain ⟨z,zP⟩ := nonempty
  obtain ⟨w,wP,L⟩ := Traverses.start_clique clP zP
  obtain ⟨v,vC,R⟩ := Traverses.end_clique clC ht
  have apartX : Disjoint P ({x} : Set V) := by simpa using xP
  have apartC : Disjoint (P ∪ ({x} : Set V)) C := by
    rw [Set.disjoint_union_left]
    exact ⟨apart,by simpa using xC⟩
  exact ⟨z,zP,(L.join (Traverses.single x) apartX (xToP _ wP).symm).join
    R apartC (xToC _ vC)⟩

/-- Splice the four half-paths of the two-exceptional-shore configuration.
The first and third halves come from one shore. The second and fourth
come from the other. The three cut vertices are used exactly once. -/
theorem traceable_of_four_exceptional_halves [DecidableEq V]
    {W X Y Z : Set V} {a r b w0 w1 x0 x1 y0 y1 z0 z1 : V}
    (apart : [W,{a},X,{r},Y,{b},Z].Pairwise Disjoint)
    (cover : ∀ v, v ∈ W ∨ v = a ∨ v ∈ X ∨ v = r ∨ v ∈ Y ∨ v = b ∨ v ∈ Z)
    (first : Traverses G W w0 w1) (second : Traverses G X x0 x1)
    (third : Traverses G Y y0 y1) (fourth : Traverses G Z z0 z1)
    (wa : G.Adj w1 a) (ax : G.Adj a x0) (xr : G.Adj x1 r)
    (ry : G.Adj r y0) (yb : G.Adj y1 b) (bz : G.Adj b z0) : Traceable G := by
  simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true] at apart
  have d1 : Disjoint W ({a} : Set V) := by tauto
  have d2 : Disjoint (W ∪ {a}) X := by simp only [Set.disjoint_union_left]; tauto
  have d3 : Disjoint ((W ∪ {a}) ∪ X) ({r} : Set V) := by
    simp only [Set.disjoint_union_left]
    tauto
  have d4 : Disjoint (((W ∪ {a}) ∪ X) ∪ {r}) Y := by
    simp only [Set.disjoint_union_left]
    tauto
  have d5 : Disjoint ((((W ∪ {a}) ∪ X) ∪ {r}) ∪ Y) ({b} : Set V) := by
    simp only [Set.disjoint_union_left]
    tauto
  have d6 : Disjoint (((((W ∪ {a}) ∪ X) ∪ {r}) ∪ Y) ∪ {b}) Z := by
    simp only [Set.disjoint_union_left]
    tauto
  have route :=
    (((((first.join (Traverses.single a) d1 wa).join second d2 ax).join
      (Traverses.single r) d3 xr).join third d4 ry).join
        (Traverses.single b) d5 yb).join fourth d6 bz
  obtain ⟨p,_,_⟩ := route
  have full : ((((((W ∪ {a}) ∪ X) ∪ {r}) ∪ Y) ∪ {b}) ∪ Z) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro v
    simp only [Set.mem_union,Set.mem_singleton_iff]
    have h := cover v
    tauto
  exact traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp ⟨full ▸ p⟩)

#print axioms private_clique_half_traversal
#print axioms traceable_of_four_exceptional_halves

end Graffiti199Depleted.Catalogue
