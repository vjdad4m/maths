import VertexSmoothing

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {D : Finset V} {z : V}

def FilledAdj (G : SimpleGraph V) (D : Finset V) (x y : V) : Prop :=
  G.Adj x y ∨ (x ≠ y ∧ x ∈ D ∧ y ∈ D)

structure FilledPath (G : SimpleGraph V) (D : Finset V) (z : V) where
  vertices : List V
  nonempty : vertices ≠ []
  nodup : vertices.Nodup
  covers : ∀ v, v ∈ vertices ↔ v ≠ z
  chain : vertices.Chain' (FilledAdj G D)

theorem filledPath_of_traceable (p : Traceable (cutTorso G D ({z} : Set V))) :
    Nonempty (FilledPath G D z) := by
  obtain ⟨a,b,w,path,all⟩ := p
  let f : (↑(({z} : Set V)ᶜ)) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let L := w.support.map f
  have empty : L ≠ [] := by simp [L]
  have chain : L.Chain' (FilledAdj G D) := by
    apply (List.chain'_map _).mpr
    apply w.chain'_adj_support.imp
    intro x y
    rintro (adj|⟨ne,hx,hy⟩)
    · exact Or.inl adj
    · exact Or.inr ⟨f.injective.ne ne,hx,hy⟩
  refine ⟨⟨L,empty,path.support_nodup.map f.injective,?_,chain⟩⟩
  intro v
  constructor
  · intro mem
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp mem
    exact x.property
  · intro off
    exact List.mem_map.mpr ⟨⟨v,off⟩,all _,rfl⟩

theorem traceable_from_augmented_fill [DecidableEq V] (p : FilledPath G D z) {L : List V}
    (perm : L.Perm (z :: p.vertices)) (chain : L.Chain' G.Adj) : Traceable G := by
  have off : z ∉ p.vertices := fun h => (p.covers z).mp h rfl
  have nd := (List.Perm.nodup_iff perm).mpr (List.nodup_cons.mpr ⟨off,p.nodup⟩)
  have all (v : V) : v ∈ L := by
    apply perm.mem_iff.mpr
    by_cases eq : v = z
    · simp [eq]
    · exact List.mem_cons_of_mem _ ((p.covers v).mpr eq)
  have ne : L ≠ [] := fun h => List.not_mem_nil (h ▸ all z)
  exact traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp
    ⟨⟨L,ne,chain,nd,fun v => iff_of_true (all v) trivial⟩⟩)

private theorem split_first_nonedge {l : List V} (bad : ¬ l.Chain' G.Adj) :
    ∃ L a b R, l = L ++ a :: b :: R ∧ ¬ G.Adj a b ∧ (L ++ [a]).Chain' G.Adj := by
  induction l with
  | nil => exact (bad (by simp)).elim
  | cons a l ih =>
    cases l with
    | nil => exact (bad (List.chain'_singleton _)).elim
    | cons b R =>
      by_cases ab : G.Adj a b
      · have tail : ¬ (b :: R).Chain' G.Adj := fun h => bad (List.chain'_cons.mpr ⟨ab,h⟩)
        obtain ⟨L,x,y,T,eq,xy,before⟩ := ih tail
        refine ⟨a :: L,x,y,T,congrArg (List.cons a) eq,xy,?_⟩
        cases L with
        | nil =>
          have bx : b = x := List.cons.inj eq |>.1
          exact List.chain'_cons.mpr ⟨bx ▸ ab,List.chain'_singleton _⟩
        | cons p P =>
          have bp : b = p := List.cons.inj eq |>.1
          exact List.chain'_cons.mpr ⟨bp ▸ ab,before⟩
      · exact ⟨[],a,b,R,rfl,ab,List.chain'_singleton _⟩

/-- With at most three fill vertices, two fictitious transitions must be
consecutive. This covers every spanning path of a smoothed cubic vertex. -/
theorem filled_chain_cases [DecidableEq V] {l : List V}
    (count : D.card ≤ 3) (nd : l.Nodup) (chain : l.Chain' (FilledAdj G D)) :
    l.Chain' G.Adj ∨
    (∃ L a b R, l = L ++ a :: b :: R ∧ a ∈ D ∧ b ∈ D ∧ ¬ G.Adj a b ∧
      (L ++ [a]).Chain' G.Adj ∧ (b :: R).Chain' G.Adj) ∨
    ∃ L a b c R, l = L ++ a :: b :: c :: R ∧ a ∈ D ∧ b ∈ D ∧ c ∈ D ∧
      ¬ G.Adj a b ∧ ¬ G.Adj b c ∧ (L ++ [a]).Chain' G.Adj ∧ (c :: R).Chain' G.Adj := by
  classical
  by_cases actual : l.Chain' G.Adj
  · exact Or.inl actual
  obtain ⟨L,a,b,R,form,noAB,left⟩ := split_first_nonedge actual
  rw [form] at nd chain
  have tail := chain.right_of_append
  have ⟨ab,aD,bD⟩ := (show FilledAdj G D a b from tail.rel_head).resolve_left noAB
  have after := tail.tail
  have nd' := (List.nodup_append.mp nd).2.1
  have aOff : a ∉ R := fun mem => (List.nodup_cons.mp nd').1 (List.mem_cons_of_mem _ mem)
  have bOff : b ∉ R := (List.nodup_cons.mp (List.nodup_cons.mp nd').2).1
  have cap : ((D.erase a).erase b).card ≤ 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ab.symm,bD⟩),Finset.card_erase_of_mem aD]
    omega
  have actualR : R.Chain' G.Adj := by
    apply (List.Chain'.iff_mem.mp after.tail).imp
    intro x y h
    obtain ⟨xR,yR,e⟩ := h
    rcases e with real|⟨ne,xD,yD⟩
    · exact real
    · have mem (u : V) (uR : u ∈ R) (uD : u ∈ D) : u ∈ (D.erase a).erase b :=
        Finset.mem_erase.mpr ⟨fun h => bOff (h ▸ uR),
          Finset.mem_erase.mpr ⟨fun h => aOff (h ▸ uR),uD⟩⟩
      exact (ne (Finset.card_le_one_iff.mp cap (mem x xR xD) (mem y yR yD))).elim
  cases R with
  | nil => exact Or.inr (Or.inl ⟨L,a,b,[],form,aD,bD,noAB,left,List.chain'_singleton _⟩)
  | cons c R =>
    rcases after.rel_head with bc|⟨_,_,cD⟩
    · exact Or.inr (Or.inl ⟨L,a,b,c :: R,form,aD,bD,noAB,left,List.chain'_cons.mpr ⟨bc,actualR⟩⟩)
    · by_cases bc : G.Adj b c
      · exact Or.inr (Or.inl ⟨L,a,b,c :: R,form,aD,bD,noAB,left,List.chain'_cons.mpr ⟨bc,actualR⟩⟩)
      · exact Or.inr (Or.inr ⟨L,a,b,c,R,form,aD,bD,cD,noAB,bc,left,actualR⟩)

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A single filled transition can be replaced by the omitted vertex. -/
theorem traceable_of_single_fill (p : FilledPath G (G.neighborFinset z) z)
    {L R : List V} {a b : V} (form : p.vertices = L ++ a :: b :: R)
    (aD : a ∈ G.neighborFinset z) (bD : b ∈ G.neighborFinset z)
    (left : (L ++ [a]).Chain' G.Adj) (right : (b :: R).Chain' G.Adj) : Traceable G := by
  let P := (L ++ [a]) ++ z :: b :: R
  have za := (G.mem_neighborFinset _ _).mp aD
  have zb := (G.mem_neighborFinset _ _).mp bD
  have real : P.Chain' G.Adj := by
    apply left.append (List.chain'_cons.mpr ⟨zb,right⟩)
    intro x hx y hy
    have ex : a = x := by simpa using hx
    have ey : z = y := by simpa using hy
    exact ex ▸ ey ▸ za.symm
  apply traceable_from_augmented_fill p (L := P) _ real
  simpa only [P,form,List.append_assoc,List.cons_append,List.nil_append] using
    (List.perm_middle (a := z) (l₁ := L ++ [a]) (l₂ := b :: R))

universe u
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The two surviving forms of a spanning path of the smoothed vertex. -/
def CubicSmoothingRemainder {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (z : V) : Prop :=
  ∃ p : FilledPath G (G.neighborFinset z) z, p.vertices.Chain' G.Adj ∨
    ∃ L a b c R, p.vertices = L ++ a :: b :: c :: R ∧
      (∀ v, G.Adj z v ↔ v = a ∨ v = b ∨ v = c) ∧
      ¬ G.Adj a b ∧ ¬ G.Adj b c ∧ (L ++ [a]).Chain' G.Adj ∧ (c :: R).Chain' G.Adj

theorem cubic_smoothing_remainder {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {z : V}
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (degree : G.degree z = 3)
    (notTraceable : ¬ Traceable G) : CubicSmoothingRemainder G z := by
  classical
  let D := G.neighborFinset z
  have size : D.card = 3 := (G.card_neighborFinset_eq_degree _).trans degree
  obtain ⟨p⟩ := filledPath_of_traceable
    (traceable_after_smoothing_of_smaller (z := z) smaller conn budget order)
  refine ⟨p,?_⟩
  rcases filled_chain_cases size.le p.nodup p.chain with actual|one|two
  · exact Or.inl actual
  · obtain ⟨L,a,b,R,form,aD,bD,_,left,right⟩ := one
    exact (notTraceable (traceable_of_single_fill p form aD bD left right)).elim
  · obtain ⟨L,a,b,c,R,form,aD,bD,cD,noAB,noBC,left,right⟩ := two
    have nd := (List.nodup_append.mp (form ▸ p.nodup)).2.1
    have ab : a ≠ b := fun h => (List.nodup_cons.mp nd).1 (by simp [h])
    have ac : a ≠ c := fun h => (List.nodup_cons.mp nd).1 (by simp [h])
    have bc : b ≠ c := fun h => (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [h])
    let S : Finset V := {a,b,c}
    have sub : S ⊆ D := by
      intro v h
      rcases (show v = a ∨ v = b ∨ v = c by simpa [S] using h) with rfl|rfl|rfl
      · exact aD
      · exact bD
      · exact cD
    have count : S.card = 3 := by
      change (insert a ({b,c} : Finset V)).card = 3
      rw [Finset.card_insert_of_not_mem (by simp [ab,ac]),Finset.card_pair bc]
    have eq : S = D := Finset.eq_of_subset_of_card_le sub (by rw [size,count])
    refine Or.inr ⟨L,a,b,c,R,form,?_,noAB,noBC,left,right⟩
    intro v
    rw [← G.mem_neighborFinset]
    change v ∈ D ↔ _
    rw [← eq]
    simp [S]

#print axioms filled_chain_cases
#print axioms cubic_smoothing_remainder

end Graffiti199Depleted.Catalogue
