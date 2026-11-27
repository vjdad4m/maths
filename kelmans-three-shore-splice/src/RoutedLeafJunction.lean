import RoutedLeafFactor
import CopyMimic

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open Substitute FourRingCyclicEquivalence CopyMimic
noncomputable section
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Given the three explicit cap contacts, carry the prescribed-leaf
factor back to an original shore together with a chosen outside vertex.
Only the new vertex's specified old contact must be present. -/
theorem close_shore_using_prescribed_leaf
    (promise : CyclicUniversal.{u}) {S : Finset V} {x p q z : V}
    (_xS : x∉S) (pS : p∈S) (qS : q∈S) (pq : p≠q)
    (H : SimpleGraph (↑(insert x S):Type u)) [DecidableRel H.Adj]
    (dom : CyclicDomain H)
    (xp : H.Adj ⟨x,mem_insert_self _ _⟩ ⟨p,mem_insert_of_mem pS⟩)
    (xq : H.Adj ⟨x,mem_insert_self _ _⟩ ⟨q,mem_insert_of_mem qS⟩)
    (nbr : ∀ n (ns : n∈S),H.Adj ⟨x,mem_insert_self _ _⟩ ⟨n,mem_insert_of_mem ns⟩→
      n=p ∨ n=q ∨ n=z)
    (keep : ∀ u v (us : u∈S) (vs : v∈S),
      H.Adj ⟨u,mem_insert_of_mem us⟩ ⟨v,mem_insert_of_mem vs⟩→G.Adj u v)
    (xz : G.Adj x z) : Closed G (insert x S) := by
  classical
  let Rv : (↑(insert x S):Type u) := ⟨x,mem_insert_self _ _⟩
  let Pv : (↑(insert x S):Type u) := ⟨p,mem_insert_of_mem pS⟩
  let Qv : (↑(insert x S):Type u) := ⟨q,mem_insert_of_mem qS⟩
  let K := avoidAt H Rv Pv Qv
  have f : KelmansStarter.HasP3Factor K := cyclic4_factor_avoids_adjacent promise dom xp xq
    (fun e=>pq (congrArg Subtype.val e))
  have br (u : (↑(insert x S):Type u)) (edge : K.Adj Rv u) : u.val=z := by
    have us : u.val∈S := by
      rcases mem_insert.mp u.property with eq|out
      · exact (edge.1.ne (Subtype.ext eq.symm)).elim
      · exact out
    rcases nbr u.val us edge.1 with e|e|e
    · exact (edge.2 (Or.inl ⟨rfl,Or.inl (Subtype.ext e)⟩)).elim
    · exact (edge.2 (Or.inl ⟨rfl,Or.inr (Subtype.ext e)⟩)).elim
    · exact e
  have reflects (u v : (↑(insert x S):Type u)) (adj : K.Adj u v) : G.Adj u.val v.val := by
    rcases mem_insert.mp u.property with ux|us
    · have root : u=Rv := Subtype.ext ux
      have e := br v (root ▸ adj)
      rw [ux,e]
      exact xz
    · rcases mem_insert.mp v.property with vx|vs
      · have root : v=Rv := Subtype.ext vx
        have e := br u (root ▸ adj.symm)
        rw [vx,e]
        exact xz.symm
      · exact keep u.val v.val us vs adj.1
  obtain ⟨P,tile,disj,cover⟩ := f
  let e := Function.Embedding.subtype (fun v : V=>v∈insert x S)
  have localPart : Assemble.LocalPart K P univ := ⟨tile,disj,cover⟩
  have part := CopyMimic.local_map e (fun u _ v _ adj=>reflects u v adj) localPart
  have whole : (univ : Finset (↑(insert x S):Type u)).map e=insert x S := by
    ext v
    constructor
    · intro vM
      obtain ⟨w,_,rfl⟩ := mem_map.mp vM
      exact w.property
    · intro vS
      exact mem_map.mpr ⟨⟨v,vS⟩,mem_univ _,rfl⟩
  rw [whole] at part
  exact ⟨_,part⟩

/-- Assembly rule for the (0,0,2) case. Unlike the previous triangle
special case, both zero shores can be arbitrary closed regions. -/
theorem junction_two_zero_shores_using_leaf [Fintype V]
    {A B C : Finset V} {x : V}
    (one : Closed G (insert x A)) (zeroB : Closed G B) (zeroC : Closed G C)
    (ab : Disjoint (insert x A) B) (ac : Disjoint (insert x A) C) (bc : Disjoint B C)
    (whole : insert x A∪B∪C=univ) : KelmansStarter.HasP3Factor G := by
  have cl := add_closed (add_closed one zeroB ab) zeroC (disjoint_union_left.mpr ⟨ac,bc⟩)
  obtain ⟨P,Pok⟩ := cl
  exact ⟨P,Pok.tile,Pok.disj,Pok.cover.trans whole⟩

/-- Assembly rule for the (1,2,2) case. First use the singleton as a
leaf on an order-two shore; use the specified free port of the order-one
shore as a leaf on the other two shore. -/
theorem junction_two_two_shores_using_leaf [Fintype V]
    {A B C : Finset V} {x d : V}
    (aLeaf : Closed G (insert x A)) (bLeaf : Closed G (insert d B))
    (cPort : Closed G (C.erase d))
    (ab : Disjoint (insert x A) (insert d B))
    (ac : Disjoint (insert x A) (C.erase d))
    (bc : Disjoint (insert d B) (C.erase d))
    (whole : insert x A∪insert d B∪C.erase d=univ) :
    KelmansStarter.HasP3Factor G := by
  have cl := add_closed (add_closed aLeaf bLeaf ab) cPort (disjoint_union_left.mpr ⟨ac,bc⟩)
  obtain ⟨P,Pok⟩ := cl
  exact ⟨P,Pok.tile,Pok.disj,Pok.cover.trans whole⟩

#print axioms close_shore_using_prescribed_leaf
#print axioms junction_two_zero_shores_using_leaf
#print axioms junction_two_two_shores_using_leaf
end
end KelmansCactus.AtomicBridge
