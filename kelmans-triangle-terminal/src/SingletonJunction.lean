import ZeroPort

open Finset
namespace KelmansCactus.AtomicBridge
open ThreePort Substitute MinimalSeams

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Two shores supplying a one-vertex fragment on their links to a common
singleton can always be joined through it. A further closed shore may be
adjoined; all of its seam edges are unused. No restrictions on unused edges
are needed. -/
theorem singleton_joins_two_leaf_shores
    {A B C : Finset V} {a b x : V}
    (ad : a∈A) (bd : b∈B)
    (disAB : Disjoint A B) (disAC : Disjoint A C) (disBC : Disjoint B C)
    (xA : x∉A) (xB : x∉B) (xC : x∉C)
    (ax : G.Adj a x) (xb : G.Adj x b)
    (aCl : Closed G (A.erase a)) (bCl : Closed G (B.erase b)) (cCl : Closed G C) :
    Closed G (insert x (A∪B∪C)) := by
  have ab : a≠b := fun e=>disjoint_left.mp disAB (e ▸ ad : b∈A) bd
  have sc : ({a,x,b} : Finset V).card=3 := by simp [ax.ne,xb.ne,ab]
  have tile : KelmansStarter.IsTile G {a,x,b} := ⟨sc,
    (Kelmans.tile_iff_path G {a,x,b} sc).mpr ⟨a,x,b,ax.ne,ab,xb.ne,ax,xb,rfl⟩⟩
  have ae : A.erase a⊆A := erase_subset _ _
  have be : B.erase b⊆B := erase_subset _ _
  have both := add_closed aCl bCl (disjoint_of_subset_left ae (disjoint_of_subset_right be disAB))
  have split1 : Disjoint (A.erase a ∪ B.erase b) C :=
    disjoint_union_left.mpr ⟨disjoint_of_subset_left ae disAC,disjoint_of_subset_left be disBC⟩
  have all := add_closed both cCl split1
  have split2 : Disjoint (A.erase a∪B.erase b∪C) ({a,x,b}:Finset V) := by
    apply disjoint_left.mpr
    intro u uR uT
    simp only [mem_insert,mem_singleton] at uT
    rcases uT with rfl|rfl|rfl
    · rcases mem_union.mp uR with m|m
      · rcases mem_union.mp m with n|n
        · exact (mem_erase.mp n).1 rfl
        · exact disjoint_left.mp disAB ad (be n)
      · exact disjoint_left.mp disAC ad m
    · rcases mem_union.mp uR with m|m
      · exact (mem_union.mp m).elim (fun n=>xA (ae n)) (fun n=>xB (be n))
      · exact xC m
    · rcases mem_union.mp uR with m|m
      · rcases mem_union.mp m with n|n
        · exact disjoint_left.mp disAB (ae n) bd
        · exact (mem_erase.mp n).1 rfl
      · exact disjoint_left.mp disBC bd m 
  have out := add_closed all (tile_closed tile) split2
  convert out using 1
  ext v
  simp only [mem_erase,mem_union,mem_insert,mem_singleton]
  by_cases va : v=a
  · subst v
    simp [ad]
  by_cases vb : v=b
  · subst v
    simp [bd]
  by_cases vx : v=x
  · simp [vx]
  · simp [va,vb,vx]

/-- The same gluing rule with port signatures rather than pre-specified
closed subgraphs. It applies to K4 with three inflated terminal shores
of residues (1,1,0), using T2 for the first two caps and F1 for the last. -/
theorem singleton_joins_two_signatures
    {A B C : Finset V} {p q : Fin 3→V} {i j : Fin 3} {x : V}
    (disAB : Disjoint A B) (disAC : Disjoint A C) (disBC : Disjoint B C)
    (xA : x∉A) (xB : x∉B) (xC : x∉C)
    (ax : G.Adj (p i) x) (xb : G.Adj x (q j))
    (aCl : Signature (G:=G) A p (fun k=>if k=i then 1 else 0))
    (bCl : Signature (G:=G) B q (fun k=>if k=j then 1 else 0))
    (cCl : Closed G C) :
    Closed G (insert x (A∪B∪C)) := by
  have raw {S : Finset V} {r : Fin 3→V} (u : Fin 3)
      (hs : Signature (G:=G) S r (fun k=>if k=u then 1 else 0)) :
      r u∈S ∧ Closed G (S.erase (r u)) := by
    obtain ⟨F,hF,_,P,hP⟩ := hs
    have cu : (F u).card=1 := by simpa using (hF u).1
    have mu : r u∈F u := (hF u).2.includes (card_pos.mp (by omega))
    obtain ⟨f,eq⟩ := card_eq_one.mp cu
    have same : F u={r u} := by
      have en : r u = f := mem_singleton.mp (eq ▸ mu)
      exact eq.trans (congrArg singleton en.symm)
    have all : (univ : Finset (Fin 3)).biUnion F={r u} := by
      ext x
      constructor
      · intro m
        obtain ⟨k,_,hk⟩ := mem_biUnion.mp m
        by_cases e : k=u
        · simpa [e,same] using hk
        · have empty : F k=∅ := card_eq_zero.mp (by simpa [e] using (hF k).1)
          exact (not_mem_empty _ (empty ▸ hk)).elim
      · intro m
        exact mem_biUnion.mpr ⟨u,mem_univ _,same.symm ▸ m⟩
    rw [all,sdiff_singleton_eq_erase] at hP
    exact ⟨(hF u).2.inside mu,⟨P,hP⟩⟩
  obtain ⟨a,fa⟩ := raw i aCl
  obtain ⟨b,fb⟩ := raw j bCl
  exact singleton_joins_two_leaf_shores a b disAB disAC disBC xA xB xC ax xb fa fb cCl

#print axioms singleton_joins_two_leaf_shores
#print axioms singleton_joins_two_signatures
end KelmansCactus.AtomicBridge
