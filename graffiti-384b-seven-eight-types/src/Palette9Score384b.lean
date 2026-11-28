import SmallPalette384b
namespace Graffiti384b.SmallPalette
end Graffiti384b.SmallPalette

namespace Graffiti384b.SmallPalette.N9
open Graffiti384b.SmallPalette
abbrev Label := Fin 9
abbrev Relation := Rel 9
open SimpleGraph Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem pair_nodup : (orderedPairs 9).Nodup := by decide
private theorem pair_iff (i j : Label) : (i,j)∈orderedPairs 9 ↔ i<j := by
  have all : ∀ i j : Label,(i,j)∈orderedPairs 9 ↔ i<j := by decide
  exact all i j

theorem score_eq_triangles (p : Label ≃ V) (E : Relation)
    (fits : ∀ i j,E i j=true↔G.Adj (p i) (p j)) (v : Label) :
    score E v = trianglesAt G (p v) := by
  classical
  let ok (ij : Label×Label) := E v ij.1 && E v ij.2 && E ij.1 ij.2
  let L := (orderedPairs 9).filter ok
  let U := L.toFinset
  let tag (ij : Label×Label) : Finset V := {p ij.1,p ij.2}
  let W := ((G.neighborFinset (p v)).powersetCard 2).filter
      (fun A=>∀ x∈A,∀ y∈A,x≠y→G.Adj x y)
  have good (i j : Label) : (i,j)∈U ↔
      i<j ∧ G.Adj (p v) (p i) ∧ G.Adj (p v) (p j) ∧ G.Adj (p i) (p j) := by
    simp only [U,L,List.mem_toFinset,List.mem_filter,pair_iff,ok,Prod.fst,Prod.snd,
      Bool.and_eq_true,fits,and_assoc]
  have bij : Set.InjOn tag (U : Set (Label×Label)) := by
    intro ⟨i,j⟩ im ⟨a,b⟩ am eq
    have ij := ((good i j).mp im).1
    have ab := ((good a b).mp am).1
    have ei : p i∈({p a,p b}:Finset V) := by
      change p i ∈ tag (a,b)
      rw [←eq]
      exact mem_insert_self _ _
    have ej : p j∈({p a,p b}:Finset V) := by
      change p j ∈ tag (a,b)
      rw [←eq]
      exact mem_insert_of_mem (mem_singleton_self _)
    simp only [mem_insert,mem_singleton,p.injective.eq_iff] at ei ej
    rcases ei with rfl|rfl <;> rcases ej with rfl|rfl
    · exact (lt_irrefl _ ij).elim
    · rfl
    · exact (lt_asymm ij ab).elim
    · exact (lt_irrefl _ ij).elim
  have union : U.image tag=W := by
    ext Z
    constructor
    · intro Zm
      obtain ⟨⟨i,j⟩,im,rfl⟩ := mem_image.mp Zm
      obtain ⟨ij,vi,vj,edge⟩ := (good i j).mp im
      apply mem_filter.mpr
      refine ⟨mem_powersetCard.mpr ⟨?_,card_pair edge.ne⟩,?_⟩
      · exact insert_subset ((G.mem_neighborFinset _ _).mpr vi)
          (singleton_subset_iff.mpr ((G.mem_neighborFinset _ _).mpr vj))
      · intro a am b bm ne
        simp only [tag,Prod.fst,Prod.snd,mem_insert,mem_singleton] at am bm
        rcases am with rfl|rfl <;> rcases bm with rfl|rfl
        · exact (ne rfl).elim
        · exact edge
        · exact edge.symm
        · exact (ne rfl).elim
    · intro Zm
      obtain ⟨hz,ze⟩ := mem_filter.mp Zm
      obtain ⟨ss,two⟩ := mem_powersetCard.mp hz
      obtain ⟨x,y,xy,rfl⟩ := card_eq_two.mp two
      have xM : x∈({x,y}:Finset V) := mem_insert_self _ _
      have yM : y∈({x,y}:Finset V) := mem_insert_of_mem (mem_singleton_self _)
      obtain ⟨i,rfl⟩ := p.surjective x
      obtain ⟨j,rfl⟩ := p.surjective y
      have vi := (G.mem_neighborFinset _ _).mp (ss xM)
      have vj := (G.mem_neighborFinset _ _).mp (ss yM)
      have adj := ze _ xM _ yM xy
      rcases lt_or_gt_of_ne (fun h=>xy (congrArg p h)) with ord|ord
      · exact mem_image.mpr ⟨(i,j),(good i j).mpr ⟨ord,vi,vj,adj⟩,rfl⟩
      · exact mem_image.mpr ⟨(j,i),(good j i).mpr ⟨ord,vj,vi,adj.symm⟩,by simp [tag,pair_comm]⟩
  change L.length = W.card
  rw [←List.toFinset_card_of_nodup (pair_nodup.filter ok),←union,card_image_iff.mpr bij]


#print axioms score_eq_triangles
end Graffiti384b.SmallPalette.N9
