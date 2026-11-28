import Proof384b
namespace Graffiti384b.ShorePairs
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
/-- Adjacent unordered pairs in a given vertex set. -/
def pairs (D : Finset V) : Finset (Finset V) :=
  (D.powersetCard 2).filter (fun p => ∀ x∈p,∀ y∈p,x≠y → H.Adj x y)

theorem pair_mem {D E : Finset V} : E∈pairs H D ↔ ∃ x∈D,∃ y∈D,H.Adj x y ∧ E={x,y} := by
  constructor
  · intro m
    obtain ⟨p,cl⟩ := mem_filter.mp m
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp p
    obtain ⟨x,y,ne,rfl⟩ := card_eq_two.mp sz
    have xmem : x∈({x,y} : Finset V) := mem_insert_self ..
    have ymem : y∈({x,y} : Finset V) := mem_insert_of_mem (mem_singleton_self _)
    exact ⟨x,sub xmem,y,sub ymem,cl x xmem y ymem ne,rfl⟩
  · rintro ⟨x,xm,y,ym,edge,rfl⟩
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨insert_subset xm (singleton_subset_iff.mpr ym),card_pair edge.ne⟩,?_⟩
    intro p hp q hq ne
    rcases (show p=x ∨ p=y by simpa using hp) with rfl|rfl <;>
      rcases (show q=_ ∨ q=_ by simpa only [mem_insert,mem_singleton] using hq) with rfl|rfl <;>
      first | exact (ne rfl).elim | exact edge | exact edge.symm

theorem pairs_insert {D : Finset V} {x : V} (off : x∉D) :
    (pairs H (insert x D)).card=(pairs H D).card+nbr H x D := by
  classical
  let f (y : V) : Finset V := {x,y}
  let M := D.filter (H.Adj x)
  have eq : pairs H (insert x D)=pairs H D ∪ M.image f := by
    ext E; constructor
    · intro m
      obtain ⟨v,vm,w,wm,vw,rfl⟩ := (pair_mem H).mp m
      rcases mem_insert.mp vm with rfl|vD
      · have wd := (mem_insert.mp wm).resolve_left vw.ne.symm
        exact mem_union_right _ (mem_image.mpr ⟨w,mem_filter.mpr ⟨wd,vw⟩,rfl⟩)
      rcases mem_insert.mp wm with rfl|wD
      · exact mem_union_right _ (mem_image.mpr ⟨v,mem_filter.mpr ⟨vD,vw.symm⟩,pair_comm ..⟩)
      · exact mem_union_left _ ((pair_mem H).mpr ⟨v,vD,w,wD,vw,rfl⟩)
    · intro m
      rcases mem_union.mp m with p|q
      · obtain ⟨v,vm,w,wm,vw,rfl⟩ := (pair_mem H).mp p
        exact (pair_mem H).mpr ⟨v,mem_insert_of_mem vm,w,mem_insert_of_mem wm,vw,rfl⟩
      · obtain ⟨y,ym,rfl⟩ := mem_image.mp q
        obtain ⟨yd,xy⟩ := mem_filter.mp ym
        exact (pair_mem H).mpr ⟨x,mem_insert_self ..,y,mem_insert_of_mem yd,xy,rfl⟩
  have dis : Disjoint (pairs H D) (M.image f) := by
    apply disjoint_left.mpr; intro E em fm
    obtain ⟨y,_,rfl⟩ := mem_image.mp fm
    exact off ((mem_powersetCard.mp (mem_filter.mp em).1).1 (mem_insert_self ..))
  have ci : (M.image f).card=M.card := card_image_of_injOn (by
    intro y ym z _ eq
    have m : y∈f z := eq ▸ (show y∈f y from mem_insert_of_mem (mem_singleton_self _))
    exact (mem_insert.mp m).resolve_left (mem_filter.mp ym).2.ne.symm |> mem_singleton.mp)
  rw [eq,card_union_of_disjoint dis,ci]; rfl

end Graffiti384b.ShorePairs

namespace Graffiti384b.ShorePairs
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
private theorem empty_pairs : (pairs G ∅).card=0 := by
  apply Nat.eq_zero_of_le_zero
  exact (card_filter_le ..).trans (by rw [card_powersetCard,card_empty]; decide)

theorem degree_sum (S : Finset V) : (∑ v∈S,nbr G v S)=2*(pairs G S).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [empty_pairs]
  | @insert w S out ih =>
    have add (v : V) : nbr G v (insert w S)=nbr G v S+(if G.Adj w v then 1 else 0) := by
      by_cases h : G.Adj w v
      · simp [nbr,filter_insert,h,h.symm,out,card_insert_of_not_mem]
      · have rev : ¬G.Adj v w := fun a => h a.symm
        simp [nbr,filter_insert,h,rev]
    rw [sum_insert out,pairs_insert G out]
    simp_rw [add]
    rw [sum_add_distrib,ih,sum_boole]
    simp only [G.irrefl,ite_false,Nat.add_zero]
    change nbr G w S+(2*(pairs G S).card+nbr G w S)=2*((pairs G S).card+nbr G w S)
    omega

end Graffiti384b.ShorePairs
#print axioms Graffiti384b.ShorePairs.pair_mem
#print axioms Graffiti384b.ShorePairs.pairs_insert
#print axioms Graffiti384b.ShorePairs.degree_sum
