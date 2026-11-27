import SparseLink28

namespace Graffiti384b.Sparse28
open Finset SimpleGraph EarFrame33
open private EarFrame33.merge_shared from EarFrame33
open private CubicShore.square_frame CubicShore.half_tight from CubicDiamondCut33
open private CliquePivot33.isolated_degree from CliquePivot33
open private Repair.isolate Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A four-cycle inside the open neighborhood of x can be combined with
a protected ear square if at most one pin is shared. The only outside
cubics have scores two and three, and neither loses a neighbor. -/
theorem sparse_link {A B : Finset V} {e u v x : V} (fr : Frame G A B) (em : e∈A∪B)
    (pos : ∀ w,0<trianglesAt G w) (fi : Function.Injective (trianglesAt G))
    (ear : trianglesAt G e=1) (two : trianglesAt G u=2) (three : trianglesAt G v=3)
    (half : Fintype.card V≤2*gamma G) (xm : x∉A∪B) (ux : ¬G.Adj u x) (vx : ¬G.Adj v x)
    (one : nbr G x (A∪B)≤1) : CommonSparse G (G.neighborFinset x) := by
  classical
  intro a am b bm ab
  apply Nat.le_of_not_gt
  intro many
  obtain ⟨p,pm,q,qm,pq⟩ := one_lt_card.mp many
  obtain ⟨pn,ap,bp⟩ := mem_filter.mp pm
  obtain ⟨qn,aq,bq⟩ := mem_filter.mp qm
  let P : Finset V := {a,b}
  let Q : Finset V := {p,q}
  have fa : Frame G P Q := CubicShore.square_frame G ap aq bp.symm bq.symm ab pq
  have pN : P⊆G.neighborFinset x := insert_subset am (singleton_subset_iff.mpr bm)
  have qN : Q⊆G.neighborFinset x := insert_subset pn (singleton_subset_iff.mpr qn)
  have over := card_le_card (show (A∪B)∩(P∪Q)⊆(A∪B).filter (G.Adj x) from by
    intro z zm; obtain ⟨zf,zp⟩ := mem_inter.mp zm
    exact mem_filter.mpr ⟨zf,(G.mem_neighborFinset ..).mp ((union_subset pN qN) zp)⟩)
  have sees {S : Finset V} (sub : S⊆G.neighborFinset x) (sz : S.card=2) : 2≤nbr G x S := by
    simp [nbr,filter_true_of_mem (fun z zm => (G.mem_neighborFinset ..).mp (sub zm)),sz]
  apply (EarFrame33.merge_shared G ∅ fr fa.1 (over.trans one) xm
    (fun m => G.not_mem_neighborFinset_self _ (pN m)) (fun m => G.not_mem_neighborFinset_self _ (qN m))
    (sees pN (card_pair ab)) (sees qN (card_pair pq)) fa.2.1 fa.2.2 ?_) (CubicShore.half_tight G half)
  intro w wf wx _ _
  have w1 : trianglesAt G w≠1 := fun h => wf ((fi (h.trans ear.symm)) ▸ em)
  have cap := Repair.triangles_le_choose G w
  have pw := pos w
  simp only [not_mem_empty,ite_false,Nat.mul_zero,Nat.add_zero]
  rw [CliquePivot33.isolated_degree G wx]
  by_cases edge : G.Adj w x
  · have w2 : trianglesAt G w≠2 := fun h => ux ((fi (h.trans two.symm)) ▸ edge)
    have w3 : trianglesAt G w≠3 := fun h => vx ((fi (h.trans three.symm)) ▸ edge)
    have d : 4≤G.degree w := by
      apply Nat.le_of_not_gt; intro small
      have z := cap.trans (Nat.choose_le_choose 2 (Nat.le_of_lt_succ small : G.degree w≤3))
      change trianglesAt G w≤3 at z; omega
    rw [card_erase_of_mem ((G.mem_neighborFinset ..).mpr edge),card_neighborFinset_eq_degree]; omega
  · rw [erase_eq_of_not_mem (fun m => edge ((G.mem_neighborFinset ..).mp m)),card_neighborFinset_eq_degree]
    apply Nat.le_of_not_gt; intro small
    have z := cap.trans (Nat.choose_le_choose 2 (Nat.le_of_lt_succ small : G.degree w≤2))
    rw [Nat.choose_self] at z; omega

end Graffiti384b.Sparse28
#print axioms Graffiti384b.Sparse28.sparse_link
