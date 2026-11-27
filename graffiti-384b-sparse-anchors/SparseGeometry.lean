import AnchorCuts
namespace Graffiti384b.SparsePairs
open Finset SimpleGraph
open private Squares29.pair_at from SquareTriple29
open private Repair.linkEdges Repair.edge_info from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private noncomputable def inner (X : Finset V) : Finset (Finset V) := by
  classical
  exact (X.powersetCard 2).filter (fun a => ∀ i∈a,∀ j∈a,i≠j → G.Adj i j)

private theorem inner_match (X : Finset V) (small : ∀a∈X,nbr G a X≤1) :
    2*(inner G X).card≤X.card := by
  classical
  let I := inner G X
  have info {a : Finset V} (am : a∈I) : a⊆X ∧ a.card=2 ∧ ∀i∈a,∀j∈a,i≠j → G.Adj i j :=
    ⟨(mem_powersetCard.mp (mem_filter.mp am).1).1,(mem_powersetCard.mp (mem_filter.mp am).1).2,(mem_filter.mp am).2⟩
  have dis : (I:Set (Finset V)).PairwiseDisjoint id := by
    intro a am b bm ab
    apply disjoint_left.mpr
    intro v va vb
    obtain ⟨ia,ca,ea⟩ := info am
    obtain ⟨ib,cb,eb⟩ := info bm
    obtain ⟨x,vx,ax⟩ := Squares29.pair_at ca va
    obtain ⟨y,vy,by'⟩ := Squares29.pair_at cb vb
    have xa : x∈a := ax ▸ mem_insert_of_mem (mem_singleton_self _)
    have yb : y∈b := by' ▸ mem_insert_of_mem (mem_singleton_self _)
    have xy : x≠y := fun h => ab (ax.trans (h ▸ by'.symm))
    have ct := PinnedColor34.two G xy (ea _ va _ xa vx) (eb _ vb _ yb vy) (ia xa) (ib yb)
    have lim := small v (ia va); omega
  have sub : I.biUnion id⊆X := by
    intro i im; obtain ⟨a,am,ia⟩ := mem_biUnion.mp im; exact (info am).1 ia
  have ct := card_le_card sub
  rw [card_biUnion dis,sum_congr rfl (fun a am => show (id a).card=2 from (info am).2.1),sum_const,smul_eq_mul] at ct
  change 2*I.card≤_; omega

/-- Count triangles inside the exterior row, across the two rows, and wholly
inside the four anchors. At most one triangle lies wholly in the anchors. -/
theorem link_with_triangle (A B : Finset V) (ac : A.card=4) {v p : V} (va : v∈A) (pa : p∈A)
    (pd : nbr G p A≤1) (lowCount : nbr G v (LowSample.twos G)≤1) (mixed present : Bool)
    (sparse : Bool) (matchingRow : sparse=true → ∀ i∈(high G\A).filter (G.Adj v),nbr G i ((high G\A).filter (G.Adj v))≤1)
    (noPure : present=false → ∀ i∈A,∀ j∈A,G.Adj v i → G.Adj v j → ¬G.Adj i j)
    (allowed : ∀ i∈high G\A,∀ j∈A,G.Adj v i → G.Adj v j → G.Adj i j → j∈B)
    (noMix : mixed=false → ∀ i∈high G\A,∀ j∈A,G.Adj v i → G.Adj v j → ¬G.Adj i j) :
    let x := nbr G v (high G\A)
    let y := nbr G v B
    trianglesAt G v≤1+(if v=p ∨ present=false then 0 else 1)+(if sparse then x/2 else x.choose 2)+(if mixed then x*y else 0) := by
  classical
  let X := (high G\A).filter (G.Adj v)
  let H := B.filter (G.Adj v)
  let edge (z : V×V) : Finset V := {z.1,z.2}
  let M := if mixed then (X×ˢH).image edge else ∅
  let I : Finset (Finset V) := if v=p ∨ present=false then ∅ else {(A.erase p).erase v}
  have off {u i j : V} (iu : G.Adj u i) (ju : G.Adj u j) (ij : i≠j) (ia : i∈A) (ja : j∈A) : u≠p := by
    rintro rfl; have h := PinnedColor34.two G ij iu ju ia ja; omega
  have pure {i j : V} (vi : G.Adj v i) (vj : G.Adj v j) (ij : G.Adj i j) (ia : i∈A) (ja : j∈A) :
      ({i,j}:Finset V)∈I := by
    have vp := off vi vj ij.ne ia ja
    have ip := off vi.symm ij vj.ne va ja
    have jp := off vj.symm ij.symm vi.ne va ia
    have ve : v∈A.erase p := mem_erase.mpr ⟨vp,va⟩
    have sub : {i,j}⊆(A.erase p).erase v := insert_subset (mem_erase.mpr ⟨vi.ne.symm,mem_erase.mpr ⟨ip,ia⟩⟩)
      (singleton_subset_iff.mpr (mem_erase.mpr ⟨vj.ne.symm,mem_erase.mpr ⟨jp,ja⟩⟩))
    have eq := eq_of_subset_of_card_le sub (by rw [card_erase_of_mem ve,card_erase_of_mem pa,ac,card_pair ij.ne])
    have yes : present≠false := fun h => noPure h i ia j ja vi vj ij
    simpa [I,vp,yes] using eq
  have cross {i j : V} (vi : G.Adj v i) (vj : G.Adj v j) (ij : G.Adj i j) (ix : i∈high G\A) (ja : j∈A) :
      ({i,j}:Finset V)∈M := by
    cases mixed with
    | false => exact (noMix rfl i ix j ja vi vj ij).elim
    | true => exact mem_image.mpr ⟨(i,j),mem_product.mpr ⟨mem_filter.mpr ⟨ix,vi⟩,mem_filter.mpr ⟨allowed i ix j ja vi vj ij,vj⟩⟩,rfl⟩
  let code (w : V) := insert w ((G.neighborFinset w).erase v)
  have low {i j : V} (vi : G.Adj v i) (vj : G.Adj v j) (ij : G.Adj i j) (ih : i∉high G) :
      i∈LowSample.twos G ∧ code i={i,j} := by
    have sub : {v,j}⊆G.neighborFinset i := insert_subset ((G.mem_neighborFinset ..).mpr vi.symm)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr ij))
    have lower := card_le_card sub
    rw [card_pair vj.ne,card_neighborFinset_eq_degree] at lower
    have upper : G.degree i≤2 := Nat.le_of_not_gt (fun h => ih (mem_filter.mpr ⟨mem_univ _,h⟩))
    have eq := eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree,card_pair vj.ne]; exact upper)
    exact ⟨mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,lower⟩,ih⟩,by simp [code,←eq,vj.ne,vj.ne.symm]⟩
  let L := ((LowSample.twos G).filter (G.Adj v)).image code
  have cover : Repair.linkEdges G v⊆((L∪I)∪inner G X)∪M := by
    intro t tm; obtain ⟨sub,sz,cl⟩ := Repair.edge_info G tm
    obtain ⟨i,j,ij,rfl⟩ := card_eq_two.mp sz
    have im : i∈({i,j}:Finset V) := mem_insert_self ..
    have jm : j∈({i,j}:Finset V) := mem_insert_of_mem (mem_singleton_self _)
    have vi := (G.mem_neighborFinset ..).mp (sub im)
    have vj := (G.mem_neighborFinset ..).mp (sub jm)
    have near := cl _ im _ jm ij
    by_cases ih : i∈high G
    · by_cases jh : j∈high G
      · by_cases ia : i∈A
        · by_cases ja : j∈A
          · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (pure vi vj near ia ja)))
          · exact mem_union_right _ ((pair_comm i j) ▸ cross vj vi near.symm (mem_sdiff.mpr ⟨jh,ja⟩) ia)
        · by_cases ja : j∈A
          · exact mem_union_right _ (cross vi vj near (mem_sdiff.mpr ⟨ih,ia⟩) ja)
          · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_powersetCard.mpr ⟨insert_subset (mem_filter.mpr ⟨mem_sdiff.mpr ⟨ih,ia⟩,vi⟩)
              (singleton_subset_iff.mpr (mem_filter.mpr ⟨mem_sdiff.mpr ⟨jh,ja⟩,vj⟩)),sz⟩,cl⟩))
      · obtain ⟨em,eq⟩ := low vj vi near.symm jh
        exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨j,mem_filter.mpr ⟨em,vj⟩,eq.trans (pair_comm ..)⟩)))
    · obtain ⟨em,eq⟩ := low vi vj near ih
      exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨i,mem_filter.mpr ⟨em,vi⟩,eq⟩)))
  have ll : L.card≤1 := card_image_le.trans lowCount
  have ic : I.card≤(if v=p ∨ present=false then 0 else 1) := by by_cases h : v=p ∨ present=false <;> simp [I,h]
  have mc : M.card≤(if mixed then X.card*H.card else 0) := by
    cases mixed <;> simp only [M,Bool.false_eq_true,if_false,card_empty,le_refl,if_true]
    exact card_image_le.trans_eq (card_product ..)
  have cnt := (card_le_card cover).trans (card_union_le ..)
  have ci := card_union_le (L∪I) (inner G X)
  have li := card_union_le L I
  have xc : (inner G X).card≤(if sparse then X.card/2 else X.card.choose 2) := by
    cases sparse with
    | true => have h := inner_match G X (matchingRow rfl); simp only [if_true]; omega
    | false => exact (card_le_card (filter_subset ..)).trans_eq (card_powersetCard 2 X)
  change trianglesAt G v≤_ at cnt
  change trianglesAt G v≤1+(if v=p ∨ present=false then 0 else 1)+(if sparse then X.card/2 else X.card.choose 2)+(if mixed then X.card*H.card else 0)
  omega

theorem link_local (A B : Finset V) (ac : A.card=4) {v p : V} (va : v∈A) (pa : p∈A)
    (pd : nbr G p A≤1) (lowCount : nbr G v (LowSample.twos G)≤1) (mixed : Bool)
    (sparse : Bool) (matchingRow : sparse=true → ∀ i∈(high G\A).filter (G.Adj v),nbr G i ((high G\A).filter (G.Adj v))≤1)
    (allowed : ∀ i∈high G\A,∀ j∈A,G.Adj v i → G.Adj v j → G.Adj i j → j∈B)
    (noMix : mixed=false → ∀ i∈high G\A,∀ j∈A,G.Adj v i → G.Adj v j → ¬G.Adj i j) :
    let x := nbr G v (high G\A)
    let y := nbr G v B
    trianglesAt G v≤1+(if v=p then 0 else 1)+(if sparse then x/2 else x.choose 2)+(if mixed then x*y else 0) := by
  simpa only [Bool.true_eq_false,or_false] using link_with_triangle G A B ac va pa pd lowCount mixed true sparse matchingRow (by simp) allowed noMix

theorem link_budget (A : Finset V) (ac : A.card=4) {v p : V} (va : v∈A) (pa : p∈A)
    (pd : nbr G p A≤1) (lowCount : nbr G v (LowSample.twos G)≤1) (mixed : Bool)
    (sparse : Bool) (matchingRow : sparse=true → ∀ i∈(high G\A).filter (G.Adj v),nbr G i ((high G\A).filter (G.Adj v))≤1)
    (noMix : mixed=false → ∀ i∈high G\A,∀ j∈A,G.Adj v i → G.Adj v j → ¬G.Adj i j) :
    let x := nbr G v (high G\A)
    let y := nbr G v A
    trianglesAt G v≤1+(if v=p then 0 else 1)+(if sparse then x/2 else x.choose 2)+(if mixed then x*y else 0) := by
  exact link_local G A A ac va pa pd lowCount mixed sparse matchingRow (fun _ _ _ h _ _ _ => h) noMix

end Graffiti384b.SparsePairs
#print axioms Graffiti384b.SparsePairs.link_with_triangle
#print axioms Graffiti384b.SparsePairs.link_local
#print axioms Graffiti384b.SparsePairs.link_budget
