import EarFrame33

namespace Graffiti384b.EarAttachment33
open Finset SimpleGraph CliquePivot33 EarFrame33 EarExchange33
open private Repair.triangles_le_choose Repair.nbr_mono from Repair384b
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private OneEar.deg2 from OneEarFinish384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Any frame covering the ear meets every five-clique. If the overlap has
size at most one, both remaining cubic scores are forced outside the frame
and away from all roots. They cover the four other clique vertices exactly. -/
theorem frame_obstruction {e : V} (de : H.degree e=2) (positive : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) {R A B C : Finset V} (tight : Tight H R)
    (frame : Frame H A B) (ear : e∈A∪B) (cl : H.IsNClique 5 C) (over : ((A∪B)∩C).card≤1) :
    let cub := univ.filter (fun v => H.degree v=3)
    let rest := C\(A∪B)
    ((A∪B)∩C).card=1 ∧ cub.card=2 ∧ cub.image (trianglesAt H)=Icc 2 3 ∧
      (∀ v∈cub,v∉C ∧ v∉A∪B ∧ v∉R ∧ nbr H v rest=2) ∧
      rest=cub.biUnion (fun v => rest.filter (H.Adj v)) := by
  classical
  let F := A∪B
  let K := C\F
  let U := univ.filter (fun v => H.degree v=3)
  let L := U.filter (fun v => v∉C ∧ v∉F ∧ v∉R ∧ nbr H v C≤2)
  have one (v : V) (d : H.degree v=2) : trianglesAt H v=1 := by
    have small := Repair.triangles_le_choose H v
    rw [d,Nat.choose_self] at small
    have := positive v; omega
  have min (v : V) (off : v∉F) : 2≤H.degree v ∧ (v∉R → 3≤H.degree v) := by
    obtain ⟨a,b,va,vb,ab⟩ := (TrianglePrune.triangle_iff H v).mp (positive v)
    have two := OneEar.deg2 H ab.ne va vb
    have ne : H.degree v≠2 := fun dv => off ((inj ((one v dv).trans (one e de).symm)) ▸ ear)
    exact ⟨two,fun _ => by omega⟩
  have imageSub : U.image (trianglesAt H)⊆Icc 2 3 := by
    intro j jm
    obtain ⟨v,vm,rfl⟩ := mem_image.mp jm
    have dv := (mem_filter.mp vm).2
    have hi := Repair.triangles_le_choose H v
    rw [dv] at hi
    have ne : trianglesAt H v≠1 := by
      intro h; have eq := inj (h.trans (one e de).symm); subst v; omega
    have := positive v
    exact mem_Icc.mpr ⟨by omega,hi⟩
  have num : (Icc 2 3 : Finset ℕ).card=2 := by decide
  have uc := card_le_card imageSub
  rw [card_image_of_injective _ inj,num] at uc
  have cover : K⊆L.biUnion (fun v => K.filter (H.Adj v)) := by
    intro x xm
    obtain ⟨xc,off⟩ := mem_sdiff.mp xm
    obtain ⟨v,vc,d,edge,vr,vf,nbrs⟩ := EarFrame33.cover H R A B frame min inj tight cl xc over off
    exact mem_biUnion.mpr ⟨v,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,d⟩,vc,vf,vr,nbrs⟩,
      mem_filter.mpr ⟨xm,edge⟩⟩
  have per (v : V) (vm : v∈L) : nbr H v K≤2 :=
    (Repair.nbr_mono H _ (show K⊆C from sdiff_subset)).trans (mem_filter.mp vm).2.2.2.2
  have total : K.card≤∑ v∈L,nbr H v K := (card_le_card cover).trans card_biUnion_le
  have limit : (∑ v∈L,nbr H v K)≤L.card*2 := by
    calc _ ≤ ∑ _v∈L,2 := sum_le_sum per
         _ = _ := by simp
  have size := card_sdiff_add_card_inter C F
  rw [inter_comm C F,cl.2] at size
  change K.card+(F∩C).card=5 at size
  change (F∩C).card≤1 at over
  have lu : L⊆U := filter_subset _ _
  have lc := card_le_card lu
  have eq : L=U := eq_of_subset_of_card_le lu (by omega)
  have count : U.card=2 := by omega
  have exactImage := eq_of_subset_of_card_le imageSub (by rw [num,card_image_of_injective _ inj,count])
  change (F∩C).card=1 ∧ U.card=2 ∧ U.image (trianglesAt H)=Icc 2 3 ∧ _
  refine ⟨by omega,count,exactImage,?_,?_⟩
  · intro v vu
    have vl : v∈L := eq ▸ vu
    obtain ⟨vc,vf,vr,_⟩ := (mem_filter.mp vl).2
    refine ⟨vc,vf,vr,?_⟩
    have other : (∑ u∈L.erase v,nbr H u K)≤(L.erase v).card*2 := by
      calc _ ≤ ∑ _u∈L.erase v,2 := sum_le_sum (fun u m => per u (mem_of_mem_erase m))
           _ = _ := by simp
    rw [card_erase_of_mem vl] at other
    have add := sum_erase_add L (fun u => nbr H u K) vl
    dsimp only at add
    have upper := per v vl
    change nbr H v K=2
    omega
  · change K=U.biUnion _
    rw [← eq]
    exact Subset.antisymm cover (by intro x m; obtain ⟨_,_,h⟩ := mem_biUnion.mp m; exact (mem_filter.mp h).1)

/-- If the root of a retained leaf is cubic, every ear frame meets every
five-clique in at least two vertices. -/
theorem rooted_overlap {e a : V} (de : H.degree e=2) (da : H.degree a=3)
    (positive : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {A B C : Finset V} (tight : Tight H {a}) (frame : Frame H A B) (ear : e∈A∪B)
    (cl : H.IsNClique 5 C) : 2≤((A∪B)∩C).card := by
  by_contra! few
  obtain ⟨_,_,_,restr,_⟩ := frame_obstruction H de positive inj tight frame ear cl (by omega)
  exact (restr a (mem_filter.mpr ⟨mem_univ _,da⟩)).2.2.1 (mem_singleton_self _)

omit [Fintype V] in
/-- Alternating cycles provide frames. More generally the successor may
be any fixed-point-free permutation, allowing several cycles. -/
theorem alternating_frame {I : Type*} [Fintype I] (u v : I ↪ V) (next : Equiv.Perm I)
    (moves : ∀ i,next i≠i) (sep : ∀ i j,u i≠v j)
    (straight : ∀ i,H.Adj (u i) (v i)) (cross : ∀ i,H.Adj (u i) (v (next i))) :
    Frame H (univ.image u) (univ.image v) := by
  classical
  have um (i : I) : u i∈univ.image u := mem_image_of_mem _ (mem_univ _)
  have vm (i : I) : v i∈univ.image v := mem_image_of_mem _ (mem_univ _)
  refine ⟨disjoint_left.mpr ?_,?_,?_⟩
  · intro x xu xv
    obtain ⟨i,_,rfl⟩ := mem_image.mp xu
    obtain ⟨j,_,eq⟩ := mem_image.mp xv
    exact sep i j eq.symm
  · intro x xm
    obtain ⟨i,_,rfl⟩ := mem_image.mp xm
    exact PinnedColor34.two H (fun eq => moves i (v.injective eq.symm)) (straight i) (cross i) (vm i) (vm _)
  · intro x xm
    obtain ⟨i,_,rfl⟩ := mem_image.mp xm
    let j := next.symm i
    have ji : next j=i := next.apply_symm_apply i
    have diff : i≠j := fun eq => moves j (ji.trans eq)
    exact PinnedColor34.two H (fun eq => diff (u.injective eq)) (straight i).symm
      (ji ▸ (cross j).symm) (um i) (um j)

/-- If both anchors miss a five-clique, each of their common neighbors
other than the ear must belong to that clique. -/
theorem common_neighbor {e b c w : V} (de : H.degree e=2) (positive : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) {R C : Finset V} (tight : Tight H R)
    (cl : H.IsNClique 5 C) (ec : e∉C) (bc : b∉C) (cc : c∉C) (ne : b≠c) (ew : e≠w)
    (eb : H.Adj e b) (ec' : H.Adj e c) (wb : H.Adj w b) (wc : H.Adj w c) : w∈C := by
  classical
  by_contra outside
  let A : Finset V := {e,w}
  let B : Finset V := {b,c}
  have frame : Frame H A B := by
    refine ⟨?_,?_,?_⟩
    · simp [A,B,Finset.disjoint_left,eb.ne,ec'.ne,wb.ne,wc.ne]
    · intro v vm
      rcases (show v=e ∨ v=w by simpa [A] using vm) with rfl|rfl
      · exact PinnedColor34.two H ne eb ec' (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))
      · exact PinnedColor34.two H ne wb wc (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))
    · intro v vm
      rcases (show v=b ∨ v=c by simpa [B] using vm) with rfl|rfl
      · exact PinnedColor34.two H ew eb.symm wb.symm (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))
      · exact PinnedColor34.two H ew ec'.symm wc.symm (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))
  have empty : (A∪B)∩C=∅ := eq_empty_of_forall_not_mem (by
    intro v vm
    obtain ⟨m,inC⟩ := mem_inter.mp vm
    simp only [A,B,mem_union,mem_insert,mem_singleton] at m
    rcases m with (rfl|rfl)|(rfl|rfl)
    · exact ec inC
    · exact outside inC
    · exact bc inC
    · exact cc inC)
  have hit := (frame_obstruction H de positive inj tight frame
    (mem_union_left B (mem_insert_self ..)) cl (by simp [empty])).1
  rw [empty,card_empty] at hit
  omega

end Graffiti384b.EarAttachment33
#print axioms Graffiti384b.EarAttachment33.frame_obstruction
#print axioms Graffiti384b.EarAttachment33.rooted_overlap
#print axioms Graffiti384b.EarAttachment33.alternating_frame
#print axioms Graffiti384b.EarAttachment33.common_neighbor
