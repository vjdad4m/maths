import AnchorDeletion33

namespace Graffiti384b.EarAnchor
open Finset SimpleGraph CliquePivot33 EarExchange33
open private Repair.nbr_mono Repair.nbr_add Repair.full_nbr from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

private def mask (W : Finset V) : SimpleGraph V where
  Adj u v := u∈W ∧ v∈W ∧ H.Adj u v
  symm := fun _ _ ⟨u,v,e⟩ => ⟨v,u,e.symm⟩
  loopless := fun v h => H.loopless v h.2.2
private instance (W : Finset V) : DecidableRel (mask H W).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

omit [Fintype V] in
private theorem masked {W : Finset V} {v : V} (vm : v∈W) (A : Finset V) :
    nbr (mask H W) v A=nbr H v (W∩A) := by
  unfold nbr; congr 1; ext w
  simp only [mem_filter,mem_inter,mask,vm,true_and]; tauto

/-- A four-clique in the neighborhood of the opposite anchor can be pinned
two against two. Both sides then meet the additional domination guard. -/
theorem guarded_cut {W C : Finset V} {c : V} (cl : H.IsNClique 4 C) (inside : C⊆W)
    (support : ∀ v∈C,H.Adj c v) (minimum : ∀ v∈W,3≤nbr H v W) :
    ∃ X,Covers H W X ∧ Meets H c X ∧ 2*X.card≤W.card := by
  classical
  obtain ⟨P,pc,ps⟩ := exists_subset_card_eq (show 2≤C.card by rw [cl.2]; decide)
  let Q := C\P
  have qc : Q⊆C := sdiff_subset
  have qs : Q.card=2 := by rw [show Q=C\P from rfl,card_sdiff pc,cl.2,ps]
  have dis : Disjoint P Q := disjoint_left.mpr (fun _ p q => (mem_sdiff.mp q).2 p)
  let J := mask H W
  obtain ⟨A,pa,qb,left,right⟩ := PinnedColor34.cut J P Q dis
  let X := W∩A
  let Y := W∩Aᶜ
  have px : P⊆X := fun _ m => mem_inter.mpr ⟨inside (pc m),pa m⟩
  have qy : Q⊆Y := fun _ m => mem_inter.mpr ⟨inside (qc m),qb m⟩
  have xy : Disjoint X Y := disjoint_left.mpr (fun _ x y => mem_compl.mp (mem_inter.mp y).2 (mem_inter.mp x).2)
  have allW : X∪Y=W := by ext v; simp only [X,Y,mem_inter,mem_union,mem_compl]; tauto
  have see {v : V} (vc : v∈C) {D : Finset V} (dc : D⊆C) (out : v∉D) (ds : D.card=2) : 2≤nbr H v D := by
    have h : D.filter (H.Adj v)=D := filter_true_of_mem (fun w wm => cl.1 vc (dc wm) (fun eq => out (eq ▸ wm)))
    simp only [nbr,h,ds,le_rfl]
  have cx : Covers H W X := by
    refine ⟨inter_subset_left,?_⟩
    intro v vm none
    by_cases vq : v∈Q
    · exact (see (qc vq) pc (mem_sdiff.mp vq).2 ps).trans (Repair.nbr_mono H v px)
    have outside : v∈Aᶜ := mem_compl.mpr (fun va => none (mem_inter.mpr ⟨vm,va⟩))
    have h := right v outside vq
    change nbr (mask H W) v Aᶜ<nbr (mask H W) v A at h
    rw [masked H vm,masked H vm] at h
    have sum := Repair.nbr_add H v xy
    rw [allW] at sum
    have := minimum v vm
    change nbr H v Y<nbr H v X at h
    omega
  have cy : Covers H W Y := by
    refine ⟨inter_subset_left,?_⟩
    intro v vm none
    by_cases vp : v∈P
    · exact (see (pc vp) qc (fun m => disjoint_left.mp dis vp m) qs).trans (Repair.nbr_mono H v qy)
    have va : v∈A := by
      apply Classical.byContradiction; intro absent; exact none (mem_inter.mpr ⟨vm,mem_compl.mpr absent⟩)
    have h := left v va vp
    change nbr (mask H W) v A≤nbr (mask H W) v Aᶜ at h
    rw [masked H vm,masked H vm] at h
    have sum := Repair.nbr_add H v xy
    rw [allW] at sum
    have := minimum v vm
    change nbr H v X≤nbr H v Y at h
    omega
  obtain ⟨p,pm⟩ := card_pos.mp (show 0<P.card by omega)
  obtain ⟨q,qm⟩ := card_pos.mp (show 0<Q.card by omega)
  have sum := card_union_of_disjoint xy
  rw [allW] at sum
  by_cases small : 2*X.card≤W.card
  · exact ⟨X,cx,⟨p,px pm,support p (pc pm)⟩,small⟩
  · exact ⟨Y,cy,⟨q,qy qm,support q (qc qm)⟩,by omega⟩

omit [Fintype V] in
/-- With one possible exception to residual minimum degree three, adding
that vertex to both sides of a maximum cut gives the ceiling-half bound. -/
theorem single_low {W : Finset V} {v : V} (vm : v∈W)
    (minimum : ∀ x∈W,x≠v → 3≤nbr H x W) :
    ∃ X,Covers H W X ∧ 2*X.card≤W.card+1 := by
  classical
  obtain ⟨A,B,dis,parts,left,right⟩ := Repair.asymmetric_cut H W
  have aW : A⊆W := parts ▸ subset_union_left
  have bW : B⊆W := parts ▸ subset_union_right
  have split (x : V) := Repair.nbr_add H x dis
  have ax : Covers H W (insert v A) := by
    refine ⟨insert_subset vm aW,?_⟩
    intro x xm no
    have xa : x∉A := fun m => no (mem_insert_of_mem m)
    have xb := (mem_union.mp (show x∈A∪B from parts ▸ xm)).resolve_left xa
    have h := right x xb
    have s := split x; rw [parts] at s
    have lo := minimum x xm (fun eq => no (eq ▸ mem_insert_self ..))
    exact (show 2≤nbr H x A by omega).trans (Repair.nbr_mono H x (subset_insert ..))
  have bx : Covers H W (insert v B) := by
    refine ⟨insert_subset vm bW,?_⟩
    intro x xm no
    have xb : x∉B := fun m => no (mem_insert_of_mem m)
    have xa := (mem_union.mp (show x∈A∪B from parts ▸ xm)).resolve_right xb
    have h := left x xa
    have s := split x; rw [parts] at s
    have lo := minimum x xm (fun eq => no (eq ▸ mem_insert_self ..))
    exact (show 2≤nbr H x B by omega).trans (Repair.nbr_mono H x (subset_insert ..))
  have sz := card_union_of_disjoint dis; rw [parts] at sz
  have ca := card_insert_le v A; have cb := card_insert_le v B
  have either := mem_union.mp (show v∈A∪B from parts ▸ vm)
  by_cases sm : 2*(insert v A).card≤W.card+1
  · exact ⟨_,ax,sm⟩
  · refine ⟨_,bx,?_⟩
    rcases either with av|bv
    · rw [insert_eq_of_mem av] at sm; omega
    · rw [insert_eq_of_mem bv]; omega

end Graffiti384b.EarAnchor
#print axioms Graffiti384b.EarAnchor.guarded_cut
#print axioms Graffiti384b.EarAnchor.single_low
