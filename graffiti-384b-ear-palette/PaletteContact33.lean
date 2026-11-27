import HighEarRootCap33

namespace Graffiti384b.EarPalette
open Finset SimpleGraph EarFrame33 CliquePivot33 HighEar
open private HighEar.nonEar from HighEarBypass33
open private CubicShore.square_frame CubicShore.half_tight CubicShore.clique_score from CubicDiamondCut33
open private EarAnchor.sees_in_clique from CubicAnchor33
open private EarExchange33.count_insert from Exchange33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The unique clique contact of an ear frame is exactly the clique vertex
with no cubic neighbor. In particular the contact is independent of the frame. -/
theorem single_contact {e q : V} (de : H.degree e=2) (pos : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) {A B C R : Finset V} (tight : Tight H R)
    (fr : Frame H A B) (ef : e∈A∪B) (cl : H.IsNClique 5 C) (touch : (A∪B)∩C={q}) :
    ∀ x∈C,(∃ u,H.degree u=3 ∧ H.Adj u x) ↔ x≠q := by
  classical
  let F := A∪B
  let U := univ.filter (fun u => H.degree u=3)
  let L := U.filter (fun u => nbr H u C≤2)
  let K := C\F
  have over : ((A∪B)∩C).card≤1 := by simp [touch]
  have ⟨_,num,_,contacts,_⟩ := EarAttachment33.frame_obstruction H de pos inj tight fr ef cl over
  have minimum (v : V) (off : v∉A∪B) : 2≤H.degree v ∧ (v∉R → 3≤H.degree v) := by
    have d := HighEar.nonEar H de (t:=v) (fun eq => off (eq ▸ ef)) pos inj
    exact ⟨by omega,fun _ => d⟩
  have block (x : V) (xm : x∈K) : ∃ u∈L,H.Adj u x := by
    obtain ⟨mc,off⟩ := mem_sdiff.mp xm
    obtain ⟨u,_,du,edge,_,_,cap⟩ := EarFrame33.cover H R A B fr minimum inj tight cl mc over off
    exact ⟨u,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,du⟩,cap⟩,edge⟩
  have ks : K.card=4 := by
    have h := card_sdiff_add_card_inter C F
    rw [inter_comm C F,show F∩C={q} from touch,card_singleton,cl.2] at h
    change K.card+1=5 at h; omega
  have cover : K⊆L.biUnion (fun u => K.filter (H.Adj u)) := by
    intro x xm; obtain ⟨u,um,ux⟩ := block x xm
    exact mem_biUnion.mpr ⟨u,um,mem_filter.mpr ⟨xm,ux⟩⟩
  have lU : L⊆U := filter_subset ..
  have per (u : V) (um : u∈L) : nbr H u K=2 := (contacts u (lU um)).2.2.2
  have cap : K.card≤L.card*2 := calc
    _ ≤ ∑ u∈L,nbr H u K := (card_le_card cover).trans card_biUnion_le
    _ = ∑ _u∈L,2 := sum_congr rfl per
    _ = _ := by simp
  change U.card=2 at num
  have eq : L=U := eq_of_subset_of_card_le lU (by omega)
  have qF : q∈F := (mem_inter.mp (show q∈F∩C from touch ▸ mem_singleton_self _)).1
  have qc : q∈C := (mem_inter.mp (show q∈F∩C from touch ▸ mem_singleton_self _)).2
  have split : insert q K=C := by
    apply Subset.antisymm (insert_subset qc sdiff_subset); intro z zc
    by_cases m : z∈F
    · have one : z∈({q}:Finset V) := touch ▸ mem_inter.mpr ⟨m,zc⟩
      exact mem_insert.mpr (Or.inl (mem_singleton.mp one))
    · exact mem_insert_of_mem (mem_sdiff.mpr ⟨zc,m⟩)
  intro x xc
  constructor
  · rintro ⟨u,du,ux⟩ hx
    subst x
    have ul : u∈L := eq ▸ mem_filter.mpr ⟨mem_univ _,du⟩
    have low := (mem_filter.mp ul).2
    have add := EarExchange33.count_insert H q u (show q∉K from fun m => (mem_sdiff.mp m).2 qF)
    rw [split,if_pos ux] at add
    have n := per u ul; omega
  · intro diff
    have inK : x∈K := (mem_insert.mp (show x∈insert q K from split ▸ xc)).resolve_left diff
    obtain ⟨u,um,ux⟩ := block x inK
    exact ⟨u,(mem_filter.mp (lU um)).2,ux⟩

omit [Fintype V] in
private theorem touch_square {e a c w q : V} {C : Finset V}
    (qc : q∈C) (qF : q∈({e,w}:Finset V)∪{a,c})
    (only : ∀ z∈({e,w}:Finset V)∪{a,c},z∈C → z=q) :
    ((({e,w}:Finset V)∪{a,c})∩C)={q} := by
  ext z; constructor
  · intro m; exact mem_singleton.mpr (only z (mem_inter.mp m).1 (mem_inter.mp m).2)
  · intro h; exact mem_singleton.mp h ▸ mem_inter.mpr ⟨qF,qc⟩

/-- Two common neighbors in addition to the ear force its endpoint pair to
meet every five-clique. There is no restriction on the degrees of the endpoints. -/
theorem hit_clique {e a c s t : V} (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : a≠c)
    (as' : H.Adj a s) (cs : H.Adj c s) (se : s≠e)
    (at' : H.Adj a t) (ct : H.Adj c t) (te : t≠e) (st : s≠t)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) : a∈C ∨ c∈C := by
  classical
  by_contra! none
  have en : e∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have contact {w : V} (aw : H.Adj a w) (cw : H.Adj c w) (we : w≠e) :
      w∈C ∧ ∀ x∈C,(∃ u,H.degree u=3 ∧ H.Adj u x) ↔ x≠w := by
    have wc := EarAttachment33.common_neighbor H de pos inj tight cl en none.1 none.2 ac we.symm ea ec aw.symm cw.symm
    have f := CubicShore.square_frame H ea ec aw cw we.symm ac
    have touch := touch_square (e:=e) (w:=w) (a:=a) (c:=c) wc (by simp) (by
      intro z zm zc
      simp only [mem_union,mem_insert,mem_singleton] at zm
      rcases zm with (rfl|rfl)|(rfl|rfl)
      · exact (en zc).elim
      · rfl
      · exact (none.1 zc).elim
      · exact (none.2 zc).elim)
    exact ⟨wc,single_contact H de pos inj tight f (by simp) cl touch⟩
  obtain ⟨sc,sp⟩ := contact as' cs se
  obtain ⟨_,tp⟩ := contact at' ct te
  exact (sp s sc).mp ((tp s sc).mpr st) rfl

end Graffiti384b.EarPalette
#print axioms Graffiti384b.EarPalette.single_contact
#print axioms Graffiti384b.EarPalette.hit_clique
