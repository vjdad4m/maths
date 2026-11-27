import PrivatePivot33

namespace Graffiti384b.RootCut
open Finset SimpleGraph HighEar OneEar EarAnchor CliquePivot33
open private Repair.isolate from Repair384b
open private EarAnchor.sees_in_clique from CubicAnchor33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

theorem exterior_count {e a c : V} (de : H.degree e=2) (ea : H.Adj e a) (ec : H.Adj e c)
    (ac : H.Adj a c) (thin : additional H e a c=∅) :
    trianglesAt H a=1+(pairs H (exterior H e a c)).card := by
  have ear : H.neighborFinset e={a,c} := (eq_of_subset_of_card_le
    (insert_subset ((H.mem_neighborFinset _ _).mpr ea) (singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr ec)))
    (by rw [card_pair ac.ne,card_neighborFinset_eq_degree,de])).symm
  simpa [thin] using (exact_count H ear ea ec ac).2

private theorem ext_info {e a c p : V} (m : p∈exterior H e a c) :
    H.Adj a p ∧ p≠e ∧ p≠a ∧ p≠c := by
  obtain ⟨pn,off⟩ := mem_sdiff.mp m
  have adj := (H.mem_neighborFinset _ _).mp pn
  have z : p≠e ∧ p≠c := by simpa [not_or] using off
  exact ⟨adj,z.1,adj.ne.symm,z.2⟩

theorem edge_cover {e a c : V} (de : H.degree e=2) (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (apart : ¬(a∈C ∧ c∈C))
    {x : V} (xm : x∈C) (safe : Safe H R x) (xa : x≠a) (xc : x≠c)
    {E F : Finset V} (EM : E∈pairs H (exterior H e a c)) (FM : F∈pairs H (exterior H e c a)) : x∈E∪F := by
  apply Classical.byContradiction; intro no
  obtain ⟨p,pm,q,qm,pq,rfl⟩ := (pair_mem H).mp EM
  obtain ⟨u,um,v,vm,uv,rfl⟩ := (pair_mem H).mp FM
  have removed : (x≠p ∧ x≠q) ∧ x≠u ∧ x≠v := by simpa only [mem_union,mem_insert,mem_singleton,not_or] using no
  have ⟨ap,pe,pa,pc⟩ := ext_info H pm
  have ⟨aq,qe,qa,qc⟩ := ext_info H qm
  have ⟨cu,ue,uc,ua⟩ := ext_info H um
  have ⟨cv,ve,vc,va⟩ := ext_info H vm
  exact cannot_survive H de ea ec ac pos inj tight cl safe xm xa xc apart
    (mem_interior.mpr ⟨removed.1.1.symm,pe,pa,pc⟩) (mem_interior.mpr ⟨removed.1.2.symm,qe,qa,qc⟩)
    (mem_interior.mpr ⟨removed.2.1.symm,ue,ua,uc⟩) (mem_interior.mpr ⟨removed.2.2.symm,ve,va,vc⟩)
    ap aq pq cu cv uv

theorem has_edge {e a c : V} (de : H.degree e=2) (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (thin : additional H e a c=∅) (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H)) :
    (pairs H (exterior H e a c)).Nonempty := by
  have val := exterior_count H de ea ec ac thin
  have diff : trianglesAt H a≠1 := fun h => ea.ne (inj ((ear_one H de pos).trans h.symm))
  apply card_pos.mp; omega

/-- Two safe choices exclude either ear endpoint from a five-clique. -/
theorem off_clique {e a c : V} (de : H.degree e=2) (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (thin : additional H e a c=∅) (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C M : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (apart : ¬(a∈C ∧ c∈C))
    (mc : M⊆C) (safe : ∀ x∈M,Safe H R x) (ms : 2≤M.card) : a∉C := by
  classical
  intro am
  have cn : c∉C := fun cm => apart ⟨am,cm⟩
  have en : e∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  obtain ⟨x,xm,xa⟩ := exists_ne_of_one_lt_card (by omega : 1<M.card) a
  have xc : x≠c := fun eq => cn (eq ▸ mc xm)
  let K := C\{a,x}
  have ks : K.card=3 := by rw [show K=C\{a,x} from rfl,card_sdiff (insert_subset am (singleton_subset_iff.mpr (mc xm))),cl.2,card_pair xa.symm]
  obtain ⟨p,pm⟩ := card_pos.mp (show 0<K.card by omega)
  obtain ⟨q,qm,qp⟩ := exists_ne_of_one_lt_card (by omega : 1<K.card) p
  have inD {z : V} (zm : z∈K) : z∈exterior H e a c := by
    obtain ⟨zc,out⟩ := mem_sdiff.mp zm
    have za : z≠a := fun eq => out (eq ▸ mem_insert_self ..)
    exact mem_sdiff.mpr ⟨(H.mem_neighborFinset _ _).mpr (cl.1 am zc za.symm),by
      simp [show z≠e from fun eq => en (eq ▸ zc),show z≠c from fun eq => cn (eq ▸ zc)]⟩
  have E := (pair_mem H).mpr ⟨p,inD pm,q,inD qm,cl.1 (mem_sdiff.mp pm).1 (mem_sdiff.mp qm).1 qp.symm,rfl⟩
  have flip : additional H e c a=∅ := by simpa only [additional,inter_comm] using thin
  obtain ⟨F,FM⟩ := has_edge H de ec ea ac.symm flip pos inj
  have cover := edge_cover H de ea ec ac pos inj tight cl apart (mc xm) (safe x xm) xa xc E FM
  rcases mem_union.mp cover with first|last
  · have xk : x∈K := (mem_insert.mp first).elim (fun eq => eq ▸ pm) (fun m => mem_singleton.mp m ▸ qm)
    exact (mem_sdiff.mp xk).2 (mem_insert_of_mem (mem_singleton_self _))
  · have xd := (mem_powersetCard.mp (mem_filter.mp FM).1).1 last
    have ⟨cx,xe,_,_⟩ := ext_info H xd
    have m := (additional_mem H).mpr ⟨xe,cl.1 am (mc xm) xa.symm,cx⟩
    rw [thin] at m; exact not_mem_empty _ m

/-- If both endpoints see the clique at distinct contacts p,q, deleting
any further safe clique vertex leaves an even route via a third clique vertex. -/
theorem contact_cover {e a c p q x : V} (de : H.degree e=2) (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (an : a∉C) (cn : c∉C)
    (pc : p∈C) (qc : q∈C) (pq : p≠q) (ap : H.Adj a p) (cq : H.Adj c q)
    (xm : x∈C) (safe : Safe H R x) : x∈({p,q}:Finset V) := by
  classical
  apply Classical.byContradiction; intro no
  have off : x≠p ∧ x≠q := by simpa [not_or] using no
  have en : e∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have size : ({x,p,q}:Finset V).card<C.card := by rw [cl.2]; simp [off.1,off.2,pq]
  obtain ⟨z,zm,zo⟩ := exists_mem_not_mem_of_card_lt_card size
  have ⟨zx,zp,zq⟩ := (show z≠x ∧ z≠p ∧ z≠q by simpa [not_or] using zo)
  let J := Repair.isolate H x
  have aC {w : V} (m : w∈C) : a≠w := fun eq => an (eq ▸ m)
  have cC {w : V} (m : w∈C) : c≠w := fun eq => cn (eq ▸ m)
  have eC {w : V} (m : w∈C) : e≠w := fun eq => en (eq ▸ m)
  let f : ℕ → V := fun i => match i with | 0 => a | 1 => p | 2 => z | 3 => q | _ => c
  have L : J.Adj a p := ⟨ap,aC xm,off.1.symm⟩
  have A : J.Adj p z := ⟨cl.1 pc zm zp.symm,off.1.symm,zx⟩
  have B : J.Adj z q := ⟨cl.1 zm qc zq,zx,off.2.symm⟩
  have T : J.Adj q c := ⟨cq.symm,off.2.symm,cC xm⟩
  let route : Route J e a c 4 := {
    atIdx := f
    start := rfl
    finish := rfl
    step := by intro i hi; rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by omega) with rfl|rfl|rfl|rfl <;> assumption
    unique := by
      intro i hi j hj eq
      rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 by omega) with rfl|rfl|rfl|rfl|rfl <;> rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 by omega) with rfl|rfl|rfl|rfl|rfl <;> simp_all only [f,Nat.reduceAdd,
        (aC pc),(aC zm),(aC qc),ac.ne,(cC pc),(cC zm),(cC qc),pq,zp,zq,
        (aC pc).symm,(aC zm).symm,(aC qc).symm,ac.ne.symm,(cC pc).symm,(cC zm).symm,(cC qc).symm,pq.symm,zp.symm,zq.symm]
    avoid := by intro i hi; rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 by omega) with rfl|rfl|rfl|rfl|rfl <;> first | exact ea.ne.symm | exact ec.ne.symm | exact (eC pc).symm | exact (eC qc).symm | exact (eC zm).symm }
  have h := pivot_odd H de ea ec ac.ne pos inj tight cl xm safe 4 route
  omega

end Graffiti384b.RootCut
#print axioms Graffiti384b.RootCut.exterior_count
#print axioms Graffiti384b.RootCut.edge_cover
#print axioms Graffiti384b.RootCut.off_clique
#print axioms Graffiti384b.RootCut.contact_cover
