import SevenTrial
namespace Graffiti384b.Seven
open SimpleGraph Finset EarFrame33
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private CubicShore.square_frame CubicShore.half_tight from CubicDiamondCut33
open private Repair.nbr_mono Repair.isolate from Repair384b
open private CliquePivot33.isolated_degree from CliquePivot33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

theorem split_pivot {x : V} (dx : H.degree x=4) (sx : trianglesAt H x=5) :
    ∃ P Q : Finset V,P∪Q=H.neighborFinset x ∧ P.card=2 ∧ Q.card=2 ∧ Disjoint P Q ∧
    (∀ a∈P,∀ b∈Q,H.Adj a b) ∧ (∀ a∈P,∀ b∈P,¬H.Adj a b) := by
  classical
  let N := H.neighborFinset x
  let E := BlockGeometry.gaps H N
  have sz : N.card=4 := (card_neighborFinset_eq_degree ..).trans dx
  have clock := BlockGeometry.gap_count H x
  change E.card+trianglesAt H x=(H.degree x).choose 2 at clock
  rw [dx,sx] at clock; change E.card+5=6 at clock
  obtain ⟨P,eq⟩ := card_eq_one.mp (show E.card=1 by omega)
  have pm : P∈E := eq ▸ mem_singleton_self _
  have ⟨sub,ps⟩ := mem_powersetCard.mp (mem_filter.mp pm).1
  let Q := N\P
  refine ⟨P,Q,union_sdiff_of_subset sub,ps,by rw [show Q=N\P from rfl,card_sdiff sub,sz,ps],disjoint_sdiff,?_,?_⟩
  · intro a am b bm
    obtain ⟨bn,bp⟩ := mem_sdiff.mp bm
    apply Classical.byContradiction; intro no
    have m := BlockGeometry.pair_gap H (sub am) bn (fun e => bp (e ▸ am)) no
    have same : {a,b}=P := mem_singleton.mp (eq ▸ m)
    exact bp (same ▸ (mem_insert_of_mem (mem_singleton_self b) : b∈({a,b}:Finset V)))
  · intro a am b bm ab
    have pair : ({a,b} : Finset V)=P := eq_of_subset_of_card_le (insert_subset am (singleton_subset_iff.mpr bm)) (by rw [card_pair ab.ne,ps])
    have no := (mem_filter.mp pm).2
    apply no
    rw [←pair]; intro i im j jm ne
    simp only [mem_insert,mem_singleton] at im jm
    rcases im with rfl|rfl <;> rcases jm with rfl|rfl <;> first |exact (ne rfl).elim | exact ab | exact ab.symm

private theorem third {e u : V} (de : H.degree e=2) (eu : H.Adj e u) (pos : 0<trianglesAt H e) :
    ∃ r,H.Adj e r ∧ H.Adj u r := by
  obtain ⟨a,b,ea,eb,ab⟩ := (TrianglePrune.triangle_iff H e).mp pos
  have sub : ({a,b}:Finset V)⊆H.neighborFinset e := insert_subset ((H.mem_neighborFinset ..).mpr ea) (singleton_subset_iff.mpr ((H.mem_neighborFinset ..).mpr eb))
  have eq := eq_of_subset_of_card_le sub (by rw [card_pair ab.ne,card_neighborFinset_eq_degree,de])
  have m := (H.mem_neighborFinset ..).mpr eu
  rw [←eq,mem_insert,mem_singleton] at m
  rcases m with rfl|rfl
  · exact ⟨b,eb,ab⟩
  · exact ⟨a,ea,ab.symm⟩

private theorem compatible {A B P Q : Finset V} {x : V} (af : Frame H A B) (pf : Frame H P Q)
    (un : P∪Q=H.neighborFinset x) (off : x∉A∪B) (aq : Disjoint A Q) (bp : Disjoint B P)
    (px : 2≤nbr H x P) (qx : 2≤nbr H x Q) (rest : ∀ v,v∉A∪B → 3≤H.degree v)
    (half : Fintype.card V≤2*gamma H) : False := by
  classical
  have xn := H.not_mem_neighborFinset_self x
  have xp : x∉P := fun m => xn (un ▸ mem_union_left Q m)
  have xq : x∉Q := fun m => xn (un ▸ mem_union_right P m)
  have ux : x∉A := fun m => off (mem_union_left B m)
  have wx : x∉B := fun m => off (mem_union_right A m)
  apply (CliquePivot33.shared H (∅:Finset V) (x:=x) (P:=P∪A) (Q:=Q∪B)
    (by simp only [disjoint_union_left,disjoint_union_right]; exact ⟨⟨pf.1,aq⟩,bp.symm,af.1⟩)
    (by simpa using And.intro xp ux) (by simpa using And.intro xq wx)
    (px.trans (Repair.nbr_mono H _ subset_union_left)) (qx.trans (Repair.nbr_mono H _ subset_union_left)) ?_ ?_ ?_) (CubicShore.half_tight H half)
  · intro v m
    exact (mem_union.mp m).elim (fun h => (pf.2.1 _ h).trans (Repair.nbr_mono H _ subset_union_left))
      (fun h => (af.2.1 _ h).trans (Repair.nbr_mono H _ subset_union_right))
  · intro v m
    exact (mem_union.mp m).elim (fun h => (pf.2.2 _ h).trans (Repair.nbr_mono H _ subset_union_left))
      (fun h => (af.2.2 _ h).trans (Repair.nbr_mono H _ subset_union_right))
  · intro v vx pa qb
    have no : x∉H.neighborFinset v := by
      intro m; have z := (H.mem_neighborFinset ..).mpr ((H.mem_neighborFinset ..).mp m).symm
      rw [←un] at z
      exact (mem_union.mp z).elim (fun h => pa (mem_union_left _ h)) (fun h => qb (mem_union_left _ h))
    have notp : v∉A∪B := fun m => (mem_union.mp m).elim (fun h => pa (mem_union_right _ h)) (fun h => qb (mem_union_right _ h))
    simpa [CliquePivot33.isolated_degree H vx,erase_eq_of_not_mem no] using rest v notp

set_option maxHeartbeats 2500000 in
theorem contact {e u x : V} (de : H.degree e=2) (du : H.degree u=3) (dx : H.degree x=4)
    (sx : trianglesAt H x=5) (eu : H.Adj e u) (pos : ∀ v,0<trianglesAt H v)
    (fi : Function.Injective (trianglesAt H)) (rest : ∀ v,v≠e → 3≤H.degree v)
    (half : Fintype.card V≤2*gamma H) :
    ∃ r t p q,H.neighborFinset e={u,r} ∧ H.neighborFinset u={e,r,t} ∧
      H.neighborFinset x={r,t,p,q} ∧ H.Adj e u ∧ H.Adj e r ∧ H.Adj u r ∧ H.Adj u t ∧ H.Adj r t ∧
      ¬H.Adj x e ∧ ¬H.Adj x u ∧ H.Adj p r ∧ H.Adj p t ∧ H.Adj q r ∧ H.Adj q t ∧ p≠q ∧ ¬H.Adj p q ∧ e≠t := by
  classical
  obtain ⟨r,er,ur⟩ := third H de eu (pos e)
  obtain ⟨t,tm,ut,rt,en,unbr,_⟩ := EarAnchor.diamond H de du eu er ur pos fi
  have et := (EarAnchor.outside_mem.mp tm).1.symm
  obtain ⟨P,Q,un,ps,qs,dis,cross,ind⟩ := split_pivot H dx sx
  let N := H.neighborFinset x
  have xp : P⊆N := by change P⊆H.neighborFinset x; rw [←un]; exact subset_union_left
  have xq : Q⊆N := by change Q⊆H.neighborFinset x; rw [←un]; exact subset_union_right
  have turn (v : V) (vm : v∈N) : ∃ D : Finset V,D⊆N ∧ D.card=2 ∧ D⊆H.neighborFinset v := by
    rcases mem_union.mp (un.symm ▸ vm : v∈P∪Q) with h|h
    · exact ⟨Q,xq,qs,fun z zm => (H.mem_neighborFinset ..).mpr (cross v h z zm)⟩
    · exact ⟨P,xp,ps,fun z zm => (H.mem_neighborFinset ..).mpr (cross z zm v h).symm⟩
  have xn : x∉N := H.not_mem_neighborFinset_self _
  have ex : e≠x := fun eq => by subst x; omega
  have has (v : V) (vm : v∈N) : ∃ D : Finset V,D.card=3 ∧ D⊆H.neighborFinset v ∧ D⊆insert x N := by
    obtain ⟨L,lN,sz,lv⟩ := turn v vm
    exact ⟨insert x L,by rw [card_insert_of_not_mem (fun m => xn (lN m)),sz],
      insert_subset ((H.mem_neighborFinset ..).mpr ((H.mem_neighborFinset ..).mp vm).symm) lv,insert_subset_insert _ lN⟩
  have eout : e∉N := by
    intro em; obtain ⟨D,ds,sub,_⟩ := has e em
    have h := card_le_card sub; rw [ds,card_neighborFinset_eq_degree,de] at h; omega
  have uout : u∉N := by
    intro um; obtain ⟨D,ds,sub,inside⟩ := has u um
    have ed : e∉D := fun m => (mem_insert.mp (inside m)).elim ex eout
    have h := card_le_card (insert_subset ((H.mem_neighborFinset ..).mpr eu.symm) sub)
    rw [card_insert_of_not_mem ed,ds,card_neighborFinset_eq_degree,du] at h; omega
  let A : Finset V := {e,t}
  let B : Finset V := {u,r}
  have frame : Frame H A B := CubicShore.square_frame H eu er ut rt et ur.ne
  have pr (v : V) (m : v∉A∪B) : 3≤H.degree v := rest v (fun eq => m (eq ▸ mem_union_left _ (mem_insert_self ..)))
  have large := Frontier31.frame_hits H dx sx half frame pr
  have inc : (A∪B)∩N⊆{r,t} := by
    intro z zm; obtain ⟨m,zn⟩ := mem_inter.mp zm
    simp only [A,B,mem_union,mem_insert,mem_singleton] at m ⊢
    rcases m with (h|h)|(h|h)
    · exact (eout (h ▸ zn)).elim
    · exact Or.inr h
    · exact (uout (h ▸ zn)).elim
    · exact Or.inl h
  have ij := eq_of_subset_of_card_le inc (by rw [card_pair rt.ne]; exact large)
  have rn : r∈N := (mem_inter.mp (show r∈(A∪B)∩N by rw [ij]; simp)).2
  have tn : t∈N := (mem_inter.mp (show t∈(A∪B)∩N by rw [ij]; simp)).2
  have xoff : x∉A∪B := by
    have xu : x≠u := fun eq => by subst x; omega
    have xr : x≠r := fun eq => xn (eq ▸ rn)
    have xt : x≠t := fun eq => xn (eq ▸ tn)
    simp [A,B,ex.symm,xu,xr,xt]
  have pins (v : V) (D : Finset V) (sz : D.card=2) (ad : ∀ z∈D,H.Adj v z) : 2≤nbr H v D := by
    change 2≤(D.filter _).card; rw [filter_true_of_mem ad,sz]
  have pf : Frame H P Q := ⟨dis,fun v m => pins v Q qs (cross v m),fun v m => pins v P ps (fun z zm => (cross z zm v m).symm)⟩
  have px := pins x P ps (fun z zm => (H.mem_neighborFinset ..).mp (xp zm))
  have qx := pins x Q qs (fun z zm => (H.mem_neighborFinset ..).mp (xq zm))
  have orient {L F : Finset V} (lf : Disjoint L F) (lnn : L⊆N) (fnn : F⊆N)
      (tl : t∈L) (rf : r∈F) : Disjoint A F ∧ Disjoint B L := by
    exact ⟨disjoint_left.mpr (fun z zm f => (show z=e ∨ z=t by simpa [A] using zm).elim
      (fun eq => eout (eq ▸ fnn f)) (fun eq => disjoint_left.mp lf tl (eq ▸ f))),
      disjoint_left.mpr (fun z zm l => (show z=u ∨ z=r by simpa [B] using zm).elim
      (fun eq => uout (eq ▸ lnn l)) (fun eq => disjoint_left.mp lf (eq ▸ l) rf))⟩
  have both : r∈Q ∧ t∈Q := by
    have rm := mem_union.mp (un.symm ▸ rn : r∈P∪Q)
    have tm' := mem_union.mp (un.symm ▸ tn : t∈P∪Q)
    rcases rm with rp|rq <;> rcases tm' with tp|tq
    · exact (ind r rp t tp rt).elim
    · obtain ⟨a,b⟩ := orient dis.symm xq xp tq rp
      exact (compatible H frame ⟨dis.symm,pf.2.2,pf.2.1⟩ ((union_comm Q P).trans un) xoff a b qx px pr half).elim
    · obtain ⟨a,b⟩ := orient dis xp xq tp rq
      exact (compatible H frame pf un xoff a b px qx pr half).elim
    · exact ⟨rq,tq⟩
  have qeq : ({r,t}:Finset V)=Q := eq_of_subset_of_card_le (insert_subset both.1 (singleton_subset_iff.mpr both.2)) (by rw [card_pair rt.ne,qs])
  obtain ⟨p,q,pq,peq⟩ := card_eq_two.mp ps
  have pm : p∈P := by rw [peq]; simp
  have qm : q∈P := by rw [peq]; simp
  refine ⟨r,t,p,q,en,unbr,?_,eu,er,ur,ut,rt,fun h => eout ((H.mem_neighborFinset ..).mpr h),
    fun h => uout ((H.mem_neighborFinset ..).mpr h),cross p pm r both.1,cross p pm t both.2,cross q qm r both.1,
    cross q qm t both.2,pq,ind p pm q qm,et⟩
  rw [←un,←qeq,peq]; ext z; simp [or_left_comm,or_comm,or_assoc]

end Graffiti384b.Seven
#print axioms Graffiti384b.Seven.split_pivot
#print axioms Graffiti384b.Seven.contact
