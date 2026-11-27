import Exchange33

namespace Graffiti384b.EarFrame33
open Finset SimpleGraph CliquePivot33
open private Repair.isolate Repair.nbr_mono Repair.triangles_le_choose from Repair384b
open private CliquePivot33.isolated_degree CliquePivot33.full_cubic from CliquePivot33
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two disjoint pin sets in which each vertex already sees two opposite pins. -/
def Frame (A B : Finset V) : Prop :=
  Disjoint A B ∧ (∀ v∈A,2≤nbr G v B) ∧ (∀ v∈B,2≤nbr G v A)

omit [Fintype V] in
private theorem align {A B P Q : Finset V} (ab : Disjoint A B) (pq : Disjoint P Q)
    (small : ((A∪B)∩(P∪Q)).card≤1) :
    (Disjoint A Q ∧ Disjoint B P) ∨ (Disjoint B Q ∧ Disjoint A P) := by
  classical
  have uniq := card_le_one.mp small
  simp only [disjoint_left] at ab pq ⊢
  by_contra bad
  have conflict : (∃ v,v∈A ∧ v∈Q) ∨ ∃ v,v∈B ∧ v∈P := by
    by_contra! no
    exact bad (Or.inl ⟨fun _ h => no.1 _ h,fun _ h => no.2 _ h⟩)
  have other : (∃ v,v∈B ∧ v∈Q) ∨ ∃ v,v∈A ∧ v∈P := by
    by_contra! no
    exact bad (Or.inr ⟨fun _ h => no.1 _ h,fun _ h => no.2 _ h⟩)
  rcases conflict with ⟨u,ua,uq⟩|⟨u,ub,up⟩ <;> rcases other with ⟨v,vb,vq⟩|⟨v,va,vp⟩
  all_goals
    have hu : u∈(A∪B)∩(P∪Q) := mem_inter.mpr (by first
      | exact ⟨mem_union_left _ ua,mem_union_right _ uq⟩
      | exact ⟨mem_union_right _ ub,mem_union_left _ up⟩)
    have hv : v∈(A∪B)∩(P∪Q) := mem_inter.mpr (by first
      | exact ⟨mem_union_right _ vb,mem_union_right _ vq⟩
      | exact ⟨mem_union_left _ va,mem_union_left _ vp⟩)
    have h : u=v := uniq u hu v hv
    subst v
    first | exact ab ua vb | exact pq up vq | exact pq vp uq | exact ab va ub

private theorem merge_shared (R : Finset V) {A B P Q : Finset V} (f : Frame G A B) (pq : Disjoint P Q)
    (small : ((A∪B)∩(P∪Q)).card≤1) {x : V} (off : x∉A∪B) (xp : x∉P) (xq : x∉Q)
    (px : 2≤nbr G x P) (qx : 2≤nbr G x Q)
    (lp : ∀ v∈P,2≤nbr G v Q) (rq : ∀ v∈Q,2≤nbr G v P)
    (free : ∀ v,v∉A∪B → v≠x → v∉P → v∉Q →
      3≤(Repair.isolate G x).degree v+2*(if v∈R then 1 else 0)) : ¬Tight G R := by
  have use (U W : Finset V) (frame : Frame G U W) (same : U∪W=A∪B)
      (uq : Disjoint U Q) (wp : Disjoint W P) : ¬Tight G R := by
    have ux : x∉U := fun m => off (same ▸ mem_union_left W m)
    have wx : x∉W := fun m => off (same ▸ mem_union_right U m)
    apply shared G R (P:=P∪U) (Q:=Q∪W)
      (by simp only [disjoint_union_left,disjoint_union_right]; exact ⟨⟨pq,uq⟩,wp.symm,frame.1⟩)
      (by simpa using And.intro xp ux) (by simpa using And.intro xq wx)
      (px.trans (Repair.nbr_mono G _ subset_union_left)) (qx.trans (Repair.nbr_mono G _ subset_union_left))
    · intro v m
      exact (mem_union.mp m).elim (fun h => (lp _ h).trans (Repair.nbr_mono G _ subset_union_left))
        (fun h => (frame.2.1 _ h).trans (Repair.nbr_mono G _ subset_union_right))
    · intro v m
      exact (mem_union.mp m).elim (fun h => (rq _ h).trans (Repair.nbr_mono G _ subset_union_left))
        (fun h => (frame.2.2 _ h).trans (Repair.nbr_mono G _ subset_union_right))
    · intro v vx pu qw
      apply free v _ vx (fun m => pu (mem_union_left _ m)) (fun m => qw (mem_union_left _ m))
      rw [← same]
      intro m
      exact (mem_union.mp m).elim (fun h => pu (mem_union_right _ h)) (fun h => qw (mem_union_right _ h))
  rcases align f.1 pq small with ⟨aq,bp⟩|⟨bq,ap⟩
  · exact use A B f rfl aq bp
  · exact use B A ⟨f.1.symm,f.2.2,f.2.1⟩ (union_comm ..) bq ap

private theorem paired_frame (R A B : Finset V) (frame : Frame G A B)
    (minimum : ∀ v,v∉A∪B → 2≤G.degree v ∧ (v∉R → 3≤G.degree v))
    {C P : Finset V} {x : V} (cl : G.IsNClique 5 C) (xc : x∈C)
    (over : ((A∪B)∩C).card≤1) (outside : x∉A∪B)
    (pc : P⊆C.erase x) (two : P.card=2)
    (protect : ∀ v,v∉C → G.degree v=3 → G.Adj v x → v∉R → v∉A∪B → 2≤nbr G v P) : ¬Tight G R := by
  classical
  let Q := C.erase x\P
  let E := (univ : Finset V).filter (fun v => v∉C ∧ G.degree v=3 ∧ G.Adj v x ∧ v∉R ∧ v∉A∪B)
  have qsize : Q.card=2 := by rw [show Q=C.erase x\P from rfl,card_sdiff pc,card_erase_of_mem xc,cl.2,two]
  have qc : Q⊆C.erase x := sdiff_subset
  have pC := pc.trans (erase_subset _ _)
  have qC := qc.trans (erase_subset _ _)
  have see {v : V} (vc : v∈C) {D : Finset V} (dc : D⊆C) (vd : v∉D) (dz : D.card=2) :
      2≤nbr G v D := by
    have eq : D.filter (G.Adj v)=D := filter_true_of_mem
      (fun w wm => cl.1 vc (dc wm) (fun e => vd (e ▸ wm)))
    simp only [nbr,eq,dz,le_rfl]
  have xp : x∉P := fun m => not_mem_erase _ _ (pc m)
  have xq : x∉Q := fun m => not_mem_erase _ _ (qc m)
  have xe : x∉E := fun m => (mem_filter.mp m).2.1 xc
  have dis : Disjoint P (Q∪E) := disjoint_left.mpr (by
    intro v vm m
    exact (mem_union.mp m).elim (fun h => (mem_sdiff.mp h).2 vm) (fun h => (mem_filter.mp h).2.1 (pC vm)))
  have small : ((A∪B)∩(P∪(Q∪E))).card≤1 := (card_le_card (show (A∪B)∩(P∪(Q∪E))⊆(A∪B)∩C from by
    intro v vm
    obtain ⟨f,m⟩ := mem_inter.mp vm
    apply mem_inter.mpr ⟨f,?_⟩
    rcases mem_union.mp m with p|m
    · exact pC p
    rcases mem_union.mp m with q|e
    · exact qC q
    · exact ((mem_filter.mp e).2.2.2.2.2 f).elim)).trans over
  apply merge_shared G R frame dis small outside xp (fun m => (mem_union.mp m).elim xq xe) (see xc pC xp two)
    ((see xc qC xq qsize).trans (Repair.nbr_mono G _ subset_union_left))
  · intro v vm
    exact (see (pC vm) qC (fun q => (mem_sdiff.mp q).2 vm) qsize).trans (Repair.nbr_mono G _ subset_union_left)
  · intro v vm
    rcases mem_union.mp vm with vq|ve
    · exact see (qC vq) pC (mem_sdiff.mp vq).2 two
    · obtain ⟨vc,d,a,vr,off⟩ := (mem_filter.mp ve).2
      exact protect _ vc d a vr off
  · intro v off vx vp vq
    have vc : v∉C := fun m => vq (mem_union_left _ (mem_sdiff.mpr ⟨mem_erase.mpr ⟨vx,m⟩,vp⟩))
    rw [CliquePivot33.isolated_degree G vx]
    by_cases adj : G.Adj v x
    · rw [card_erase_of_mem ((G.mem_neighborFinset _ _).mpr adj),card_neighborFinset_eq_degree]
      by_cases vr : v∈R
      · rw [if_pos vr]; have := (minimum v off).1; omega
      rw [if_neg vr]
      have not3 : G.degree v≠3 := fun eq => vq (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,vc,eq,adj,vr,off⟩))
      have := (minimum v off).2 vr; omega
    · rw [erase_eq_of_not_mem (fun m => adj ((G.mem_neighborFinset _ _).mp m)),card_neighborFinset_eq_degree]
      by_cases vr : v∈R
      · rw [if_pos vr]; have := (minimum v off).1; omega
      · rw [if_neg vr]; have := (minimum v off).2 vr; omega

theorem cover (R A B : Finset V) (frame : Frame G A B)
    (minimum : ∀ v,v∉A∪B → 2≤G.degree v ∧ (v∉R → 3≤G.degree v))
    (inj : Function.Injective (trianglesAt G)) (extremal : Tight G R)
    {C : Finset V} (cl : G.IsNClique 5 C) {x : V} (xc : x∈C) (over : ((A∪B)∩C).card≤1) (outside : x∉A∪B) :
    ∃ v,v∉C ∧ G.degree v=3 ∧ G.Adj v x ∧ v∉R ∧ v∉A∪B ∧ nbr G v C≤2 := by
  classical
  apply Classical.byContradiction; intro no
  have full (v : V) (vc : v∉C) (dv : G.degree v=3) (adj : G.Adj v x) (vr : v∉R) (off : v∉A∪B) :
      G.neighborFinset v⊆C ∧ trianglesAt G v=3 := by
    apply CliquePivot33.full_cubic G cl dv
    have few : ¬nbr G v C≤2 := fun small => no ⟨v,vc,dv,adj,vr,off,small⟩
    omega
  have enough (P : Finset V) (pc : P⊆C.erase x) (sz : P.card=2)
      (protect : ∀ v,v∉C → G.degree v=3 → G.Adj v x → v∉R → v∉A∪B → 2≤nbr G v P) : False := by
    exact paired_frame G R A B frame minimum cl xc over outside pc sz protect extremal
  by_cases existsV : ∃ u,u∉C ∧ G.degree u=3 ∧ G.Adj u x ∧ u∉R ∧ u∉A∪B
  · obtain ⟨u,uc,du,ux,ur,uf⟩ := existsV
    obtain ⟨sub,score⟩ := full _ uc du ux ur uf
    let P := (G.neighborFinset u).erase x
    have pc : P⊆C.erase x := fun v vm => mem_erase.mpr ⟨(mem_erase.mp vm).1,sub (mem_erase.mp vm).2⟩
    have sz : P.card=2 := by rw [show P=(G.neighborFinset u).erase x from rfl,
      card_erase_of_mem ((G.mem_neighborFinset _ _).mpr ux),card_neighborFinset_eq_degree,du]
    apply enough P pc sz
    intro v vc dv vx vr off
    have eq : v=u := inj ((full v vc dv vx vr off).2.trans score.symm)
    subst v
    have allP : P.filter (G.Adj u)=P := filter_true_of_mem (fun w wm =>
      (G.mem_neighborFinset _ _).mp (erase_subset _ _ wm))
    simp only [nbr,allP,sz,le_rfl]
  · obtain ⟨P,pc,sz⟩ := exists_subset_card_eq (show 2≤(C.erase x).card by rw [card_erase_of_mem xc,cl.2]; decide)
    exact enough P pc sz (fun v vc dv vx vr off => (existsV ⟨v,vc,dv,vx,vr,off⟩).elim)


end Graffiti384b.EarFrame33
#print axioms Graffiti384b.EarFrame33.cover
