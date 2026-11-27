import EarRoot33

namespace Graffiti384b.EarOnClique33
open Finset SimpleGraph CliquePivot33 EarFrame33
open private Repair.nbr_mono Repair.isolate Repair.triangles_le_choose from Repair384b
open private CliquePivot33.isolated_degree from CliquePivot33
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private OneEar.deg2 from OneEarFinish384b
open private EarExchange33.count_insert from Exchange33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Deficient vertices seeing two original pins on either side can all be
protected simultaneously, including vertices requiring different sides. -/
theorem mixed_blocker {R P Q : Finset V} (t : Tight H R) (f : Frame H P Q)
    {x : V} (xp : x∉P) (xq : x∉Q) (px : 2≤nbr H x P) (qx : 2≤nbr H x Q) :
    ∃ v,v≠x ∧ v∉P ∧ v∉Q ∧
      (Repair.isolate H x).degree v+2*(if v∈R then 1 else 0)<3 ∧
      nbr H v P≤1 ∧ nbr H v Q≤1 := by
  classical
  apply Classical.byContradiction
  intro no
  let E := univ.filter (fun v => v≠x ∧ v∉P ∧ v∉Q ∧
    (Repair.isolate H x).degree v+2*(if v∈R then 1 else 0)<3)
  let L := E.filter (fun v => 2≤nbr H v Q)
  let K := E\L
  have kl {v : V} (m : v∈K) : 2≤nbr H v P := by
    obtain ⟨em,nl⟩ := mem_sdiff.mp m
    obtain ⟨ne,vp,vq,sm⟩ := (mem_filter.mp em).2
    have nq : ¬2≤nbr H v Q := fun h => nl (mem_filter.mpr ⟨em,h⟩)
    by_contra! p
    exact no ⟨v,ne,vp,vq,sm,by omega,by omega⟩
  have le : L⊆E := filter_subset _ _
  have ke : K⊆E := sdiff_subset
  have d : Disjoint (P∪L) (Q∪K) := disjoint_left.mpr (by
    intro v a b
    rcases mem_union.mp a with p|l <;> rcases mem_union.mp b with q|k
    · exact disjoint_left.mp f.1 p q
    · exact (mem_filter.mp (ke k)).2.2.1 p
    · exact (mem_filter.mp (le l)).2.2.2.1 q
    · exact (mem_sdiff.mp k).2 l)
  have xe : x∉E := fun m => (mem_filter.mp m).2.1 rfl
  apply shared H R d (fun m => (mem_union.mp m).elim xp (fun l => xe (le l)))
    (fun m => (mem_union.mp m).elim xq (fun k => xe (ke k)))
    (px.trans (Repair.nbr_mono H _ subset_union_left)) (qx.trans (Repair.nbr_mono H _ subset_union_left)) _ _ _ t
  · intro v m
    apply LE.le.trans _ (Repair.nbr_mono H v (show Q⊆Q∪K from subset_union_left))
    exact (mem_union.mp m).elim (f.2.1 v) (fun l => (mem_filter.mp l).2)
  · intro v m
    apply LE.le.trans _ (Repair.nbr_mono H v (show P⊆P∪L from subset_union_left))
    exact (mem_union.mp m).elim (f.2.2 v) kl
  · intro v vx pl qk
    apply le_of_not_gt
    intro sm
    have e : v∈E := mem_filter.mpr ⟨mem_univ _,vx,fun h => pl (mem_union_left _ h),
      fun h => qk (mem_union_left _ h),sm⟩
    by_cases l : v∈L
    · exact pl (mem_union_right _ l)
    · exact qk (mem_union_right _ (mem_sdiff.mpr ⟨e,l⟩))

/-- If the ear sees two vertices of one five-clique, the other three clique
vertices each need a cubic outside the clique and outside the root set. No
such cubic can cover more than two of those three vertices. -/
theorem edge_cover {e : V} (de : H.degree e=2) (positive : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) {R C P : Finset V} (tight : Tight H R)
    (cl : H.IsNClique 5 C) (sub : P⊆C) (ps : P.card=2) (ear : 2≤nbr H e P)
    {x : V} (xm : x∈C\P) :
    ∃ v,v∉C ∧ v∉R ∧ H.degree v=3 ∧ H.Adj v x ∧ nbr H v (C\P)≤2 ∧ nbr H v P≤1 := by
  classical
  let T := C\P
  let Q := T.erase x
  have ts : T.card=3 := by rw [show T=C\P from rfl,card_sdiff sub,cl.2,ps]
  have qs : Q.card=2 := by rw [show Q=T.erase x from rfl,card_erase_of_mem xm,ts]
  have qc : Q⊆C := (erase_subset _ _).trans sdiff_subset
  have see {v : V} (vc : v∈C) {D : Finset V} (inc : D⊆C) (out : v∉D) (ds : D.card=2) :
      2≤nbr H v D := by
    have eq : D.filter (H.Adj v)=D := filter_true_of_mem (fun w wm => cl.1 vc (inc wm) (fun h => out (h ▸ wm)))
    simp only [nbr,eq,ds,le_rfl]
  have dis : Disjoint P Q := disjoint_left.mpr (fun _ p q => (mem_sdiff.mp (erase_subset _ _ q)).2 p)
  have f : Frame H P Q := ⟨dis,fun _ p => see (sub p) qc (fun q => disjoint_left.mp dis p q) qs,
    fun _ q => see (qc q) sub (fun p => disjoint_left.mp dis p q) ps⟩
  have xc := (mem_sdiff.mp xm).1
  have xp := (mem_sdiff.mp xm).2
  obtain ⟨v,vx,vp,vq,small,lo,r⟩ := mixed_blocker H tight f xp (not_mem_erase x T)
    (see xc sub xp ps) (see xc qc (not_mem_erase x T) qs)
  have vc : v∉C := fun m => vq (mem_erase.mpr ⟨vx,mem_sdiff.mpr ⟨m,vp⟩⟩)
  have ve : v≠e := by intro eq; subst v; omega
  obtain ⟨a,b,va,vb,ab⟩ := (TrianglePrune.triangle_iff H v).mp (positive v)
  have min := OneEar.deg2 H ab.ne va vb
  have one (u : V) (du : H.degree u=2) : trianglesAt H u=1 := by
    have ub := Repair.triangles_le_choose H u
    rw [du,Nat.choose_self] at ub
    have := positive u; omega
  have high : 3≤H.degree v := by
    have wrong : H.degree v≠2 := fun eq => ve (inj ((one v eq).trans (one e de).symm))
    omega
  rw [CliquePivot33.isolated_degree H vx] at small
  have edge : H.Adj v x := by
    by_contra absent
    rw [erase_eq_of_not_mem (fun m => absent ((H.mem_neighborFinset _ _).mp m)),card_neighborFinset_eq_degree] at small
    omega
  rw [card_erase_of_mem ((H.mem_neighborFinset _ _).mpr edge),card_neighborFinset_eq_degree] at small
  have vr : v∉R := by intro m; rw [if_pos m] at small; omega
  rw [if_neg vr] at small
  have recover : insert x Q=T := insert_erase xm
  have step := EarExchange33.count_insert H x v (S:=Q) (not_mem_erase x T)
  rw [recover,if_pos edge] at step
  exact ⟨v,vc,vr,by omega,edge,by change nbr H v T≤2; omega,lo⟩

/-- Both cubic scores 2 and 3 are mandatory when the ear is on a five-clique
edge. Neither of these two cubics may be a root for the leaf. -/
theorem edge_restriction {e : V} (de : H.degree e=2) (positive : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) {R C P : Finset V} (tight : Tight H R)
    (cl : H.IsNClique 5 C) (sub : P⊆C) (ps : P.card=2) (ear : 2≤nbr H e P) :
    let U := univ.filter (fun v => H.degree v=3)
    U.card=2 ∧ U.image (trianglesAt H)=Icc 2 3 ∧
    (∀ v∈U,v∉C ∧ v∉R ∧ nbr H v (C\P)≤2 ∧ nbr H v P≤1) ∧
    C\P⊆U.biUnion (fun v => (C\P).filter (H.Adj v)) := by
  classical
  let U := univ.filter (fun v => H.degree v=3)
  let T := C\P
  let L := U.filter (fun v => v∉C ∧ v∉R ∧ nbr H v T≤2 ∧ nbr H v P≤1)
  have cover : T⊆L.biUnion (fun v => T.filter (H.Adj v)) := by
    intro x xm
    obtain ⟨v,vc,vr,d,edge,few,lo⟩ := edge_cover H de positive inj tight cl sub ps ear xm
    exact mem_biUnion.mpr ⟨v,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,d⟩,vc,vr,few,lo⟩,mem_filter.mpr ⟨xm,edge⟩⟩
  have cnt : 3≤L.card*2 := calc
    3 = T.card := by rw [show T=C\P from rfl,card_sdiff sub,cl.2,ps]
    _ ≤ _ := card_le_card cover
    _ ≤ ∑ v∈L,nbr H v T := card_biUnion_le
    _ ≤ ∑ _v∈L,2 := sum_le_sum (fun v vm => (mem_filter.mp vm).2.2.2.1)
    _ = _ := by simp
  have small := Repair.triangles_le_choose H e
  rw [de,Nat.choose_self] at small
  have one : trianglesAt H e=1 := by have := positive e; omega
  have subI : U.image (trianglesAt H)⊆Icc 2 3 := by
    intro i im
    obtain ⟨v,vm,rfl⟩ := mem_image.mp im
    have degree := (mem_filter.mp vm).2
    have ub := Repair.triangles_le_choose H v
    rw [degree] at ub
    have ne : trianglesAt H v≠1 := by intro eq; have ve := inj (eq.trans one.symm); subst v; omega
    have := positive v
    exact mem_Icc.mpr ⟨by omega,ub⟩
  have ic : (Icc 2 3 : Finset ℕ).card=2 := by decide
  have cap := card_le_card subI
  rw [card_image_of_injective _ inj,ic] at cap
  have lu : L⊆U := filter_subset _ _
  have lc := card_le_card lu
  have eq : L=U := eq_of_subset_of_card_le lu (by omega)
  have size : U.card=2 := by omega
  refine ⟨size,eq_of_subset_of_card_le subI (by rw [ic,card_image_of_injective _ inj,size]),?_,?_⟩
  · exact fun v m => (mem_filter.mp (show v∈L from eq ▸ m)).2
  · change T⊆U.biUnion _
    rwa [← eq]

private theorem misses_ear {e : V} (de : H.degree e=2) {C : Finset V} (cl : H.IsNClique 5 C) : e∉C := by
  intro ec
  have sub : C.erase e⊆H.neighborFinset e := by
    intro v vm
    exact (H.mem_neighborFinset _ _).mpr (cl.1 ec (erase_subset _ _ vm) (mem_erase.mp vm).1.symm)
  have le := card_le_card sub
  rw [card_erase_of_mem ec,cl.2,card_neighborFinset_eq_degree,de] at le
  omega

/-- Both cubic scores above the ear are represented away from the roots. -/
def Available (R : Finset V) : Prop :=
  ∃ u v,H.degree u=3 ∧ trianglesAt H u=2 ∧ u∉R ∧
    H.degree v=3 ∧ trianglesAt H v=3 ∧ v∉R

private theorem from_scores {R : Finset V}
    (scores : (univ.filter (fun v => H.degree v=3)).image (trianglesAt H)=Icc 2 3)
    (off : ∀ v∈univ.filter (fun u => H.degree u=3),v∉R) : Available H R := by
  have two : 2∈(univ.filter (fun v => H.degree v=3)).image (trianglesAt H) := by rw [scores]; decide
  have three : 3∈(univ.filter (fun v => H.degree v=3)).image (trianglesAt H) := by rw [scores]; decide
  obtain ⟨u,um,us⟩ := mem_image.mp two
  obtain ⟨v,vm,vs⟩ := mem_image.mp three
  exact ⟨u,v,(mem_filter.mp um).2,us,off u um,(mem_filter.mp vm).2,vs,off v vm⟩

private theorem scarce_at_root {a e : V} (da : H.degree a=3) (de : H.degree e=2)
    (positive : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H)) :
    ¬Available H {a} := by
  rintro ⟨u,v,_,us,ur,_,vs,vr⟩
  have cap := Repair.triangles_le_choose H a
  have low := Repair.triangles_le_choose H e
  rw [da] at cap
  rw [de,Nat.choose_self] at low
  have es : trianglesAt H e=1 := by have := positive e; omega
  have ne1 : trianglesAt H a≠1 := by intro eq; have ae := inj (eq.trans es.symm); subst a; omega
  have ne2 : trianglesAt H a≠2 := fun eq => ur (mem_singleton.mpr (inj (us.trans eq.symm)))
  have ne3 : trianglesAt H a≠3 := fun eq => vr (mem_singleton.mpr (inj (vs.trans eq.symm)))
  have upper : trianglesAt H a≤3 := cap
  have := positive a
  omega

/-- With fewer than two available cubic scores, the two ear anchors cannot lie
in one five-clique. Each additional common neighbor lies in every five-clique. -/
theorem scarce_cliques {R : Finset V} {e b c : V} (scarce : ¬Available H R) (de : H.degree e=2)
    (bc : b≠c) (eb : H.Adj e b) (ec : H.Adj e c) (positive : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) (tight : Tight H R) {C : Finset V}
    (cl : H.IsNClique 5 C) : ¬(b∈C ∧ c∈C) ∧
      ∀ w,w≠e → H.Adj b w → H.Adj c w → w∈C ∧ (b∈C ∨ c∈C) := by
  classical
  have apart : ¬(b∈C ∧ c∈C) := by
    rintro ⟨bm,cm⟩
    have sub : ({b,c} : Finset V)⊆C := by
      intro v m
      rcases (show v=b ∨ v=c by simpa using m) with rfl|rfl
      · exact bm
      · exact cm
    have sz : ({b,c} : Finset V).card=2 := by simp [bc]
    have sees : 2≤nbr H e {b,c} := PinnedColor34.two H bc eb ec (mem_insert_self ..)
      (mem_insert_of_mem (mem_singleton_self _))
    obtain ⟨_,scores,restr,_⟩ := edge_restriction H de positive inj tight cl sub sz sees
    exact scarce (from_scores H scores (fun u m => (restr u m).2.1))
  refine ⟨apart,?_⟩
  intro w we bw cw
  let U : Finset V := {e,w}
  let W : Finset V := {b,c}
  have frame : Frame H U W := by
    refine ⟨?_,?_,?_⟩
    · simp [U,W,disjoint_left,eb.ne,ec.ne,bw.ne.symm,cw.ne.symm]
    · intro v vm
      rcases (show v=e ∨ v=w by simpa [U] using vm) with rfl|rfl
      · exact PinnedColor34.two H bc eb ec (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))
      · exact PinnedColor34.two H bc bw.symm cw.symm (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))
    · intro v vm
      rcases (show v=b ∨ v=c by simpa [W] using vm) with rfl|rfl
      · exact PinnedColor34.two H we.symm eb.symm bw (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))
      · exact PinnedColor34.two H we.symm ec.symm cw (mem_insert_self ..) (mem_insert_of_mem (mem_singleton_self _))
  have size : 2≤((U∪W)∩C).card := by
    apply le_of_not_gt
    intro few
    obtain ⟨_,_,scores,rest,_⟩ := EarAttachment33.frame_obstruction H de positive inj tight frame
      (mem_union_left W (mem_insert_self ..)) cl (by omega)
    exact scarce (from_scores H scores (fun v m => (rest v m).2.2.1))
  have en := misses_ear H de cl
  have member {v : V} (m : v∈(U∪W)∩C) : v=w ∨ v=b ∨ v=c := by
    obtain ⟨h,vc⟩ := mem_inter.mp m
    simp only [U,W,mem_union,mem_insert,mem_singleton] at h
    rcases h with (rfl|rfl)|(rfl|rfl)
    · exact (en vc).elim
    all_goals tauto
  have notone (v : V) (allv : ∀ y∈(U∪W)∩C,y=v) : False := by
    have inc : (U∪W)∩C⊆{v} := fun y m => mem_singleton.mpr (allv y m)
    have upper := card_le_card inc
    rw [card_singleton] at upper; omega
  have wm : w∈C := by
    apply Classical.byContradiction
    intro wn
    by_cases bm : b∈C
    · apply notone b
      intro y ym
      have yc := (mem_inter.mp ym).2
      rcases member ym with rfl|rfl|rfl
      · exact (wn yc).elim
      · rfl
      · exact (apart ⟨bm,yc⟩).elim
    · apply notone c
      intro y ym
      have yc := (mem_inter.mp ym).2
      rcases member ym with rfl|rfl|rfl
      · exact (wn yc).elim
      · exact (bm yc).elim
      · rfl
  refine ⟨wm,?_⟩
  apply Classical.byContradiction
  intro absent
  have missing : b∉C ∧ c∉C := not_or.mp absent
  apply notone w
  intro y ym
  have yc := (mem_inter.mp ym).2
  rcases member ym with rfl|rfl|rfl
  · rfl
  · exact (missing.1 yc).elim
  · exact (missing.2 yc).elim

/-- With fewer than two available cubic scores the ear edge belongs to at most three triangles. -/
theorem scarce_codegree {R : Finset V} {e b c : V} (scarce : ¬Available H R) (de : H.degree e=2)
    (bc : H.Adj b c) (eb : H.Adj e b) (ec : H.Adj e c) (positive : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) (tight : Tight H R) {C : Finset V}
    (cl : H.IsNClique 5 C) : (H.neighborFinset b ∩ H.neighborFinset c).card≤3 := by
  classical
  let U := (H.neighborFinset b ∩ H.neighborFinset c).erase e
  have inside (v : V) (m : v∈U) : H.Adj b v ∧ H.Adj c v := by
    obtain ⟨l,r⟩ := mem_inter.mp (mem_erase.mp m).2
    exact ⟨(H.mem_neighborFinset _ _).mp l,(H.mem_neighborFinset _ _).mp r⟩
  have universal : U⊆C := by
    intro w wm
    have h := inside _ wm
    exact ((scarce_cliques H scarce de bc.ne eb ec positive inj tight cl).2 w (mem_erase.mp wm).1 h.1 h.2).1
  have cap : U.card≤2 := by
    by_contra! many
    obtain ⟨S,su,sc⟩ := exists_subset_card_eq (show 3≤U.card by omega)
    have bfree : b∉S := fun m => H.loopless b (inside b (su m)).1
    have cfree : c∉S := fun m => H.loopless c (inside c (su m)).2
    let K := insert b (insert c S)
    have clique : H.IsNClique 5 K := by
      constructor
      · intro u um v vm uv
        simp only [K,Finset.mem_coe,mem_insert] at um vm
        rcases um with rfl|rfl|us
        · rcases vm with rfl|rfl|vs
          · exact (uv rfl).elim
          · exact bc
          · exact (inside _ (su vs)).1
        · rcases vm with rfl|rfl|vs
          · exact bc.symm
          · exact (uv rfl).elim
          · exact (inside _ (su vs)).2
        · rcases vm with rfl|rfl|vs
          · exact (inside _ (su us)).1.symm
          · exact (inside _ (su us)).2.symm
          · exact cl.1 (universal (su us)) (universal (su vs)) uv
      · simp [K,bc.ne,bfree,cfree,sc]
    exact (scarce_cliques H scarce de bc.ne eb ec positive inj tight clique).1
      ⟨mem_insert_self ..,mem_insert_of_mem (mem_insert_self ..)⟩
  have em : e∈H.neighborFinset b ∩ H.neighborFinset c := mem_inter.mpr
    ⟨(H.mem_neighborFinset _ _).mpr eb.symm,(H.mem_neighborFinset _ _).mpr ec.symm⟩
  change ((H.neighborFinset b ∩ H.neighborFinset c).erase e).card≤2 at cap
  rw [card_erase_of_mem em] at cap
  omega

/-- A cubic leaf root prevents both ear anchors from belonging to any
five-clique. Every additional common neighbor belongs to every five-clique,
which then contains exactly one of the two ear anchors. -/
theorem cubic_root_cliques {a e b c : V} (da : H.degree a=3) (de : H.degree e=2)
    (bc : b≠c) (eb : H.Adj e b) (ec : H.Adj e c) (positive : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) (tight : Tight H {a}) {C : Finset V}
    (cl : H.IsNClique 5 C) : ¬(b∈C ∧ c∈C) ∧
      ∀ w,w≠e → H.Adj b w → H.Adj c w → w∈C ∧ (b∈C ∨ c∈C) :=
  scarce_cliques H (scarce_at_root H da de positive inj) de bc eb ec positive inj tight cl

/-- At a cubic leaf root the ear anchor edge belongs to at most three
triangles, including the ear triangle itself. -/
theorem cubic_root_codegree {a e b c : V} (da : H.degree a=3) (de : H.degree e=2)
    (bc : H.Adj b c) (eb : H.Adj e b) (ec : H.Adj e c) (positive : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) (tight : Tight H {a}) {C : Finset V}
    (cl : H.IsNClique 5 C) : (H.neighborFinset b ∩ H.neighborFinset c).card≤3 :=
  scarce_codegree H (scarce_at_root H da de positive inj) de bc eb ec positive inj tight cl

/-- A thick ear edge forces two specific cubic witnesses away from all roots,
including when the neighbor of the retained leaf has high degree. -/
theorem thick_forces_available {R C : Finset V} {e b c : V} (de : H.degree e=2)
    (bc : H.Adj b c) (eb : H.Adj e b) (ec : H.Adj e c) (positive : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) (tight : Tight H R) (cl : H.IsNClique 5 C)
    (thick : 4≤(H.neighborFinset b ∩ H.neighborFinset c).card) : Available H R := by
  apply Classical.byContradiction
  intro no
  have h := scarce_codegree H no de bc eb ec positive inj tight cl
  omega

/-- Application to the normalized order-33 failure. Degrees and codegrees in
this statement are measured in the positive induced core. -/
theorem failure_codegree (n : Fintype.card V=33) (t : (types H).card=33)
    (conn : H.Connected) (bad : bound H<gamma H) (inj : Function.Injective (trianglesAt H))
    {z a : V} (zero : trianglesAt H z=0) (leaf : H.neighborFinset z={a}) :
    let P := ({z} : Finset V)ᶜ
    let J := H.induce (P : Set V)
    ∀ r e b c : P,r.val=a → J.degree r=3 → J.degree e=2 → J.Adj b c →
      J.Adj e b → J.Adj e c → (∃ C,J.IsNClique 5 C) →
      (J.neighborFinset b ∩ J.neighborFinset c).card≤3 := by
  let P := ({z} : Finset V)ᶜ
  let J := H.induce (P : Set V)
  change ∀ r e b c : P,_ 
  intro r e b c ra dr de bc eb ec five
  have za : H.Adj z a := (H.mem_neighborFinset _ _).mp (leaf ▸ mem_singleton_self _)
  obtain ⟨_,_,_,positive,distinct,_⟩ := PositiveCore33.extremal_core H n t conn bad inj zero za
  have roots : univ.filter (fun v : P => H.Adj v.val z)={r} := by
    ext v
    simp only [mem_filter,mem_univ,true_and,mem_singleton]
    rw [adj_comm,← H.mem_neighborFinset,leaf,mem_singleton]
    exact ⟨fun h => Subtype.ext (h.trans ra.symm),fun h => h ▸ ra⟩
  have tight := PositiveCore33.rooted_tight H n t bad z
  change Tight J (univ.filter (fun v : P => H.Adj v.val z)) at tight
  obtain ⟨C,cl⟩ := five
  exact cubic_root_codegree J dr de bc eb ec positive distinct (roots ▸ tight) cl

/-- The thickness obstruction also holds before a leaf is attached. Only the
half-order lower bound for the positive core is used in this corollary. -/
theorem core_thick_requires_both {C : Finset V} {e b c : V} (half : Fintype.card V≤2*gamma H)
    (de : H.degree e=2) (bc : H.Adj b c) (eb : H.Adj e b) (ec : H.Adj e c)
    (positive : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (cl : H.IsNClique 5 C) (thick : 4≤(H.neighborFinset b ∩ H.neighborFinset c).card) :
    ∃ u v,H.degree u=3 ∧ trianglesAt H u=2 ∧ H.degree v=3 ∧ trianglesAt H v=3 := by
  have tight : Tight H ∅ := by
    intro D good
    have dom : TwoDominates H D := fun v out => by simpa using good v out
    have le : gamma H≤D.card := Nat.sInf_le ⟨D,dom,rfl⟩
    omega
  obtain ⟨u,v,du,su,_,dv,sv,_⟩ := thick_forces_available H de bc eb ec positive inj tight cl thick
  exact ⟨u,v,du,su,dv,sv⟩

end Graffiti384b.EarOnClique33
#print axioms Graffiti384b.EarOnClique33.mixed_blocker
#print axioms Graffiti384b.EarOnClique33.edge_cover
#print axioms Graffiti384b.EarOnClique33.edge_restriction
#print axioms Graffiti384b.EarOnClique33.cubic_root_cliques
#print axioms Graffiti384b.EarOnClique33.cubic_root_codegree
#print axioms Graffiti384b.EarOnClique33.failure_codegree
#print axioms Graffiti384b.EarOnClique33.scarce_cliques
#print axioms Graffiti384b.EarOnClique33.scarce_codegree
#print axioms Graffiti384b.EarOnClique33.thick_forces_available
#print axioms Graffiti384b.EarOnClique33.core_thick_requires_both
