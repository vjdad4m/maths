import AnchorEdge33

namespace Graffiti384b.CubicShore
open Finset SimpleGraph EarAnchor EarFrame33 CliquePivot33 EarExchange33
open private Repair.nbr_mono Repair.isolate Repair.triangles_le_choose from Repair384b
open private CliquePivot33.isolated_degree from CliquePivot33
open private EarAnchor.sees_in_clique from CubicAnchor33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

private theorem half_tight (half : Fintype.card V≤2*gamma H) : Tight H ∅ := by
  intro D dom
  have good : TwoDominates H D := fun v out => by simpa [Relaxed] using dom v out
  have le : gamma H≤D.card := Nat.sInf_le ⟨_,good,rfl⟩
  omega

private theorem clique_score {C : Finset V} (cl : H.IsNClique 5 C) {a : V} (am : a∈C) : 6≤trianglesAt H a := by
  let K := C.erase a
  have size : K.card=4 := by rw [show K=C.erase a from rfl,card_erase_of_mem am,cl.2]
  have here : K⊆H.neighborFinset a := fun y ym => (H.mem_neighborFinset _ _).mpr
    (cl.1 am (erase_subset _ _ ym) (mem_erase.mp ym).1.symm)
  have sub : K.powersetCard 2⊆((H.neighborFinset a).powersetCard 2).filter
      (fun p => ∀ x∈p,∀ y∈p,x≠y → H.Adj x y) := by
    intro p m
    obtain ⟨inc,ps⟩ := mem_powersetCard.mp m
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨inc.trans here,ps⟩,
      fun x xm y ym xy => cl.1 (erase_subset _ _ (inc xm)) (erase_subset _ _ (inc ym)) xy⟩
  have cap := card_le_card sub
  rw [card_powersetCard,size] at cap
  exact cap

omit [Fintype V] in
private theorem square_frame {e a c w : V} (ea : H.Adj e a) (ec : H.Adj e c)
    (aw : H.Adj a w) (cw : H.Adj c w) (ew : e≠w) (ac : a≠c) :
    Frame H {e,w} {a,c} := by
  let U : Finset V := {e,w}
  let D : Finset V := {a,c}
  change Frame H U D
  refine ⟨?_,?_,?_⟩
  · simp [U,D,disjoint_left,ea.ne,ec.ne,aw.ne.symm,cw.ne.symm]
  · intro x xm
    rcases (show x=e ∨ x=w by simpa [U] using xm) with rfl|rfl
    · exact PinnedColor34.two H ac ea ec (by simp [D]) (by simp [D])
    · exact PinnedColor34.two H ac aw.symm cw.symm (by simp [D]) (by simp [D])
  · intro x xm
    rcases (show x=a ∨ x=c by simpa [D] using xm) with rfl|rfl
    · exact PinnedColor34.two H ew ea.symm aw (by simp [U]) (by simp [U])
    · exact PinnedColor34.two H ew ec.symm cw (by simp [U]) (by simp [U])

/-- The ear and its low-count neighbor already provide a four-cycle. Missing one
of the other two vertices of that cycle contradicts the earlier frame theorem. -/
theorem clique_contains {e a c w : V} (de : H.degree e=2) (rare : trianglesAt H a=2 ∨ trianglesAt H a=3)
    (ea : H.Adj e a) (ec : H.Adj e c) (aw : H.Adj a w) (cw : H.Adj c w) (ew : e≠w) (ac : a≠c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (half : Fintype.card V≤2*gamma H) {C : Finset V} (cl : H.IsNClique 5 C) : c∈C ∧ w∈C := by
  classical
  let U : Finset V := {e,w}
  let D : Finset V := {a,c}
  have frame : Frame H U D := square_frame H ea ec aw cw ew ac
  have en : e∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have an : a∉C := fun m => by have := clique_score H cl m; omega
  have inc : ((U∪D)∩C)⊆{w,c} := by
    intro x xm
    obtain ⟨u,xc⟩ := mem_inter.mp xm
    rcases (show (x=e ∨ x=w) ∨ (x=a ∨ x=c) by simpa only [U,D,mem_union,mem_insert,mem_singleton] using u) with (rfl|rfl)|(rfl|rfl)
    · exact (en xc).elim
    · simp
    · exact (an xc).elim
    · simp
  have large : 2≤((U∪D)∩C).card := by
    apply Nat.le_of_not_gt; intro small
    obtain ⟨_,_,scores,restrict,_⟩ := EarAttachment33.frame_obstruction H de pos inj (half_tight H half) frame
      (show e∈U∪D by simp [U]) cl (by omega)
    have listed : trianglesAt H a∈(univ.filter (fun t => H.degree t=3)).image (trianglesAt H) := by
      rw [scores]; exact mem_Icc.mpr ⟨by omega,by omega⟩
    obtain ⟨t,tm,h⟩ := mem_image.mp listed
    have eq := inj h
    subst t
    exact (restrict a tm).2.1 (mem_union_right _ (mem_insert_self ..))
  have eq := eq_of_subset_of_card_le inc (by simpa [cw.ne.symm] using large)
  exact ⟨(mem_inter.mp (show c∈(U∪D)∩C by rw [eq]; simp)).2,
    (mem_inter.mp (show w∈(U∪D)∩C by rw [eq]; simp)).2⟩

/-- Omit x in both color classes. Prescribe opposite colors for c and w,
retaining two clique pins of each color and the alternating ear square. -/
theorem blocker {e a c w x : V} (de : H.degree e=2) (rare : trianglesAt H a=2 ∨ trianglesAt H a=3)
    (ea : H.Adj e a) (ec : H.Adj e c) (aw : H.Adj a w) (cw : H.Adj c w) (ew : e≠w) (ac : a≠c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H)) (one : trianglesAt H e=1)
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (cm : c∈C) (wm : w∈C)
    (xm : x∈C) (xc : x≠c) (xw : x≠w) :
    ∃ u,u≠e ∧ u≠a ∧ u∉R ∧ H.degree u=3 ∧ H.Adj u x := by
  classical
  have en : e∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have an : a∉C := fun m => by have := clique_score H cl m; omega
  let K := C.erase x
  have ks : K.card=4 := by rw [show K=C.erase x from rfl,card_erase_of_mem xm,cl.2]
  have ck : c∈K := mem_erase.mpr ⟨xc.symm,cm⟩
  have wk : w∈K := mem_erase.mpr ⟨xw.symm,wm⟩
  obtain ⟨j,jk,jout⟩ := exists_mem_not_mem_of_card_lt_card
    (show ({c,w} : Finset V).card<K.card by rw [card_pair cw.ne,ks]; decide)
  have jc : j≠c ∧ j≠w := by simpa [not_or] using jout
  let P : Finset V := {c,j}
  let Q := K\P
  have pc : P⊆K := insert_subset ck (singleton_subset_iff.mpr jk)
  have qc : Q⊆K := sdiff_subset
  have ps : P.card=2 := card_pair jc.1.symm
  have qs : Q.card=2 := by rw [show Q=K\P from rfl,card_sdiff pc,ks,ps]
  have pC := pc.trans (erase_subset x C)
  have qC := qc.trans (erase_subset x C)
  have cp : c∈P := mem_insert_self ..
  have wq : w∈Q := mem_sdiff.mpr ⟨wk,by simp [P,cw.ne.symm,jc.2.symm]⟩
  have see {t : V} (tm : t∈C) {S : Finset V} (sub : S⊆C) (size : S.card=2) (off : t∉S) : 2≤nbr H t S := by
    have eq : S.filter (H.Adj t)=S := filter_true_of_mem (fun y ym => cl.1 tm (sub ym) (fun h => off (h ▸ ym)))
    simp [nbr,eq,size]
  let A := insert a P
  let B := insert e Q
  have dis : Disjoint A B := by
    apply disjoint_left.mpr; intro y ya yb
    rcases mem_insert.mp ya with rfl|yp <;> rcases mem_insert.mp yb with eq|yq
    · exact ea.ne eq.symm
    · exact an (qC yq)
    · exact en (eq ▸ pC yp)
    · exact (mem_sdiff.mp yq).2 yp
  have frame : Frame H A B := by
    refine ⟨dis,?_,?_⟩
    · intro y ya
      rcases mem_insert.mp ya with rfl|yp
      · exact PinnedColor34.two H ew ea.symm aw (mem_insert_self ..) (mem_insert_of_mem wq)
      · exact (see (pC yp) qC qs (fun m => (mem_sdiff.mp m).2 yp)).trans (Repair.nbr_mono H y (subset_insert ..))
    · intro y yb
      rcases mem_insert.mp yb with rfl|yq
      · exact PinnedColor34.two H ac ea ec (mem_insert_self ..) (mem_insert_of_mem cp)
      · exact (see (qC yq) pC ps (mem_sdiff.mp yq).2).trans (Repair.nbr_mono H y (subset_insert ..))
  have xp : x∉P := fun m => not_mem_erase x C (pc m)
  have xq : x∉Q := fun m => not_mem_erase x C (qc m)
  obtain ⟨u,ux,ua,ub,small,_,_⟩ := EarOnClique33.mixed_blocker H tight frame
    (show x∉A from fun m => (mem_insert.mp m).elim (fun h => an (h ▸ xm)) xp)
    (show x∉B from fun m => (mem_insert.mp m).elim (fun h => en (h ▸ xm)) xq)
    ((see xm pC ps xp).trans (Repair.nbr_mono H x (subset_insert ..)))
    ((see xm qC qs xq).trans (Repair.nbr_mono H x (subset_insert ..)))
  have ue : u≠e := fun eq => ub (eq ▸ mem_insert_self ..)
  have n1 := fun (h : trianglesAt H u=1) => ue (inj (h.trans one.symm))
  have lo : 3≤H.degree u := by
    by_contra! low
    have cap := Repair.triangles_le_choose H u
    have po := pos u
    have d : H.degree u=0 ∨ H.degree u=1 ∨ H.degree u=2 := by omega
    have upper : (H.degree u).choose 2≤1 := by rcases d with h|h|h <;> rw [h] <;> decide
    exact n1 (by omega)
  rw [CliquePivot33.isolated_degree H ux] at small
  by_cases adj : H.Adj u x
  · have m := (H.mem_neighborFinset _ _).mpr adj
    rw [card_erase_of_mem m,card_neighborFinset_eq_degree] at small
    by_cases ur : u∈R
    · simp [ur] at small; omega
    · simp [ur] at small
      exact ⟨u,ue,fun eq => ua (eq ▸ mem_insert_self ..),ur,by omega,adj⟩
  · have m : x∉H.neighborFinset u := fun h => adj ((H.mem_neighborFinset _ _).mp h)
    rw [erase_eq_of_not_mem m,card_neighborFinset_eq_degree] at small
    omega

end Graffiti384b.CubicShore
#print axioms Graffiti384b.CubicShore.clique_contains
#print axioms Graffiti384b.CubicShore.blocker
