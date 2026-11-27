import PaletteFinish33

namespace Graffiti384b.RootCut
open Finset SimpleGraph CliquePivot33
open private Repair.isolate Repair.iso_nbr Repair.full_nbr Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem credited_shared (R : Finset V) {x : V} {P Q : Finset V} (dis : Disjoint P Q)
    (xp : x∉P) (xq : x∉Q) (px : 2≤nbr G x P) (qx : 2≤nbr G x Q)
    (pinnedP : ∀ v∈P,2≤nbr G v Q+(if v∈R then 1 else 0)) (pinnedQ : ∀ v∈Q,2≤nbr G v P+(if v∈R then 1 else 0))
    (free : ∀ v,v≠x → v∉P → v∉Q → 3≤(Repair.isolate G x).degree v+2*(if v∈R then 1 else 0)) : ¬Tight G R := by
  intro tight
  let J := Repair.isolate G x
  obtain ⟨A,pa,qb,la,rb⟩ := PinnedColor34.cut J P Q dis
  have pa' : P⊆A.erase x := fun v vp => mem_erase.mpr ⟨fun eq => xp (eq ▸ vp),pa vp⟩
  have qb' : Q⊆Aᶜ.erase x := fun v vq => mem_erase.mpr ⟨fun eq => xq (eq ▸ vq),qb vq⟩
  have first : Relaxed G R (A.erase x) := by
    intro v out
    by_cases vx : v=x
    · subst v; exact Nat.le_add_right_of_le (px.trans (Repair.nbr_mono G _ pa'))
    have va : v∉A := fun h => out (mem_erase.mpr ⟨vx,h⟩)
    by_cases vq : v∈Q
    · exact (pinnedQ _ vq).trans (Nat.add_le_add_right (Repair.nbr_mono G _ pa') _)
    have deg := free _ vx (fun m => va (pa m)) vq
    have r := rb v (mem_compl.mpr va) vq
    have tot := Repair.full_nbr J v A
    change 3≤J.degree v+2*(if v∈R then 1 else 0) at deg
    rw [← Repair.iso_nbr G vx A]
    change 2≤nbr J v A+(if v∈R then 1 else 0)
    omega
  have second : Relaxed G R (Aᶜ.erase x) := by
    intro v out
    by_cases vx : v=x
    · subst v; exact Nat.le_add_right_of_le (qx.trans (Repair.nbr_mono G _ qb'))
    have va : v∈A := by
      apply Classical.byContradiction; intro m
      exact out (mem_erase.mpr ⟨vx,mem_compl.mpr m⟩)
    by_cases vp : v∈P
    · exact (pinnedP _ vp).trans (Nat.add_le_add_right (Repair.nbr_mono G _ qb') _)
    have deg := free _ vx vp (fun m => mem_compl.mp (qb m) va)
    have l := la v va vp
    have tot := Repair.full_nbr J v A
    change 3≤J.degree v+2*(if v∈R then 1 else 0) at deg
    rw [← Repair.iso_nbr G vx Aᶜ]
    change 2≤nbr J v Aᶜ+(if v∈R then 1 else 0)
    omega
  have l := tight _ first
  have r := tight _ second
  by_cases xa : x∈A
  · have pos := card_pos.mpr (show A.Nonempty from ⟨x,xa⟩)
    have cap := card_le_univ A
    rw [card_erase_of_mem xa] at l
    rw [erase_eq_of_not_mem (fun m => mem_compl.mp m xa),card_compl] at r
    omega
  · have pos := card_pos.mpr (show Aᶜ.Nonempty from ⟨x,mem_compl.mpr xa⟩)
    rw [card_compl] at pos
    rw [erase_eq_of_not_mem xa] at l
    rw [card_erase_of_mem (mem_compl.mpr xa),card_compl] at r
    omega

variable (H J : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel J.Adj]

/-- Switch the cut independently on components. The two ear endpoints
receive the same color while the four clique pins stay split two against two. -/
theorem patch_switch {W R K : Finset V} {e a c x : V}
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : a≠c)
    (xe : x≠e) (xa : x≠a) (xc : x≠c)
    (sub : J≤H) (ie : ∀ y,¬J.Adj e y) (ix : ∀ y,¬J.Adj x y)
    (apart : ¬J.Reachable a c) (cl : J.IsNClique 4 K)
    (ke : e∉K) (kx : x∉K) (sees : ∀ y∈K,H.Adj x y)
    (da : 0<J.degree a) (dc : 0<J.degree c)
    (ew : e∈W) (aw : a∈W) (cw : c∈W) (kw : K⊆W)
    (closed : ∀ v∈W,∀ u,J.Adj v u → u∈W)
    (free : ∀ v,v≠x → v∉W → 3≤(Repair.isolate H x).degree v+2*(if v∈R then 1 else 0))
    (dg : ∀ v∈W,v≠e → v≠a → v≠c → v≠x → 3≤J.degree v+2*(if v∈R then 1 else 0)) : ¬Tight H R := by
  classical
  obtain ⟨P,pk,ps⟩ := exists_subset_card_eq (show 2≤K.card by rw [cl.2]; decide)
  let Q := K\P
  have qk : Q⊆K := sdiff_subset
  have qs : Q.card=2 := by rw [show Q=K\P from rfl,card_sdiff pk,cl.2,ps]
  have dis : Disjoint P Q := disjoint_left.mpr (fun _ p q => (mem_sdiff.mp q).2 p)
  have see {v : V} (vm : v∈K) {T : Finset V} (tk : T⊆K) (ts : T.card=2) (off : v∉T) : 2≤nbr J v T := by
    have eq : T.filter (J.Adj v)=T := filter_true_of_mem (fun y m => cl.1 vm (tk m) (fun h => off (h ▸ m)))
    simp [nbr,eq,ts]
  obtain ⟨A,pa,qa,left,right⟩ := PinnedColor34.cut J P Q dis
  let opp (v : V) := if v∈A then Aᶜ else A
  have sufficient (v : V) : 2≤nbr J v (opp v) ∨ J.degree v≤2*nbr J v (opp v) := by
    have tot := Repair.full_nbr J v A
    by_cases va : v∈A
    · simp only [opp,if_pos va]
      by_cases vp : v∈P
      · exact Or.inl ((see (pk vp) qk qs (fun m => disjoint_left.mp dis vp m)).trans (Repair.nbr_mono J v qa))
      · have h := left v va vp; exact Or.inr (by omega)
    · simp only [opp,if_neg va]
      by_cases vq : v∈Q
      · exact Or.inl ((see (qk vq) pk ps (mem_sdiff.mp vq).2).trans (Repair.nbr_mono J v pa))
      · have h := right v (mem_compl.mpr va) vq; exact Or.inr (by omega)
  let ref (v : V) := if J.Reachable a v then a else c
  let S := univ.filter (fun v => v≠e ∧ (v∈A ↔ ref v∈A))
  have sm {v : V} : v∈S ↔ v≠e ∧ (v∈A ↔ ref v∈A) := by simp [S]
  have aS : a∈S := sm.mpr ⟨ea.ne.symm,by simp [ref,Reachable.refl]⟩
  have cS : c∈S := sm.mpr ⟨ec.ne.symm,by simp [ref,apart]⟩
  have eS : e∉S := fun m => (sm.mp m).1 rfl
  have fixed {v u : V} (r : J.Reachable v u) : ref v=ref u := by
    have eq : J.Reachable a v ↔ J.Reachable a u := ⟨fun h => h.trans r,fun h => h.trans r.symm⟩
    simp only [ref,eq]
  have across {u v : V} (edge : J.Adj u v) (m : v∈opp u) : (v∈S ↔ u∉S) := by
    have ue : u≠e := fun h => ie _ (h ▸ edge)
    have ve : v≠e := fun h => ie _ (h ▸ edge.symm)
    rw [sm,sm]; simp only [ue,ve,true_and,fixed edge.reachable]
    by_cases ua : u∈A
    · have va := mem_compl.mp (show v∈Aᶜ by simpa [opp,ua] using m)
      simp [va,ua,ue,ve]
    · have va : v∈A := by simpa [opp,ua] using m
      simp [va,ua,ue,ve]
  let O (v : V) := (if v∈S then Sᶜ else S).erase x ∩ W
  have inc (v : V) (vw : v∈W) : (opp v).filter (J.Adj v)⊆(O v).filter (H.Adj v) := by
    intro u um; obtain ⟨uo,edge⟩ := mem_filter.mp um
    have ux : u≠x := fun h => ix _ (h ▸ edge.symm)
    exact mem_filter.mpr ⟨mem_inter.mpr ⟨mem_erase.mpr ⟨ux,by
      have h := across edge uo
      by_cases vs : v∈S <;> simp [vs,h]⟩,closed v vw u edge⟩,sub edge⟩
  have anchor (v : V) (vw : v∈W) (vs : v∈S) (ev : H.Adj e v) (dv : 0<J.degree v) : 2≤nbr H v (O v) := by
    have suff := sufficient v
    obtain ⟨y,ym⟩ := card_pos.mp (show 0<((opp v).filter (J.Adj v)).card by change 0<nbr J v (opp v); omega)
    have edge := (mem_filter.mp ym).2
    exact PinnedColor34.two H (fun h => ie _ (h ▸ edge.symm)) (sub edge) ev.symm (mem_filter.mp (inc v vw ym)).1
      (by simp [O,vs,eS,xe.symm,ew])
  have good (v : V) (vw : v∈W) (vx : v≠x) : 2≤nbr H v (O v)+(if v∈R then 1 else 0) := by
    by_cases ve : v=e
    · subst v
      have lo : 2≤nbr H e (O e) := PinnedColor34.two H ac ea ec
        (by simp [O,eS,aS,xa.symm,aw]) (by simp [O,eS,cS,xc.symm,cw])
      omega
    by_cases va : v=a
    · subst v; have := anchor a aw aS ea da; omega
    by_cases vc : v=c
    · subst v; have := anchor c cw cS ec dc; omega
    have d := dg v vw ve va vc vx
    have h := sufficient v
    have bound : nbr J v (opp v)≤nbr H v (O v) := card_le_card (inc v vw)
    omega
  obtain ⟨k,km⟩ := card_pos.mp (show 0<K.card by rw [cl.2]; decide)
  have same (v : V) (vm : v∈K) : ref v=ref k := by
    by_cases h : v=k
    · exact congrArg ref h
    · exact fixed (cl.1 vm km h).reachable
  have incl {T : Finset V} (tk : T⊆K) (ts : T.card=2) {D : Finset V} (membership : ∀ y∈T,y∈D) :
      2≤nbr H x (D.erase x∩W) := by
    have f : T.filter (H.Adj x)=T := filter_true_of_mem (fun y m => sees y (tk m))
    apply (show 2≤nbr H x T by simp [nbr,f,ts]).trans
    exact Repair.nbr_mono H x (fun y m => mem_inter.mpr ⟨mem_erase.mpr ⟨fun h => kx (h ▸ tk m),membership y m⟩,kw (tk m)⟩)
  have pivot : 2≤nbr H x (S.erase x∩W) ∧ 2≤nbr H x (Sᶜ.erase x∩W) := by
    have color {y : V} (yk : y∈K) : y∈S ↔ (y∈A ↔ ref k∈A) := by
      rw [sm,same y yk]; simp [show y≠e from fun eq => ke (eq ▸ yk)]
    by_cases red : ref k∈A
    · exact ⟨incl pk ps (fun y m => (color (pk m)).mpr (by simp [red,pa m])),
        incl qk qs (fun y m => mem_compl.mpr (fun h => (mem_compl.mp (qa m)) (((color (qk m)).mp h).mpr red)))⟩
    · exact ⟨incl qk qs (fun y m => (color (qk m)).mpr (by simp [red,mem_compl.mp (qa m)])),
        incl pk ps (fun y m => mem_compl.mpr (fun h => red (((color (pk m)).mp h).mp (pa m))))⟩
  apply credited_shared H R (P:=S.erase x∩W) (Q:=Sᶜ.erase x∩W)
    (disjoint_left.mpr (fun y yp yq => mem_compl.mp (mem_erase.mp (mem_inter.mp yq).1).2 (mem_erase.mp (mem_inter.mp yp).1).2))
    (fun m => not_mem_erase x S (mem_inter.mp m).1) (fun m => not_mem_erase x Sᶜ (mem_inter.mp m).1) pivot.1 pivot.2
  · intro y ym; obtain ⟨side,yw⟩ := mem_inter.mp ym
    obtain ⟨yx,yes⟩ := mem_erase.mp side
    simpa only [O,if_pos yes] using good y yw yx
  · intro y ym; obtain ⟨side,yw⟩ := mem_inter.mp ym
    obtain ⟨yx,no⟩ := mem_erase.mp side
    simpa only [O,if_neg (mem_compl.mp no)] using good y yw yx
  · intro y yx yp yq; apply free y yx; intro yw
    by_cases yes : y∈S
    · exact yp (mem_inter.mpr ⟨mem_erase.mpr ⟨yx,yes⟩,yw⟩)
    · exact yq (mem_inter.mpr ⟨mem_erase.mpr ⟨yx,mem_compl.mpr yes⟩,yw⟩)

end Graffiti384b.RootCut
#print axioms Graffiti384b.RootCut.patch_switch
