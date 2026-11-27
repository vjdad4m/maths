import HighEarDegree33

namespace Graffiti384b.HighEar
open Finset SimpleGraph CliquePivot33
open private Repair.full_nbr Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H J : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableRel J.Adj]

/-- Switch the cut independently on components. The two ear endpoints
receive the same color while the four clique pins stay split two against two. -/
theorem switch_cut {R K : Finset V} {e a c x : V}
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : a≠c)
    (xe : x≠e) (xa : x≠a) (xc : x≠c)
    (sub : J≤H) (ie : ∀ y,¬J.Adj e y) (ix : ∀ y,¬J.Adj x y)
    (apart : ¬J.Reachable a c) (cl : J.IsNClique 4 K)
    (ke : e∉K) (kx : x∉K) (sees : ∀ y∈K,H.Adj x y)
    (da : 0<J.degree a) (dc : 0<J.degree c)
    (dg : ∀ v,v≠e → v≠a → v≠c → v≠x → 3≤J.degree v+2*(if v∈R then 1 else 0)) : ¬Tight H R := by
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
  let O (v : V) := (if v∈S then Sᶜ else S).erase x
  have inc (v : V) : (opp v).filter (J.Adj v)⊆(O v).filter (H.Adj v) := by
    intro u um; obtain ⟨uo,edge⟩ := mem_filter.mp um
    have ux : u≠x := fun h => ix _ (h ▸ edge.symm)
    exact mem_filter.mpr ⟨mem_erase.mpr ⟨ux,by
      have h := across edge uo
      by_cases vs : v∈S <;> simp [vs,h]⟩,sub edge⟩
  have anchor (v : V) (vs : v∈S) (ev : H.Adj e v) (dv : 0<J.degree v) : 2≤nbr H v (O v) := by
    have suff := sufficient v
    obtain ⟨y,ym⟩ := card_pos.mp (show 0<((opp v).filter (J.Adj v)).card by change 0<nbr J v (opp v); omega)
    have edge := (mem_filter.mp ym).2
    exact PinnedColor34.two H (fun h => ie _ (h ▸ edge.symm)) (sub edge) ev.symm (mem_filter.mp (inc v ym)).1
      (by simp [O,vs,eS,xe.symm])
  have good (v : V) (vx : v≠x) : 2≤nbr H v (O v)+(if v∈R then 1 else 0) := by
    by_cases ve : v=e
    · subst v
      have lo : 2≤nbr H e (O e) := PinnedColor34.two H ac ea ec
        (by simp [O,eS,aS,xa.symm]) (by simp [O,eS,cS,xc.symm])
      omega
    by_cases va : v=a
    · subst v; have := anchor a aS ea da; omega
    by_cases vc : v=c
    · subst v; have := anchor c cS ec dc; omega
    have d := dg v ve va vc vx
    have h := sufficient v
    have bound : nbr J v (opp v)≤nbr H v (O v) := card_le_card (inc v)
    omega
  obtain ⟨k,km⟩ := card_pos.mp (show 0<K.card by rw [cl.2]; decide)
  have same (v : V) (vm : v∈K) : ref v=ref k := by
    by_cases h : v=k
    · exact congrArg ref h
    · exact fixed (cl.1 vm km h).reachable
  have incl {T : Finset V} (tk : T⊆K) (ts : T.card=2) {D : Finset V} (membership : ∀ y∈T,y∈D) :
      2≤nbr H x (D.erase x) := by
    have f : T.filter (H.Adj x)=T := filter_true_of_mem (fun y m => sees y (tk m))
    apply (show 2≤nbr H x T by simp [nbr,f,ts]).trans
    exact Repair.nbr_mono H x (fun y m => mem_erase.mpr ⟨fun h => kx (h ▸ tk m),membership y m⟩)
  have pivot : 2≤nbr H x (S.erase x) ∧ 2≤nbr H x (Sᶜ.erase x) := by
    have color {y : V} (yk : y∈K) : y∈S ↔ (y∈A ↔ ref k∈A) := by
      rw [sm,same y yk]; simp [show y≠e from fun eq => ke (eq ▸ yk)]
    by_cases red : ref k∈A
    · exact ⟨incl pk ps (fun y m => (color (pk m)).mpr (by simp [red,pa m])),
        incl qk qs (fun y m => mem_compl.mpr (fun h => (mem_compl.mp (qa m)) (((color (qk m)).mp h).mpr red)))⟩
    · exact ⟨incl qk qs (fun y m => (color (qk m)).mpr (by simp [red,mem_compl.mp (qa m)])),
        incl pk ps (fun y m => mem_compl.mpr (fun h => red (((color (pk m)).mp h).mp (pa m))))⟩
  have first : Relaxed H R (S.erase x) := by
    intro v off
    by_cases vx : v=x
    · subst v; have := pivot.1; omega
    have no : v∉S := fun m => off (mem_erase.mpr ⟨vx,m⟩)
    simpa only [O,if_neg no] using good v vx
  have second : Relaxed H R (Sᶜ.erase x) := by
    intro v off
    by_cases vx : v=x
    · subst v; have := pivot.2; omega
    have yes : v∈S := by apply Classical.byContradiction; intro no; exact off (mem_erase.mpr ⟨vx,mem_compl.mpr no⟩)
    simpa only [O,if_pos yes] using good v vx
  intro tight
  have l := tight _ first
  have r := tight _ second
  have cap := card_le_univ S
  by_cases xs : x∈S
  · have pos := card_pos.mpr (show S.Nonempty from ⟨x,xs⟩)
    rw [card_erase_of_mem xs] at l
    rw [erase_eq_of_not_mem (fun m => mem_compl.mp m xs),card_compl] at r
    omega
  · have pos := card_pos.mpr (show Sᶜ.Nonempty from ⟨x,mem_compl.mpr xs⟩)
    rw [card_compl] at pos
    rw [erase_eq_of_not_mem xs] at l
    rw [card_erase_of_mem (mem_compl.mpr xs),card_compl] at r
    omega

end Graffiti384b.HighEar
#print axioms Graffiti384b.HighEar.switch_cut
