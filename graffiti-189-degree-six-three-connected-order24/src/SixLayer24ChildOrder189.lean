import SixLayer24CanonicalPartition189
namespace Graffiti189LongestPath.Layer24Numbering
open SimpleGraph Finset
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {x : V}

theorem child_order24 (L : Layer24Cover G x) (Q : CanonicalPartition24 L) :
    let t := L.T.card
    let c := (Shell G x 3).card
    ∃ e : Fin c ≃ (↑(Shell G x 3) : Set V),
      (∀ (i : Fin t) (j : Fin c),
        (e j).val∈Layer25Group G x (Q.sel i).val ↔ childHas Q.mode t i.val j.val) ∧
      (∀ (i : Fin t) (j : Fin c), firstChild Q.mode t i.val j.val →
        G.Adj (L.rep (Q.sel i).val) (e j).val) := by
  classical
  let t := L.T.card
  let c := (Shell G x 3).card
  let m := Q.mode
  let A (i : Fin t) := Q.primary (Q.sel i).val
  let sz (i : Fin t) := childCap m t i.val
  have pos (i : Fin t) : 0<sz i := positive_child_cap m L.tSize i
  let first (i : Fin t) : Fin (sz i) := ⟨0,pos i⟩
  let last (i : Fin t) : Fin (sz i) := ⟨sz i-1,by have := pos i; omega⟩
  have tpos : 0<t := by
    have h := L.tSize
    change t=3 ∨ t=4 at h
    omega
  let i0 : Fin t := ⟨0,tpos⟩
  choose w wm wad wn using Q.witness
  have rowExists (i : Fin t) : ∃ e : Fin (sz i) ≃ (↑(A i) : Set V),
      (e (first i)).val=w i ∧
      (m=2 → i.val=0 → (e (last i)).val=Q.shared) := by
    let E := (Fintype.equivFinOfCardEq ((Fintype.card_coe (A i)).trans (Q.pSize i))).symm
    by_cases mode : m=2
    · by_cases iz : i.val=0
      · have g : Q.shared∈A i := Q.sharedFirst mode i iz
        have ne : (⟨w i,wm i⟩ : (↑(A i) : Set V))≠⟨Q.shared,g⟩ :=
          fun e=>wn i mode (congrArg Subtype.val e)
        have sz' : sz i=cap t := by simp [sz,childCap,shortIndex,mode,iz]
        have t' := L.tSize
        change t=3 ∨ t=4 at t'
        have s : 1<sz i := by rw [sz']; unfold cap; omega
        have fl : first i≠last i := by
          intro e
          have h := congrArg Fin.val e
          change 0=sz i-1 at h
          omega
        obtain ⟨e,r,q⟩ := equiv_two_pins E fl ne
        exact ⟨e,congrArg Subtype.val r,fun _ _=>congrArg Subtype.val q⟩
      · obtain ⟨e,h⟩ := equiv_one_pin E (first i) ⟨w i,wm i⟩
        exact ⟨e,congrArg Subtype.val h,fun _ bad=>False.elim (iz bad)⟩
    · obtain ⟨e,h⟩ := equiv_one_pin E (first i) ⟨w i,wm i⟩
      exact ⟨e,congrArg Subtype.val h,fun bad _=>False.elim (mode bad)⟩
  choose rows rowFirst rowLast using rowExists
  let sE : Fin c ≃ Σ i : Fin t,Fin (sz i) := slotEquiv m L.tSize Q.childSize
  let u (p : Σ i : Fin t,Fin (sz i)) : (↑(Shell G x 3) : Set V) :=
    ⟨(rows p.1 p.2).val,(mem_inter.mp (Q.pSub (Q.sel p.1).val (Q.sel p.1).property (rows p.1 p.2).property)).1⟩
  have ui : Function.Injective u := by
    rintro ⟨i,r⟩ ⟨j,s⟩ eq
    have hv := congrArg Subtype.val eq
    have ij : i=j := by
      by_contra ne
      have ds := Q.pDis (Q.sel i).val (Q.sel i).property (Q.sel j).val (Q.sel j).property
        (fun e=>ne (Q.sel.injective (Subtype.ext e)))
      have yy : (rows i r).val∈A j := hv.symm ▸ (rows j s).property
      exact disjoint_left.mp ds (rows i r).property yy
    subst j
    have rs := (rows i).injective (Subtype.ext hv)
    change r=s at rs
    cases rs
    rfl
  have us : Function.Surjective u := by
    rintro ⟨y,ym⟩
    obtain ⟨a,aT,ya⟩ := mem_biUnion.mp (Q.pCover ym)
    obtain ⟨i,h⟩ := Q.sel.surjective ⟨a,aT⟩
    have ia : (Q.sel i).val=a := congrArg Subtype.val h
    have yi : y∈A i := by change y∈Q.primary (Q.sel i).val; rwa [ia]
    obtain ⟨j,jm⟩ := (rows i).surjective ⟨y,yi⟩
    refine ⟨⟨i,j⟩,Subtype.ext ?_⟩
    change (rows i j).val=y
    exact congrArg Subtype.val jm
  let E := sE.trans (Equiv.ofBijective u ⟨ui,us⟩)
  have val (j : Fin c) :
      (E j).val=(rows (sE j).1 (sE j).2).val := rfl
  have own (i : Fin t) (j : Fin c) :
      (E j).val∈A i ↔ owner m t j.val=i.val := by
    have q : (E j).val∈A (sE j).1 := by rw [val]; exact (rows _ _).property
    have pv := slot_owner m L.tSize Q.childSize j
    change ((sE j).1).val=owner m t j.val at pv
    constructor
    · intro p
      by_cases h : owner m t j.val=i.val
      · exact h
      exfalso
      have ne : i≠(sE j).1 := by
        intro e
        exact h (e.symm ▸ pv.symm)
      exact disjoint_left.mp
        (Q.pDis (Q.sel i).val (Q.sel i).property (Q.sel (sE j).1).val (Q.sel (sE j).1).property
          (fun e=>ne (Q.sel.injective (Subtype.ext e)))) p q
    · intro p
      have e : (sE j).1=i := Fin.ext (pv.trans p)
      exact e ▸ q
  have shared (h : m=2) (j : Fin c) :
      (E j).val=Q.shared ↔ rawSlot m t j.val=cap t-1 := by
    have c11 : c=11 := by
      have v := Q.childSize
      change c=childCount m at v
      rw [h] at v
      exact v
    have ar : rawSlot m t j.val=cap t-1 ↔
        owner m t j.val=0 ∧ cell m t j.val=cap t-1 := by
      rw [h]
      exact overlap_shared_slot L.tSize ⟨j.val,by have jj:=j.isLt; change j.val<c at jj; omega⟩
    let i := (sE j).1
    have v : i.val=owner m t j.val := slot_owner m L.tSize Q.childSize j
    have w : ((sE j).2).val=cell m t j.val := slot_cell m L.tSize Q.childSize j
    have szEq (ii : Fin t) (zero : ii.val=0) : sz ii=cap t := by
      simp [sz,childCap,shortIndex,h,zero]
    constructor
    · intro eq
      have q : (E j).val∈A i0 := by
        rw [eq]
        exact Q.sharedFirst h i0 rfl
      have oz := (own i0 j).mp q
      have z : i.val=0 := v.trans oz
      have u : (rows i (sE j).2).val = (rows i (last i)).val :=
        (val j).symm.trans (eq.trans (rowLast i h z).symm)
      have k := (rows i).injective (Subtype.ext u)
      have k' := congrArg Fin.val k
      change ((sE j).2).val=sz i-1 at k'
      exact ar.mpr ⟨oz,w.symm.trans (k'.trans (congrArg (fun n : ℕ=>n-1) (szEq i z)))⟩
    · intro eq
      obtain ⟨zero,cellEq⟩ := ar.mp eq
      have zi : i.val=0 := v.trans zero
      have lastEq : (sE j).2=last i := by
        apply Fin.ext
        change ((sE j).2).val=sz i-1
        rw [w,cellEq,szEq i zi]
      change (rows i (sE j).2).val=Q.shared
      rw [lastEq]
      exact rowLast i h zi
  refine ⟨E,?_,?_⟩
  · intro i j
    change (E j).val∈Layer25Group G x (Q.sel i).val ↔ childHas m t i.val j.val
    rw [Q.pMembership,own]
    unfold childHas
    constructor
    · rintro (p|⟨h,i1,eq⟩)
      · exact Or.inl p
      · exact Or.inr ⟨h,i1,(shared h j).mp eq⟩
    · rintro (p|⟨h,i1,eq⟩)
      · exact Or.inl p
      · exact Or.inr ⟨h,i1,(shared h j).mpr eq⟩
  · intro i j h
    have iv : ((sE j).1).val=owner m t j.val := slot_owner m L.tSize Q.childSize j
    have kv : ((sE j).2).val=cell m t j.val := slot_cell m L.tSize Q.childSize j
    have k : (sE j).2=first (sE j).1 := Fin.ext (kv.trans h.2)
    have e : (sE j).1=i := Fin.ext (iv.trans h.1)
    rw [val,k,rowFirst,e]
    exact wad i

#print axioms child_order24
end Graffiti189LongestPath.Layer24Numbering
