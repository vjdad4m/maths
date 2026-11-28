import SixLayer24Slots189

namespace Graffiti189LongestPath.Layer24Numbering
open SimpleGraph Finset
set_option linter.unusedSectionVars false

theorem equiv_one_pin {U W : Type*} [DecidableEq W] (e : U≃W) (i : U) (u : W) :
    ∃ f : U≃W,f i=u := by
  refine ⟨e.trans (Equiv.swap (e i) u),?_⟩
  simp

theorem equiv_two_pins {U W : Type*} [DecidableEq W] (e : U≃W) {i j : U} {u v : W}
    (ij : i≠j) (uv : u≠v) :
    ∃ f : U≃W,f i=u ∧ f j=v := by
  obtain ⟨g,gi⟩ := equiv_one_pin e i u
  let f := g.trans (Equiv.swap (g j) v)
  have d : g i≠g j := g.injective.ne ij
  use f
  constructor
  · change Equiv.swap (g j) v (g i)=u
    rw [Equiv.swap_apply_of_ne_of_ne d (gi.trans_ne uv),gi]
  · simp [f]

variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {x : V}

structure CanonicalPartition24 (L : Layer24Cover G x) where
  mode : Kind
  sel : Fin L.T.card ≃ (↑L.T : Set V)
  primary : V→Finset V
  shared : V
  childSize : (Shell G x 3).card=childCount mode
  pSize : ∀ i : Fin L.T.card,(primary (sel i).val).card=childCap mode L.T.card i.val
  pCover : Shell G x 3⊆L.T.biUnion primary
  pSub : ∀ a∈L.T,primary a⊆Layer25Group G x a
  pDis : ∀ a∈L.T,∀ b∈L.T,a≠b → Disjoint (primary a) (primary b)
  pMembership : ∀ (i : Fin L.T.card) (z : V),z∈Layer25Group G x (sel i).val ↔
    z∈primary (sel i).val ∨ (mode=2 ∧ i.val=1 ∧ z=shared)
  sharedFirst : mode=2 → ∀ i : Fin L.T.card,i.val=0→shared∈primary (sel i).val
  full : ∀ i : Fin L.T.card,fullSelector mode L.T.card i.val →
    (Layer25Group G x (sel i).val).card=cap L.T.card
  witness : ∀ i : Fin L.T.card,∃ z∈primary (sel i).val,G.Adj (L.rep (sel i).val) z ∧
    (mode=2 → z≠shared)

theorem canonical_partition24 (L : Layer24Cover G x) :
    Nonempty (CanonicalPartition24 L) := by
  classical
  let T := L.T
  let E := Fintype.equivFinOfCardEq (Fintype.card_coe T)
  let F := Layer25Group G x
  let k := 7-T.card
  have tn : 2<T.card := by
    have h := L.tSize
    change T.card=3 ∨ T.card=4 at h
    omega
  have tpos : 0<T.card := by omega
  have base : ∀ a∈T,∃ z∈F a,G.Adj (L.rep a) z := by
    intro a aT
    obtain ⟨z,zm,az,_⟩ := L.repWitness a aT
    exact ⟨z,zm,az⟩
  have priv {a b z : V} (aT : a∈T) (bT : b∈T) (ab : a≠b) (za : z∈F a) (zb : z∈F b) :
      ∀ i∈T,∃ y∈F i,G.Adj (L.rep i) y ∧ y≠z := by
    intro i iT
    obtain ⟨w,wm,iw,wp⟩ := L.repWitness i iT
    refine ⟨w,wm,iw,?_⟩
    intro e
    subst w
    by_cases ai : a=i
    · exact wp b bT (fun h=>ab (ai.trans h.symm)) zb
    · exact wp a aT ai za
  rcases L.near_group_cases with ⟨c12,full,sep⟩|⟨c11,a,aT,sizes,sep⟩|⟨c11,full,a,aT,b,bT,z,za,zb,ab,cov,sizes,sep⟩
  · refine ⟨⟨0,E.symm,F,x,?_,?_,L.groupCover,fun _ _=>Subset.rfl,sep,?_,?_,?_,?_⟩⟩
    · simpa [childCount] using c12
    · intro i
      simpa [childCap,cap] using full (E.symm i).val (E.symm i).property
    · intro i z
      simp [F]
    · simp
    · intro i _
      exact full (E.symm i).val (E.symm i).property
    · intro i
      obtain ⟨z,zm,az⟩ := base (E.symm i).val (E.symm i).property
      exact ⟨z,zm,az,by simp⟩
  · let p : Fin T.card := ⟨T.card-1,by omega⟩
    obtain ⟨e,ep⟩ := equiv_one_pin E.symm p (⟨a,aT⟩ : (↑T : Set V))
    have eq (i : Fin T.card) : (e i).val=a ↔ i.val=T.card-1 := by
      constructor
      · intro h
        have s : e i=e p := by rw [ep]; exact Subtype.ext h
        exact congrArg Fin.val (e.injective s)
      · intro z
        have p' : i=p := Fin.ext z
        rw [p',ep]
    refine ⟨⟨1,e,F,x,?_,?_,L.groupCover,fun _ _=>Subset.rfl,sep,?_,?_,?_,?_⟩⟩
    · simpa [childCount] using c11
    · intro i
      have s := sizes (e i).val (e i).property
      change (F (e i).val).card=singleShort k a (e i).val at s
      simpa [childCap,shortIndex,cap,singleShort,eq i] using s
    · intro i z
      simp [F]
    · simp
    · intro i h
      have v := sizes (e i).val (e i).property
      have no : (e i).val≠a := by
        simpa [fullSelector,shortIndex,eq i] using h
      change (F (e i).val).card=singleShort k a (e i).val at v
      simpa [singleShort,no,cap] using v
    · intro i
      obtain ⟨z,zm,az⟩ := base (e i).val (e i).property
      exact ⟨z,zm,az,by simp⟩
  · let p : Fin T.card := ⟨0,tpos⟩
    let q : Fin T.card := ⟨1,by omega⟩
    have pq : p≠q := fun h=>by have s := congrArg Fin.val h; simp [p,q] at s
    have ab' : (⟨a,aT⟩ : (↑T : Set V))≠⟨b,bT⟩ := fun h=>ab (congrArg Subtype.val h)
    obtain ⟨e,ep,eq⟩ := equiv_two_pins E.symm pq ab'
    have atA (i : Fin T.card) : i.val=0 → (e i).val=a := by
      intro h
      rw [show i=p from Fin.ext h,ep]
    have atB (i : Fin T.card) : (e i).val=b ↔ i.val=1 := by
      constructor
      · intro h
        have s : e i=e q := by rw [eq]; exact Subtype.ext h
        exact congrArg Fin.val (e.injective s)
      · intro h
        rw [show i=q from Fin.ext h,eq]
    let P (i : V) := if i=b then (F i).erase z else F i
    refine ⟨⟨2,e,P,z,?_,?_,cov,?_,sep,?_,?_,?_,?_⟩⟩
    · simpa [childCount] using c11
    · intro i
      have h := sizes (e i).val (e i).property
      change (P (e i).val).card=singleShort k b (e i).val at h
      simpa [childCap,shortIndex,cap,singleShort,atB i] using h
    · intro u _
      by_cases e : u=b
      · simpa [P,e] using (erase_subset z (F b))
      · simp [P,e,F]
    · intro i w
      change w∈F (e i).val ↔ w∈P (e i).val ∨ ((2:Kind)=2 ∧ i.val=1 ∧ w=z)
      by_cases h : (e i).val=b
      · have i1 := (atB i).mp h
        have rest : w∈F (e i).val ↔ w∈(F (e i).val).erase z ∨ w=z := by
          constructor
          · intro wF
            by_cases u : w=z
            · exact Or.inr u
            · exact Or.inl (mem_erase.mpr ⟨u,wF⟩)
          · rintro (wE|rfl)
            · exact (mem_erase.mp wE).2
            · exact h.symm ▸ zb
        have p : P (e i).val=(F (e i).val).erase z := if_pos h
        rw [p]
        simpa only [i1,true_and] using rest
      · have i1 : i.val≠1 := fun zz=>h ((atB i).mpr zz)
        have p : P (e i).val=F (e i).val := if_neg h
        rw [p]
        simp [i1]
    · intro _ i ih
      change z∈P (e i).val
      rw [atA i ih]
      simpa [P,ab] using za
    · intro i _
      exact full (e i).val (e i).property
    · intro i
      obtain ⟨y,ym,iy,yz⟩ := priv aT bT ab za zb (e i).val (e i).property
      have yp : y∈P (e i).val := by
        by_cases h : (e i).val=b
        · simpa [P,h,mem_erase,yz] using ym
        · simpa [P,h] using ym
      exact ⟨y,yp,iy,fun _=>yz⟩

#print axioms canonical_partition24
end Graffiti189LongestPath.Layer24Numbering
