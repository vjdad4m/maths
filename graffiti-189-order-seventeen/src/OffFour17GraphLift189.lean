import OffFour17Base189
import OffSix17CoreLift189

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack OffFour17
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
open private pin_data pin_pos no_endpoints dist_two mem_distanceTwo
  LeftMarks RightMarks card_leftMarks card_rightMarks from SmallOrderFour189
open private offSix_walk_of_chain from OffSix17CoreLift189

structure FourOmissionPattern17 {a b : V} (p : G.Walk a b) (t i j k l : ℕ) where
  labels : Fin 4→V
  injectiveLabels : Function.Injective labels
  offLabels : ∀ q,labels q∉p.support
  left : i  ≤  11
  right : j  ≤  11
  low : k  ≤  11
  high : l  ≤  11
  marked : ∀ r, r=i ∨ r=j ∨ (t=3 ∧ (r=k ∨ r=l)) → ∃ z∉p.support,r∈Pins p z
  retainedPorts : ∀ (s : Fin 4) r,OffFour17.attach t i j k l r (13+s.val) → r∈Pins p (labels s)
  retainedCore : ∀ s u : Fin 4,core t (13+s.val) (13+u.val) → G.Adj (labels s) (labels u)
  holes : t≠0 → ∀ r,hole i j r → r∉LeftMarks p∪RightMarks p

private theorem offFour17_endpoint_d2 (hc : G.Connected)
    (φ : Fin 17 → V) (inj : Function.Injective φ)
    (E : Fin 17 → Fin 17 → Bool) (z : Fin 17)
    (forw : ∀ u v,E u v=true → G.Adj (φ u) (φ v))
    (rev : ∀ u,G.Adj (φ z) (φ u) → E z u=true)
    (cap : (DistanceTwo G (φ z)).card ≤ 4) :
    (univ.filter fun y => y≠z ∧ !E z y = true ∧
      ∃ u : Fin 17,E z u=true ∧ E u y=true).card ≤ 4 := by
  classical
  let Q := univ.filter fun y => y≠z ∧ !E z y = true ∧
      ∃ u : Fin 17,E z u=true ∧ E u y=true
  have sub : Q.image φ ⊆ DistanceTwo G (φ z) := by
    intro y hy
    obtain ⟨v,vq,rfl⟩ := mem_image.mp hy
    obtain ⟨vne,no,w,zw,wv⟩ := (mem_filter.mp vq).2
    have ne : φ z≠φ v := fun e => vne (inj e).symm
    have no' : ¬G.Adj (φ z) (φ v) := fun e => by
      have r := rev v e
      simp [r] at no
    exact mem_distanceTwo.mpr (dist_two hc ne no' (forw z w zw) (forw w v wv))
  have c := card_le_card sub
  rw [card_image_of_injective _ inj] at c
  exact c.trans cap






private theorem off_four_17_marks
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4  ≤  G.degree a) (bh : 4  ≤  G.degree b) (len : p.length=12)
    (xo : x∉p.support)
    {i : ℕ} (hi : i∈Pins p x) :
    ∃ m : Marks, m 0=1 ∧ m 11=2 ∧
      4  ≤  count m 1 ∧ 4  ≤  count m 2 ∧
      (∀ k : Fin 12,m k=1 ↔ G.Adj a (p.getVert (k.val+1))) ∧
      (∀ k : Fin 12,m k=2 ↔ G.Adj b (p.getVert k.val))  := by
  classical
  have e : ∀ k<p.length, ¬(G.Adj a (p.getVert (k+1)) ∧ G.Adj b (p.getVert k)) := by
    intro k kr h
    exact not_adj_both_end_marks hp.1 xo (p.getVert_mem_support i) (pin_data hi).2 kr h.1 h.2
  let m : Marks := fun k => if G.Adj a (p.getVert (k.val+1)) then 1
    else if G.Adj b (p.getVert k.val) then 2 else 0
  have l (k : Fin 12) : m k=1 ↔ G.Adj a (p.getVert (k.val+1)) := by
    by_cases h : G.Adj a (p.getVert (k.val+1))
    · simp [m,h]
    · by_cases r : G.Adj b (p.getVert k.val) <;> simp [m,h,r]
  have r (k : Fin 12) : m k=2 ↔ G.Adj b (p.getVert k.val) := by
    have kb := k.isLt
    by_cases h : G.Adj a (p.getVert (k.val+1))
    · have no : ¬G.Adj b (p.getVert k.val) := fun n => e _ (by omega) ⟨h,n⟩
      simp [m,h,no]
    · by_cases s : G.Adj b (p.getVert k.val) <;> simp [m,h,s]
  have m0 : m 0=1 := (l 0).mpr (by simpa using p.adj_getVert_succ (i:=0) (by omega))
  have m11 : m 11=2 := (r 11).mpr (by
    have rr := (p.adj_getVert_succ (i:=11) (by omega)).symm
    rw [show 11+1=p.length by omega,p.getVert_length] at rr
    exact rr)
  refine ⟨m,m0,m11,?_,?_,l,r⟩
  · unfold count
    let N := univ.filter (fun k : Fin 12 => m k=1)
    have eq : N.image Fin.val=LeftMarks p := by
      ext n
      constructor
      · rintro H
        obtain ⟨k,km,rfl⟩ := mem_image.mp H
        exact mem_filter.mpr ⟨mem_range.mpr (by have g := k.isLt; omega), (l k).mp (mem_filter.mp km).2⟩
      · intro nm
        have nb := mem_range.mp (mem_filter.mp nm).1
        exact mem_image.mpr ⟨⟨n,by omega⟩,mem_filter.mpr ⟨mem_univ _,(l ⟨n,by omega⟩).mpr (mem_filter.mp nm).2⟩,rfl⟩
    have ce : (N.image Fin.val).card=N.card := card_image_iff.mpr (fun _ _ _ _ e => Fin.ext e)
    change 4  ≤  N.card
    rwa [←ce,eq,card_leftMarks hp.1]
  · unfold count
    let N := univ.filter (fun k : Fin 12 => m k=2)
    have eq : N.image Fin.val=RightMarks p := by
      ext n
      constructor
      · rintro H
        obtain ⟨k,km,rfl⟩ := mem_image.mp H
        exact mem_filter.mpr ⟨mem_range.mpr (by have g := k.isLt; omega),(r k).mp (mem_filter.mp km).2⟩
      · intro nm
        have nb := mem_range.mp (mem_filter.mp nm).1
        exact mem_image.mpr ⟨⟨n,by omega⟩,mem_filter.mpr ⟨mem_univ _,(r ⟨n,by omega⟩).mpr (mem_filter.mp nm).2⟩,rfl⟩
    have ce : (N.image Fin.val).card=N.card := card_image_iff.mpr (fun _ _ _ _ e => Fin.ext e)
    change 4  ≤  N.card
    rwa [←ce,eq,card_rightMarks hp.1]

/-- Lifts a checked reduced-model row to an actual longer graph path. -/
theorem four_omissions_row_contradiction
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card  ≤  5)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4  ≤  G.degree a) (bh : 4  ≤  G.degree b)
    (len : p.length=12) {t i j k l : ℕ} (P : FourOmissionPattern17 p t i j k l)
    (rowProof : row t i j=true) (extraProof : (k,l)∈extra t i j) : False := by
  classical
  obtain ⟨x,xo,xi⟩ := P.marked i (.inl rfl)
  obtain ⟨m,m0,m11,ml,mr,L,R⟩ := off_four_17_marks hp ah bh len xo xi
  have markL (q : Fin 12) (h : m q=1) (r : ℕ)
      (p' : r=i ∨ r=j ∨ (t=3 ∧ (r=k ∨ r=l))) : q.val≠r := by
    intro e
    obtain ⟨z,zo,zr⟩ := P.marked r p'
    exact start_not_adj_pin_successor hp.1 zo zr (e ▸ (L q).mp h)
  have markR (q : Fin 12) (h : m q=2) (r : ℕ)
      (p' : r=i ∨ r=j ∨ (t=3 ∧ (r=k ∨ r=l))) : q.val+1≠r := by
    intro e
    obtain ⟨z,zo,zr⟩ := P.marked r p'
    exact end_not_adj_pin_predecessor hp.1 zo zr (by
      simpa only [show r-1=q.val by omega] using (R q).mp h)
  have zero (q : Fin 12) : m q=0 ↔ q.val∉LeftMarks p∪RightMarks p := by
    constructor
    · intro q0 hm
      rcases mem_union.mp hm with la|ra
      · have c := (L q).mpr (mem_filter.mp la).2
        rw [q0] at c
        contradiction
      · have c := (R q).mpr (mem_filter.mp ra).2
        rw [q0] at c
        contradiction
    · intro no
      have r := (m q).isLt
      have e : (m q).val=0 ∨ (m q).val=1 ∨ (m q).val=2 := by omega
      rcases e with h|h|h
      · exact Fin.ext h
      · exact (no (mem_union.mpr (.inl (mem_filter.mpr ⟨mem_range.mpr (by
          have e:=q.isLt; omega),(L q).mp (Fin.ext h)⟩)))).elim
      · exact (no (mem_union.mpr (.inr (mem_filter.mpr ⟨mem_range.mpr (by
          have e:=q.isLt; omega),(R q).mp (Fin.ext h)⟩)))).elim
  have v (q : Fin 12) : valid t i j q.val (m q) :=
    ⟨fun h=>⟨markL q h i (.inl rfl), markL q h j (.inr (.inl rfl))⟩,
     fun h=>⟨markR q h i (.inl rfl), markR q h j (.inr (.inl rfl))⟩,
     fun ht hr=>(zero q).mpr (P.holes ht _ hr)⟩
  have sd : sideValid t k l m := by
    intro t3 q
    exact ⟨fun h=>⟨markL q h k (.inr (.inr ⟨t3,.inl rfl⟩)),markL q h l (.inr (.inr ⟨t3,.inr rfl⟩))⟩,
     fun h=>⟨markR q h k (.inr (.inr ⟨t3,.inl rfl⟩)),markR q h l (.inr (.inr ⟨t3,.inr rfl⟩))⟩⟩
  let φ (u : Fin 17) : V :=
    if h : u.val  ≤  12 then p.getVert u.val
    else P.labels ⟨u.val-13, by have q:=u.isLt; omega⟩
  have atSp (u : Fin 17) (h : u.val  ≤  12) : φ u=p.getVert u.val := by simp [φ,h]
  have atOff (u : Fin 17) (h : 13  ≤  u.val) :
      φ u=P.labels ⟨u.val-13, by have q:=u.isLt; omega⟩ := by simp [φ,show ¬u.val  ≤  12 by omega]
  have om (u : Fin 17) (h : 13  ≤  u.val) : φ u∉p.support := by rw [atOff u h]; apply P.offLabels
  have inj : Function.Injective φ := by
    intro u w e
    by_cases hu : u.val  ≤  12 <;> by_cases hw : w.val  ≤  12
    · rw [atSp u hu,atSp w hw] at e
      exact Fin.ext (hp.1.1.getVert_injOn (show u.val ≤ p.length by omega) (show w.val ≤ p.length by omega) e)
    · exact (om w (by omega) (e ▸ ((atSp u hu).symm ▸ p.getVert_mem_support u.val))).elim
    · exact (om u (by omega) (e.symm ▸ ((atSp w hw).symm ▸ p.getVert_mem_support w.val))).elim
    · rw [atOff u (by omega),atOff w (by omega)] at e
      have g := congrArg Fin.val (P.injectiveLabels e)
      change u.val-13=w.val-13 at g
      exact Fin.ext (by omega)
  have A0 : φ 0=a := by rw [atSp _ (by decide)]; exact p.getVert_zero
  have B12 : φ 12=b := by rw [atSp _ (by decide)]; simpa only [len] using p.getVert_length
  have fwDir (u w : Fin 17) (h : dir t i j k l m u w=true) : G.Adj (φ u) (φ w) := by
    simp only [dir,Bool.or_eq_true,decide_eq_true_eq] at h
    rcases h with ((((ht|c)|d)|s)|r)
    · rw [atSp u (by omega),atSp w ht.2,ht.1]
      exact p.adj_getVert_succ (by omega)
    · have cu : 13  ≤  u.val := c.1
      have cv : 13  ≤  w.val := by have e:=c.2.1; omega
      rw [atOff u cu,atOff w cv]
      apply P.retainedCore
      simpa only [show 13+(u.val-13)=u.val by omega,show 13+(w.val-13)=w.val by omega] using c
    · have dd : u.val  ≤  12 ∧ 13  ≤  w.val := by
        unfold OffFour17.attach at d
        split at d
        · rcases d with ⟨e,f⟩|⟨e,f⟩ <;> have g:=P.left <;> have h:=P.right <;> omega
        split at d
        · rcases d with ⟨e,f⟩|⟨f,e⟩
          · rcases e with h|h <;> have a:=P.left <;> have b:=P.right <;> omega
          · rcases e with ⟨_,h⟩|⟨_,h⟩ <;> have a:=P.left <;> have b:=P.right <;> omega
        · rcases d with ⟨e,f,h⟩|⟨e,f⟩
          · rcases e with h|h <;> have a:=P.left <;> have b:=P.right <;> omega
          · rcases e with h|h <;> have a:=P.low <;> have b:=P.high <;> omega
      rw [atSp u dd.1,atOff w dd.2]
      have pin := P.retainedPorts ⟨w.val-13,by have e:=w.isLt; omega⟩ u.val
        (by simpa only [show 13+(w.val-13)=w.val by omega] using d)
      exact (pin_data pin).2.symm
    · by_cases q : u.val=0 ∧ 1  ≤  w.val ∧ w.val  ≤  12
      · simp only [dif_pos q,decide_eq_true_eq] at s
        rw [atSp u (by omega),atSp w q.2.2,q.1,p.getVert_zero]
        have h := (L ⟨w.val-1,by omega⟩).mp s
        change G.Adj a (p.getVert (w.val-1+1)) at h
        rwa [show w.val-1+1=w.val by omega] at h
      · simp only [dif_neg q] at s
        exact False.elim (Bool.false_ne_true s)
    · by_cases q : w.val=12 ∧ u.val<12
      · simp only [dif_pos q,decide_eq_true_eq] at r
        rw [atSp u (by omega),atSp w (by omega),q.1,←len,p.getVert_length]
        exact ((R ⟨u.val,q.2⟩).mp r).symm
      · simp only [dif_neg q] at r
        exact False.elim (Bool.false_ne_true r)
  have fw (u w : Fin 17) (h : edge t i j k l m u w=true) : G.Adj (φ u) (φ w) := by
    simp only [edge,Bool.or_eq_true] at h
    exact h.elim (fwDir _ _) (fun e=>(fwDir _ _ e).symm)
  have revL (u : Fin 17) (e : G.Adj (φ 0) (φ u)) : edge t i j k l m 0 u=true := by
    have up : u.val  ≤  12 := by
      by_cases c : u.val  ≤  12
      · exact c
      exact ((no_endpoints hp.1 (om u (by omega))).1 ((A0 ▸ e).symm)).elim
    have low : 1  ≤  u.val := by
      by_cases c : 1  ≤  u.val
      · exact c
      have eq : u=0 := Fin.ext (by omega)
      exact (G.loopless _ (eq ▸ e)).elim
    have z : (0:Fin 17).val=0 ∧ 1  ≤  u.val ∧ u.val  ≤  12 := ⟨rfl,low,up⟩
    have h : m ⟨u.val-1,by omega⟩=1 := (L _).mpr (by
      change G.Adj a (p.getVert (u.val-1+1))
      rw [show u.val-1+1=u.val by omega,←atSp u up,←A0]
      exact e)
    simp only [edge,Bool.or_eq_true]
    left
    simp [dir,z,h]
  have revR (u : Fin 17) (e : G.Adj (φ 12) (φ u)) : edge t i j k l m 12 u=true := by
    have up : u.val  ≤  12 := by
      by_cases c : u.val  ≤  12
      · exact c
      exact ((no_endpoints hp.1 (om u (by omega))).2 ((B12 ▸ e).symm)).elim
    have low : u.val<12 := by
      by_cases c : u.val<12
      · exact c
      have eq : u=12 := Fin.ext (by change u.val=12; omega)
      exact (G.loopless _ (eq ▸ e)).elim
    have z : (12:Fin 17).val=12 ∧ u.val<12 := ⟨rfl,low⟩
    have h : m ⟨u.val,low⟩=2 := (R _).mpr (by rw [←atSp u up,←B12]; exact e)
    simp only [edge,Bool.or_eq_true]
    right
    simp [dir,z,h]
  have cap := fun u=>distanceTwo_le_of_even 4 u (even u)
  have dl : (two t i j k l m 0).card  ≤  4 := offFour17_endpoint_d2 hc φ inj _ 0 fw revL (cap _)
  have dr : (two t i j k l m 12).card  ≤  4 := offFour17_endpoint_d2 hc φ inj _ 12 fw revR (cap _)
  obtain ⟨S,ll,nd,chain⟩ := row_sound rowProof extraProof m0 m11 v sd ml mr dl dr
  let L := S.map φ
  have n : L.Nodup := nd.map inj
  have lenL : L.length=14 := by simp [L,ll]
  have c : List.Chain' G.Adj L := List.chain'_map_of_chain' φ fw chain
  cases e : L with
  | nil => simp [e] at lenL
  | cons w R =>
    obtain ⟨r,q,eq⟩ := offSix_walk_of_chain w R (e ▸ c)
    have qp : q.IsPath := IsPath.mk' (eq.symm ▸ (e ▸ n))
    have d := hp.1.2 _ _ q qp
    have e' := congrArg List.length eq
    rw [length_support,←e,lenL] at e'
    omega

#print axioms four_omissions_row_contradiction
end Graffiti189LongestPath.TwoCut
