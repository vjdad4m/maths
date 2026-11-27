import OffFive17CentralTransfers189
import OffFive17SingletonBase189

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack OffFive17Singleton
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
open private pin_data pin_pos no_endpoints dist_two mem_distanceTwo reverse_pin reverse_long
   same_support_optimal LeftMarks RightMarks card_leftMarks card_rightMarks from SmallOrderFour189

private theorem offFive17_endpoint_d2 (hc : G.Connected)
    (φ : Fin 15 → V) (inj : Function.Injective φ)
    (E : Fin 15 → Fin 15 → Bool) (z : Fin 15)
    (forw : ∀ u v,E u v=true → G.Adj (φ u) (φ v))
    (rev : ∀ u,G.Adj (φ z) (φ u) → E z u=true)
    (cap : (DistanceTwo G (φ z)).card≤4) :
    (univ.filter fun y => y≠z ∧ !E z y = true ∧
      ∃ u : Fin 15,E z u=true ∧ E u y=true).card≤4 := by
  classical
  let Q := univ.filter fun y => y≠z ∧ !E z y = true ∧
      ∃ u : Fin 15,E z u=true ∧ E u y=true
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





private theorem off_five_17_singleton_marks
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4 ≤ G.degree a) (bh : 4 ≤ G.degree b) (len : p.length=11)
    (xo : x∉p.support)
    (hi : 1∈Pins p x) :
    ∃ m : Mark, m 0=1 ∧ m 10=2 ∧
      4 ≤ count m 1 ∧ 4 ≤ count m 2 ∧
      (∀ k : Fin 11,m k=1 ↔ G.Adj a (p.getVert (k.val+1))) ∧
      (∀ k : Fin 11,m k=2 ↔ G.Adj b (p.getVert k.val))  := by
  classical
  have e : ∀ k<p.length, ¬(G.Adj a (p.getVert (k+1)) ∧ G.Adj b (p.getVert k)) := by
    intro k kr h
    exact not_adj_both_end_marks hp.1 xo (p.getVert_mem_support 1) (pin_data hi).2 kr h.1 h.2
  let m : Mark := fun k => if G.Adj a (p.getVert (k.val+1)) then 1
    else if G.Adj b (p.getVert k.val) then 2 else 0
  have l (k : Fin 11) : m k=1 ↔ G.Adj a (p.getVert (k.val+1)) := by
    by_cases h : G.Adj a (p.getVert (k.val+1))
    · simp [m,h]
    · by_cases r : G.Adj b (p.getVert k.val) <;> simp [m,h,r]
  have r (k : Fin 11) : m k=2 ↔ G.Adj b (p.getVert k.val) := by
    have kb := k.isLt
    by_cases h : G.Adj a (p.getVert (k.val+1))
    · have no : ¬G.Adj b (p.getVert k.val) := fun n => e _ (by omega) ⟨h,n⟩
      simp [m,h,no]
    · by_cases s : G.Adj b (p.getVert k.val) <;> simp [m,h,s]
  have m0 : m 0=1 := (l 0).mpr (by simpa using p.adj_getVert_succ (i:=0) (by omega))
  have m10 : m 10=2 := (r 10).mpr (by
    have rr := (p.adj_getVert_succ (i:=10) (by omega)).symm
    rw [show 10+1=p.length by omega,p.getVert_length] at rr
    exact rr)
  refine ⟨m,m0,m10,?_,?_,l,r⟩
  · unfold count
    let N := univ.filter (fun k : Fin 11 => m k=1)
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
    change 4 ≤ N.card
    rwa [←ce,eq,card_leftMarks hp.1]
  · unfold count
    let N := univ.filter (fun k : Fin 11 => m k=2)
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
    change 4 ≤ N.card
    rwa [←ce,eq,card_rightMarks hp.1]


private theorem off_five_17_singleton_oriented
    (table : ∀ j : ℕ,4  ≤  j → j  ≤  10 → j≠4 → j≠7 → row j=true)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card  ≤  5)
    {a b x y z : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4  ≤  G.degree a) (bh : 4  ≤  G.degree b)
    (len : p.length=11) (xo : x∉p.support) (yo : y∉p.support) (zo : z∉p.support)
    (xy : x≠y) (xz : x≠z) (yz : y≠z)
    {j : ℕ} (xi : 1∈Pins p x) (xj : j∈Pins p x) (lo : 4  ≤  j) (j4 : j≠4) (j7 : j≠7)
    (y4 : 4∈Pins p y) (z7 : 7∈Pins p z) : False := by
  classical
  obtain ⟨m,m0,m10,ml,mr,L,R⟩ := off_five_17_singleton_marks hp ah bh len xo xi
  have jup := (pin_data xj).1
  have valid (k : Fin 11) : validMark j k.val (m k) := by
    constructor
    · intro h km
      have a := (L k).mp h
      rcases km with hh|hh|hh|hh
      · exact start_not_adj_pin_successor hp.1 xo xi (hh ▸ a)
      · exact start_not_adj_pin_successor hp.1 xo xj (hh ▸ a)
      · exact start_not_adj_pin_successor hp.1 yo y4 (hh ▸ a)
      · exact start_not_adj_pin_successor hp.1 zo z7 (hh ▸ a)
    · intro h km
      have b := (R k).mp h
      rcases km with hh|hh|hh|hh
      · exact end_not_adj_pin_predecessor hp.1 xo xi (by simpa only [show 1-1=k.val by omega] using b)
      · exact end_not_adj_pin_predecessor hp.1 xo xj (by simpa only [show j-1=k.val by omega] using b)
      · exact end_not_adj_pin_predecessor hp.1 yo y4 (by simpa only [show 4-1=k.val by omega] using b)
      · exact end_not_adj_pin_predecessor hp.1 zo z7 (by simpa only [show 7-1=k.val by omega] using b)
  let φ (k : Fin 15) : V := if k.val=12 then x else if k.val=13 then y else
    if k.val=14 then z else p.getVert k.val
  have value {k : Fin 15} (h : k.val ≤ 11) : φ k=p.getVert k.val := by
    simp [φ,show k.val≠12 by omega,show k.val≠13 by omega,show k.val≠14 by omega]
  have classify (k : Fin 15) : k.val ≤ 11 ∨ k=12 ∨ k=13 ∨ k=14 := by
    by_cases h11 : k.val=12
    · exact .inr (.inl (Fin.ext h11))
    by_cases h12 : k.val=13
    · exact .inr (.inr (.inl (Fin.ext h12)))
    by_cases h13 : k.val=14
    · exact .inr (.inr (.inr (Fin.ext h13)))
    exact .inl (by omega)
  have val12 : φ 12=x := rfl
  have val13 : φ 13=y := rfl
  have val14 : φ 14=z := rfl
  have conflict {r : V} {k : ℕ} (ro : r∉p.support) (e : p.getVert k=r) : False :=
    ro (e ▸ p.getVert_mem_support k)
  have lab_inj : Function.Injective φ := by
    intro k l eq
    rcases classify k with kh|rfl|rfl|rfl <;> rcases classify l with lh|rfl|rfl|rfl
    · exact Fin.ext (hp.1.1.getVert_injOn (show k.val ≤ p.length by omega)
        (show l.val ≤ p.length by omega) ((value kh).symm.trans (eq.trans (value lh))))
    · exact (conflict xo ((value kh).symm.trans (eq.trans val12))).elim
    · exact (conflict yo ((value kh).symm.trans (eq.trans val13))).elim
    · exact (conflict zo ((value kh).symm.trans (eq.trans val14))).elim
    · exact (conflict xo ((value lh).symm.trans (eq.symm.trans val12))).elim
    · rfl
    · exact (xy (val12.symm.trans (eq.trans val13))).elim
    · exact (xz (val12.symm.trans (eq.trans val14))).elim
    · exact (conflict yo ((value lh).symm.trans (eq.symm.trans val13))).elim
    · exact (xy (val12.symm.trans (eq.symm.trans val13))).elim
    · rfl
    · exact (yz (val13.symm.trans (eq.trans val14))).elim
    · exact (conflict zo ((value lh).symm.trans (eq.symm.trans val14))).elim
    · exact (xz (val12.symm.trans (eq.symm.trans val14))).elim
    · exact (yz (val13.symm.trans (eq.symm.trans val14))).elim
    · rfl

  have a0 : φ 0=a := by rw [value (show (0:Fin 15).val ≤ 11 by decide)]; exact p.getVert_zero
  have b11 : φ 11=b := by rw [value (show (11:Fin 15).val ≤ 11 by decide)]; simpa only [len] using p.getVert_length
  have pld {k : Fin 15} (kh : 12 ≤ k.val) : φ k∉p.support := by
    rcases classify k with n|rfl|rfl|rfl
    · omega
    · exact xo
    · exact yo
    · exact zo
  have direction (u v : Fin 15) (h : dir j m u v=true) : G.Adj (φ u) (φ v) := by
    simp only [dir,Bool.or_eq_true,decide_eq_true_eq] at h
    rcases h with (((ha|hb)|he)|hf)
    · rw [value (show u.val  ≤  11 by omega),value ha.2,ha.1]
      exact p.adj_getVert_succ (by omega)
    · rcases hb with ⟨up,vx⟩|⟨u4,vy⟩|⟨u7,vz⟩
      · have ur : u.val  ≤  11 := by rcases up with e|e <;> omega
        rw [value ur,show v=12 from Fin.ext vx,val12]
        exact (up.elim (fun e => e.symm ▸ (pin_data xi).2)
          (fun e => e.symm ▸ (pin_data xj).2)).symm
      · rw [value (by omega),show v=13 from Fin.ext vy,val13,u4]
        exact (pin_data y4).2.symm
      · rw [value (by omega),show v=14 from Fin.ext vz,val14,u7]
        exact (pin_data z7).2.symm
    · by_cases q : u.val=0 ∧ 1 ≤ v.val ∧ v.val ≤ 11
      · simp only [dif_pos q,decide_eq_true_eq] at he
        rw [value (show u.val ≤ 11 by omega),value q.2.2,q.1,p.getVert_zero]
        have h := (L ⟨v.val-1,by omega⟩).mp he
        change G.Adj a (p.getVert (v.val-1+1)) at h
        rwa [show v.val-1+1=v.val by omega] at h
      · simp only [dif_neg q] at he
        exact False.elim (Bool.false_ne_true he)
    · by_cases q : v.val=11 ∧ u.val<11
      · simp only [dif_pos q,decide_eq_true_eq] at hf
        rw [value (show u.val ≤ 11 by omega),value (show v.val ≤ 11 by omega),q.1,←len,p.getVert_length]
        exact ((R ⟨u.val,q.2⟩).mp hf).symm
      · simp only [dif_neg q] at hf
        exact False.elim (Bool.false_ne_true hf)
  have edgeOK (u v : Fin 15) (h : edge j m u v=true) : G.Adj (φ u) (φ v) := by
    simp only [edge,Bool.or_eq_true] at h
    exact h.elim (direction _ _) (fun e => (direction _ _ e).symm)
  have leftE (u : Fin 15) (uA : G.Adj (φ 0) (φ u)) : edge j m 0 u=true := by
    have onP : u.val ≤ 11 := by
      by_contra no
      exact (no_endpoints hp.1 (pld (show 12 ≤ u.val by omega))).1 ((a0 ▸ uA).symm)
    have up : 1 ≤ u.val := by
      by_cases e : 1 ≤ u.val
      · exact e
      exfalso
      have u0 : u=0 := Fin.ext (show u.val=0 by omega)
      exact G.loopless _ (u0 ▸ uA)
    have q : (0:Fin 15).val=0 ∧ 1 ≤ u.val ∧ u.val ≤ 11 := ⟨rfl,up,onP⟩
    have ia : G.Adj a (p.getVert ((u.val-1)+1)) := by
      rw [show u.val-1+1=u.val by omega,←value onP,←a0]
      exact uA
    have h : m ⟨u.val-1,by omega⟩=1 := (L _).mpr ia
    simp only [edge,Bool.or_eq_true]
    left
    simp [dir,q,h]
  have rightE (u : Fin 15) (uB : G.Adj (φ 11) (φ u)) : edge j m 11 u=true := by
    have onP : u.val ≤ 11 := by
      by_contra no
      exact (no_endpoints hp.1 (pld (show 12 ≤ u.val by omega))).2 ((b11 ▸ uB).symm)
    have up : u.val<11 := by
      by_cases e : u.val<11
      · exact e
      exfalso
      have u11 : u=11 := Fin.ext (show u.val=(11:Fin 15).val by change u.val=11; omega)
      exact G.loopless _ (u11 ▸ uB)
    have q : (11:Fin 15).val=11 ∧ u.val<11 := ⟨rfl,up⟩
    have ib : G.Adj b (p.getVert u.val) := by
      rw [←value onP,←b11]
      exact uB
    have h : m ⟨u.val,up⟩=2 := (R _).mpr ib
    simp only [edge,Bool.or_eq_true]
    right
    simp [dir,q,h]
  have cap := fun u => distanceTwo_le_of_even 4 u (even u)
  have E0 : (two j m 0).card ≤ 4 := offFive17_endpoint_d2 hc φ lab_inj _ 0 edgeOK leftE (cap _)
  have E11 : (two j m 11).card ≤ 4 := offFive17_endpoint_d2 hc φ lab_inj _ 11 edgeOK rightE (cap _)
  exact row_sound (table j lo (by omega) j4 j7) m0 m10 valid ml mr E0 E11

#print axioms off_five_17_singleton_oriented

theorem no_length_eleven_with_central_four_component_of_endpoint_table
    (table : ∀ j : ℕ,4 ≤ j → j ≤ 10 → j≠4 → j≠7 → row j=true)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card ≤ 5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4 ≤ G.degree a) (bh : 4 ≤ G.degree b)
    (len : p.length=11) (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (H : OmittedComponent p) (h4 : H.vertices.card=4)
    (one : ∀ z∈H.vertices,(Pins p z).card ≤ 1)
    (left : ∃ y∈H.vertices,4∈Pins p y) (right : ∃ z∈H.vertices,7∈Pins p z) : False := by
  classical
  obtain ⟨y,yh,y4⟩ := left
  obtain ⟨z,zh,z7⟩ := right
  obtain ⟨x,xo,xh,_,i,j,xi,xj,gap,edge,i4,i7,j4,j7⟩ :=
    length_eleven_five_off_four_component_singleton hc even conn degree hp ah bh len off H h4 yh zh y4 z7
  have yo := H.off _ yh
  have zo := H.off _ zh
  have xy : x≠y := fun e=>xh (e ▸ yh)
  have xz : x≠z := fun e=>xh (e ▸ zh)
  have yz : y≠z := by
    intro e
    subst z
    exact (Nat.not_lt_of_ge (one _ yh)) (one_lt_card.mpr ⟨4,y4,7,z7,by decide⟩)
  rcases edge with rfl|j10
  · exact off_five_17_singleton_oriented table hc even hp ah bh len xo yo zo xy xz yz
      xi xj (by omega) j4 j7 y4 z7
  have rx : 1∈Pins p.reverse x := by simpa only [show p.length-j=1 by omega] using reverse_pin hp.1 xo xj
  have rj : p.length-i∈Pins p.reverse x := reverse_pin hp.1 xo xi
  have ry : 7∈Pins p.reverse y := by simpa only [show p.length-4=7 by omega] using reverse_pin hp.1 yo y4
  have rz : 4∈Pins p.reverse z := by simpa only [show p.length-7=4 by omega] using reverse_pin hp.1 zo z7
  have rbest : EdgeOptimal p.reverse := same_support_optimal hp (reverse_long hp.1) (by intro z; simp)
  exact off_five_17_singleton_oriented table hc even rbest bh ah (by simpa using len)
    (by simpa using xo) (by simpa using zo) (by simpa using yo) xz xy yz.symm
    rx rj (by omega) (by omega) (by omega) rz ry

#print axioms no_length_eleven_with_central_four_component_of_endpoint_table
end Graffiti189LongestPath.TwoCut
