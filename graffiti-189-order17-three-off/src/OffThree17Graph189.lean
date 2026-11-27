import OffThree17LongerBase189
import OrderSixteenFoundation189
import FourOffGraphCore189

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack OffThree17Longer
open private LeftMarks RightMarks card_leftMarks card_rightMarks mark_holes_of_pin_and_missing_endpoint
  pin_two_contacts_end three_off_labeled_clique three_off_same_ports from OrderSixteenFoundation189
open private pin_pos pin_data no_endpoints dist_two mem_distanceTwo reverse_pin reverse_long same_support_optimal from SmallOrderFour189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false


private theorem edge_zero_mono (i j : ℕ) (m : Marks) (u v : Vertex)
    (h : edge i j (fun _=>0) u v=true) : edge i j m u v=true := by
  have d (u v : Vertex) (h : dir i j (fun _=>0) u v=true) : dir i j m u v=true := by
    have l : (if q : u.val=0 ∧ 1≤v.val ∧ v.val≤13 then decide ((0:Fin 3)=1) else false)=false := by
      split <;> decide
    have r : (if q : v.val=13 ∧ u.val<13 then decide ((0:Fin 3)=2) else false)=false := by
      split <;> decide
    simp only [dir,l,r,Bool.or_false] at h
    simp only [dir,Bool.or_eq_true] at h ⊢
    exact .inl (.inl h)
  simp only [edge,Bool.or_eq_true] at h ⊢
  exact h.imp (d _ _) (d _ _)

private theorem boundary_longer (j : ℕ) (lo : 4≤j) (hi : j≤12) (m : Marks) :
    ∃ l,Chain 1 j m l := by
  suffices h : ∃ l,Chain 1 j (fun _=>0) l by
    obtain ⟨l,a,b,c⟩ := h
    exact ⟨l,a,b,c.imp (fun u v e=>edge_zero_mono _ _ m u v e)⟩
  have q : j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 := by omega
  rcases q with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨[3,2,1,14,15,4,5,6,7,8,9,10,11,12,13],by decide +kernel⟩
  · exact ⟨[4,3,2,1,14,15,5,6,7,8,9,10,11,12,13],by decide +kernel⟩
  · exact ⟨[5,4,3,2,1,14,15,6,7,8,9,10,11,12,13],by decide +kernel⟩
  · exact ⟨[6,5,4,3,2,1,14,15,7,8,9,10,11,12,13],by decide +kernel⟩
  · exact ⟨[7,6,5,4,3,2,1,14,15,8,9,10,11,12,13],by decide +kernel⟩
  · exact ⟨[8,7,6,5,4,3,2,1,14,15,9,10,11,12,13],by decide +kernel⟩
  · exact ⟨[9,8,7,6,5,4,3,2,1,14,15,10,11,12,13],by decide +kernel⟩
  · exact ⟨[10,9,8,7,6,5,4,3,2,1,14,15,11,12,13],by decide +kernel⟩
  · exact ⟨[11,10,9,8,7,6,5,4,3,2,1,14,15,12,13],by decide +kernel⟩

private theorem walk_of_nonempty_chain (a : V) (L : List V)
    (adj : List.Chain' G.Adj (a::L)) :
    ∃ b,∃ p : G.Walk a b,p.support=a::L := by
  induction L generalizing a with
  | nil => exact ⟨a,.nil,rfl⟩
  | cons b L ih =>
    obtain ⟨c,p,eq⟩ := ih b adj.tail
    exact ⟨c,.cons adj.rel_head p,by simp [eq]⟩



private theorem order17_model_d2 (hc : G.Connected)
    (φ : Fin 17 → V) (inj : Function.Injective φ)
    (E : Fin 17 → Fin 17 → Bool) (z : Fin 17)
    (forw : ∀ u v,E u v=true → G.Adj (φ u) (φ v))
    (rev : ∀ u,G.Adj (φ z) (φ u) → E z u=true)
    (cap : (DistanceTwo G (φ z)).card≤4) :
    (univ.filter fun y => y≠z ∧ !E z y = true ∧
      ∃ u : Fin 17,E z u=true ∧ E u y=true).card≤4 := by
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



private theorem length_thirteen_three_off_interior_marks
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=13)
    (xo : x∉p.support) {i j : ℕ}
    (hi : i∈Pins p x) (hj : j∈Pins p x) (gap : i+3≤j) :
    ∃ m : Marks, m 0=1 ∧ m 12=2 ∧
      (1<i → j≤11 → ∀ k : Fin 13,Hole i j k.val → m k=0) ∧
      4≤markCount m 1 ∧ 4≤markCount m 2 ∧
      (∀ k : Fin 13,m k=1 ↔ G.Adj a (p.getVert (k.val+1))) ∧
      (∀ k : Fin 13,m k=2 ↔ G.Adj b (p.getVert k.val))  := by
  classical
  have e : ∀ k<p.length, ¬(G.Adj a (p.getVert (k+1)) ∧ G.Adj b (p.getVert k)) := by
    intro k kr h
    exact not_adj_both_end_marks hp.1 xo (p.getVert_mem_support i) (pin_data hi).2 kr h.1 h.2
  let m : Marks := fun k => if G.Adj a (p.getVert (k.val+1)) then 1
    else if G.Adj b (p.getVert k.val) then 2 else 0
  have l (k : Fin 13) : m k=1 ↔ G.Adj a (p.getVert (k.val+1)) := by
    by_cases h : G.Adj a (p.getVert (k.val+1))
    · simp [m,h]
    · by_cases r : G.Adj b (p.getVert k.val) <;> simp [m,h,r]
  have r (k : Fin 13) : m k=2 ↔ G.Adj b (p.getVert k.val) := by
    have kb := k.isLt
    by_cases h : G.Adj a (p.getVert (k.val+1))
    · have no : ¬G.Adj b (p.getVert k.val) := fun n => e _ (by omega) ⟨h,n⟩
      simp [m,h,no]
    · by_cases s : G.Adj b (p.getVert k.val) <;> simp [m,h,s]
  have zero (k : Fin 13) : m k=0 ↔ k.val∉LeftMarks p∪RightMarks p := by
    have kr : k.val<p.length := by have ee := k.isLt; omega
    have km : k.val∈range p.length := mem_range.mpr kr
    by_cases al : G.Adj a (p.getVert (k.val+1)) <;>
      by_cases br : G.Adj b (p.getVert k.val) <;> simp [m,al,br,LeftMarks,RightMarks,km]
  have m0 : m 0=1 := (l 0).mpr (by simpa using p.adj_getVert_succ (i:=0) (by omega))
  have m12 : m 12=2 := (r 12).mpr (by
    have rr := (p.adj_getVert_succ (i:=12) (by omega)).symm
    rw [show 12+1=p.length by omega,p.getVert_length] at rr
    exact rr)
  refine ⟨m,m0,m12,?_,?_,?_,l,r⟩
  · intro lo up k hk
    unfold Hole at hk
    have dcap := fun x => distanceTwo_le_of_even 4 x (even x)
    have f := (at_most_two_pins_one_slack hc 2 (by decide) dcap conn degree hp xo).1
    obtain ⟨ll,rr⟩ := pin_two_contacts_end hp.1 hc xo f (dcap x) hi hj gap
    have missI := mark_holes_of_pin_and_missing_endpoint hp.1 xo hi
    have missJ := mark_holes_of_pin_and_missing_endpoint hp.1 xo hj
    apply (zero k).mpr
    rcases hk.2.2 with e|e|e|e
    · rw [e]
      exact missI.1 (fun h => (by omega : i≠1) (ll i hi h))
    · rw [e]
      exact missI.2 (fun h => (by omega : j+1≠p.length) (rr i hi h))
    · rw [e]
      exact missJ.1 (fun h => (by omega : i≠1) (ll j hj h))
    · rw [e]
      exact missJ.2 (fun h => (by omega : j+1≠p.length) (rr j hj h))
  · unfold markCount
    let N := univ.filter (fun k : Fin 13 => m k=1)
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
    change 4≤N.card
    rwa [←ce,eq,card_leftMarks hp.1]
  · unfold markCount
    let N := univ.filter (fun k : Fin 13 => m k=2)
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
    change 4≤N.card
    rwa [←ce,eq,card_rightMarks hp.1]

private theorem length_thirteen_three_off_oriented
    (table : ∀ (i j : ℕ), 1<i → i+3≤j → i+j≤13 → j≤11 → row i j=true)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=13) (off : ((univ : Finset V)\p.support.toFinset).card=3)
    (xo : x∉p.support) {i j : ℕ} (lo : 1≤i) (gap : i+3≤j) (orient : i+j≤13) (up : j≤12)
    (xi : i∈Pins p x) (xj : j∈Pins p x)
    (commonHigh : ∀ y∉p.support,4≤G.degree y → Pins p y={i,j})
    (clique : ∀ y∉p.support,∀ z∉p.support,y≠z → G.Adj z y) :
    False := by
  classical
  obtain ⟨y,z,yo,zo,xy,xz,yz,yd,_⟩ := three_off_labeled_clique degree xo off
  have yi : i∈Pins p y := by rw [commonHigh y yo yd]; simp
  have yj : j∈Pins p y := by rw [commonHigh y yo yd]; simp
  obtain ⟨m,m0,m12,holes,ml,mr,L,R⟩ := length_thirteen_three_off_interior_marks
    hc even conn degree hp ah bh len xo xi xj gap
  let φ (k : Fin 17) : V := if k.val=14 then x else if k.val=15 then y else
    if k.val=16 then z else p.getVert k.val
  have value {k : Fin 17} (h : k.val≤13) : φ k=p.getVert k.val := by
    simp [φ,show k.val≠14 by omega,show k.val≠15 by omega,show k.val≠16 by omega]
  have classify (k : Fin 17) : k.val≤13 ∨ k=14 ∨ k=15 ∨ k=16 := by
    by_cases h11 : k.val=14
    · exact .inr (.inl (Fin.ext h11))
    by_cases h12 : k.val=15
    · exact .inr (.inr (.inl (Fin.ext h12)))
    by_cases h13 : k.val=16
    · exact .inr (.inr (.inr (Fin.ext h13)))
    exact .inl (by omega)
  have val14 : φ 14=x := rfl
  have val15 : φ 15=y := rfl
  have val16 : φ 16=z := rfl
  have conflict {r : V} {k : ℕ} (ro : r∉p.support) (e : p.getVert k=r) : False :=
    ro (e ▸ p.getVert_mem_support k)
  have lab_inj : Function.Injective φ := by
    intro k l eq
    rcases classify k with kh|kh|kh|kh <;> rcases classify l with lh|lh|lh|lh
    · exact Fin.ext (hp.1.1.getVert_injOn (show k.val≤p.length by omega)
        (show l.val≤p.length by omega) ((value kh).symm.trans (eq.trans (value lh))))
    all_goals try subst k
    all_goals try subst l
    all_goals try rfl
    all_goals try rw [value kh] at eq
    all_goals try rw [value lh] at eq
    all_goals simp only [val14,val15,val16] at eq
    all_goals exfalso
    all_goals first | contradiction | exact xy eq.symm | exact xz eq.symm | exact yz eq.symm | exact conflict xo eq | exact conflict xo eq.symm | exact conflict yo eq | exact conflict yo eq.symm | exact conflict zo eq | exact conflict zo eq.symm

  have a0 : φ 0=a := by rw [value (show (0:Fin 17).val≤13 by decide)]; exact p.getVert_zero
  have b13 : φ 13=b := by rw [value (show (13:Fin 17).val≤13 by decide)]; simpa only [len] using p.getVert_length
  have pld {k : Fin 17} (kh : 14≤k.val) : φ k∉p.support := by
    rcases classify k with n|rfl|rfl|rfl
    · omega
    · exact xo
    · exact yo
    · exact zo
  have direction (u v : Fin 17) (h : dir i j m u v=true) : G.Adj (φ u) (φ v) := by
    simp only [dir,Bool.or_eq_true,decide_eq_true_eq] at h
    rcases h with ((((ha|hb)|hc)|he)|hf)
    · rw [value (show u.val≤13 by omega),value ha.2,ha.1]
      exact p.adj_getVert_succ (by omega)
    · exact clique _ (pld (by omega : 14≤v.val)) _ (pld hb.1)
        (fun e => by have q := congrArg Fin.val (lab_inj e); omega)
    · have ur : u.val≤13 := by rcases hc.1 with e|e <;> omega
      rcases hc.2 with vx|vy
      · have eq : v=14 := Fin.ext vx
        rw [value ur,eq,val14]
        exact (hc.1.elim (fun e => e.symm ▸ (pin_data xi).2)
          (fun e => e.symm ▸ (pin_data xj).2)).symm
      · have eq : v=15 := Fin.ext vy
        rw [value ur,eq,val15]
        exact (hc.1.elim (fun e => e.symm ▸ (pin_data yi).2)
          (fun e => e.symm ▸ (pin_data yj).2)).symm
    · by_cases q : u.val=0 ∧ 1≤v.val ∧ v.val≤13
      · simp only [dif_pos q,decide_eq_true_eq] at he
        rw [value (show u.val≤13 by omega),value q.2.2,q.1,p.getVert_zero]
        have h := (L ⟨v.val-1,by omega⟩).mp he
        change G.Adj a (p.getVert (v.val-1+1)) at h
        rwa [show v.val-1+1=v.val by omega] at h
      · simp only [dif_neg q] at he
        contradiction
    · by_cases q : v.val=13 ∧ u.val<13
      · simp only [dif_pos q,decide_eq_true_eq] at hf
        rw [value (show u.val≤13 by omega),value (show v.val≤13 by omega),q.1,←len,p.getVert_length]
        exact ((R ⟨u.val,q.2⟩).mp hf).symm
      · simp only [dif_neg q] at hf
        contradiction
  have edgeOK (u v : Fin 17) (h : edge i j m u v=true) : G.Adj (φ u) (φ v) := by
    simp only [edge,Bool.or_eq_true] at h
    exact h.elim (direction _ _) (fun e => (direction _ _ e).symm)
  have leftE (u : Fin 17) (uA : G.Adj (φ 0) (φ u)) : edge i j m 0 u=true := by
    have onP : u.val≤13 := by
      by_contra no
      exact (no_endpoints hp.1 (pld (show 14≤u.val by omega))).1 ((a0 ▸ uA).symm)
    have up : 1≤u.val := by
      by_contra no
      have u0 : u=0 := Fin.ext (show u.val=0 by omega)
      exact G.loopless _ (u0 ▸ uA)
    have q : (0:Fin 17).val=0 ∧ 1≤u.val ∧ u.val≤13 := ⟨rfl,up,onP⟩
    have ia : G.Adj a (p.getVert ((u.val-1)+1)) := by
      rw [show u.val-1+1=u.val by omega,←value onP,←a0]
      exact uA
    have h : m ⟨u.val-1,by omega⟩=1 := (L _).mpr ia
    simp only [edge,Bool.or_eq_true]
    left
    simp [dir,q,h]
  have rightE (u : Fin 17) (uB : G.Adj (φ 13) (φ u)) : edge i j m 13 u=true := by
    have onP : u.val≤13 := by
      by_contra no
      exact (no_endpoints hp.1 (pld (show 14≤u.val by omega))).2 ((b13 ▸ uB).symm)
    have up : u.val<13 := by
      by_contra no
      have u12 : u=13 := Fin.ext (show u.val=(13:Fin 17).val by change u.val=13; omega)
      exact G.loopless _ (u12 ▸ uB)
    have q : (13:Fin 17).val=13 ∧ u.val<13 := ⟨rfl,up⟩
    have ib : G.Adj b (p.getVert u.val) := by
      rw [←value onP,←b13]
      exact uB
    have h : m ⟨u.val,up⟩=2 := (R _).mpr ib
    simp only [edge,Bool.or_eq_true]
    right
    simp [dir,q,h]
  have cap := fun u => distanceTwo_le_of_even 4 u (even u)
  have E0 : (d2Set i j m 0).card≤4 := order17_model_d2 hc φ lab_inj _ 0 edgeOK leftE (cap _)
  have E13 : (d2Set i j m 13).card≤4 := order17_model_d2 hc φ lab_inj _ 13 edgeOK rightE (cap _)
  obtain ⟨l,ll,nd,chain⟩ : ∃ l,Chain i j m l := by
    by_cases one : i=1
    · subst i
      exact boundary_longer j (by omega) up m
    have ilo : 1<i := by omega
    have jup : j≤11 := by omega
    exact row_sound (table i j ilo gap orient jup) m0 m12 (holes ilo jup) ml mr E0 E13
  let R := l.map φ
  have rn : R.Nodup := nd.map lab_inj
  have rc : List.Chain' G.Adj R := List.chain'_map_of_chain' φ edgeOK chain
  have ln : R.length=15 := by simp [R,ll]
  cases e : R with
  | nil => simp [e] at ln
  | cons v t =>
    obtain ⟨w,q,eq⟩ := walk_of_nonempty_chain v t (e ▸ rc)
    have qp : q.IsPath := IsPath.mk' (eq.symm ▸ (e ▸ rn))
    have short := hp.1.2 _ _ q qp
    have leq := congrArg List.length eq
    rw [length_support,←e,ln] at leq
    omega

#print axioms length_thirteen_three_off_oriented

theorem no_length_thirteen_with_three_off_at_degree_four_table
    (table : ∀ (i j : ℕ), 1<i → i+3≤j → i+j≤13 → j≤11 → OffThree17Longer.row i j=true)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=13) (off : ((univ : Finset V)\p.support.toFinset).card=3) :
    False := by
  classical
  obtain ⟨x,i,j,xo,xh,xi,xj,gap,C,_,H⟩ := three_off_same_ports hc even conn degree hp ah bh off
  have i1 := pin_pos hp.1 xo xi
  have j13 := (pin_data xj).1
  have close {a' b' : V} {q : G.Walk a' b'} (h : EdgeOptimal q)
      (l : 4≤G.degree a') (r : 4≤G.degree b') (n : q.length=13)
      (o : ((univ : Finset V)\q.support.toFinset).card=3)
      (xo : x∉q.support) {i j : ℕ} (il : 1≤i) (gg : i+3≤j) (fl : i+j≤13)
      (jx : j∈Pins q x) (ix : i∈Pins q x)
      (H : ∀ y∉q.support,4≤G.degree y → Pins q y={i,j})
      (C : ∀ y∉q.support,∀ z∉q.support,y≠z → G.Adj y z) : False := by
    have up := (pin_data jx).1
    exact length_thirteen_three_off_oriented table hc even conn degree h l r n o xo
      il gg fl (by omega) ix jx H (fun y yo z zo hyz => (C y yo z zo hyz).symm)
  by_cases orient : i+j≤13
  · exact close hp ah bh len off xo i1 gap orient xj xi H C
  have ep : EdgeOptimal p.reverse := same_support_optimal hp (reverse_long hp.1) (by intro z; simp)
  have off' : ((univ : Finset V)\p.reverse.support.toFinset).card=3 := by
    simpa [support_reverse] using off
  have xp1 : 13-j∈Pins p.reverse x := by simpa [len] using reverse_pin hp.1 xo xj
  have xp2 : 13-i∈Pins p.reverse x := by simpa [len] using reverse_pin hp.1 xo xi
  have H' (y : V) (yo : y∉p.reverse.support) (yh : 4≤G.degree y) :
      Pins p.reverse y=({13-j,13-i}:Finset ℕ) := by
    have yp : y∉p.support := by simpa using yo
    have ypi : i∈Pins p y := by rw [H y yp yh]; simp
    have ypj : j∈Pins p y := by rw [H y yp yh]; simp
    have a : 13-j∈Pins p.reverse y := by simpa [len] using reverse_pin hp.1 yp ypj
    have b : 13-i∈Pins p.reverse y := by simpa [len] using reverse_pin hp.1 yp ypi
    have s : ({13-j,13-i}:Finset ℕ)⊆Pins p.reverse y := by
      intro z az
      rcases mem_insert.mp az with he|he
      · exact he.symm ▸ a
      · exact (mem_singleton.mp he).symm ▸ b
    have few := (at_most_two_pins_one_slack hc 2 (by decide)
      (fun z => distanceTwo_le_of_even 4 z (even z)) conn degree ep yo).1
    have card2 : ({13-j,13-i}:Finset ℕ).card=2 := by
      have ne : 13-j∉({13-i}:Finset ℕ) := by
        simp only [mem_singleton]
        omega
      rw [card_insert_of_not_mem ne,card_singleton]
    exact (eq_of_subset_of_card_le s (by rwa [card2])).symm
  exact close ep bh ah (by simpa using len) off' (by simpa using xo) (by omega) (by omega) (by omega)
    xp2 xp1 H' (by simpa only [support_reverse,List.mem_reverse] using C)

#print axioms no_length_thirteen_with_three_off_at_degree_four_table

end Graffiti189LongestPath.TwoCut
