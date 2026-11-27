import OffFiveMixedModel189
import FourOffGraphCore189

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
open private pin_data LeftMarks RightMarks mark_length card_leftMarks card_rightMarks no_endpoints from SmallOrderFour189
open OffFive16DisconnectedMixed in
private theorem off_five_disconnected_mixed_marks
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (xo : x∉p.support) (h1 : 1∈Pins p x)
    (hole1 : 1∉LeftMarks p∪RightMarks p) (hole8 : 8∉LeftMarks p∪RightMarks p) :
    ∃ m : Marks, m 0=1 ∧ m 9=2 ∧
      (∀ k : Fin 10,(k.val=1 ∨ k.val=8) → m k=0) ∧
      (∀ k : Fin 10,(2≤k.val → k.val≤7 → m k≠0)) ∧
      count m 1=4 ∧ count m 2=4 ∧
      (∀ k : Fin 10,m k=1 ↔ G.Adj a (p.getVert (k.val+1))) ∧
      (∀ k : Fin 10,m k=2 ↔ G.Adj b (p.getVert k.val)) := by
  classical
  let T : Finset ℕ := {1,8}
  have tc : T.card=2 := by decide
  have mt {k : ℕ} : k∈T ↔ k=1 ∨ k=8 := by simp [T]
  have ts : T⊆range p.length := by
    intro k km
    have v := mt.mp km
    rcases v with rfl|rfl <;> exact mem_range.mpr (by omega)
  have tv {k : ℕ} (ki : k∈T) : k∉LeftMarks p∪RightMarks p := by
    have e := mt.mp ki
    rcases e with rfl|rfl <;> assumption
  have td : Disjoint (LeftMarks p∪RightMarks p) T :=
    disjoint_left.mpr (fun _ h m => tv m h)
  have degreeSum := mark_length hp xo (p.getVert_mem_support 1) (pin_data h1).2 T ts td
  have exactL : G.degree a=4 := by omega
  have exactR : G.degree b=4 := by omega
  have all {k : ℕ} (kr : k<p.length) (no : k∉T) : k∈LeftMarks p∪RightMarks p := by
    by_contra z
    have dep : Disjoint (LeftMarks p∪RightMarks p) (insert k T) :=
      disjoint_left.mpr (fun w h m => (mem_insert.mp m).elim
        (fun e => z (e ▸ h)) (fun e => tv e h))
    have sub : insert k T⊆range p.length := insert_subset (mem_range.mpr kr) ts
    have bd := mark_length hp xo (p.getVert_mem_support 1) (pin_data h1).2 _ sub dep
    rw [card_insert_of_not_mem no] at bd
    omega
  have e : ∀ k<p.length, ¬(G.Adj a (p.getVert (k+1)) ∧ G.Adj b (p.getVert k)) := by
    intro k kr h
    exact not_adj_both_end_marks hp xo (p.getVert_mem_support 1) (pin_data h1).2 kr h.1 h.2
  let m : Marks := fun k => if G.Adj a (p.getVert (k.val+1)) then 1
    else if G.Adj b (p.getVert k.val) then 2 else 0
  have l (k : Fin 10) : m k=1 ↔ G.Adj a (p.getVert (k.val+1)) := by
    by_cases h : G.Adj a (p.getVert (k.val+1))
    · simp [m,h]
    · by_cases r : G.Adj b (p.getVert k.val) <;> simp [m,h,r]
  have r (k : Fin 10) : m k=2 ↔ G.Adj b (p.getVert k.val) := by
    have kb := k.isLt
    by_cases h : G.Adj a (p.getVert (k.val+1))
    · have no : ¬G.Adj b (p.getVert k.val) := fun n => e _ (by omega) ⟨h,n⟩
      simp [m,h,no]
    · by_cases s : G.Adj b (p.getVert k.val) <;> simp [m,h,s]
  have zero (k : Fin 10) : m k=0 ↔ k.val∉LeftMarks p∪RightMarks p := by
    have kr : k.val<p.length := by have ee := k.isLt; omega
    have km : k.val∈range p.length := mem_range.mpr kr
    by_cases al : G.Adj a (p.getVert (k.val+1)) <;>
      by_cases br : G.Adj b (p.getVert k.val) <;> simp [m,al,br,LeftMarks,RightMarks,km]
  have m0 : m 0=1 := (l 0).mpr (by simpa using p.adj_getVert_succ (i:=0) (by omega))
  have m9 : m 9=2 := (r 9).mpr (by
    have rr := (p.adj_getVert_succ (i:=9) (by omega)).symm
    rw [show 9+1=p.length by omega,p.getVert_length] at rr
    exact rr)
  refine ⟨m,m0,m9,fun k h => (zero k).mpr (tv (mt.mpr h)),?_,?_,?_,l,r⟩
  · intro k kl kr km
    exact (zero k).mp km (all (by have zz := k.isLt; omega) (fun e => by have bad := mt.mp e; omega))
  · unfold count
    let N := univ.filter (fun k : Fin 10 => m k=1)
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
    change N.card=4
    rw [←ce,eq,card_leftMarks hp,exactL]
  · unfold count
    let N := univ.filter (fun k : Fin 10 => m k=2)
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
    change N.card=4
    rw [←ce,eq,card_rightMarks hp,exactR]

#print axioms off_five_disconnected_mixed_marks

open OffFive16DisconnectedMixed in
private theorem off_five_mixed_model_forward
    {a b x y : V} {p : G.Walk a b} (len : p.length=10)
    (ψ : Fin 13→V) (value : ∀ k : Fin 13,k.val≤10 → ψ k=p.getVert k.val)
    (x11 : ψ 11=x) (y12 : ψ 12=y)
    (x1 : 1∈Pins p x) (x8 : 8∈Pins p x) (y2 : 2∈Pins p y) (y9 : 9∈Pins p y)
    (m : Marks)
    (L : ∀ k : Fin 10,m k=1 ↔ G.Adj a (p.getVert (k.val+1)))
    (R : ∀ k : Fin 10,m k=2 ↔ G.Adj b (p.getVert k.val)) :
    ∀ v w,edge m v w=true → G.Adj (ψ v) (ψ w) := by
  have direction (v w : Fin 13) (h : dir m v w=true) : G.Adj (ψ v) (ψ w) := by
    simp only [dir,Bool.or_eq_true,decide_eq_true_eq] at h
    rcases h with ((((ha|⟨hx,h11⟩)|⟨hy,h12⟩)|he)|hf)
    · rw [value v (by omega),value w ha.2,ha.1]
      exact p.adj_getVert_succ (by omega)
    · have w11 : w=11 := Fin.ext h11
      rw [value v (by omega),w11,x11]
      rcases hx with h|h
      · rw [h]; exact (pin_data x1).2.symm
      · rw [h]; exact (pin_data x8).2.symm
    · have w12 : w=12 := Fin.ext h12
      rw [value v (by omega),w12,y12]
      rcases hy with h|h
      · rw [h]; exact (pin_data y2).2.symm
      · rw [h]; exact (pin_data y9).2.symm
    · by_cases q : v.val=0 ∧ 1≤w.val ∧ w.val≤10
      · simp only [dif_pos q,decide_eq_true_eq] at he
        rw [value v (by omega),value w q.2.2,q.1,p.getVert_zero]
        have h := (L ⟨w.val-1,by omega⟩).mp he
        change G.Adj a (p.getVert (w.val-1+1)) at h
        rwa [show w.val-1+1=w.val by omega] at h
      · simp only [dif_neg q] at he
        contradiction
    · by_cases q : w.val=10 ∧ v.val<10
      · simp only [dif_pos q,decide_eq_true_eq] at hf
        rw [value v (by omega),value w (by omega),q.1,←len,p.getVert_length]
        exact ((R ⟨v.val,q.2⟩).mp hf).symm
      · simp only [dif_neg q] at hf
        contradiction
  intro v w h
  simp only [edge,Bool.or_eq_true] at h
  exact h.elim (direction v w) (fun e => (direction w v e).symm)
#print axioms off_five_mixed_model_forward

private theorem path_neighbor_is_pin_of_off
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (xo : x∉p.support) {k : ℕ} (kl : k≤p.length) (adj : G.Adj x (p.getVert k)) :
    k∈Pins p x := by
  have kr : k<p.length := by
    by_contra! late
    have ke : k=p.length := by omega
    exact (no_endpoints hp xo).2 (by simpa only [ke,p.getVert_length] using adj)
  exact mem_filter.mpr ⟨mem_range.mpr kr,adj⟩

open OffFive16DisconnectedMixed in
private theorem off_five_mixed_model_exact
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=10)
    (ψ : Fin 13→V) (value : ∀ k : Fin 13,k.val≤10 → ψ k=p.getVert k.val)
    (x11 : ψ 11=x) (y12 : ψ 12=y)
    (xo : x∉p.support) (yo : y∉p.support) (nxy : ¬G.Adj x y)
    (xPins : Pins p x=({1,8}:Finset ℕ)) (yPins : Pins p y=({2,9}:Finset ℕ))
    (m : Marks)
    (L : ∀ k : Fin 10,m k=1 ↔ G.Adj a (p.getVert (k.val+1)))
    (R : ∀ k : Fin 10,m k=2 ↔ G.Adj b (p.getVert k.val)) :
    (∀ v,G.Adj (ψ 0) (ψ v) → edge m 0 v=true) ∧
    (∀ v,G.Adj (ψ 10) (ψ v) → edge m 10 v=true) ∧
    (∀ v,G.Adj (ψ 11) (ψ v) → edge m 11 v=true) ∧
    (∀ v,G.Adj (ψ 12) (ψ v) → edge m 12 v=true) := by
  classical
  have a0 : ψ 0=a := by rw [value 0 (by decide)]; exact p.getVert_zero
  have b10 : ψ 10=b := by rw [value 10 (by decide)]; simpa only [len] using p.getVert_length
  refine ⟨?_,?_,?_,?_⟩
  · intro v va
    have vp : v.val≤10 := by
      by_cases yes : v.val≤10
      · exact yes
      · exfalso
        have vv := v.isLt
        have q : v.val=11 ∨ v.val=12 := by omega
        rcases q with e|e
        · have ve : v=11 := Fin.ext e
          exact (no_endpoints hp xo).1 (by rw [ve,x11,a0] at va; exact va.symm)
        · have ve : v=12 := Fin.ext e
          exact (no_endpoints hp yo).1 (by rw [ve,y12,a0] at va; exact va.symm)
    have up : 1≤v.val := by
      by_cases yes : 1≤v.val
      · exact yes
      · have ev : v=0 := Fin.ext (show v.val=(0:Fin 13).val by change v.val=0; omega)
        exact False.elim (G.loopless _ (ev ▸ va))
    have q : (0:Fin 13).val=0 ∧ 1≤v.val ∧ v.val≤10 := ⟨rfl,up,vp⟩
    have ia : G.Adj a (p.getVert ((v.val-1)+1)) := by
      rw [show v.val-1+1=v.val by omega,←value v vp,←a0]
      exact va
    have h : m ⟨v.val-1,by omega⟩=1 := (L _).mpr ia
    simp only [edge,Bool.or_eq_true]
    left
    simp only [dir,Bool.or_eq_true]
    exact .inl (.inr (by simp only [dif_pos q,decide_eq_true_eq,h]))
  · intro v vb
    have vp : v.val≤10 := by
      by_cases yes : v.val≤10
      · exact yes
      · exfalso
        have vv := v.isLt
        have q : v.val=11 ∨ v.val=12 := by omega
        rcases q with e|e
        · have ve : v=11 := Fin.ext e
          exact (no_endpoints hp xo).2 (by rw [ve,x11,b10] at vb; exact vb.symm)
        · have ve : v=12 := Fin.ext e
          exact (no_endpoints hp yo).2 (by rw [ve,y12,b10] at vb; exact vb.symm)
    have up : v.val<10 := by
      by_cases yes : v.val<10
      · exact yes
      · have ev : v=10 := Fin.ext (show v.val=(10:Fin 13).val by change v.val=10; omega)
        exact False.elim (G.loopless _ (ev ▸ vb))
    have q : (10:Fin 13).val=10 ∧ v.val<10 := ⟨rfl,up⟩
    have ib : G.Adj b (p.getVert v.val) := by rw [←value v vp,←b10]; exact vb
    have h : m ⟨v.val,up⟩=2 := (R _).mpr ib
    simp only [edge,Bool.or_eq_true]
    right
    simp only [dir,Bool.or_eq_true]
    exact .inr (by simp only [dif_pos q,decide_eq_true_eq,h])
  · intro v vx
    have vp : v.val≤10 := by
      by_cases yes : v.val≤10
      · exact yes
      · exfalso
        have vv := v.isLt
        have q : v.val=11 ∨ v.val=12 := by omega
        rcases q with e|e
        · have ve : v=11 := Fin.ext e
          exact G.loopless _ (ve ▸ vx)
        · have ve : v=12 := Fin.ext e
          exact nxy (by rwa [ve,x11,y12] at vx)
    have pi := path_neighbor_is_pin_of_off hp xo (show v.val≤p.length by omega)
      (by rwa [←value v vp,←x11])
    have p1 : v.val=1 ∨ v.val=8 := by simpa [xPins] using pi
    simp only [edge,Bool.or_eq_true]
    right
    simp only [dir,Bool.or_eq_true,decide_eq_true_eq]
    exact .inl (.inl (.inl (.inr ⟨p1,rfl⟩)))
  · intro v vy
    have vp : v.val≤10 := by
      by_cases yes : v.val≤10
      · exact yes
      · exfalso
        have vv := v.isLt
        have q : v.val=11 ∨ v.val=12 := by omega
        rcases q with e|e
        · have ve : v=11 := Fin.ext e
          exact nxy (by rw [ve,x11,y12] at vy; exact vy.symm)
        · have ve : v=12 := Fin.ext e
          exact G.loopless _ (ve ▸ vy)
    have pi := path_neighbor_is_pin_of_off hp yo (show v.val≤p.length by omega)
      (by rwa [←value v vp,←y12])
    have p1 : v.val=2 ∨ v.val=9 := by simpa [yPins] using pi
    simp only [edge,Bool.or_eq_true]
    right
    simp only [dir,Bool.or_eq_true,decide_eq_true_eq]
    exact .inl (.inl (.inr ⟨p1,rfl⟩))
#print axioms off_five_mixed_model_exact

end Graffiti189LongestPath.TwoCut.SmallOrderFour
