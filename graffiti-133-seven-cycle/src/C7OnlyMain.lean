import C7OnlyCert
import PentagonStructure133
import SixCycle133

namespace Graffiti133C7Only
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133RevisitSix Graffiti133NoFive Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem local_bound {v : V} (A : Finset V)
    (hb : ∀ x, G.Adj v x → x ∈ A) : localIndependence G v ≤ A.card := by
  classical
  apply Finset.sup_le_iff.mpr
  intro s hs
  exact Finset.card_le_card fun w hw => hb w (Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hs |>.1 w hw)

private theorem side_neighbor (h4 : FourCycleFree G) {v s : V} (e : G.Adj v s)
    (hv : 2 ≤ localIndependence G v) :
    ∃ w, G.Adj v w ∧ w ≠ s ∧ ¬G.Adj w s := by
  classical
  obtain ⟨A,hA,hM⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  have N (u) (hu : u ∈ A) := (Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1 u hu
  have no : ¬G.Adj x y := (Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).2 x hx y hy
  by_cases ex : x = s
  · subst x
    exact ⟨y,N y hy,hxy.symm,fun h => no h.symm⟩
  by_cases ey : y = s
  · subst y
    exact ⟨x,N x hx,hxy,no⟩
  by_cases ex' : G.Adj x s
  · refine ⟨y,N y hy,ey,?_⟩
    intro ey'
    exact e.ne (h4 x y v s hxy (N x hx).symm (N y hy).symm ex' ey')
  · exact ⟨x,N x hx,ex,ex'⟩

private theorem extension {n : ℕ} (hn : 0 < n) {p : Fin n → V} {x y : V}
    {U : V → Prop} (hp : InducedPath G p) (head : p ⟨0,hn⟩=x)
    (tail : ∀ i : Fin n, 0 < i.val → U (p i))
    (ex : G.Adj y x) (off : ∀ v, U v → y≠v ∧ ¬G.Adj y v) :
    ∃ q : Fin (n+1) → V, InducedPath G q ∧ q ⟨0,by omega⟩=y ∧
      ∀ i : Fin (n+1), 0 < i.val → q i=x ∨ U (q i) := by
  have no (i : Fin n) : y ≠ p i := by
    by_cases h : 0 < i.val
    · exact (off _ (tail _ h)).1
    · have eq : i=⟨0,hn⟩ := Fin.ext (by change i.val = 0; omega)
      rw [eq,head]
      exact ex.ne
  obtain ⟨q,hq,h0,hqt⟩ := prepend_induced_with_positions hn hp y no (head.symm ▸ ex)
    (fun i hi => (off _ (tail _ hi)).2)
  refine ⟨q,hq,h0,?_⟩
  intro i hi
  rw [hqt i hi]
  let j : Fin n := ⟨i.val-1,by have := i.isLt; omega⟩
  change p j=x ∨ U (p j)
  by_cases hj : 0 < j.val
  · exact Or.inr (tail _ hj)
  · exact Or.inl ((congrArg p (Fin.ext (by change j.val = 0; omega) : j=⟨0,hn⟩)).trans head)

private theorem far_step (H : Hole G 7) (h4 : FourCycleFree G)
    (h7 : ¬∃ p : Fin 7 → V, InducedPath G p)
    (h6 : ¬Nonempty (Hole G 6)) (hl : ∀ v, 2 ≤ localIndependence G v)
    {x a b : V} {i : Fin 7} (hx : IsProfile H x i)
    (ha : OnlyFar H a) (hb : OnlyFar H b) (exa : G.Adj x a) (eab : G.Adj a b) :
    G.Adj x b := by
  classical
  by_contra noxb
  obtain ⟨c,ebc,can,eca⟩ := side_neighbor h4 eab.symm (hl b)
  have xbn : x≠b := by
    intro e
    exact hb.2 i (e ▸ (hx.2 i).mpr (Or.inl rfl))
  have cOut (j) : c ≠ H.c j := fun e => hb.2 j (e ▸ ebc)
  have cneX : c≠x := fun e => noxb (e ▸ ebc.symm)
  have hc : OnlyFar H c := by
    refine ⟨cOut,?_⟩
    intro j e
    obtain ⟨k,hk⟩ := classify H h4 h7 h6 cOut ⟨j,e⟩
    exact cneX (single_front H h4 h7 h6 hk hx)
  have noxc : ¬G.Adj x c := by
    intro e
    exact can (h4 x b c a xbn e ebc exa eab.symm)
  obtain ⟨p,hp,h0,ht⟩ := rooted4 H hx
  obtain ⟨q,hq,q0,qt⟩ := extension (by decide) (U := fun z => ∃ j, z=H.c j) hp h0 ht
    exa.symm (by rintro v ⟨j,rfl⟩; exact ⟨ha.1 j,ha.2 j⟩)
  obtain ⟨r,hr,r0,rt⟩ := extension (by decide) (U := fun z => z=x ∨ ∃ j, z=H.c j) hq q0 qt eab.symm (by
    intro v hv
    rcases hv with rfl | ⟨j,rfl⟩
    · exact ⟨xbn.symm,fun e => noxb e.symm⟩
    · exact ⟨hb.1 j,hb.2 j⟩)
  obtain ⟨s,hs,_,_⟩ := extension (by decide) (U := fun z => z=a ∨ z=x ∨ ∃ j, z=H.c j) hr r0 rt ebc.symm (by
    intro v hv
    rcases hv with rfl | rfl | ⟨j,rfl⟩
    · exact ⟨can,eca⟩
    · exact ⟨cneX,fun e => noxc e.symm⟩
    · exact ⟨hc.1 j,hc.2 j⟩)
  exact h7 ⟨s,hs⟩

private theorem no_far (H : Hole G 7) (h4 : FourCycleFree G)
    (h7 : ¬∃ p : Fin 7 → V, InducedPath G p)
    (h6 : ¬Nonempty (Hole G 6)) (conn : G.Connected)
    (hl : ∀ v, 2 ≤ localIndependence G v)
    {x : V} {i : Fin 7} (hx : IsProfile H x i) (b : V) : ¬OnlyFar H b := by
  classical
  have walkProp {u v : V} (p : G.Walk u v) (h : OnlyFar H v → G.Adj x v) :
      OnlyFar H u → G.Adj x u := by
    induction p with
    | nil => exact h
    | @cons u z v e p ih =>
      intro hu
      by_cases hz : Outside H.c z
      · by_cases hz' : OnlyFar H z
        · exact far_step H h4 h7 h6 hl hx hz' hu (ih h hz') e.symm
        · have contacts : ∃ j, G.Adj z (H.c j) := by
            by_contra n
            exact hz' ⟨hz,fun j ej => n ⟨j,ej⟩⟩
          obtain ⟨k,hk⟩ := classify H h4 h7 h6 hz contacts
          have eq := single_front H h4 h7 h6 hk hx
          exact eq ▸ e.symm
      · unfold Outside at hz
        push_neg at hz
        obtain ⟨j,rfl⟩ := hz
        exact (hu.2 j e).elim
  have allX (v : V) (hv : OnlyFar H v) : G.Adj x v := by
    obtain ⟨p⟩ := conn v x
    exact walkProp p (fun hf => (hf.2 i ((hx.2 i).mpr (Or.inl rfl))).elim) hv
  intro hf
  obtain ⟨c,hbc,hcn,hn⟩ := side_neighbor h4 (allX b hf).symm (hl b)
  have cOut (j) : c ≠ H.c j := fun e => hf.2 j (e ▸ hbc)
  apply hn
  apply (allX c ⟨cOut,?_⟩).symm
  intro j e
  obtain ⟨k,hk⟩ := classify H h4 h7 h6 cOut ⟨j,e⟩
  exact hcn (single_front H h4 h7 h6 hk hx)

private theorem covered_null (H : Hole G 7) (conn : G.Connected)
    (hn : ¬∃ x, Outside H.c x ∧ ∃ i, G.Adj x (H.c i)) (v : V) :
    ∃ i, v=H.c i := by
  classical
  have walkProp {u v : V} (p : G.Walk u v) (h : ∃ i, v=H.c i) :
      ∃ i, u=H.c i := by
    induction p with
    | nil => exact h
    | @cons u z v e p ih =>
      obtain ⟨i,hi⟩ := ih h
      by_contra bad
      push_neg at bad
      exact hn ⟨u,bad,i,hi ▸ e⟩
  obtain ⟨p⟩ := conn v (H.c 0)
  exact walkProp p ⟨0,rfl⟩

private theorem cyclic_indices : ∀ i j : Fin 7, Cyclic i j → j=i+1 ∨ j=i+6 := by decide
private theorem profile_avoids_next : ∀ i : Fin 7, ¬Profile i (i+1) := by decide

theorem sum_lt_three_of_hole_seven_no_six
    (H : Hole G 7) (h4 : FourCycleFree G)
    (h7 : ¬∃ p : Fin 7 → V, InducedPath G p)
    (h6 : ¬Nonempty (Hole G 6)) (conn : G.Connected)
    (hl : ∀ v, 2 ≤ localIndependence G v) :
    (∑ v : V, localIndependence G v) < 3 * Fintype.card V := by
  classical
  suffices (∀ v, localIndependence G v ≤ 3) ∧ ∃ v, localIndependence G v < 3 by
    obtain ⟨le, v, lt⟩ := this
    calc
      _ < ∑ _ : V, (3:ℕ) := Finset.sum_lt_sum (fun w _ => le w) ⟨v,Finset.mem_univ v,lt⟩
      _ = _ := by simp [Nat.mul_comm]
  by_cases hn : ∃ x, Outside H.c x ∧ ∃ i, G.Adj x (H.c i)
  · obtain ⟨x,hxo,has⟩ := hn
    obtain ⟨k,hx⟩ := classify H h4 h7 h6 hxo has
    have cover (v : V) : v=x ∨ ∃ i, v=H.c i := by
      by_cases hw : Outside H.c v
      · by_cases ha : ∃ i, G.Adj v (H.c i)
        · obtain ⟨i,hi⟩ := classify H h4 h7 h6 hw ha
          exact Or.inl (single_front H h4 h7 h6 hi hx)
        · push_neg at ha
          exact (no_far H h4 h7 h6 conn hl hx v ⟨hw,ha⟩).elim
      · unfold Outside at hw
        push_neg at hw
        exact Or.inr hw
    have cycleN (i j : Fin 7) (e : G.Adj (H.c i) (H.c j)) :
        j=i+1 ∨ j=i+6 := cyclic_indices _ _ ((H.adj _ _).mp e)
    constructor
    · intro v
      rcases cover v with rfl | ⟨i,rfl⟩
      · refine (local_bound ({H.c k,H.c (k+3),H.c (k+4)} : Finset V) ?_).trans ?_
        · intro w hw
          rcases cover w with rfl | ⟨i,rfl⟩
          · exact (G.loopless _ hw).elim
          · rcases (hx.2 _).mp hw with rfl | rfl | rfl <;> simp
        · exact (Finset.card_insert_le _ _).trans
            (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
      · refine (local_bound ({x,H.c (i+1),H.c (i+6)} : Finset V) ?_).trans ?_
        · intro w hw
          rcases cover w with rfl | ⟨j,rfl⟩
          · simp
          · rcases cycleN _ _ hw with rfl | rfl <;> simp
        · exact (Finset.card_insert_le _ _).trans
            (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
    · refine ⟨H.c (k+1), lt_of_le_of_lt ((local_bound
          ({H.c (k+1+1),H.c (k+1+6)} : Finset V) ?_).trans ?_) (by decide : 2 < 3)⟩
      · intro w hw
        rcases cover w with rfl | ⟨j,rfl⟩
        · exact (profile_avoids_next k ((hx.2 _).mp hw.symm)).elim
        · rcases cycleN _ _ hw with rfl | rfl <;> simp
      · exact (Finset.card_insert_le _ _).trans (by simp)
  · have le (v : V) : localIndependence G v ≤ 2 := by
      obtain ⟨i,rfl⟩ := covered_null H conn hn v
      refine (local_bound ({H.c (i+1),H.c (i+6)} : Finset V) ?_).trans
        ((Finset.card_insert_le _ _).trans (by simp))
      intro w hw
      obtain ⟨j,rfl⟩ := covered_null H conn hn w
      rcases cyclic_indices _ _ ((H.adj _ _).mp hw) with rfl | rfl <;> simp
    exact ⟨fun v => (le v).trans (by decide),H.c 0,(le (H.c 0)).trans_lt (by decide : 2 < 3)⟩

#print axioms sum_lt_three_of_hole_seven_no_six
end Graffiti133C7Only
