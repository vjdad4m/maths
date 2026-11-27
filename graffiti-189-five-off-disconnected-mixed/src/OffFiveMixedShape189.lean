import FourOffGraphCore189

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
open private pin_data pin_pos mem_distanceTwo dist_two LeftMarks RightMarks from SmallOrderFour189
open private two_pin_flanks_path_only length_ten_two_pin_shape mark_length_ten_at_most_two_holes pins_gap_at_four from FourOffGraphSupport189
open private two_pins_choose_ordered from FourOffGraphCore189

/-- Two different double porters, one isolated in the omitted graph, force
the same pair of length-ten mark holes and the two indicated pin pairs. -/
theorem off_five_mixed_forced_pins
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x y : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (xo : x∉p.support) (yo : y∉p.support) (xy : x≠y) (nxy : ¬G.Adj x y)
    (xTwo : 2≤(Pins p x).card) (yTwo : 2≤(Pins p y).card) :
    (1∈Pins p x ∧ 8∈Pins p x ∧ 2∈Pins p y ∧ 9∈Pins p y ∨
     2∈Pins p x ∧ 9∈Pins p x ∧ 1∈Pins p y ∧ 8∈Pins p y) ∧
    1∉LeftMarks p∪RightMarks p ∧ 8∉LeftMarks p∪RightMarks p := by
  classical
  obtain ⟨i,j,xi,xj,ij⟩ := two_pins_choose_ordered xTwo
  obtain ⟨k,l,yk,yl,kl⟩ := two_pins_choose_ordered yTwo
  have xgap := pins_gap_at_four hc even conn degree hp ah bh xo xi xj ij
  have ygap := pins_gap_at_four hc even conn degree hp ah bh yo yk yl kl
  have iq := pin_pos hp.1 xo xi
  have jq := (pin_data xj).1
  have kq := pin_pos hp.1 yo yk
  have lq := (pin_data yl).1
  have xshape := length_ten_two_pin_shape hc even conn degree hp ah bh len xo xi xj ij
  have yshape := length_ten_two_pin_shape hc even conn degree hp ah bh len yo yk yl kl
  have xPath := (two_pin_flanks_path_only hc even conn degree hp ah bh xo xi xj ij).1
  have dis {t : ℕ} (tx : t∈Pins p x) (ty : t∈Pins p y) : False :=
    yo (xPath y (mem_distanceTwo.mpr (dist_two hc xy nxy (pin_data tx).2 (pin_data ty).2.symm)))
  have ik : i≠k := fun e => dis xi (e.symm ▸ yk)
  have jl : j≠l := fun e => dis xj (e.symm ▸ yl)
  have hole {u v w : ℕ}
      (bu : u<p.length) (bv : v<p.length) (bw : w<p.length)
      (uh : u∉LeftMarks p∪RightMarks p)
      (vh : v∉LeftMarks p∪RightMarks p)
      (wh : w∉LeftMarks p∪RightMarks p) : u=v ∨ u=w ∨ v=w :=
    mark_length_ten_at_most_two_holes hp.1 xo (p.getVert_mem_support i)
      (pin_data xi).2 ah bh len.le bu bv bw uh vh wh
  have derive {s t : ℕ} (ss : 4≤s) (st : s≤8) (ts : 2≤t) (tt : t≤6)
      (h1 : 1∉LeftMarks p∪RightMarks p) (hs : s∉LeftMarks p∪RightMarks p)
      (ht : t-1∉LeftMarks p∪RightMarks p) (h8 : 8∉LeftMarks p∪RightMarks p) :
      s=8 ∧ t=2 := by
    have e := hole (u:=1) (v:=s) (w:=8) (by omega) (by omega) (by omega) h1 hs h8
    have f := hole (u:=1) (v:=8) (w:=t-1) (by omega) (by omega) (by omega) h1 h8 ht
    omega
  rcases xshape.1 with rfl|rfl
  · have l9 : l=9 := yshape.1.resolve_left (Ne.symm ik)
    subst l
    have xr := xshape.2.2 jl
    have yr := yshape.2.1 (Ne.symm ik)
    obtain ⟨rfl,rfl⟩ := derive (s:=j) (t:=k) (by omega) (by omega) (by omega) (by omega)
      xr.1 xr.2 yr.1 yr.2
    exact ⟨.inl ⟨xi,xj,yk,yl⟩,xr.1,yr.2⟩
  · have k1 : k=1 := yshape.1.resolve_right (Ne.symm jl)
    subst k
    have xr := xshape.2.1 ik
    have yr := yshape.2.2 (Ne.symm jl)
    obtain ⟨rfl,rfl⟩ := derive (s:=l) (t:=i) (by omega) (by omega) (by omega) (by omega)
      yr.1 yr.2 xr.1 xr.2
    exact ⟨.inr ⟨xi,xj,yk,yl⟩,yr.1,xr.2⟩

#print axioms off_five_mixed_forced_pins
end Graffiti189LongestPath.TwoCut.SmallOrderFour
