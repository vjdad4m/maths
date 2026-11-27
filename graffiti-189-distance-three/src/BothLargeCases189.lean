import BothLargeBase189
namespace Graffiti189LongestPath.TwoCut.DistThreeCtx
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.FourCut.Three
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V} {S : CutPair G a b} (C : DistThreeCtx S)
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

theorem bridge_either : C.Bridge ∨ C.other.Bridge := by
  obtain ⟨w,wl⟩ := S.con.exists_walk_length_eq_dist a b
  rw [C.cut_dist] at wl
  cases w with
  | nil => simp at wl
  | @cons _ x _ ax w =>
    cases w with
    | nil => simp at wl
    | @cons _ y _ xy w =>
      cases w with
      | nil => simp at wl
      | @cons _ z _ yz w =>
        have e : w.length=0 := by simp at wl; omega
        have zb : z=b := eq_of_length_eq_zero (p:=w) e
        subst z
        have xb : x≠b := fun e => C.cut_not_adj (e ▸ ax)
        have za : y≠a := fun e => C.cut_not_adj (e ▸ yz)
        rcases S.all x with e|e|⟨i,ix⟩
        · exact (ax.ne e.symm).elim
        · exact (xb e).elim
        have yh : y∈S.H i := by
          rcases S.closed i x ix y xy with e|e|e
          · exact (za e).elim
          · exact (yz.ne e).elim
          · exact e
        by_cases ih : i=C.j
        · have q : x∈C.H := show x∈S.H _ from ih ▸ ix
          have r : y∈C.H := show y∈S.H _ from ih ▸ yh
          exact Or.inl ⟨x,C.memA.mpr ⟨q,ax⟩,y,C.memB.mpr ⟨r,yz.symm⟩,xy⟩
        · have e : i=C.i := by
            have ne := C.different
            cases i <;> cases hc : C.i <;> cases hd : C.j <;> simp_all
          have q : x∈C.other.H := show x∈S.H C.i from e ▸ ix
          have r : y∈C.other.H := show y∈S.H C.i from e ▸ yh
          exact Or.inr ⟨x,C.other.memA.mpr ⟨q,ax⟩,y,C.other.memB.mpr ⟨r,yz.symm⟩,xy⟩

theorem quota (two : 2≤C.A.card) : 4≤C.A.card+C.E.card := by
  obtain ⟨x,xa,high⟩ := C.high_of_two two
  exact high.trans (C.degree_A xa)

theorem exact_if_twos (A2 : C.A.card=2) (U2 : C.U.card=2) :
    C.E.card=2 ∧ C.other.E.card=2 := by
  have s := C.shell_sum
  have q := C.quota (by omega)
  have r := C.other.quota (show 2≤C.U.card by omega)
  change 4≤C.U.card+C.other.E.card at r
  exact ⟨by omega,by omega⟩

theorem all_high_group :
    (∀ x∈C.A,4≤G.degree x) ∨ (∀ x∈C.B,4≤G.degree x) := by
  by_cases h : ∀ x∈C.A,4≤G.degree x
  · exact Or.inl h
  obtain ⟨x,hx⟩ := not_forall.mp h
  have xa : x∈C.A := Classical.byContradiction (fun na => hx (fun e => (na e).elim))
  have xlow : ¬4≤G.degree x := fun hi => hx (fun _ => hi)
  right
  intro y yb
  have ne : x≠y := fun e => disjoint_left.mp C.dis_AB xa (e.symm ▸ yb)
  exact (S.degree x y ne).resolve_left xlow

theorem d2_cross_group {x y z : V} (xa : x∈C.A) (yb : y∈C.B)
    (no : ¬G.Adj x y) (xz : G.Adj x z) (zy : G.Adj z y) :
    y∈DistanceTwo G x := by
  have ne : x≠y := fun e => disjoint_left.mp C.dis_AB xa (e.symm ▸ yb)
  exact Sides.mem_d2.mpr (Sides.dist_two S.con ne no xz zy)

theorem shared_inner_impossible (A3 : C.A.card=3) (B3 : C.B.card=3)
    (U2 : 2≤C.U.card) (W2 : 2≤C.W.card)
    (I1 : C.I.card=1) (no : ¬C.Bridge) : False := by
  obtain ⟨z,zi⟩ := card_eq_one.mp I1
  have attach (D : DistThreeCtx S) {x r : V} (xa : x∈D.A)
      (h : 4≤G.degree x) (none : ¬D.Bridge) (one : D.I={r}) : G.Adj x r := by
    obtain ⟨u,ue,xu⟩ := D.high_port_has_E xa h
    have ui := D.shell_sub_inner_no_bridge none ue
    have e : u=r := by simpa [one] using ui
    exact e ▸ xu
  have attachb {x : V} (xb : x∈C.B) (h : 4≤G.degree x) : G.Adj x z := by
    obtain ⟨u,ue,xu⟩ := C.swap.high_port_has_E xb h
    have no' : ¬C.swap.Bridge := fun e => no (C.bridge_swap.mp e)
    have ui := C.swap.shell_sub_inner_no_bridge no' ue
    rw [C.swap_I,zi] at ui
    exact (mem_singleton.mp ui) ▸ xu
  rcases C.all_high_group with all|all
  · obtain ⟨y,yb,hi⟩ := C.high_of_two (show 2≤C.B.card by omega)
    have yz := attachb yb hi
    have d2 : C.A⊆DistanceTwo G y := fun x xa => C.swap.d2_cross_group yb xa
      (fun xy => no ⟨x,xa,y,yb,xy.symm⟩) yz (attach C xa (all x xa) no zi).symm
    have s := C.swap.local_d2_cap yb C.A_sub_H d2
    change C.A.card+C.W.card≤4 at s
    omega
  · obtain ⟨x,xa,hi⟩ := C.high_of_two (show 2≤C.A.card by omega)
    have xz := attach C xa hi no zi
    have d2 : C.B⊆DistanceTwo G x := fun y yb =>
      C.d2_cross_group xa yb (fun xy => no ⟨x,xa,y,yb,xy⟩) xz (attachb yb (all y yb)).symm
    have s := C.local_d2_cap xa C.B_sub_H d2
    omega

theorem shell_opp_of_bridge_with_three (U3 : C.U.card=3) (_B2 : 2≤C.B.card)
    (bridge : C.Bridge) : C.B⊆C.E ∧ C.I⊆C.E ∧ C.E=C.H\C.A := by
  obtain ⟨x,xa,y,yb,xy⟩ := bridge
  have e := C.shell_eq_of_universal xa (C.bridge_universal xa yb xy U3)
  refine ⟨?_,?_,e⟩
  · intro z zb
    rw [e]
    exact mem_sdiff.mpr ⟨C.B_sub_H zb,fun za => disjoint_left.mp C.dis_AB za zb⟩
  · intro z zi
    rw [e]
    exact mem_sdiff.mpr ⟨C.I_sub_H zi,fun za => (C.memI.mp zi).2.1 (C.memA.mp za).2⟩

-- If both sides of a separator have three ports, and the other separator
-- has twice two, either internal bridge already exceeds a shell.
theorem impossible_22_33 (A2 : C.A.card=2) (U2 : C.U.card=2) (B3 : C.B.card=3) (W3 : C.W.card=3) : False := by
  have f (D : DistThreeCtx S) (a2 : D.A.card=2) (u2 : D.U.card=2) (b3 : D.B.card=3) (w3 : D.W.card=3)
      (bridge : D.Bridge) : False := by
    obtain ⟨x,xa,y,yb,xy⟩ := bridge
    have all := D.swap.bridge_propagates yb xa xy.symm w3 (by change 2≤D.A.card; omega)
    have sub : D.B⊆D.E := by
      intro z zb
      have ne : z≠x := fun e => disjoint_left.mp D.dis_AB (e.symm ▸ xa) zb
      have zx := (all z zb x (D.A_sub_H xa)).resolve_left ne
      exact D.local_a_d2 xa (D.B_sub_H zb) (fun za => disjoint_left.mp D.dis_AB za zb) zx.symm
    have g := card_le_card sub
    have c := (D.exact_if_twos a2 u2).1
    omega
  exact C.bridge_either.elim (f C A2 U2 B3 W3) (f C.other U2 A2 W3 B3)

private theorem no_bridge_if_shells_single (A3 : C.A.card=3) (E1 : C.E.card=1) (F1 : C.F.card=1) :
    ¬C.Bridge := by
  rintro ⟨x,xa,y,yb,xy⟩
  have xe := C.swap.local_a_d2 yb (C.A_sub_H xa) (fun xb => disjoint_left.mp C.dis_AB xa xb) xy.symm
  have ye := C.local_a_d2 xa (C.B_sub_H yb) (fun ya => disjoint_left.mp C.dis_AB ya yb) xy
  obtain ⟨u,uq,hi⟩ := C.high_of_two (show 2≤(C.A.erase x).card by rw [card_erase_of_mem xa,A3])
  obtain ⟨ux,ua⟩ := mem_erase.mp uq
  obtain ⟨v,ve,uv⟩ := C.high_port_has_E ua hi
  have eqv : v=y := card_le_one.mp (by omega : C.E.card≤1) v ve y ye
  subst v
  have uf := C.swap.local_a_d2 yb (C.A_sub_H ua) (fun ub => disjoint_left.mp C.dis_AB ua ub) uv.symm
  exact ux (card_le_one.mp (by omega : C.F.card≤1) u uf x xe)

private theorem finish_large_if_bridge_and_foreign_shell_small
    (Aforeign3 : C.U.card=3) (Bforeign3 : C.W.card=3)
    (Aatleast2 : 2≤C.A.card) (Batleast2 : 2≤C.B.card)
    (Enear : C.other.E.card≤1) (no : ¬C.other.Bridge)
    (bridge : C.Bridge) : False := by
  obtain ⟨x,xa,y,yb,xy⟩ := bridge
  have inter := C.foreign_inner_near xa yb xy Aforeign3
  have back := C.other.shell_sub_inner_no_bridge no
  have I1 : C.other.I.card=1 := by
    have ic := card_le_card inter
    have ec := card_le_card back
    have po := C.other.E_pos
    omega
  exact C.other.shared_inner_impossible Aforeign3 Bforeign3 Aatleast2 Batleast2 I1 no

theorem impossible_33_33 (A3 : C.A.card=3) (U3 : C.U.card=3) (B3 : C.B.card=3) (W3 : C.W.card=3) : False := by
  have absurd (D : DistThreeCtx S) (a3 : D.A.card=3) (u3 : D.U.card=3) (b3 : D.B.card=3) (w3 : D.W.card=3)
      (bridge : D.Bridge) : False := by
    have e := (D.shell_opp_of_bridge_with_three u3 (by omega) bridge).1
    have f := (D.swap.shell_opp_of_bridge_with_three w3 (by change 2≤D.A.card; omega)
      (D.bridge_swap.mpr bridge)).1
    have ed := card_le_card e
    have fd := card_le_card f
    change D.A.card≤D.F.card at fd
    have es := D.shell_sum
    have fs := D.swap.shell_sum
    change D.F.card+D.other.F.card≤4 at fs
    have DEn : D.other.E.card≤1 := by omega
    have DFn : D.other.F.card≤1 := by omega
    have ep := D.other.E_pos
    have fp := D.other.swap.E_pos
    change 1≤D.other.F.card at fp
    have nb := D.other.no_bridge_if_shells_single u3 (by omega) (by omega)
    exact D.finish_large_if_bridge_and_foreign_shell_small u3 w3 (by omega) (by omega) DEn nb bridge
  exact C.bridge_either.elim (absurd C A3 U3 B3 W3) (absurd C.other U3 A3 W3 B3)

theorem impossible_23_23_same (A2 : C.A.card=2) (U3 : C.U.card=3)
    (B2 : C.B.card=2) (W3 : C.W.card=3) (lg : 5≤C.H.card) : False := by
  have bridge : C.Bridge := by
    by_cases ex : C.Bridge
    · exact ex
    exfalso
    obtain ⟨x,xa⟩ := card_pos.mp C.Apos
    have near := card_le_card (C.foreign_opp_near xa U3 (fun y yb xy => ex ⟨x,xa,y,yb,xy⟩))
    have q := C.quota (by omega : 2≤C.A.card)
    have su := C.shell_sum
    omega
  have ee := (C.shell_opp_of_bridge_with_three U3 (by omega) bridge).2.2
  have ff := (C.swap.shell_opp_of_bridge_with_three W3 (by change 2≤C.A.card; omega)
    (C.bridge_swap.mpr bridge)).2.2
  have e := card_sdiff_add_card_eq_card C.A_sub_H
  rw [←ee] at e
  have f := card_sdiff_add_card_eq_card C.B_sub_H
  change C.F=C.H\C.B at ff
  rw [←ff] at f
  have es := C.shell_sum
  have fs := C.swap.shell_sum
  change C.F.card+C.other.F.card≤4 at fs
  have ep := C.other.E_pos
  have fp := C.other.swap.E_pos
  change 1≤C.other.F.card at fp
  have no := C.other.no_bridge_if_shells_single U3 (by omega) (by omega)
  exact C.finish_large_if_bridge_and_foreign_shell_small U3 W3 (by omega) (by omega)
    (by omega) no bridge

theorem impossible_23_23_opposite (A2 : C.A.card=2) (U3 : C.U.card=3)
    (B3 : C.B.card=3) (W2 : C.W.card=2) (lg : 5≤C.H.card) (lk : 5≤C.K.card) : False := by
  have must {u v : V} {T : CutPair G u v} (D : DistThreeCtx T) (a2 : D.A.card=2) (u3 : D.U.card=3)
      (b3 : D.B.card=3) (w2 : D.W.card=2) (lg : 5≤D.K.card) : D.Bridge := by
    by_cases ex : D.Bridge
    · exact ex
    exfalso
    obtain ⟨x,xa⟩ := card_pos.mp D.Apos
    have near := D.foreign_opp_near xa u3 (fun y yb xy => ex ⟨x,xa,y,yb,xy⟩)
    have q := D.quota (by omega : 2≤D.A.card)
    have sum := D.shell_sum
    have cc := card_le_card near
    have e := card_le_card (D.shell_sub_inner_no_bridge ex)
    obtain ⟨y,yw⟩ := card_pos.mp D.swap.Upos
    obtain ⟨z,za,zy⟩ := D.other.local_a_witness (near yw)
    have Kbridge : D.other.swap.Bridge := ⟨y,yw,z,za,zy.symm⟩
    have eq := (D.other.swap.shell_opp_of_bridge_with_three b3 (by change 2≤D.U.card; omega)
      Kbridge).2.2
    change D.other.F=D.K\D.W at eq
    have cf := card_sdiff_add_card_eq_card
      (show D.W⊆D.K from fun _ hy => (D.memW.mp hy).1)
    rw [←eq] at cf
    have fs := D.swap.shell_sum
    change D.F.card+D.other.F.card≤4 at fs
    have inh := D.other.swap.foreign_inner_near yw za zy.symm b3
    have c := card_le_card inh
    change (D.swap.I).card≤D.F.card at c
    rw [D.swap_I] at c
    omega
  have Hbridge := must C A2 U3 B3 W2 lk
  have Kbridge := must C.other.swap W2 B3 U3 A2 lg
  have aeq := (C.shell_opp_of_bridge_with_three U3 (by omega) Hbridge).2.2
  have cd := card_sdiff_add_card_eq_card C.A_sub_H
  rw [←aeq] at cd
  obtain ⟨y,yw,z,za,yz⟩ := Kbridge
  have all := C.other.swap.bridge_propagates yw za yz B3 (by change 2≤C.U.card; omega)
  have sub : C.W⊆C.other.E := by
    intro w ww
    have ne : w≠z := fun e => disjoint_left.mp C.dis_UW za (e ▸ ww)
    have a := (all w ww z (C.other.A_sub_H za)).resolve_left ne
    exact C.other.local_a_d2 za (C.other.B_sub_H ww) (fun wa => disjoint_left.mp C.dis_UW wa ww) a.symm
  have wc := card_le_card sub
  have es := C.shell_sum
  omega

theorem impossible_23_33 (A2 : C.A.card=2) (U3 : C.U.card=3)
    (B3 : C.B.card=3) (W3 : C.W.card=3) (lg : 5≤C.H.card) : False := by
  have bridge : C.Bridge := by
    by_cases ex : C.Bridge
    · exact ex
    exfalso
    obtain ⟨x,xa⟩ := card_pos.mp C.Apos
    have near := card_le_card (C.foreign_opp_near xa U3 (fun y yb xy => ex ⟨x,xa,y,yb,xy⟩))
    have q := C.quota (by omega : 2≤C.A.card)
    have su := C.shell_sum
    omega
  have ee := (C.shell_opp_of_bridge_with_three U3 (by omega) bridge).2.2
  have ff := (C.swap.shell_opp_of_bridge_with_three W3 (by change 2≤C.A.card; omega)
    (C.bridge_swap.mpr bridge)).2.2
  have e := card_sdiff_add_card_eq_card C.A_sub_H
  rw [←ee] at e
  have f := card_sdiff_add_card_eq_card C.B_sub_H
  change C.F=C.H\C.B at ff
  rw [←ff] at f
  have es := C.shell_sum
  have fs := C.swap.shell_sum
  change C.F.card+C.other.F.card≤4 at fs
  have no : ¬C.other.Bridge := by
    intro ex
    have sub := (C.other.swap.shell_opp_of_bridge_with_three B3 (by change 2≤C.U.card; omega)
      (C.other.bridge_swap.mpr ex)).1
    have cap := card_le_card sub
    change C.U.card≤C.other.F.card at cap
    omega
  exact C.finish_large_if_bridge_and_foreign_shell_small U3 W3 (by omega) (by omega) (by omega) no bridge

#print axioms impossible_22_33
#print axioms impossible_33_33
#print axioms impossible_23_23_same
#print axioms impossible_23_23_opposite
#print axioms impossible_23_33
end Graffiti189LongestPath.TwoCut.DistThreeCtx
