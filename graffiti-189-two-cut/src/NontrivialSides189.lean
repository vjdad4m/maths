import ThreeSide189
import Mathlib.Tactic.FinCases
namespace Graffiti189LongestPath.FourCut.Three.Sides
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false
noncomputable section
variable {a b : V} (S : Sides G a b)

private theorem indices_onto {i j k : Fin 3} (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (l : Fin 3) : l=i ∨ l=j ∨ l=k := by
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  have hl := l.isLt
  simp only [←Fin.val_ne_iff,←Fin.val_eq_val] at *
  omega

private theorem dsum_any {i j k : Fin 3} (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (R : Finset V) (sub : R⊆DistanceTwo G a) (off : ∀ x∈R, ∀ i, x∉S.H i) :
    (S.D i).card+(S.D j).card+(S.D k).card+R.card ≤ (DistanceTwo G a).card := by
  have ds (i : Fin 3) : S.D i ⊆ DistanceTwo G a := fun _ h => (mem_filter.mp h).2
  have dis (i j : Fin 3) (ne : i≠j) : Disjoint (S.D i) (S.D j) :=
    (S.dis i j ne).mono (filter_subset _ _) (filter_subset _ _)
  have dr (i : Fin 3) : Disjoint (S.D i) R := disjoint_left.mpr
    (fun x hx hr => off x hr i (mem_filter.mp hx).1)
  have c := card_le_card (union_subset (union_subset (union_subset (ds i) (ds j)) (ds k)) sub)
  rwa [card_union_of_disjoint (disjoint_union_left.mpr
          ⟨disjoint_union_left.mpr ⟨dr i,dr j⟩,dr k⟩),
        card_union_of_disjoint (disjoint_union_left.mpr ⟨dis i k ik, dis j k jk⟩),
        card_union_of_disjoint (dis i j ij)] at c

private theorem dsum_le {i j k : Fin 3} (ij : i≠j) (ik : i≠k) (jk : j≠k) :
    (S.D i).card+(S.D j).card+(S.D k).card≤4 := by
  have c := S.dsum_any ij ik jk ∅ (empty_subset _) (by simp)
  have h := S.d2 a
  simp at c
  omega

private theorem universal_high {i : Fin 3} {x : V} (xi : x∈S.A i) (xb : G.Adj b x)
    (size : 3≤(S.H i).card) (all : ∀ y∈S.H i, x=y ∨ G.Adj x y) :
    4≤G.degree x := by
  have hxi := (mem_filter.mp xi).1
  have ax := (mem_filter.mp xi).2
  let N := insert a (insert b ((S.H i).erase x))
  have sub : N ⊆ G.neighborFinset x := by
    intro y hy
    apply (mem_neighborFinset G x y).mpr
    rcases mem_insert.mp hy with rfl|hy
    · exact ax.symm
    rcases mem_insert.mp hy with rfl|hy
    · exact xb.symm
    exact (all y (mem_erase.mp hy).2).resolve_left (Ne.symm (mem_erase.mp hy).1)
  have ca : a ∉ insert b ((S.H i).erase x) := by
    simp only [mem_insert,mem_erase,not_or]
    exact ⟨S.ab, fun h => (S.off i).1 h.2⟩
  have cb : b ∉ (S.H i).erase x := fun h => (S.off i).2 (mem_erase.mp h).2
  have c := card_le_card sub
  rw [show N=insert a (insert b ((S.H i).erase x)) from rfl,
    card_insert_of_not_mem ca,card_insert_of_not_mem cb,card_erase_of_mem hxi,
    card_neighborFinset_eq_degree] at c
  omega

private theorem saturated_singleton {i j k : Fin 3} (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (one : (S.A i).card=1) (full : (S.A j).card+(S.A k).card=4)
    (si : 3≤(S.H i).card) :
    (∃ x∈S.A i, 4≤G.degree x ∧ G.Adj b x) ∧
      (∃ y∈S.B i, y∉S.A i) ∧ S.B j⊆S.A j ∧ S.B k⊆S.A k := by
  obtain ⟨x,xi⟩ := card_pos.mp (S.apos i)
  obtain ⟨all,xb,jc,kc⟩ := S.saturates ij ik jk full xi
  have high := S.universal_high xi xb si all
  refine ⟨⟨x,xi,high,xb⟩,?_,jc,kc⟩
  by_cases ex : ∃ y∈S.B i,y∉S.A i
  · exact ex
  exfalso
  have sub : S.Ports i⊆S.A i := by
    intro y hy
    obtain ⟨hi,ha|hb⟩ := mem_filter.mp hy
    · exact mem_filter.mpr ⟨hi,ha⟩
    by_cases ya : y∈S.A i
    · exact ya
    exact (ex ⟨y,mem_filter.mpr ⟨hi,hb⟩,ya⟩).elim
  have le := card_le_card sub
  have ge := S.plenty i (by omega)
  change 2≤(S.Ports i).card at ge
  omega

private theorem high_double {i : Fin 3} (two : (S.A i).card=2) :
    ∃ x∈S.A i, 4≤G.degree x := by
  obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (show 1<(S.A i).card by omega)
  exact (S.degree x y ne).elim (fun high => ⟨x,hx,high⟩) (fun high => ⟨y,hy,high⟩)

private theorem high_common_of_122 {i j k : Fin 3} (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (one : (S.A i).card=1) (twoj : (S.A j).card=2) (twok : (S.A k).card=2)
    (si : 3≤(S.H i).card) :
    G.Adj a b ∧ ∀ l, ∀ x∈S.A l, 4≤G.degree x → x∈S.B l := by
  obtain ⟨⟨x,xi,xdeg,xb⟩,_,_,_⟩ := S.saturated_singleton ij ik jk one (by omega) si
  obtain ⟨y,yj,ydeg⟩ := S.high_double twoj
  obtain ⟨z,zk,zdeg⟩ := S.high_double twok
  have dx := S.degree_bound xi
  have dy := S.degree_bound yj
  have dz := S.degree_bound zk
  have di : 2≤(S.D i).card := by by_cases e : G.Adj x b <;> simp [e] at dx <;> omega
  have dj : 1≤(S.D j).card := by by_cases e : G.Adj y b <;> simp [e] at dy <;> omega
  have dk : 1≤(S.D k).card := by by_cases e : G.Adj z b <;> simp [e] at dz <;> omega
  have cap := S.dsum_le ij ik jk
  have edge : G.Adj a b := by
    by_cases edge : G.Adj a b
    · exact edge
    exfalso
    have bD := mem_d2.mpr (dist_two S.con S.ab edge (mem_filter.mp xi).2 xb.symm)
    have drop := S.dsum_any ij ik jk {b} (singleton_subset_iff.mpr bD)
      (by intro w hw l; simpa only [mem_singleton.mp hw] using (S.off l).2)
    rw [card_singleton] at drop
    have cm := S.d2 a
    omega
  refine ⟨edge,?_⟩
  intro l w wl high
  apply mem_filter.mpr
  refine ⟨(mem_filter.mp wl).1,?_⟩
  by_cases wb : G.Adj b w
  · exact wb
  exfalso
  have dw := S.degree_bound wl
  have nw : ¬G.Adj w b := fun e => wb e.symm
  simp only [nw,if_false,Nat.add_zero] at dw
  rcases indices_onto ij ik jk l with rfl|rfl|rfl <;> omega

#print axioms high_common_of_122

private theorem no_113 {i j k : Fin 3} (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (oi : (S.A i).card=1) (oj : (S.A j).card=1) (tk : (S.A k).card=3)
    (sizes : ∀ l, 3≤(S.H l).card) : False := by
  obtain ⟨_,_,sub,_⟩ := S.saturated_singleton ij ik jk oi (by omega) (sizes i)
  obtain ⟨_,⟨w,wb,wa⟩,_,_⟩ := S.saturated_singleton ij.symm jk ik oj (by omega) (sizes j)
  exact wa (sub wb)

private theorem no_222 (c0 : (S.A 0).card=2) (c1 : (S.A 1).card=2) (c2 : (S.A 2).card=2)
    (sizes : ∀ l, 3≤(S.H l).card) : False := by
  have cs (l : Fin 3) : (S.A l).card=2 := by fin_cases l <;> assumption
  have common (l : Fin 3) {x : V} (xl : x∈S.A l) :
      (∀ y∈S.H l, x=y ∨ G.Adj x y) ∧ G.Adj b x := by
    fin_cases l
    · exact (S.saturates (show (0:Fin 3)≠1 by decide) (show (0:Fin 3)≠2 by decide)
        (show (1:Fin 3)≠2 by decide) (by omega) xl).imp_right And.left
    · exact (S.saturates (show (1:Fin 3)≠0 by decide) (show (1:Fin 3)≠2 by decide)
        (show (0:Fin 3)≠2 by decide) (by omega) xl).imp_right And.left
    · exact (S.saturates (show (2:Fin 3)≠0 by decide) (show (2:Fin 3)≠1 by decide)
        (show (0:Fin 3)≠1 by decide) (by omega) xl).imp_right And.left
  have back (l : Fin 3) : S.B l ⊆ S.A l := by
    obtain ⟨x,xh⟩ := card_pos.mp (S.apos 0)
    obtain ⟨y,yh⟩ := card_pos.mp (S.apos 1)
    have h0 := S.saturates (show (0:Fin 3)≠1 by decide) (show (0:Fin 3)≠2 by decide)
      (show (1:Fin 3)≠2 by decide) (by omega) xh
    have h1 := S.saturates (show (1:Fin 3)≠0 by decide) (show (1:Fin 3)≠2 by decide)
      (show (0:Fin 3)≠2 by decide) (by omega) yh
    fin_cases l
    · exact h1.2.2.1
    · exact h0.2.2.1
    · exact h0.2.2.2
  let E (l : Fin 3) := S.H l \ S.A l
  have counted (l : Fin 3) : (E l).card+2=(S.H l).card := by
    have add := card_sdiff_add_card_eq_card (filter_subset (G.Adj a) (S.H l))
    change (E l).card+(S.A l).card=(S.H l).card at add
    rwa [cs l] at add
  have sub (l : Fin 3) : E l⊆S.D l := by
    intro y hy
    obtain ⟨yl,ya⟩ := mem_sdiff.mp hy
    obtain ⟨x,xl⟩ := card_pos.mp (S.apos l)
    have ne : x≠y := fun e => ya (e ▸ xl)
    have xy := (common l xl).1 y yl |>.resolve_left ne
    have ay : ¬G.Adj a y := fun e => ya (mem_filter.mpr ⟨yl,e⟩)
    have an : a≠y := fun e => (S.off l).1 (e.symm ▸ yl)
    exact mem_filter.mpr ⟨yl,mem_d2.mpr (dist_two S.con an ay (mem_filter.mp xl).2 xy)⟩
  have dpos (l : Fin 3) : 1≤(S.D l).card := by
    have h := counted l
    have r := sizes l
    have c := card_le_card (sub l)
    omega
  have big (l : Fin 3) {x : V} (xe : x∈E l) (high : 4≤G.degree x) :
      3≤(S.D l).card := by
    obtain ⟨xl,xa⟩ := mem_sdiff.mp xe
    have xna : ¬G.Adj x a := fun e => xa (mem_filter.mpr ⟨xl,e.symm⟩)
    have xnb : ¬G.Adj x b := fun e => xa (back l (mem_filter.mpr ⟨xl,e.symm⟩))
    have ns : G.neighborFinset x ⊆ (S.H l).erase x := by
      intro y hy
      have xy := (mem_neighborFinset G x y).mp hy
      rcases S.closed l x xl y xy with rfl|rfl|yl
      · exact (xna xy).elim
      · exact (xnb xy).elim
      · exact mem_erase.mpr ⟨xy.ne.symm,yl⟩
    have c := card_le_card ns
    rw [card_neighborFinset_eq_degree,card_erase_of_mem xl] at c
    have ec := counted l
    have eD := card_le_card (sub l)
    omega
  obtain ⟨x,xe⟩ := card_pos.mp (show 0<(E 0).card by
    have h := counted 0
    have r := sizes 0
    omega)
  obtain ⟨y,ye⟩ := card_pos.mp (show 0<(E 1).card by
    have h := counted 1
    have r := sizes 1
    omega)
  have ne : x≠y := fun e => disjoint_left.mp (S.dis 0 1 (by decide))
    (mem_sdiff.mp xe).1 (e.symm ▸ (mem_sdiff.mp ye).1)
  have d0 := dpos 0
  have d1 := dpos 1
  have d2 := dpos 2
  have cap := S.dsum_le (show (0:Fin 3)≠1 by decide) (show (0:Fin 3)≠2 by decide)
    (show (1:Fin 3)≠2 by decide)
  rcases S.degree x y ne with high|high
  · have big0 := big 0 xe high
    omega
  · have big1 := big 1 ye high
    omega

private theorem no_122_aux {i j k : Fin 3} (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (oi : (S.A i).card=1) (tj : (S.A j).card=2) (tk : (S.A k).card=2)
    (bj : (S.B j).card=1) (sizes : ∀ l, 3≤(S.H l).card) : False := by
  obtain ⟨_,⟨v,vB,vA⟩,subj,subk⟩ := S.saturated_singleton ij ik jk oi (by omega) (sizes i)
  have high := (S.high_common_of_122 ij ik jk oi tj tk (sizes i)).2
  obtain ⟨u,uA,uB⟩ : ∃ u∈S.A j,u∉S.B j := by
    by_cases ex : ∃ u∈S.A j,u∉S.B j
    · exact ex
    exfalso
    have sub : S.A j⊆S.B j := fun u hu => Classical.byContradiction (fun h => ex ⟨u,hu,h⟩)
    have le := card_le_card sub
    omega
  have low : ¬4≤G.degree u := fun hh => uB (high j u uA hh)
  have goodk : S.A k⊆S.B k := by
    intro w wk
    have ne : u≠w := fun e => disjoint_left.mp (S.dis j k jk)
      (mem_filter.mp uA).1 (e.symm ▸ (mem_filter.mp wk).1)
    exact high k w wk ((S.degree u w ne).resolve_left low)
  have bk : (S.B k).card=2 := by rw [Subset.antisymm subk goodk,tk]
  have bi : (S.B i).card=2 := by
    have cp := S.swap.pair_cap ij.symm jk ik
    change (S.B i).card+(S.B k).card≤4 at cp
    obtain ⟨x,xi,_,xb⟩ := (S.saturated_singleton ij ik jk oi (by omega) (sizes i)).1
    have xB : x∈S.B i := mem_filter.mpr ⟨(mem_filter.mp xi).1,xb⟩
    have ne : x≠v := fun e => vA (e ▸ xi)
    have ge := one_lt_card.mpr ⟨x,xB,v,vB,ne⟩
    omega
  have highb := (S.swap.high_common_of_122 ij.symm jk ik bj bi bk (sizes j)).2
  have lowv : ¬4≤G.degree v := fun hv => vA (highb i v vB hv)
  have ne : u≠v := fun e => disjoint_left.mp (S.dis j i ij.symm)
    (mem_filter.mp uA).1 (e.symm ▸ (mem_filter.mp vB).1)
  exact (S.degree u v ne).elim low lowv

private theorem no_122 {i j k : Fin 3} (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (oi : (S.A i).card=1) (tj : (S.A j).card=2) (tk : (S.A k).card=2)
    (sizes : ∀ l, 3≤(S.H l).card) : False := by
  obtain ⟨_,⟨v,vB,vA⟩,subj,subk⟩ := S.saturated_singleton ij ik jk oi (by omega) (sizes i)
  by_cases bj : (S.B j).card=1
  · exact S.no_122_aux ij ik jk oi tj tk bj sizes
  by_cases bk : (S.B k).card=1
  · exact S.no_122_aux ik ij jk.symm oi tk tj bk sizes
  have bj' := card_le_card subj
  have bk' := card_le_card subk
  have bj'' := S.swap.apos j
  have bk'' := S.swap.apos k
  change 1≤(S.B j).card at bj''
  change 1≤(S.B k).card at bk''
  have sat := S.swap.saturates ij ik jk (by change (S.B j).card+(S.B k).card=4; omega) vB
  exact vA (mem_filter.mpr ⟨(mem_filter.mp vB).1,sat.2.1⟩)

private theorem small_shape (sizes : ∀ l, 3≤(S.H l).card) :
    (S.A 0).card+(S.A 1).card+(S.A 2).card≤4 := by
  have cp0 := S.pair_cap (show (0:Fin 3)≠1 by decide) (show (0:Fin 3)≠2 by decide)
    (show (1:Fin 3)≠2 by decide)
  have cp1 := S.pair_cap (show (1:Fin 3)≠0 by decide) (show (1:Fin 3)≠2 by decide)
    (show (0:Fin 3)≠2 by decide)
  have cp2 := S.pair_cap (show (2:Fin 3)≠0 by decide) (show (2:Fin 3)≠1 by decide)
    (show (0:Fin 3)≠1 by decide)
  have h0 := S.apos 0
  have h1 := S.apos 1
  have h2 := S.apos 2
  have shape :
      (S.A 0).card+(S.A 1).card+(S.A 2).card≤4 ∨
      ((S.A 0).card=2 ∧ (S.A 1).card=2 ∧ (S.A 2).card=2) ∨
      ((S.A 0).card=1 ∧ (S.A 1).card=1 ∧ (S.A 2).card=3) ∨
      ((S.A 0).card=1 ∧ (S.A 2).card=1 ∧ (S.A 1).card=3) ∨
      ((S.A 1).card=1 ∧ (S.A 2).card=1 ∧ (S.A 0).card=3) ∨
      ((S.A 0).card=1 ∧ (S.A 1).card=2 ∧ (S.A 2).card=2) ∨
      ((S.A 1).card=1 ∧ (S.A 0).card=2 ∧ (S.A 2).card=2) ∨
      ((S.A 2).card=1 ∧ (S.A 0).card=2 ∧ (S.A 1).card=2) := by omega
  rcases shape with sm|⟨e0,e1,e2⟩|⟨e0,e1,e2⟩|⟨e0,e2,e1⟩|⟨e1,e2,e0⟩|
    ⟨e0,e1,e2⟩|⟨e1,e0,e2⟩|⟨e2,e0,e1⟩
  · exact sm
  · exact (S.no_222 e0 e1 e2 sizes).elim
  · exact (S.no_113 (by decide) (by decide) (by decide) e0 e1 e2 sizes).elim
  · exact (S.no_113 (by decide) (by decide) (by decide) e0 e2 e1 sizes).elim
  · exact (S.no_113 (by decide) (by decide) (by decide) e1 e2 e0 sizes).elim
  · exact (S.no_122 (by decide) (by decide) (by decide) e0 e1 e2 sizes).elim
  · exact (S.no_122 (by decide) (by decide) (by decide) e1 e0 e2 sizes).elim
  · exact (S.no_122 (by decide) (by decide) (by decide) e2 e0 e1 sizes).elim

private theorem low_side (sm : (S.A 0).card+(S.A 1).card+(S.A 2).card≤4) :
    ∃ i : Fin 3, ∀ x∈S.A i, ¬4≤G.degree x := by
  classical
  let Good (i : Fin 3) := ∃ x∈S.A i, 4≤G.degree x
  by_cases h : ∀ i, Good i
  · exfalso
    have lo (i : Fin 3) : 3≤(S.A i).card+(S.D i).card := by
      obtain ⟨x,xi,high⟩ := h i
      have deg := S.degree_bound xi
      by_cases e : G.Adj x b <;> simp [e] at deg <;> omega
    have a0 := lo 0
    have a1 := lo 1
    have a2 := lo 2
    have cap := S.Dsum
    have c := S.d2 a
    omega
  · obtain ⟨i,good⟩ := not_forall.mp h
    exact ⟨i,fun x hx high => good ⟨x,hx,high⟩⟩

/-- Three nontrivial components are impossible. -/
theorem no_three_nonsingleton (sizes : ∀ i, 3 ≤ (S.H i).card) : False := by
  obtain ⟨i,li⟩ := S.low_side (S.small_shape sizes)
  obtain ⟨j,lj⟩ := S.swap.low_side (S.swap.small_shape sizes)
  obtain ⟨x,xi⟩ := card_pos.mp (S.apos i)
  obtain ⟨y,yj⟩ := card_pos.mp (S.swap.apos j)
  have xy : x=y := Classical.byContradiction (fun ne => (S.degree x y ne).elim (li x xi) (lj y yj))
  subst y
  have ij : i=j := Classical.byContradiction (fun ne => disjoint_left.mp (S.dis i j ne)
    (mem_filter.mp xi).1 (mem_filter.mp yj).1)
  subst j
  have sub : S.Ports i⊆{x} := by
    intro w wi
    apply mem_singleton.mpr
    obtain ⟨wh,aw|bw⟩ := mem_filter.mp wi
    · exact Classical.byContradiction (fun ne =>
        (S.degree w x ne).elim (li w (mem_filter.mpr ⟨wh,aw⟩)) (li x xi))
    · exact Classical.byContradiction (fun ne =>
        (S.degree w x ne).elim (lj w (mem_filter.mpr ⟨wh,bw⟩)) (li x xi))
  have cap := card_le_card sub
  rw [card_singleton] at cap
  have ge := S.plenty i (by have h := sizes i; omega)
  change 2≤(S.Ports i).card at ge
  omega

#print axioms no_three_nonsingleton
end
end Graffiti189LongestPath.FourCut.Three.Sides
