import ForeignSaturation189
namespace Graffiti189LongestPath.CrossSaturation.Split
open SimpleGraph SimpleGraph.Walk Finset
open private d2 local_card few_steps from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

private theorem local_via_cut_le_two (hc : G.Connected)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    {x : V} (ax : G.Adj a x) (bx : G.Adj b x)
    (small : (S.L ∩ DistanceTwo G x).card < 2)
    {y : V} (yl : y ∈ S.L) : G.dist x y ≤ 2 := by
  classical
  let D := S.L ∩ DistanceTwo G x
  let W : Set V := (↑D : Set V)ᶜ
  by_contra bad
  have xo : x ∈ W := by simp [W,D,DistanceTwo,SimpleGraph.dist_self]
  have yo : y ∈ W := by
    simp only [W,D,Set.mem_compl_iff,mem_coe,mem_inter,DistanceTwo,mem_filter,mem_univ,true_and]
    omega
  obtain ⟨q⟩ := (conn D small).preconnected ⟨y,yo⟩ ⟨x,xo⟩
  have propagate {u v : W} (p : (G.induce W).Walk u v) :
      ((u : V) ∈ S.L ∧ 3 ≤ G.dist x u.val) →
        ((v : V) ∈ S.L ∧ 3 ≤ G.dist x v.val) := by
    induction p with
    | nil => exact id
    | @cons u w v e p ih =>
      intro ⟨ul,ud⟩
      change G.Adj u.val w.val at e
      apply ih
      have step := hc.dist_triangle (u:=x) (v:=w.val) (w:=u.val)
      have one := dist_eq_one_iff_adj.mpr e.symm
      have wl : w.val ∈ S.L := by
        rcases S.cover w.val with h|h|h|h
        · have h1 : G.dist x w.val = 1 := h.symm ▸ dist_eq_one_iff_adj.mpr ax.symm
          have up : G.dist x u.val ≤ 1+1 := by rwa [h1,one] at step
          omega
        · have h1 : G.dist x w.val = 1 := h.symm ▸ dist_eq_one_iff_adj.mpr bx.symm
          have up : G.dist x u.val ≤ 1+1 := by rwa [h1,one] at step
          omega
        · exact h
        · exact (S.cross _ ul _ h e).elim
      have no2 : G.dist x w.val ≠ 2 := by
        intro h
        exact w.property (mem_inter.mpr ⟨wl,by simp [DistanceTwo,h]⟩)
      exact ⟨wl,by omega⟩
  have hy : 3 ≤ G.dist x y := by omega
  have h := (propagate q ⟨yl,hy⟩).2
  change 3 ≤ G.dist x x at h
  simp [SimpleGraph.dist_self] at h

private theorem inner_exception_card (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 5)
    {x : V} (xl : x∈S.L) (ax : G.Adj a x) (bx : G.Adj b x)
    (three : S.foreignPorts.card=3) :
    ((S.L ∩ DistanceTwo G x) ∪ ((univ : Finset V).filter fun z=>G.dist x z=4)).card ≤ 1 := by
  classical
  let E := (S.L ∩ DistanceTwo G x) ∪ ((univ : Finset V).filter fun z=>G.dist x z=4)
  have sub : insert x (S.foreignPorts ∪ E) ⊆ EvenFrom G x := by
    intro z hz
    rcases mem_insert.mp hz with rfl|hz
    · simp [EvenFrom,SimpleGraph.dist_self]
    rcases mem_union.mp hz with hz|hz
    · obtain ⟨zr,az|bz⟩ := mem_filter.mp hz
      · have hd := d2 (x:=x) (z:=z) hc (fun e=>disjoint_left.mp S.dis xl (e ▸ zr)) (S.cross _ xl _ zr) ax.symm az
        have h := (mem_filter.mp hd).2
        simp [EvenFrom,h]
      · have hd := d2 (x:=x) (z:=z) hc (fun e=>disjoint_left.mp S.dis xl (e ▸ zr)) (S.cross _ xl _ zr) bx.symm bz
        have h := (mem_filter.mp hd).2
        simp [EvenFrom,h]
    rcases mem_union.mp hz with d|f
    · have h := (mem_filter.mp (mem_inter.mp d).2).2
      simp [EvenFrom,h]
    · have h := (mem_filter.mp f).2
      simp only [EvenFrom,mem_filter,mem_univ,true_and,h]
      decide
  have dis : Disjoint S.foreignPorts E := by
    apply disjoint_left.mpr
    intro z hf he
    obtain ⟨zr,az|bz⟩ := mem_filter.mp hf
    · rcases mem_union.mp he with l|r
      · exact disjoint_left.mp S.dis (mem_inter.mp l).1 zr
      have hd := d2 (x:=x) (z:=z) hc (fun e=>disjoint_left.mp S.dis xl (e ▸ zr)) (S.cross _ xl _ zr) ax.symm az
      have h := (mem_filter.mp hd).2
      have h' := (mem_filter.mp r).2
      omega
    · rcases mem_union.mp he with l|r
      · exact disjoint_left.mp S.dis (mem_inter.mp l).1 zr
      have hd := d2 (x:=x) (z:=z) hc (fun e=>disjoint_left.mp S.dis xl (e ▸ zr)) (S.cross _ xl _ zr) bx.symm bz
      have h := (mem_filter.mp hd).2
      have h' := (mem_filter.mp r).2
      omega
  have xo : x ∉ S.foreignPorts ∪ E := by
    intro h
    rcases mem_union.mp h with f|e
    · exact disjoint_left.mp S.dis xl (mem_filter.mp f).1
    rcases mem_union.mp e with l|r
    · have h := (mem_filter.mp (mem_inter.mp l).2).2
      simp [SimpleGraph.dist_self] at h
    · have h := (mem_filter.mp r).2
      simp [SimpleGraph.dist_self] at h
  have h := card_le_card sub
  rw [card_insert_of_not_mem xo,card_union_of_disjoint dis,three] at h
  have hx := even x
  change E.card ≤ 1
  omega

theorem order_le_of_three_foreign_ports_common (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 5) (ab : a≠b)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (common : ∃ x∈S.L, G.Adj a x ∧ G.Adj b x)
    (three : S.foreignPorts.card=3) (localSmall : S.localA.card≤3) :
    Fintype.card V ≤ (if G.Adj a b then 17 else 15) := by
  classical
  obtain ⟨x,xl,ax,bx⟩ := common
  let E := (S.L ∩ DistanceTwo G x) ∪ ((univ : Finset V).filter fun z=>G.dist x z=4)
  have ec : E.card ≤ 1 := inner_exception_card S hc even xl ax bx three
  have l2 : (S.L ∩ DistanceTwo G x).card < 2 := by
    have incl : S.L ∩ DistanceTwo G x ⊆ E := subset_union_left
    have ca := card_le_card incl
    omega
  have sub : S.foreignPorts ⊆ DistanceTwo G x := by
    intro z hz
    obtain ⟨zr,az|bz⟩ := mem_filter.mp hz
    · exact d2 hc (fun e=>disjoint_left.mp S.dis xl (e ▸ zr)) (S.cross _ xl _ zr) ax.symm az
    · exact d2 hc (fun e=>disjoint_left.mp S.dis xl (e ▸ zr)) (S.cross _ xl _ zr) bx.symm bz
  have rad (y : V) : G.dist x y ≤ 4 := by
    by_contra bad
    have dthree := card_le_card sub
    have hy : 5 ≤ G.dist x y := by omega
    have two := twoEvenLayers_of_radius_five hc 2 conn hy
    have b := even x
    omega
  have ac := distanceTwo_le_of_even 4 a (even a)
  have bc := distanceTwo_le_of_even 4 b (even b)
  let U := (S.localA ∪ S.foreignPorts) ∪ ((DistanceTwo G a ∪ DistanceTwo G b) ∪ E)
  have il (z : V) (zl : z∈S.L) : z∈U := by
    simp only [U,mem_union]
    by_cases az : G.Adj a z
    · exact Or.inl (Or.inl (mem_filter.mpr ⟨zl,az⟩))
    right
    have upper := local_via_cut_le_two S hc conn ax bx l2 zl
    by_cases xz : x=z
    · subst z
      exact (az ax).elim
    by_cases edge : G.Adj x z
    · exact Or.inl (Or.inl (d2 hc (fun e=>S.leftOff.1 (e ▸ zl)) az ax edge))
    have gt := hc.one_lt_dist_of_ne_of_not_adj xz edge
    exact Or.inr (mem_union.mpr (Or.inl (mem_inter.mpr ⟨zl,by simp [DistanceTwo,show G.dist x z=2 by omega]⟩)))
  have ir (z : V) (zr : z∈S.R) : z∈U := by
    simp only [U,mem_union]
    by_cases four : G.dist x z=4
    · exact Or.inr (Or.inr (mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _,four⟩))))
    obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist x z
    have r := rad z
    rcases few_steps S xl zr q (by omega) with p|⟨w,wr,p,wz⟩
    · exact Or.inl (Or.inr (mem_filter.mpr ⟨zr,p⟩))
    by_cases hz : G.Adj a z ∨ G.Adj b z
    · exact Or.inl (Or.inr (mem_filter.mpr ⟨zr,hz⟩))
    simp only [not_or] at hz
    exact Or.inr (Or.inl (p.imp
      (fun e=>d2 hc (fun eq=>S.rightOff.1 (eq ▸ zr)) hz.1 e wz)
      (fun e=>d2 hc (fun eq=>S.rightOff.2 (eq ▸ zr)) hz.2 e wz)))
  have u1 := card_union_le S.localA S.foreignPorts
  have u2 := card_union_le (DistanceTwo G a) (DistanceTwo G b)
  have u3 := card_union_le (DistanceTwo G a ∪ DistanceTwo G b) E
  have u4 := card_union_le (S.localA ∪ S.foreignPorts) ((DistanceTwo G a ∪ DistanceTwo G b) ∪ E)
  have u5 : U.card≤15 := by dsimp only [U]; omega
  by_cases adj : G.Adj a b
  · simp only [adj,if_true]
    have cov : (univ : Finset V) ⊆ insert a (insert b U) := by
      intro z _
      rcases S.cover z with rfl|rfl|zl|zr
      · simp
      · simp
      · simp [il z zl]
      · simp [ir z zr]
    have c := card_le_card cov
    rw [card_univ] at c
    have c1 := card_insert_le a (insert b U)
    have c2 := card_insert_le b U
    omega
  · simp only [adj,if_false]
    have ba := d2 hc ab adj ax bx.symm
    have ab' := d2 hc ab.symm (fun e=>adj e.symm) bx ax.symm
    have cov : (univ : Finset V) ⊆ U := by
      intro z _
      rcases S.cover z with rfl|rfl|zl|zr
      · simp [U,ab']
      · simp [U,ba]
      · exact il z zl
      · exact ir z zr
    exact (by simpa using (card_le_card cov).trans u5)


theorem traceable_of_three_or_more_foreign_ports (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 5) (ab : a≠b)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    (common : ∃ x∈S.L, G.Adj a x ∧ G.Adj b x)
    (many : 3 ≤ S.foreignPorts.card)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  have small : Fintype.card V≤17 := by
    obtain ⟨x,xl,ax,bx⟩ := common
    have sub : S.foreignPorts ⊆ DistanceTwo G x := by
      intro z hz
      obtain ⟨zr,az|bz⟩ := mem_filter.mp hz
      · exact d2 hc (fun e=>disjoint_left.mp S.dis xl (e ▸ zr)) (S.cross _ xl _ zr) ax.symm az
      · exact d2 hc (fun e=>disjoint_left.mp S.dis xl (e ▸ zr)) (S.cross _ xl _ zr) bx.symm bz
    have cap := distanceTwo_le_of_even 4 x (even x)
    have portCap := card_le_card sub
    by_cases four : S.foreignPorts.card=4
    · have h := S.order_le_of_four_foreign_ports hc even ab ⟨x,xl,ax,bx⟩ four
      split at h <;> omega
    have three : S.foreignPorts.card=3 := by omega
    obtain ⟨z,zr,az⟩ := rightA
    have ac := local_card S 4 hc even ⟨z,mem_filter.mpr ⟨zr,az⟩⟩
    by_cases sat : S.localA.card=4
    · let T : Graffiti189LongestPath.CrossSaturation.Split G a b :=
        ⟨S.R,S.L,S.dis.symm,S.rightOff,S.leftOff,rightConnected,
         (fun y yr z zl yz=>S.cross _ zl _ yr yz.symm),⟨z,zr,az⟩,rightB,
         (fun y=>by simpa only [or_comm (b:=y∈S.R) (a:=y∈S.L)] using S.cover y)⟩
      have h := T.order_le_fourteen_of_four_shared_ports hc even sat
      omega
    have h := order_le_of_three_foreign_ports_common S hc even ab conn ⟨x,xl,ax,bx⟩ three (by omega)
    split at h <;> omega
  exact Graffiti189LongestPath.TwoCut.traceable_of_order_le_seventeen hc even conn degree small

#print axioms order_le_of_three_foreign_ports_common
#print axioms traceable_of_three_or_more_foreign_ports
end Graffiti189LongestPath.CrossSaturation.Split
