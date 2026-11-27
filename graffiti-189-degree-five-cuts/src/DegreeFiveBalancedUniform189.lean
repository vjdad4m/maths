import DegreeFiveBalancedBridge189
import DegreeFiveSmallSides189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private left_boundary from AdjacentCut189
open private not_common cut_not_adj secondA_right_and_left_le_five from DegreeFiveFourPort189
open private lengths_take_drop from SmallSeparator189
open private tight_high_port_neighbors from DegreeFiveBalancedBridge189
open private count_cut_a from DegreeFiveBridgeSize189
open private left_high_inside from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

private theorem tight_high_port_target_eq (hc : G.Connected) (far : 3≤G.dist a b)
    {x : V} (xp : x∈S.localA) (high : 5≤G.degree x)
    (tight : S.localA.card+(secondA G S.L a).card=5) :
    G.neighborFinset x = insert a (S.localA.erase x ∪ secondA G S.L a) := by
  classical
  obtain ⟨xl,ax⟩ := mem_filter.mp xp
  let F := insert a ((S.localA.erase x) ∪ secondA G S.L a)
  have sub : G.neighborFinset x⊆F := by
    intro y hy
    have xy := (mem_neighborFinset G x y).mp hy
    rcases left_boundary S x xl y xy with rfl|rfl|yl
    · simp [F]
    · exact (not_common far ax xy.symm).elim
    apply mem_insert_of_mem
    by_cases ay : G.Adj a y
    · exact mem_union_left _ (mem_erase.mpr ⟨xy.ne.symm,mem_filter.mpr ⟨yl,ay⟩⟩)
    have ne : a≠y := fun e=>S.leftOff.1 (e.symm ▸ yl)
    exact mem_union_right _ (mem_inter.mpr ⟨yl,d2 hc ne ay ax xy⟩)
  have limit : F.card≤5 := by
    have u := card_insert_le a (S.localA.erase x ∪ secondA G S.L a)
    have v := card_union_le (S.localA.erase x) (secondA G S.L a)
    rw [card_erase_of_mem xp] at v
    have pos := card_pos.mpr ⟨_,xp⟩
    change F.card≤_ at u
    omega
  exact eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree]; exact limit.trans high)


private theorem mixed_five_side_high_aux (hc : G.Connected) (far : 3≤G.dist a b)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (Ahigh : ∀ u∈S.localA,5≤G.degree u)
    (Aupper : S.localA.card≤3)
    (tightA : S.localA.card+(secondA G S.L a).card=5)
    (tightB : (S.L.filter (G.Adj b)).card+(secondA G S.L b).card=5)
    (five : S.localA.card+(S.L.filter (G.Adj b)).card=5)
    (br : portBridge S) (rad : ∀ z,G.dist b z≤3) :
    ∀ u∈S.L,5≤G.degree u := by
  classical
  let A := S.localA
  let B := S.L.filter (G.Adj b)
  let E := secondA G S.L a
  let F := secondA G S.L b
  let I := inner G S.L a b
  let T := S.flip
  change A.card+B.card=5 at five
  change A.card+E.card=5 at tightA
  change B.card+F.card=5 at tightB
  have ab' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := br
  have yE : y∈E := by
    have na : ¬G.Adj a y := fun e=>not_common far e by'
    have ne : a≠y := fun e=>S.leftOff.1 (e.symm ▸ yl)
    exact mem_inter.mpr ⟨yl,d2 hc ne na ax xy⟩
  have aF : A⊆F := by
    intro v va
    obtain ⟨vl,av⟩ := mem_filter.mp va
    have c := tight_high_port_neighbors S hc far va (Ahigh _ va) tightA yE
    have vy := (mem_neighborFinset G v y).mp c
    have ne : b≠v := fun e=>S.leftOff.2 (e.symm ▸ vl)
    exact mem_inter.mpr ⟨vl,d2 hc ne (not_common far av) by' vy.symm⟩
  have F_eq : F=A := (eq_of_subset_of_card_le aF (by omega)).symm
  have xF : x∈F := aF (mem_filter.mpr ⟨xl,ax⟩)
  have bE (v : V) (vb : v∈B) (hi : 5≤G.degree v) : v∈E := by
    obtain ⟨vl,bv⟩ := mem_filter.mp vb
    have e := tight_high_port_neighbors T hc ab' vb hi tightB xF
    have vx := (mem_neighborFinset G v x).mp e
    have ne : a≠v := fun e=>S.leftOff.1 (e.symm ▸ vl)
    exact mem_inter.mpr ⟨vl,d2 hc ne (not_common ab' bv) ax vx.symm⟩
  have disBI : Disjoint B I := by
    apply disjoint_left.mpr
    intro v vb vi
    exact (mem_filter.mp vi).2.2 (mem_filter.mp vb).2
  have iE : I⊆E := by
    intro w wi
    obtain ⟨wl,aw,bw⟩ := mem_filter.mp wi
    have wbn : b≠w := fun e=>S.leftOff.2 (e.symm ▸ wl)
    have two : 1<G.dist b w := hc.one_lt_dist_of_ne_of_not_adj wbn bw
    have ntwo : G.dist b w≠2 := by
      intro e
      have wf : w∈F := mem_inter.mpr ⟨wl,by simp [DistanceTwo,e]⟩
      rw [F_eq] at wf
      exact aw (mem_filter.mp wf).2
    have b3 : G.dist b w=3 := by have cc := rad w; omega
    obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist b w
    have q3 : q.length=3 := ql.trans b3
    let v := q.getVert 2
    have vw : G.Adj v w := by
      have e := q.adj_getVert_succ (i:=2) (by omega)
      rw [show 2+1=3 by decide,←q3, q.getVert_length] at e
      exact e
    have vl : v∈S.L := by
      rcases S.cover v with va|vb|vl|vr
      · exact (aw (va ▸ vw)).elim
      · exact (bw (vb ▸ vw)).elim
      · exact vl
      exact (S.cross _ wl _ vr vw.symm).elim
    have bd : G.dist b v≤2 := by
      have e := G.dist_le (q.take 2)
      have le : 2≤q.length := by omega
      obtain ⟨tl,_⟩ := lengths_take_drop q 2 le
      rw [tl] at e
      exact e
    have bnv : ¬G.Adj b v := by
      intro bv
      have e := G.dist_le (Walk.cons bv (Walk.cons vw .nil))
      simp at e
      omega
    have bvne : b≠v := fun e=>S.leftOff.2 ((congrArg (fun z=>z∈S.L) e.symm).mp vl)
    have bg := hc.one_lt_dist_of_ne_of_not_adj bvne bnv
    have vf : v∈F := mem_inter.mpr ⟨vl,by simp [DistanceTwo,show G.dist b v=2 by omega]⟩
    rw [F_eq] at vf
    have av := (mem_filter.mp vf).2
    have wane : a≠w := fun e=>S.leftOff.1 (e.symm ▸ wl)
    exact mem_inter.mpr ⟨wl,d2 hc wane aw av vw⟩
  have noe : I.card=0 := by
    by_cases lowB : ∃ z∈B,¬5≤G.degree z
    · obtain ⟨u,ub,ulo⟩ := lowB
      have bHi : B.erase u⊆E := by
        intro v vv
        obtain ⟨ne,vb⟩ := mem_erase.mp vv
        exact bE _ vb ((degree _ _ ne).resolve_right ulo)
      have c := card_le_card (union_subset bHi iE)
      rw [card_union_of_disjoint (disBI.mono_left (erase_subset _ _)),card_erase_of_mem ub] at c
      have ub1 := card_pos.mpr ⟨u,ub⟩
      have small : I.card≤1 := by omega
      apply Classical.byContradiction
      intro bad
      obtain ⟨w,wi⟩ := card_pos.mp (Nat.pos_of_ne_zero bad)
      obtain ⟨wl,aw,bw⟩ := mem_filter.mp wi
      have wn : w≠u := fun h=>disjoint_left.mp disBI ub (h ▸ wi)
      have wh := (degree _ _ wn).resolve_right ulo
      have wsub : G.neighborFinset w⊆A := by
        intro z zz
        have wz := (mem_neighborFinset G w z).mp zz
        rcases left_boundary S w wl z wz with rfl|rfl|zl
        · exact (aw wz.symm).elim
        · exact (bw wz.symm).elim
        by_cases az : G.Adj a z
        · exact mem_filter.mpr ⟨zl,az⟩
        by_cases bz : G.Adj b z
        · have bne : b≠w := fun e=>S.leftOff.2 (e.symm ▸ wl)
          have wf : w∈F := mem_inter.mpr ⟨wl,d2 hc bne bw bz wz.symm⟩
          rw [F_eq] at wf
          exact (aw (mem_filter.mp wf).2).elim
        have zi : z∈I := mem_filter.mpr ⟨zl,az,bz⟩
        exact (wz.ne (card_le_one.mp small _ wi _ zi)).elim
      have n := card_le_card wsub
      rw [card_neighborFinset_eq_degree] at n
      change A.card≤3 at Aupper
      omega
    have allB : B⊆E := by
      intro v vb
      apply bE v vb
      exact Classical.byContradiction (fun no=>lowB ⟨v,vb,no⟩)
    have m := card_le_card (union_subset allB iE)
    rw [card_union_of_disjoint disBI] at m
    omega
  have noI : ∀ z,z∉I := by
    intro z zi
    have c := card_pos.mpr ⟨z,zi⟩
    omega
  have eB : E⊆B := by
    intro z ze
    obtain ⟨zl,z2⟩ := mem_inter.mp ze
    have za : ¬G.Adj a z := by
      intro az
      have one := dist_eq_one_iff_adj.mpr az
      have two := (mem_filter.mp z2).2
      omega
    by_cases bz : G.Adj b z
    · exact mem_filter.mpr ⟨zl,bz⟩
    exact (noI z (mem_filter.mpr ⟨zl,za,bz⟩)).elim
  have E_eq : E=B := eq_of_subset_of_card_le eB (by omega)
  intro u ul
  by_cases au : G.Adj a u
  · exact Ahigh u (mem_filter.mpr ⟨ul,au⟩)
  by_cases bu : G.Adj b u
  · apply Classical.byContradiction
    intro low
    have ub : u∈B := mem_filter.mpr ⟨ul,bu⟩
    have uE : u∈E := E_eq.symm ▸ ub
    have hsub : insert b (A∪B.erase u) ⊆ G.neighborFinset u := by
      intro v vv
      rcases mem_insert.mp vv with rfl|hh
      · exact (mem_neighborFinset _ _ _).mpr bu.symm
      rcases mem_union.mp hh with va|vb
      · have n := tight_high_port_neighbors S hc far va (Ahigh _ va) tightA uE
        exact (mem_neighborFinset _ _ _).mpr ((mem_neighborFinset _ _ _).mp n).symm
      have ne := (mem_erase.mp vb).1
      have bp := (mem_erase.mp vb).2
      have dh := (degree _ _ ne).resolve_right low
      have t := tight_high_port_target_eq T hc ab' bp dh tightB
      have uv : u∈G.neighborFinset v := by
        rw [t]
        exact mem_insert_of_mem (mem_union_left _ (mem_erase.mpr ⟨ne.symm,ub⟩))
      exact (mem_neighborFinset _ _ _).mpr ((mem_neighborFinset _ _ _).mp uv).symm
    have n := card_le_card hsub
    have off : b∉A∪B.erase u := by
      intro h
      rcases mem_union.mp h with ha|hb
      · exact S.leftOff.2 (mem_filter.mp ha).1
      exact S.leftOff.2 (mem_filter.mp (mem_of_mem_erase hb)).1
    have dis : Disjoint A (B.erase u) := by
      apply disjoint_left.mpr
      intro v va vb
      exact not_common far (mem_filter.mp va).2 (mem_filter.mp (mem_of_mem_erase vb)).2
    rw [card_insert_of_not_mem off,card_union_of_disjoint dis,card_erase_of_mem ub,
      card_neighborFinset_eq_degree] at n
    have pos := card_pos.mpr ⟨u,ub⟩
    omega
  exact (noI u (mem_filter.mpr ⟨ul,au,bu⟩)).elim

/-- Balanced five-attachment bridge case, without a hypothesis about
the location of the possible low vertex. -/
theorem traceable_of_balanced_five_port_bridge_unconditional_high_side (hc : G.Connected)
    (far : 3≤G.dist a b) (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (a5 : G.degree a=5) (b5 : G.degree b=5)
    (aL : S.localA.card≤3) (aR : S.foreignA.card≤3)
    (bL : (S.L.filter (G.Adj b)).card≤3) (bR : (S.R.filter (G.Adj b)).card≤3)
    (five : S.localA.card+(S.L.filter (G.Adj b)).card=5)
    (bridge : portBridge S) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  let T := S.flip
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have aT := tight_a_second_shells_at_degree_five S hc far even degree rightConnected rightA rightB a5 aL aR
  have bt := tight_a_second_shells_at_degree_five T hc far' even degree rightConnected rightB rightA b5 bL bR
  have high : ∀ u∈S.L,5≤G.degree u := by
    by_cases A : ∀ u∈S.localA,5≤G.degree u
    · exact mixed_five_side_high_aux S hc far degree A aL aT.1 bt.1 five bridge bt.2.2
    push_neg at A
    obtain ⟨x,xA,xlow⟩ := A
    have B (u : V) (ub : u∈T.localA) : 5≤G.degree u := by
      have ne : x≠u := fun e=>not_common far (mem_filter.mp xA).2 (e.symm ▸ (mem_filter.mp ub).2)
      exact (degree x u ne).resolve_left (by omega)
    have bBr : portBridge T := by
      obtain ⟨u,ul,v,vl,au,uv,bv⟩ := bridge
      exact ⟨v,vl,u,ul,bv,uv.symm,au⟩
    have bfive : T.localA.card+(T.L.filter (G.Adj a)).card=5 := by
      change (S.L.filter (G.Adj b)).card+S.localA.card=5
      omega
    exact mixed_five_side_high_aux T hc far' degree B bL bt.1 aT.1 bfive bBr aT.2.2
  exact traceable_of_balanced_five_port_bridge S hc far even degree rightConnected rightA rightB
    a5 b5 aL aR bL bR high five bridge


private theorem traceable_singleton_opposite_four_bridge (hc : G.Connected)
    (far : 3≤G.dist a b) (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (p1 : S.localA.card=1) (p4 : S.foreignA.card=4)
    (q4 : (S.L.filter (G.Adj b)).card=4) (q1 : (S.R.filter (G.Adj b)).card=1)
    (bridge : portBridge S) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  let B := S.L.filter (G.Adj b)
  let Q := S.R.filter (G.Adj b)
  change B.card=4 at q4
  change Q.card=1 at q1
  have L5 := bound_bridge_side_of_opposite_four S hc far even rightConnected rightA rightB p4 bridge
  obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
  have univ := bridge_four_forces_universal S hc far even p4 xl ax xy by'
  have dis : Disjoint S.localA B := by
    apply disjoint_left.mpr
    intro z za zb
    exact not_common far (mem_filter.mp za).2 (mem_filter.mp zb).2
  have inc : S.localA∪B ⊆ S.L := union_subset (filter_subset _ _) (filter_subset _ _)
  have c5 := card_le_card inc
  rw [card_union_of_disjoint dis,p1,q4] at c5
  have eqL := eq_of_subset_of_card_le inc (by rw [card_union_of_disjoint dis,p1,q4]; omega)
  have highU (u : V) (ul : u∈S.L) (hi : 5≤G.degree u) :
      ∀ z∈S.L,z≠u → G.Adj u z := by
    have cn := left_high_inside S far ul hi
    have inc : ArticulationPair.inside G S.L u ⊆ S.L.erase u := by
      intro z zz
      obtain ⟨zl,uz⟩ := mem_filter.mp zz
      exact mem_erase.mpr ⟨uz.ne.symm,zl⟩
    have eq := eq_of_subset_of_card_le inc (by rw [card_erase_of_mem ul]; omega)
    intro z zl zu
    have m : z∈ArticulationPair.inside G S.L u := eq.symm ▸ mem_erase.mpr ⟨zu,zl⟩
    exact (mem_filter.mp m).2
  have every_high (u : V) (ul : u∈S.L) : 5≤G.degree u := by
    apply Classical.byContradiction
    intro ulo
    have con : S.L.erase u ⊆ G.neighborFinset u := by
      intro z zz
      obtain ⟨ne,zl⟩ := mem_erase.mp zz
      have zh := (degree z u ne).resolve_right ulo
      exact (mem_neighborFinset _ _ _).mpr (highU z zl zh u ul ne.symm).symm
    have po : u∈S.localA∪B := eqL.symm ▸ ul
    obtain ⟨w,wo,wu⟩ : ∃ w,w∉S.L ∧ G.Adj u w := by
      rcases mem_union.mp po with pp|pp
      · exact ⟨a,S.leftOff.1,(mem_filter.mp pp).2.symm⟩
      exact ⟨b,S.leftOff.2,(mem_filter.mp pp).2.symm⟩
    have off : w∉S.L.erase u := fun e=>wo (mem_of_mem_erase e)
    have inC : insert w (S.L.erase u) ⊆ G.neighborFinset u :=
      insert_subset_iff.mpr ⟨(mem_neighborFinset _ _ _).mpr wu,con⟩
    have cap := card_le_card inC
    rw [card_insert_of_not_mem off,card_erase_of_mem ul,card_neighborFinset_eq_degree] at cap
    omega
  have d2R : (secondA G S.R a).card≤1 := by
    have e : B ⊆ secondA G S.L a := by
      intro z zz
      obtain ⟨zl,bz⟩ := mem_filter.mp zz
      have az : ¬G.Adj a z := fun e=>not_common far e bz
      have zx := (univ _ zl).resolve_left (fun e=>az (e.symm ▸ ax))
      have ne : a≠z := fun e=>S.leftOff.1 (e.symm ▸ zl)
      exact mem_inter.mpr ⟨zl,d2 hc ne az ax zx⟩
    have z := card_le_card e
    have sum := secondA_right_and_left_le_five S even
    omega
  have Rsmall : S.R.card≤6 := by
    have b2 : G.dist x b=2 := by
      have ne : x≠b := fun e=>S.leftOff.2 (e ▸ xl)
      have no : ¬G.Adj x b := fun e=>not_common far ax e.symm
      exact (mem_filter.mp (d2 hc ne no xy by'.symm)).2
    have xa := dist_eq_one_iff_adj.mpr ax.symm
    have rad := (saturated_at_opposite_four S hc far even p4 xl ax).2
    have cover : S.R ⊆ (S.foreignA∪Q)∪secondA G S.R a := by
      intro z zr
      by_cases az : G.Adj a z
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨zr,az⟩))
      by_cases bz : G.Adj b z
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨zr,bz⟩))
      have d := cross_metric S.L hc xl (fun h=>disjoint_left.mp S.dis h zr) (left_boundary S)
      have a2 := hc.one_lt_dist_of_ne_of_not_adj (show a≠z from fun e=>S.rightOff.1 (e.symm ▸ zr)) az
      have b2' := hc.one_lt_dist_of_ne_of_not_adj (show b≠z from fun e=>S.rightOff.2 (e.symm ▸ zr)) bz
      have d3 := rad z
      exact mem_union_right _ (mem_inter.mpr ⟨zr,by simp [DistanceTwo,show G.dist a z=2 by omega]⟩)
    have n := (card_le_card cover).trans (card_union_le _ _)
    have z := card_union_le S.foreignA Q
    omega
  exact traceable_of_small_sides S far degree (by omega) (by omega) every_high rightConnected rightA rightB

private theorem distance_three_has_bridge (hc : G.Connected) (dist : G.dist a b=3)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x) :
    portBridge S ∨ portBridge (switch S rightConnected rightA rightB) := by
  have far : 3≤G.dist a b := by omega
  have no := cut_not_adj far
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist a b
  have p3 : p.length=3 := pl.trans dist
  let x := p.getVert 1
  let y := p.getVert 2
  have ax : G.Adj a x := by simpa [x] using p.adj_getVert_succ (i:=0) (by omega)
  have xy : G.Adj x y := p.adj_getVert_succ (i:=1) (by omega)
  have yb : G.Adj y b := by
    have e := p.adj_getVert_succ (i:=2) (by omega)
    rw [show 2+1=3 by decide,←p3,p.getVert_length] at e
    exact e
  rcases S.cover x with xx|xx|xl|xr
  · exact (ax.ne xx.symm).elim
  · exact (no (xx ▸ ax)).elim
  · rcases left_boundary S x xl y xy with h|h|yl
    · exact (no (h ▸ yb)).elim
    · exact (yb.ne h).elim
    exact Or.inl ⟨x,xl,y,yl,ax,xy,yb.symm⟩
  have yr : y∈S.R := by
    rcases S.cover y with h|h|yl|yr
    · exact (no (h ▸ yb)).elim
    · exact (yb.ne h).elim
    · exact (S.cross _ yl _ xr xy.symm).elim
    exact yr
  exact Or.inr ⟨x,xr,y,yr,ax,xy,yb.symm⟩

private theorem traceable_balanced_oriented (hc : G.Connected)
    (far : 3≤G.dist a b) (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (a5 : G.degree a=5) (b5 : G.degree b=5)
    (five : S.localA.card+(S.L.filter (G.Adj b)).card=5)
    (bridge : portBridge S) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  let T := switch S rightConnected rightA rightB
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have p := foreign_a_ports_le_four S hc far even
  have p' := foreign_a_ports_le_four T hc far even
  have q := foreign_a_ports_le_four S.flip hc far' even
  have q' := foreign_a_ports_le_four T.flip hc far' even
  change S.localA.card≤4 at p'
  change (S.R.filter (G.Adj b)).card≤4 at q
  change (S.L.filter (G.Adj b)).card≤4 at q'
  have ca := count_cut_a S far
  have cb := count_cut_a S.flip far'
  change G.degree b=(S.L.filter (G.Adj b)).card+(S.R.filter (G.Adj b)).card at cb
  by_cases p1 : S.localA.card=1
  · exact traceable_singleton_opposite_four_bridge S hc far even degree rightConnected rightA rightB
      p1 (by omega) (by omega) (by omega) bridge
  by_cases q1 : (S.L.filter (G.Adj b)).card=1
  · have bBr : portBridge S.flip := by
      obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
      exact ⟨y,yl,x,xl,by',xy.symm,ax⟩
    exact traceable_singleton_opposite_four_bridge S.flip hc far' even degree rightConnected rightB rightA
      q1 (by change (S.R.filter (G.Adj b)).card=4; omega)
      (by change S.localA.card=4; omega) (by change S.foreignA.card=1; omega) bBr
  exact traceable_of_balanced_five_port_bridge_unconditional_high_side S hc far even degree rightConnected
    rightA rightB a5 b5 (by omega) (by omega) (by omega) (by omega) five bridge

/-- Degree-five #189 for every balanced five-attachment distance-three
two-cut with both cut vertices of degree exactly five. Neither shore size,
the location of the low vertex, nor a restriction against four ports is assumed. -/
theorem traceable_of_balanced_cut_degree_five (hc : G.Connected)
    (dist : G.dist a b=3) (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (a5 : G.degree a=5) (b5 : G.degree b=5)
    (five : S.localA.card+(S.L.filter (G.Adj b)).card=5) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  have far : 3≤G.dist a b := by omega
  rcases distance_three_has_bridge S hc dist rightConnected rightA rightB with h|h
  · exact traceable_balanced_oriented S hc far even degree rightConnected rightA rightB a5 b5 five h
  have ca := count_cut_a S far
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have cb := count_cut_a S.flip far'
  change G.degree b=(S.L.filter (G.Adj b)).card+(S.R.filter (G.Adj b)).card at cb
  exact traceable_balanced_oriented (switch S rightConnected rightA rightB) hc far even degree
    S.leftConnected S.leftA S.leftB a5 b5
    (by change S.foreignA.card+(S.R.filter (G.Adj b)).card=5; omega) h

#print axioms traceable_of_balanced_cut_degree_five
#print axioms traceable_of_balanced_five_port_bridge_unconditional_high_side
end Graffiti189LongestPath.CrossSaturation.Split.Five
