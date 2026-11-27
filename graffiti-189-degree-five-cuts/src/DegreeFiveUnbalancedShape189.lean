import DegreeFiveBridgeSize189
import DegreeFiveSmallSides189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 foreign_subset from CrossSaturation189
open private left_boundary from AdjacentCut189
open private not_common from DegreeFiveFourPort189
open private lengths_take_drop from SmallSeparator189
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


private theorem mixed_target_shell (hc : G.Connected) (far : 3≤G.dist a b)
    {x y : V} (xl : x∈S.L) (yl : y∈S.L) (ax : G.Adj a x)
    (xy : G.Adj x y) (by' : G.Adj b y) :
    y∈secondA G S.L a := by
  have ay : ¬G.Adj a y := fun e=>not_common far e by'
  have ane : a≠y := fun e=>S.leftOff.1 (e.symm ▸ yl)
  exact mem_inter.mpr ⟨yl,d2 hc ane ay ax xy⟩

private theorem all_ports_second_other_at_bridge (hc : G.Connected) (far : 3≤G.dist a b)
    (Ahigh : ∀ u∈S.localA,5≤G.degree u)
    (tight : S.localA.card+(secondA G S.L a).card=5) (bridge : portBridge S) :
    S.localA⊆secondA G S.L b := by
  obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
  have ye := mixed_target_shell S hc far xl yl ax xy by'
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  intro u ua
  obtain ⟨ul,au⟩ := mem_filter.mp ua
  have eq := tight_high_port_target_eq S hc far ua (Ahigh _ ua) tight
  have un : y∈G.neighborFinset u := by
    rw [eq]
    exact mem_insert_of_mem (mem_union_right _ ye)
  exact mixed_target_shell S.flip hc far' yl ul by' ((mem_neighborFinset _ _ _).mp un).symm au

/-- In a three-plus-three shore with tight second shells, there can be
no mixed attachment edge because one color has three high porters. -/
theorem no_mixed_three_three (hc : G.Connected) (far : 3≤G.dist a b)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (a3 : S.localA.card=3) (b3 : (S.L.filter (G.Adj b)).card=3)
    (ta : S.localA.card+(secondA G S.L a).card=5)
    (tb : (S.L.filter (G.Adj b)).card+(secondA G S.L b).card=5) :
    ¬portBridge S := by
  classical
  intro bridge
  by_cases ah : ∀ u∈S.localA,5≤G.degree u
  · have sub := card_le_card (all_ports_second_other_at_bridge S hc far ah ta bridge)
    omega
  push_neg at ah
  obtain ⟨u,ua,ulo⟩ := ah
  let T := S.flip
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have bh (v : V) (vb : v∈T.localA) : 5≤G.degree v := by
    have ne : u≠v := fun e=>not_common far (mem_filter.mp ua).2 (e.symm ▸ (mem_filter.mp vb).2)
    exact (degree _ _ ne).resolve_left (by omega)
  have br : portBridge T := by
    obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
    exact ⟨y,yl,x,xl,by',xy.symm,ax⟩
  have sub := card_le_card (all_ports_second_other_at_bridge T hc far' bh tb br)
  change (S.L.filter (G.Adj b)).card≤(secondA G S.L a).card at sub
  omega

private theorem inner_outside_a_shell_at_dist_two (hc : G.Connected) (far : 3≤G.dist a b)
    (rad : ∀ z,G.dist a z≤3) {x z : V}
    (xp : x∈S.localA) (high : 5≤G.degree x)
    (tight : S.localA.card+(secondA G S.L a).card=5)
    (zi : z∈inner G S.L a b) (ze : z∉secondA G S.L a) :
    z∈DistanceTwo G x := by
  obtain ⟨zl,az,bz⟩ := mem_filter.mp zi
  obtain ⟨xl,ax⟩ := mem_filter.mp xp
  have ne : a≠z := fun e=>S.leftOff.1 (e.symm ▸ zl)
  have lo := hc.one_lt_dist_of_ne_of_not_adj ne az
  have n2 : G.dist a z≠2 := by
    intro eq
    exact ze (mem_inter.mpr ⟨zl,by simp [DistanceTwo,eq]⟩)
  have d3 : G.dist a z=3 := by have r := rad z; omega
  obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist a z
  have q3 : q.length=3 := ql.trans d3
  let v := q.getVert 2
  have vz : G.Adj v z := by
    have e := q.adj_getVert_succ (i:=2) (by omega)
    rw [show 2+1=3 by decide,←q3,q.getVert_length] at e
    exact e
  have vl : v∈S.L := by
    rcases S.cover v with va|vb|vl|vr
    · exact (az (va ▸ vz)).elim
    · exact (bz (vb ▸ vz)).elim
    · exact vl
    exact (S.cross _ zl _ vr vz.symm).elim
  have upper : G.dist a v≤2 := by
    have e := G.dist_le (q.take 2)
    have le : 2≤q.length := by omega
    obtain ⟨n,_⟩ := lengths_take_drop q 2 le
    rw [n] at e
    exact e
  have no : ¬G.Adj a v := by
    intro av
    have l := G.dist_le (Walk.cons av (Walk.cons vz .nil))
    simp at l
    omega
  have avn : a≠v := fun h=>S.leftOff.1 ((congrArg (fun w=>w∈S.L) h.symm).mp vl)
  have lower := hc.one_lt_dist_of_ne_of_not_adj avn no
  have ve : v∈secondA G S.L a := mem_inter.mpr ⟨vl,by simp [DistanceTwo,show G.dist a v=2 by omega]⟩
  have xn := tight_high_port_target_eq S hc far xp high tight
  have xv : G.Adj x v := (mem_neighborFinset _ _ _).mp
    (xn.symm ▸ mem_insert_of_mem (mem_union_right _ ve))
  have xne : x≠z := fun e=>az (e ▸ ax)
  have xno : ¬G.Adj x z := by
    intro e
    exact ze (mem_inter.mpr ⟨zl,d2 hc ne az ax e⟩)
  exact d2 hc xne xno xv vz

private theorem mixed_two_two_le_six_oriented (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (a2 : S.localA.card=2) (b2 : (S.L.filter (G.Adj b)).card=2)
    (foreignB : (S.R.filter (G.Adj b)).card=3)
    (ta : S.localA.card+(secondA G S.L a).card=5)
    (tb : (S.L.filter (G.Adj b)).card+(secondA G S.L b).card=5)
    (radiusB : ∀ z,G.dist b z≤3)
    (allA : ∀ u∈S.localA,5≤G.degree u) (bridge : portBridge S) :
    S.L.card≤6 := by
  classical
  let A := S.localA
  let B := S.L.filter (G.Adj b)
  let F := secondA G S.L b
  let I := inner G S.L a b
  let T := S.flip
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have subA : A⊆F := all_ports_second_other_at_bridge S hc far allA ta bridge
  have b2' : B.card=2 := b2
  obtain ⟨y,yB,w,wB,yw⟩ := one_lt_card.mp (by omega : 1<B.card)
  have bh : ∃ y∈B,5≤G.degree y := (degree y w yw).elim (fun e=>⟨y,yB,e⟩) (fun e=>⟨w,wB,e⟩)
  obtain ⟨u,uB,uh⟩ := bh
  obtain ⟨ul,bu⟩ := mem_filter.mp uB
  obtain ⟨x,xl,ax⟩ := S.leftA
  have xF : x∈F := subA (mem_filter.mpr ⟨xl,ax⟩)
  have eq := tight_high_port_target_eq T hc far' uB uh tb
  have xu : G.Adj x u := by
    have mv : x∈G.neighborFinset u := by rw [eq]; exact mem_insert_of_mem (mem_union_right _ xF)
    exact ((mem_neighborFinset _ _ _).mp mv).symm
  have ad : a∈DistanceTwo G u := by
    have ne : u≠a := fun e=>S.leftOff.1 (e ▸ ul)
    have na : ¬G.Adj u a := fun e=>not_common far' bu e.symm
    exact d2 hc ne na xu.symm ax.symm
  have sd : I\F ⊆ DistanceTwo G u := by
    intro z zz
    obtain ⟨zI,zF⟩ := mem_sdiff.mp zz
    have zi : z∈inner G T.L b a := by
      obtain ⟨zl,az,bz⟩ := mem_filter.mp zI
      exact mem_filter.mpr ⟨zl,bz,az⟩
    exact inner_outside_a_shell_at_dist_two T hc far' radiusB uB uh tb zi zF
  have fd : (S.R.filter (G.Adj b))⊆DistanceTwo G u := foreign_subset T hc ul bu
  let C := S.R.filter (G.Adj b)
  have aoff : a∉C := fun h=>S.rightOff.1 (mem_filter.mp h).1
  have dis : Disjoint (insert a C) (I\F) := by
    apply disjoint_left.mpr
    intro z zc zi
    have zl := (mem_filter.mp (mem_sdiff.mp zi).1).1
    rcases mem_insert.mp zc with rfl|zr
    · exact S.leftOff.1 zl
    exact disjoint_left.mp S.dis zl (mem_filter.mp zr).1
  have c := card_le_card (union_subset (insert_subset_iff.mpr ⟨ad,fd⟩) sd)
  rw [card_union_of_disjoint dis,card_insert_of_not_mem aoff] at c
  have cap := distanceTwo_le_of_even 5 u (even u)
  change C.card=3 at foreignB
  have im : (I\F).card≤1 := by omega
  have disAI : Disjoint A I := by
    apply disjoint_left.mpr
    intro x xa xi
    exact (mem_filter.mp xi).2.1 (mem_filter.mp xa).2
  have s := card_le_card (union_subset subA (inter_subset_right : I∩F⊆F))
  have d : Disjoint A (I∩F) := disAI.mono_right inter_subset_left
  rw [card_union_of_disjoint d] at s
  have ca := card_inter_add_card_sdiff I F
  have i2 : I.card≤2 := by
    change A.card=2 at a2
    change B.card+F.card=5 at tb
    omega
  have cov : S.L⊆(A∪B)∪I := by
    intro z zl
    by_cases az : G.Adj a z
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨zl,az⟩))
    by_cases bz : G.Adj b z
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨zl,bz⟩))
    exact mem_union_right _ (mem_filter.mpr ⟨zl,az,bz⟩)
  have n := (card_le_card cov).trans (card_union_le _ _)
  have u := card_union_le A B
  change A.card=2 at a2
  omega

/-- In the 4+6 port profile, the mixed two-plus-two shore has at most
six vertices, regardless of which shore contains the possible low vertex. -/
theorem mixed_two_two_le_six (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (a2 : S.localA.card=2) (b2 : (S.L.filter (G.Adj b)).card=2)
    (a3 : S.foreignA.card=3) (b3 : (S.R.filter (G.Adj b)).card=3)
    (ta : S.localA.card+(secondA G S.L a).card=5)
    (tb : (S.L.filter (G.Adj b)).card+(secondA G S.L b).card=5)
    (radiusA : ∀ z,G.dist a z≤3) (radiusB : ∀ z,G.dist b z≤3)
    (bridge : portBridge S) : S.L.card≤6 := by
  classical
  by_cases ah : ∀ u∈S.localA,5≤G.degree u
  · exact mixed_two_two_le_six_oriented S hc far even degree a2 b2 b3 ta tb radiusB ah bridge
  push_neg at ah
  obtain ⟨u,ua,ulo⟩ := ah
  let T := S.flip
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have bh (v : V) (vb : v∈T.localA) : 5≤G.degree v := by
    have ne : u≠v := fun e=>not_common far (mem_filter.mp ua).2 (e.symm ▸ (mem_filter.mp vb).2)
    exact (degree _ _ ne).resolve_left (by omega)
  have br : portBridge T := by
    obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
    exact ⟨y,yl,x,xl,by',xy.symm,ax⟩
  exact mixed_two_two_le_six_oriented T hc far' even degree b2 a2 a3 tb ta radiusA bh br

#print axioms no_mixed_three_three
#print axioms mixed_two_two_le_six
end Graffiti189LongestPath.CrossSaturation.Split.Five
