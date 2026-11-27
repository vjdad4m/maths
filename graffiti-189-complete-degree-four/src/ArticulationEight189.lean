import ArticulationBridge189
namespace Graffiti189LongestPath.CrossSaturation.ArticulationPair
open SimpleGraph SimpleGraph.Walk Finset
open private mem_positive from AdjacentCut189
open private reaches_all_left foreign_subset from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {c : V} (S : Graffiti189LongestPath.CrossSaturation.ArticulationPair G c)
set_option linter.unusedSectionVars false

def asSplit : Split G c c :=
  ⟨S.L,S.R,S.dis,⟨S.offL,S.offL⟩,⟨S.offR,S.offR⟩,S.joinedL,S.cross,S.hitL,S.hitL,
    fun z => (S.cover z).imp id Or.inr⟩

def inside (G : SimpleGraph V) [DecidableRel G.Adj] (L : Finset V) (x : V) : Finset V := L.filter (G.Adj x)

private theorem dwalk {x y z : V} (hc : G.Connected) (xz : x≠z)
    (non : ¬G.Adj x z) (xy : G.Adj x y) (yz : G.Adj y z) :
    z∈DistanceTwo G x := by
  classical
  have h := hc.one_lt_dist_of_ne_of_not_adj xz non
  have le := G.dist_le (Walk.cons xy (Walk.cons yz .nil))
  simp at le
  simp [DistanceTwo, show G.dist x z=2 by omega]

private theorem left_boundary' {x : V} (xl : x∈S.L) {y : V} (xy : G.Adj x y) :
    y=c ∨ y∈S.L := by
  rcases S.cover y with h|h|h
  · exact .inl h
  · exact .inr h
  · exact (S.cross _ xl _ h xy).elim

private theorem right_boundary' {x : V} (xr : x∈S.R) {y : V} (xy : G.Adj x y) :
    y=c ∨ y∈S.R := by
  rcases S.cover y with h|h|h
  · exact .inl h
  · exact (S.cross _ h _ xr xy.symm).elim
  · exact .inr h

def swapSides : ArticulationPair G c :=
  ⟨S.R,S.L,S.dis.symm,S.offR,S.offL,
    (fun z=>by simpa only [or_comm (a:=z∈S.L) (b:=z∈S.R)] using S.cover z),
    (fun u ur v vl e=>S.cross _ vl _ ur e.symm),S.joinedR,S.joinedL,S.hitR,S.hitL⟩

theorem card_sides : Fintype.card V = S.L.card+S.R.card+1 := by
  classical
  have eq : (univ : Finset V) = insert c (S.L∪S.R) := by
    ext z
    simp only [mem_univ,mem_insert,mem_union,true_iff]
    exact S.cover z
  have ca := congrArg Finset.card eq
  have off : c∉S.L∪S.R := by simp [S.offL,S.offR]
  rw [card_univ,card_insert_of_not_mem off,card_union_of_disjoint S.dis] at ca
  exact ca

private theorem high_inside_left (x : V) (xl : x∈S.L) (high : 4≤G.degree x) :
    3≤(inside G S.L x).card := by
  have sub : G.neighborFinset x ⊆ insert c (inside G S.L x) := by
    intro y hy
    have e := (mem_neighborFinset G x y).mp hy
    rcases left_boundary' S xl e with rfl|yl
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_filter.mpr ⟨yl,e⟩)
  have cx := card_le_card sub
  rw [card_neighborFinset_eq_degree] at cx
  have c1 := card_insert_le c (inside G S.L x)
  omega

private theorem nonport_inside_left (x : V) (xl : x∈S.L) (high : 4≤G.degree x)
    (no : ¬G.Adj c x) : 4≤(inside G S.L x).card := by
  have sub : G.neighborFinset x ⊆ inside G S.L x := by
    intro y hy
    have e := (mem_neighborFinset G x y).mp hy
    rcases left_boundary' S xl e with rfl|yl
    · exact (no e.symm).elim
    · exact mem_filter.mpr ⟨yl,e⟩
  have d := card_le_card sub
  rw [card_neighborFinset_eq_degree] at d
  exact high.trans d

private theorem nonport_missing_two (hc : G.Connected) (eight : S.L.card=8)
    {x z : V} (xl : x∈S.L) (zl : z∈S.L) (xz : x≠z) (ne : ¬G.Adj x z)
    (x3 : 3≤(inside G S.L x).card) (z4 : 4≤(inside G S.L z).card) : z∈DistanceTwo G x := by
  classical
  have common : ∃ y, G.Adj x y ∧ G.Adj y z := by
    apply Classical.byContradiction
    intro bad
    have dj : Disjoint (inside G S.L x) (inside G S.L z) := by
      exact disjoint_left.mpr (fun y yx yz => bad ⟨y,(mem_filter.mp yx).2,(mem_filter.mp yz).2.symm⟩)
    have sub : inside G S.L x ∪ inside G S.L z ⊆ (S.L.erase x).erase z := by
      intro y hy
      rcases mem_union.mp hy with hy|hy
      · obtain ⟨yl,xy⟩ := mem_filter.mp hy
        exact mem_erase.mpr ⟨fun e=>ne (e ▸ xy),mem_erase.mpr ⟨xy.ne.symm,yl⟩⟩
      · obtain ⟨yl,zy⟩ := mem_filter.mp hy
        exact mem_erase.mpr ⟨zy.ne.symm,mem_erase.mpr ⟨fun e=>ne (e ▸ zy.symm),yl⟩⟩
    have m := card_le_card sub
    rw [card_union_of_disjoint dj,card_erase_of_mem (mem_erase.mpr ⟨xz.symm,zl⟩),card_erase_of_mem xl,eight] at m
    omega
  obtain ⟨y,xy,yz⟩ := common
  exact dwalk hc xz ne xy yz

/-- If an eight-vertex side is opposite a singleton, it has internal
minimum degree at least four. In particular a singleton cannot reduce
the Ore degree-sum threshold for finding a rooted path in this side. -/
theorem eight_singleton_internal_min_degree (hc : G.Connected)
    (even : ∀ v, (EvenFrom G v).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (eight : S.L.card=8) {y : V} (single : S.R={y}) :
    ∀ x∈S.L,4≤(inside G S.L x).card := by
  classical
  have yr : y∈S.R := by simp [single]
  have cy : G.Adj c y := by
    obtain ⟨z,zr,cz⟩ := S.hitR
    have e : z=y := by simpa [single] using zr
    exact e ▸ cz
  have low : G.degree y≤1 := by
    have sub : G.neighborFinset y ⊆ {c} := by
      intro v hv
      have e := (mem_neighborFinset G y v).mp hv
      rcases right_boundary' S yr e with rfl|vr
      · simp
      have eq : v=y := by simpa [single] using vr
      exact (e.ne eq.symm).elim
    simpa only [card_neighborFinset_eq_degree,card_singleton] using card_le_card sub
  have high (x : V) (xl : x∈S.L) : 4≤G.degree x :=
    (degree x y (fun e=>disjoint_left.mp S.dis (e ▸ xl) yr)).resolve_right (by omega)
  intro x xl
  by_cases cx : G.Adj c x
  · have neq : x≠y := fun e=>disjoint_left.mp S.dis (e ▸ xl) yr
    have yd := dwalk hc neq (S.cross _ xl _ yr) cx.symm cy
    have dcap := distanceTwo_le_of_even 4 x (even x)
    have small := card_erase_of_mem yd
    have sub : S.L ⊆ insert x (inside G S.L x ∪ (DistanceTwo G x).erase y) := by
      intro z zl
      by_cases zx : z=x
      · simp [zx]
      apply mem_insert_of_mem
      by_cases xz : G.Adj x z
      · exact mem_union_left _ (mem_filter.mpr ⟨zl,xz⟩)
      have zy : z≠y := fun e=>disjoint_left.mp S.dis (e ▸ zl) yr
      have z2 : z∈DistanceTwo G x := by
        by_cases cz : G.Adj c z
        · exact dwalk hc (Ne.symm zx) xz cx.symm cz
        exact nonport_missing_two S hc eight xl zl (Ne.symm zx) xz
          (high_inside_left S x xl (high x xl)) (nonport_inside_left S z zl (high z zl) cz)
      exact mem_union_right _ (mem_erase.mpr ⟨zy,z2⟩)
    have n := card_le_card sub
    have c1 := card_insert_le x (inside G S.L x ∪ (DistanceTwo G x).erase y)
    have c2 := card_union_le (inside G S.L x) ((DistanceTwo G x).erase y)
    omega
  exact nonport_inside_left S x xl (high x xl) cx

theorem eight_nonsingleton_port_universal (hc : G.Connected)
    (even : ∀ v, (EvenFrom G v).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (eight : S.L.card=8) (rightTwo : 2≤S.R.card) :
    Fintype.card V=13 ∧ (∀ v∈S.R,G.Adj c v) ∧
      ∀ x∈S.L,G.Adj c x → ∀ v∈S.L,v=x ∨ G.Adj x v := by
  classical
  have cnt := S.card_sides
  have upper := S.order_le_thirteen hc even
  have high_side (z : V) (zr : z∈S.R) : G.degree z ≤ S.R.card := by
    have sub : G.neighborFinset z ⊆ insert c (S.R.erase z) := by
      intro v hv
      have e := (mem_neighborFinset G z v).mp hv
      rcases right_boundary' S zr e with rfl|vr
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_erase.mpr ⟨e.ne.symm,vr⟩)
    have n := card_le_card sub
    rw [card_neighborFinset_eq_degree] at n
    have i := card_insert_le c (S.R.erase z)
    rw [card_erase_of_mem zr] at i
    omega
  have four : S.R.card=4 := by
    obtain ⟨z,zr,w,wr,zw⟩ := one_lt_card.mp (by omega : 1<S.R.card)
    have zi := high_side z zr
    have wi := high_side w wr
    rcases degree z w zw with d|d <;> omega
  have allR : ∀ v∈S.R,G.Adj c v := by
    obtain ⟨x,xl,cx⟩ := S.hitL
    obtain ⟨y,yr,cy⟩ := S.hitR
    have q := side_and_opposite_even_le_twice_budget hc 4 even S.L S.R S.dis S.offL S.cross S.cover yr cy
    have empty : (S.R ∩ PositiveEven G c).card=0 := by omega
    intro v vr
    let W : Set V := ↑S.R
    obtain ⟨w⟩ := S.joinedR.preconnected (⟨y,yr⟩ : W) (⟨v,vr⟩ : W)
    have propagate {u z : W} (p : (G.induce W).Walk u z) : G.Adj c u.val → G.Adj c z.val := by
      induction p with
      | nil => exact id
      | @cons u w z e p ih =>
        intro cu
        apply ih
        apply Classical.byContradiction
        intro bad
        have ww : w.val∈S.R := w.property
        have ne : c≠w.val := fun h=>S.offR ((congrArg (fun v=>v∈S.R) h.symm).mp ww)
        have t := dwalk hc ne bad cu (show G.Adj u.val w.val from e)
        have two := (mem_filter.mp t).2
        have pw := mem_positive.mpr ⟨Ne.symm ne,by rw [two]; decide⟩
        have h := card_pos.mpr ⟨_,mem_inter.mpr ⟨ww,pw⟩⟩
        omega
    exact propagate w cy
  refine ⟨(by omega),allR,?_⟩
  intro x xl cx v vl
  let T := S.asSplit
  have tt : T.foreignA=S.R := by
    apply Subset.antisymm (filter_subset _ _)
    intro z zr
    exact mem_filter.mpr ⟨zr,allR z zr⟩
  have u := foreign_subset T hc xl cx
  have s : DistanceTwo G x=T.foreignA := by
    have cap := distanceTwo_le_of_even 4 x (even x)
    exact (eq_of_subset_of_card_le u (by rw [tt,four]; exact cap)).symm
  exact reaches_all_left T hc xl s vl

#print axioms eight_singleton_internal_min_degree
#print axioms eight_nonsingleton_port_universal
end Graffiti189LongestPath.CrossSaturation.ArticulationPair
