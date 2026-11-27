import DegreeFivePureShoreVisible189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_connected from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff common_sub_ports from DegreeFiveBothFiveResidual189
open private missed_neighbor_is_unique_at_cap from DegreeFivePureShoreVisible189
open private local_shell_comes_from_port from DegreeFiveNonmixedThreeFour189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- If all ports touch the first cut and at least two are common,
that cut sees every nonport at distance two. -/
theorem shore_with_all_ports_touching_first_visible
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C4 : 4≤(cutPorts C).card) (shared : 2≤(sharedPortSet D).card)
    (allA : ∀ x∈cutPorts D,G.Adj a x)
    (near : ∀ x∈sharedPortSet D,(secondShore D x).card≤1 ∧
      ∀ w∈Shore D,G.dist x w≤2) :
    Shore D⊆cutPorts D ∪ secondShore D a := by
  classical
  intro z zd
  by_cases hp : z∈cutPorts D
  · exact mem_union_left _ hp
  apply mem_union_right
  apply Classical.byContradiction
  intro miss
  have za : ¬G.Adj a z := fun h=>hp (cut_mem_iff.mpr ⟨zd,.inl h⟩)
  have zb : ¬G.Adj b z := fun h=>hp (cut_mem_iff.mpr ⟨zd,.inr h⟩)
  have aNe : a≠z := fun e=>(shore_off D).1 (e.symm ▸ zd)
  have bNe : b≠z := fun e=>(shore_off D).2 (e.symm ▸ zd)
  have no {x : V} (xp : x∈cutPorts D) : ¬G.Adj x z := by
    intro xz
    exact miss (mem_inter.mpr ⟨zd,d2 hc aNe za (allA x xp) xz⟩)
  obtain ⟨x,xk⟩ := card_pos.mp (show 0<(sharedPortSet D).card by omega)
  have xp := common_sub_ports D xk
  obtain ⟨xd,ax,bx⟩ := mem_filter.mp xk
  have zx : z≠x := fun e=>hp (e.symm ▸ xp)
  let U := ↑(↑(Shore D) : Set V)
  obtain ⟨p⟩ := (shore_connected D).preconnected (⟨z,zd⟩ : U) ⟨x,xd⟩
  have hit : ∃ v∈Shore D,G.Adj z v := by
    cases p with
    | nil => exact (zx rfl).elim
    | @cons _ v _ e p => exact ⟨v.val,v.property,e⟩
  obtain ⟨v,vd,zv⟩ := hit
  have vPort : v∉cutPorts D := fun h=>no h zv.symm
  have touch {w : V} (wk : w∈sharedPortSet D) : G.Adj w v := by
    have wp := common_sub_ports D wk
    have wNe : w≠z := fun e=>hp (e ▸ wp)
    have wv : w≠v := fun e=>vPort (e ▸ wp)
    have wn := near w wk
    exact missed_neighbor_is_unique_at_cap hc wn.2 wn.1 zd wNe (no wp) v vd wv zv.ne.symm
  have localD : sharedPortSet D⊆DistanceTwo G z := by
    intro w wk
    have wp := common_sub_ports D wk
    have wz : z≠w := fun e=>hp (e.symm ▸ wp)
    exact d2 hc wz (fun e=>no wp e.symm) zv (touch wk).symm
  have phaseA : G.dist z a=3 := by
    have hi := G.dist_le (Walk.cons zv (.cons (touch xk).symm (.cons ax.symm .nil)))
    change G.dist z a≤3 at hi
    have low := hc.one_lt_dist_of_ne_of_not_adj aNe za
    have ne : G.dist a z≠2 := fun h=>miss (mem_inter.mpr ⟨zd,by simp [DistanceTwo,h]⟩)
    have comm := SimpleGraph.dist_comm (G:=G) (u:=z) (v:=a)
    omega
  have phaseB : G.dist z b=3 := by
    have hi := G.dist_le (Walk.cons zv (.cons (touch xk).symm (.cons bx.symm .nil)))
    change G.dist z b≤3 at hi
    have low := hc.one_lt_dist_of_ne_of_not_adj bNe zb
    have ne : G.dist b z≠2 := by
      intro zz
      obtain ⟨w,wp,wz⟩ := local_shell_comes_from_port hc two (.inr rfl)
        (show z∈secondShore D b from mem_inter.mpr ⟨zd,by simp [DistanceTwo,zz]⟩)
      exact no (cut_mem_iff.mpr ⟨(mem_filter.mp wp).1,.inr (mem_filter.mp wp).2⟩) wz
    have comm := SimpleGraph.dist_comm (G:=G) (u:=z) (v:=b)
    omega
  have across : cutPorts C⊆EvenFrom G z := by
    intro w wp
    obtain ⟨wc,hit⟩ := cut_mem_iff.mp wp
    have out : w∉Shore D := fun h=>disjoint_left.mp (shore_disjoint cd) wc h
    have eq := cross_metric (Shore D) hc zd out (shore_closed D)
    rw [phaseA,phaseB] at eq
    have posA := hc.pos_dist_of_ne (show a≠w from fun e=>(shore_off C).1 (e.symm ▸ wc))
    have posB := hc.pos_dist_of_ne (show b≠w from fun e=>(shore_off C).2 (e.symm ▸ wc))
    have exactFour : G.dist z w=4 := by
      rcases hit with aw|bw
      · have n := dist_eq_one_iff_adj.mpr aw
        omega
      have n := dist_eq_one_iff_adj.mpr bw
      omega
    unfold EvenFrom
    exact mem_filter.mpr ⟨mem_univ _,by rw [exactFour]; decide⟩
  have loc : sharedPortSet D⊆EvenFrom G z := by
    intro w wm
    have fact := (mem_filter.mp (localD wm)).2
    unfold EvenFrom
    exact mem_filter.mpr ⟨mem_univ _,by rw [fact]; decide⟩
  have dis : Disjoint (cutPorts C) (sharedPortSet D) :=
    (shore_disjoint cd).mono (filter_subset _ _) (filter_subset _ _)
  have nS : z∉cutPorts C∪sharedPortSet D := by
    intro h
    rcases mem_union.mp h with c|d
    · exact disjoint_left.mp (shore_disjoint cd) (cut_mem_iff.mp c).1 zd
    exact hp (common_sub_ports D d)
  have sub : insert z (cutPorts C∪sharedPortSet D)⊆EvenFrom G z := by
    intro w wm
    rcases mem_insert.mp wm with rfl|wm
    · unfold EvenFrom
      simp [SimpleGraph.dist_self]
    exact (union_subset across loc) wm
  have n := (card_le_card sub).trans (even z)
  rw [card_insert_of_not_mem nS,card_union_of_disjoint dis] at n
  omega

#print axioms shore_with_all_ports_touching_first_visible
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
