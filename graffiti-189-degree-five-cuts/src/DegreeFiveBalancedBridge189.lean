import DegreeFiveBridgeSize189
import DegreeFiveSmallSides189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private left_boundary from AdjacentCut189
open private not_common from DegreeFiveFourPort189
open private count_cut_a from DegreeFiveBridgeSize189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

private theorem tight_high_port_neighbors (hc : G.Connected) (far : 3≤G.dist a b)
    {x : V} (xp : x∈S.localA) (high : 5≤G.degree x)
    (tight : S.localA.card+(secondA G S.L a).card=5) :
    secondA G S.L a ⊆ G.neighborFinset x := by
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
  have e := eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree]; exact limit.trans high)
  intro z zz
  rw [e]
  exact mem_insert_of_mem (mem_union_right _ zz)

private theorem bridged_five_ports_cover_high_side (hc : G.Connected) (far : 3≤G.dist a b)
    (high : ∀ u∈S.L,5≤G.degree u)
    (tightA : S.localA.card+(secondA G S.L a).card=5)
    (tightB : (S.L.filter (G.Adj b)).card+(secondA G S.L b).card=5)
    (five : S.localA.card+(S.L.filter (G.Adj b)).card=5)
    (bridge : portBridge S) :
    S.L.card≤5 := by
  classical
  let A := S.localA
  let B := S.L.filter (G.Adj b)
  let T := S.flip
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
  have y2 : y∈secondA G S.L a := by
    have na : ¬G.Adj a y := fun e=>not_common far e by'
    have ne : a≠y := fun e=>S.leftOff.1 (e.symm ▸ yl)
    exact mem_inter.mpr ⟨yl,d2 hc ne na ax xy⟩
  have aF : A⊆secondA G S.L b := by
    intro z za
    obtain ⟨zl,az⟩ := mem_filter.mp za
    have e := tight_high_port_neighbors S hc far za (high _ zl) tightA y2
    have zy := (mem_neighborFinset G z y).mp e
    have ne : b≠z := fun e=>S.leftOff.2 (e.symm ▸ zl)
    exact mem_inter.mpr ⟨zl,d2 hc ne (not_common far az) by' zy.symm⟩
  have xF : x∈secondA G S.L b := aF (mem_filter.mpr ⟨xl,ax⟩)
  have bE : B⊆secondA G S.L a := by
    intro z zb
    obtain ⟨zl,bz⟩ := mem_filter.mp zb
    have e := tight_high_port_neighbors T hc far' zb (high _ zl) tightB xF
    have zx := (mem_neighborFinset G z x).mp e
    have ne : a≠z := fun e=>S.leftOff.1 (e.symm ▸ zl)
    exact mem_inter.mpr ⟨zl,d2 hc ne (not_common far' bz) ax zx.symm⟩
  have eqA : A=secondA G S.L b := eq_of_subset_of_card_le aF (by
    change A.card+B.card=5 at five
    change B.card+(secondA G S.L b).card=5 at tightB
    omega)
  have eqB : B=secondA G S.L a := eq_of_subset_of_card_le bE (by
    change A.card+B.card=5 at five
    change A.card+(secondA G S.L a).card=5 at tightA
    omega)
  have all : S.L⊆A∪B := by
    intro z zl
    let W : Set V := ↑S.L
    obtain ⟨p⟩ := S.leftConnected.preconnected (⟨x,xl⟩ : W) ⟨z,zl⟩
    have step {u v : W} (q : (G.induce W).Walk u v) :
        (G.Adj a u.val ∨ G.Adj b u.val) → G.Adj a v.val ∨ G.Adj b v.val := by
      induction q with
      | nil => exact id
      | @cons u w v uw q ih =>
        intro uh
        apply ih
        by_cases aw : G.Adj a w.val
        · exact .inl aw
        by_cases bw : G.Adj b w.val
        · exact .inr bw
        have wl : w.val∈S.L := w.property
        rcases uh with au|bu
        · have ne : a≠w.val := fun e=>S.leftOff.1 ((congrArg (fun v=>v∈S.L) e.symm).mp wl)
          have m : w.val∈secondA G S.L a :=
            mem_inter.mpr ⟨wl,d2 hc ne aw au (show G.Adj u.val w.val from uw)⟩
          have zB : w.val∈B := eqB.symm ▸ m
          exact (bw (mem_filter.mp zB).2).elim
        · have ne : b≠w.val := fun e=>S.leftOff.2 ((congrArg (fun v=>v∈S.L) e.symm).mp wl)
          have m : w.val∈secondA G S.L b :=
            mem_inter.mpr ⟨wl,d2 hc ne bw bu (show G.Adj u.val w.val from uw)⟩
          have zA : w.val∈A := eqA.symm ▸ m
          exact (aw (mem_filter.mp zA).2).elim
    rcases step p (.inl ax) with az|bz
    · exact mem_union_left _ (mem_filter.mpr ⟨zl,az⟩)
    exact mem_union_right _ (mem_filter.mpr ⟨zl,bz⟩)
  change A.card+B.card=5 at five
  exact ((card_le_card all).trans (card_union_le _ _)).trans_eq five

/-- Degree-five #189 for a balanced five-attachment distance-three cut
whose two endpoints have degree exactly five, with no four-attachment
class and a mixed edge on an all-high side. No shore size is assumed. -/
theorem traceable_of_balanced_five_port_bridge (hc : G.Connected)
    (far : 3≤G.dist a b) (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (a5 : G.degree a=5) (b5 : G.degree b=5)
    (aL : S.localA.card≤3) (aR : S.foreignA.card≤3)
    (bL : (S.L.filter (G.Adj b)).card≤3) (bR : (S.R.filter (G.Adj b)).card≤3)
    (high : ∀ u∈S.L,5≤G.degree u)
    (five : S.localA.card+(S.L.filter (G.Adj b)).card=5)
    (bridge : portBridge S) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  have ao := tight_a_second_shells_at_degree_five S hc far even degree rightConnected rightA rightB a5 aL aR
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have bo := tight_a_second_shells_at_degree_five S.flip hc far' even degree rightConnected rightB rightA b5 bL bR
  have l := bridged_five_ports_cover_high_side S hc far high ao.1 bo.1 five bridge
  have bounds := opposite_bridge_shore_le_nine_exact_cut_degree S hc far even degree rightConnected
    rightA rightB a5 b5 aL aR bL bR bridge
  have ca := count_cut_a S far
  have cb := count_cut_a S.flip far'
  change G.degree b=(S.L.filter (G.Adj b)).card+(S.R.filter (G.Adj b)).card at cb
  have r := bounds.2 (by omega)
  exact traceable_of_small_sides S far degree (by omega) r high rightConnected rightA rightB

#print axioms traceable_of_balanced_five_port_bridge
end Graffiti189LongestPath.CrossSaturation.Split.Five
