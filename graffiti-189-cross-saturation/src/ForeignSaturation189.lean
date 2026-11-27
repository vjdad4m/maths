import CrossSaturation189
import OffFour17Close189

namespace Graffiti189LongestPath.CrossSaturation.Split
open SimpleGraph SimpleGraph.Walk Finset
open private d2 local_card few_steps from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

def foreignPorts : Finset V := S.R.filter (fun z => G.Adj a z ∨ G.Adj b z)

private theorem reaches_all_of_foreign_only (hc : G.Connected) {x : V}
    (xl : x∈S.L) (sat : DistanceTwo G x ⊆ S.R) {y : V} (yl : y∈S.L) :
    y=x ∨ G.Adj x y := by
  let xl' : ↑(↑S.L : Set V) := ⟨x,xl⟩
  let yl' : ↑(↑S.L : Set V) := ⟨y,yl⟩
  obtain ⟨p⟩ := S.leftConnected.preconnected xl' yl'
  have walk_step {u v : ↑(↑S.L : Set V)} (q : (G.induce (↑S.L : Set V)).Walk u v) :
      (u.val=x ∨ G.Adj x u.val) → (v.val=x ∨ G.Adj x v.val) := by
    induction q with
    | nil => exact id
    | @cons t u v tu q ih =>
        intro ht
        apply ih
        by_cases ux : u.val=x
        · exact Or.inl ux
        right
        change G.Adj t.val u.val at tu
        rcases ht with tx|xt
        · exact tx ▸ tu
        by_contra bad
        have ud := d2 hc (Ne.symm ux) bad xt tu
        exact (disjoint_left.mp S.dis u.property (sat ud)).elim
  exact walk_step p (Or.inl rfl)

theorem order_le_of_foreign_ports_at_budget (d : ℕ) (positive : 0 < d) (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ d + 1) (ab : a≠b)
    (common : ∃ x∈S.L, G.Adj a x ∧ G.Adj b x)
    (hit : S.foreignA.Nonempty) (four : S.foreignPorts.card=d) :
    Fintype.card V ≤ (if G.Adj a b then 4*d+1 else 4*d) := by
  classical
  obtain ⟨x,xl,ax,bx⟩ := common
  have sub : S.foreignPorts ⊆ DistanceTwo G x := by
    intro z hz
    obtain ⟨zr,az|bz⟩ := mem_filter.mp hz
    · exact d2 hc (fun e=>disjoint_left.mp S.dis xl (e ▸ zr)) (S.cross _ xl _ zr) ax.symm az
    · exact d2 hc (fun e=>disjoint_left.mp S.dis xl (e ▸ zr)) (S.cross _ xl _ zr) bx.symm bz
  have dcap := distanceTwo_le_of_even d x (even x)
  have sat : DistanceTwo G x = S.foreignPorts :=
    (eq_of_subset_of_card_le sub (by omega)).symm
  have univL (y : V) (yl : y∈S.L) :=
    reaches_all_of_foreign_only S hc xl (fun _ h => by rw [sat] at h; exact (mem_filter.mp h).1) yl
  have rad (y : V) : G.dist x y ≤ 3 := by
    by_contra bad
    have far := distanceTwo_add_two_le_even_of_far hc (x:=x) (y:=y) (by omega)
    rw [sat,four] at far
    have hb := even x
    omega
  have lc := local_card S d hc even hit
  have ac := distanceTwo_le_of_even d a (even a)
  have bc := distanceTwo_le_of_even d b (even b)
  have left (z : V) (zl : z∈S.L) : z∈S.localA ∨ z∈DistanceTwo G a := by
    by_cases az : G.Adj a z
    · exact Or.inl (mem_filter.mpr ⟨zl,az⟩)
    right
    rcases univL z zl with rfl|xz
    · exact (az ax).elim
    · exact d2 hc (fun e => S.leftOff.1 (e ▸ zl)) az ax xz
  have right (z : V) (zr : z∈S.R) :
      z∈S.foreignPorts ∨ z∈DistanceTwo G a ∨ z∈DistanceTwo G b := by
    obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist x z
    have r := rad z
    rcases few_steps S xl zr q (by omega) with p|⟨w,wr,p,wz⟩
    · exact Or.inl (mem_filter.mpr ⟨zr,p⟩)
    by_cases hz : G.Adj a z ∨ G.Adj b z
    · exact Or.inl (mem_filter.mpr ⟨zr,hz⟩)
    simp only [not_or] at hz
    exact Or.inr (p.imp
      (fun e=>d2 hc (fun eq=>S.rightOff.1 (eq ▸ zr)) hz.1 e wz)
      (fun e=>d2 hc (fun eq=>S.rightOff.2 (eq ▸ zr)) hz.2 e wz))
  by_cases adj : G.Adj a b
  · simp only [adj,if_true]
    have aa : S.foreignA ⊆ S.foreignPorts := fun _ h =>
      let ⟨hr,ha⟩ := mem_filter.mp h
      mem_filter.mpr ⟨hr,Or.inl ha⟩
    by_cases big : S.foreignA.card=d
    · exact (S.order_le_three_times_budget_plus_two d positive hc even big).trans (by omega)
    have max3 := card_le_card aa
    have cover : (univ : Finset V) ⊆
        insert a (insert b ((S.localA ∪ S.foreignA) ∪ (DistanceTwo G a ∪ DistanceTwo G b))) := by
      intro z _
      simp only [mem_insert,mem_union]
      rcases S.cover z with rfl|rfl|zl|zr
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      all_goals right; right
      · exact (left z zl).imp Or.inl Or.inl
      rcases right z zr with fr|da|db
      · obtain ⟨_,az|bz⟩ := mem_filter.mp fr
        · exact Or.inl (Or.inr (mem_filter.mpr ⟨zr,az⟩))
        by_cases az : G.Adj a z
        · exact Or.inl (Or.inr (mem_filter.mpr ⟨zr,az⟩))
        · exact Or.inr (Or.inl (d2 hc (fun e=>S.rightOff.1 (e ▸ zr)) az adj bz))
      · exact Or.inr (Or.inl da)
      · exact Or.inr (Or.inr db)
    have c := card_le_card cover
    rw [card_univ] at c
    have c1 := card_insert_le a (insert b ((S.localA ∪ S.foreignA) ∪ (DistanceTwo G a ∪ DistanceTwo G b)))
    have c2 := card_insert_le b ((S.localA ∪ S.foreignA) ∪ (DistanceTwo G a ∪ DistanceTwo G b))
    have c3 := card_union_le (S.localA ∪ S.foreignA) (DistanceTwo G a ∪ DistanceTwo G b)
    have c4 := card_union_le S.localA S.foreignA
    have c5 := card_union_le (DistanceTwo G a) (DistanceTwo G b)
    omega
  · simp only [adj,if_false]
    have ba := d2 hc ab adj ax bx.symm
    have ab' := d2 hc ab.symm (fun e=>adj e.symm) bx ax.symm
    have cover : (univ : Finset V) ⊆
        (S.localA ∪ S.foreignPorts) ∪ (DistanceTwo G a ∪ DistanceTwo G b) := by
      intro z _
      simp only [mem_union]
      rcases S.cover z with rfl|rfl|zl|zr
      · exact Or.inr (Or.inr ab')
      · exact Or.inr (Or.inl ba)
      · exact (left z zl).imp Or.inl Or.inl
      · exact (right z zr).imp Or.inr id
    have c := card_le_card cover
    rw [card_univ] at c
    have c1 := card_union_le (S.localA ∪ S.foreignPorts) (DistanceTwo G a ∪ DistanceTwo G b)
    have c2 := card_union_le S.localA S.foreignPorts
    have c3 := card_union_le (DistanceTwo G a) (DistanceTwo G b)
    omega
/-- Switching the names of the deleted vertices leaves the sides unchanged. -/
def flip : Graffiti189LongestPath.CrossSaturation.Split G b a :=
  ⟨S.L,S.R,S.dis,⟨S.leftOff.2,S.leftOff.1⟩,⟨S.rightOff.2,S.rightOff.1⟩,S.leftConnected,
   S.cross,S.leftB,S.leftA,fun z => by simpa only [or_left_comm] using S.cover z⟩

theorem order_le_of_four_foreign_ports (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 5) (ab : a≠b)
    (common : ∃ x∈S.L, G.Adj a x ∧ G.Adj b x)
    (four : S.foreignPorts.card=4) :
    Fintype.card V ≤ (if G.Adj a b then 17 else 16) := by
  classical
  by_cases hit : S.foreignA.Nonempty
  · exact order_le_of_foreign_ports_at_budget S 4 (by decide) hc even ab common hit four
  have flipEq : S.flip.foreignPorts = S.foreignPorts := by
    ext z
    simp [foreignPorts,flip,or_comm]
  obtain ⟨z,hz⟩ := card_pos.mp (show 0 < S.foreignPorts.card by omega)
  obtain ⟨zr,az|bz⟩ := mem_filter.mp hz
  · exact (hit ⟨z,mem_filter.mpr ⟨zr,az⟩⟩).elim
  have hit' : S.flip.foreignA.Nonempty := ⟨z,mem_filter.mpr ⟨zr,bz⟩⟩
  have common' : ∃ x∈S.flip.L, G.Adj b x ∧ G.Adj a x := by
    obtain ⟨x,xl,ax,bx⟩ := common
    exact ⟨x,xl,bx,ax⟩
  have h := order_le_of_foreign_ports_at_budget S.flip 4 (by decide) hc even ab.symm
    common' hit' (flipEq.symm ▸ four)
  simpa [G.adj_comm b a] using h

theorem traceable_of_four_foreign_ports (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 5) (ab : a≠b)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    (common : ∃ x∈S.L, G.Adj a x ∧ G.Adj b x)
    (four : S.foreignPorts.card=4) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  have h := S.order_le_of_four_foreign_ports hc even ab common four
  have small : Fintype.card V ≤ 17 := by split at h <;> omega
  exact Graffiti189LongestPath.TwoCut.traceable_of_order_le_seventeen hc even conn degree small

#print axioms order_le_of_foreign_ports_at_budget
#print axioms order_le_of_four_foreign_ports
#print axioms traceable_of_four_foreign_ports
end Graffiti189LongestPath.CrossSaturation.Split
