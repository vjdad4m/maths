import DegreeFiveOneFiveFarRoutesBase189
import TerminalOreClosure189
import DegreeFiveOneFiveCapGlue189


namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open ArticulationPair
open private inside_high_at_least_three inside_high_at_least_four_if_exclusive from DegreeFiveBalancedCommonRoot189
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_nonempty shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset from DegreeFiveThreeFiveShapes189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

namespace OneFiveFarProfile
variable {D : Cmp (G:=G) (a:=a) (b:=b)} (S : OneFiveFarProfile D)
open private F LS from DegreeFiveOneFiveFarRoutesBase189

private theorem shore_partition : Shore D = insert S.e (insert S.f (S.T∪S.F)) := by
  classical
  have sub : cutPorts D⊆Shore D := filter_subset _ _
  have cover : cutPorts D∪S.F=Shore D := union_sdiff_of_subset sub
  rw [←cover,S.all_ports]
  ext z
  simp [or_assoc]

/-- A path through the nonports (possibly minus one absorbed vertex)
joins the two exclusively-colored contacts. -/
theorem finish_with_two_exclusives
    {C : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D) (ab : a≠b)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {r : V} (ce : Shore C={r}) (ar : G.Adj a r) (br : G.Adj b r)
    {A B : Finset V} (A_sub : A⊆Shore D) (B_sub : B⊆Shore D)
    (A_ep : S.e∉A) (A_fp : S.f∉A) (B_ep : S.e∉B) (B_fp : S.f∉B)
    (abDis : Disjoint A B) (abCover : A∪B=S.T∪S.F)
    {x y u v : V} (p : RouteOn G A x y) (q : RouteOn G B u v)
    (ex : G.Adj S.e x) (fy : G.Adj S.f y) (uT : u∈S.T) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have ar' : a∉Shore D := (shore_off D).1
  have br' : b∉Shore D := (shore_off D).2
  have rr : r∉Shore D := fun h=>disjoint_left.mp (shore_disjoint cd) (by simp [ce]) h
  have ed : S.e∈Shore D := (mem_filter.mp S.e_port).1
  have fd : S.f∈Shore D := (mem_filter.mp S.f_port).1
  have aA : a∉A := fun h=>ar' (A_sub h)
  have bA : b∉A := fun h=>br' (A_sub h)
  have rA : r∉A := fun h=>rr (A_sub h)
  have ae : a≠S.e := fun e=>ar' (Eq.mp (congrArg (fun x : V=>x∈Shore D) e.symm) ed)
  have af : a≠S.f := fun e=>ar' (Eq.mp (congrArg (fun x : V=>x∈Shore D) e.symm) fd)
  have be : b≠S.e := fun e=>br' (Eq.mp (congrArg (fun x : V=>x∈Shore D) e.symm) ed)
  have bf : b≠S.f := fun e=>br' (Eq.mp (congrArg (fun x : V=>x∈Shore D) e.symm) fd)
  have re : r≠S.e := fun e=>rr (e.symm ▸ ed)
  have rf : r≠S.f := fun e=>rr (e.symm ▸ fd)
  let H := insert r (insert b (insert a (insert S.f (insert S.e A))))
  have body : RouteOn G H a r := by
    have t := p.prefix ex A_ep
    have u := t.suffix fy.symm (by simp [S.e_ne_f.symm,A_fp])
    have fromA := u.prefix S.eA (by simp [af,ae,aA])
    have untilB := fromA.suffix S.fB.symm (by simp [ab.symm,be,bf,bA])
    exact untilB.suffix br (by simp [ar.ne.symm,br.ne.symm,re,rf,rA])
  have bApart : Disjoint B H := by
    apply disjoint_left.mpr
    intro z zb zh
    simp only [H,mem_insert] at zh
    rcases zh with h|h|h|h|h|h
    · exact rr (h ▸ B_sub zb)
    · exact br' (h ▸ B_sub zb)
    · exact ar' (h ▸ B_sub zb)
    · exact B_fp (h ▸ zb)
    · exact B_ep (h ▸ zb)
    exact disjoint_left.mp abDis h zb
  have zRoute := q.reverse.join body bApart (S.both_of_mem_T uT).2.1.symm
  obtain ⟨walk,wp,wS⟩ := zRoute
  refine ⟨v,r,walk,wp,?_⟩
  intro z
  apply (wS z).mpr
  rcases cover z with h|h|h|h
  · exact mem_union_right _ (by simp [H,h])
  · exact mem_union_right _ (by simp [H,h])
  · have eq : z=r := by simpa [ce] using h
    exact mem_union_right _ (by simp [H,eq])
  rw [S.shore_partition,←abCover] at h
  simp only [mem_insert,mem_union] at h ⊢
  exact h.elim (fun e=>.inr (by simp [H,e])) (fun h=>h.elim
    (fun e=>.inr (by simp [H,e])) (fun h=>h.elim (fun a=>.inr (by simp [H,a])) Or.inl))

end OneFiveFarProfile

#print axioms OneFiveFarProfile.finish_with_two_exclusives
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
