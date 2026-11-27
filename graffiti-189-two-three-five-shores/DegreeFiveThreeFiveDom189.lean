import DegreeFiveThreeForeignImpossible189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Once a common porter has five foreign cut-port neighbors at distance
two, they exhaust its distance-two shell and its eccentricity is at most
three. Every nonporter on the other shore sees a porter of that shore. -/
theorem saturated_common_foreign_port_domination
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (D5 : (cutPorts D).card=5)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    (∀ v : V,G.dist x v≤3) ∧
    (∀ z∈Shore D,z∉cutPorts D → ∃ y∈cutPorts D,G.Adj z y) := by
  classical
  have cross {z : V} (zd : z∈Shore D) : ¬G.Adj x z := by
    intro e
    rcases shore_closed C x xc z e with rfl|rfl|zc
    · exact (shore_off D).1 zd
    · exact (shore_off D).2 zd
    exact disjoint_left.mp (shore_disjoint cd) zc zd
  have foreign : cutPorts D⊆DistanceTwo G x := by
    intro z zp
    obtain ⟨zd,hit⟩ := mem_filter.mp zp
    have ne : x≠z := fun e=>disjoint_left.mp (shore_disjoint cd) xc (e.symm ▸ zd)
    exact hit.elim (fun h=>d2 hc ne (cross zd) ax.symm h)
      (fun h=>d2 hc ne (cross zd) bx.symm h)
  have ds := card_le_card foreign
  rw [D5] at ds
  have eq : cutPorts D=DistanceTwo G x := eq_of_subset_of_card_le foreign
    ((distanceTwo_le_of_even 5 x (even x)).trans (le_of_eq D5.symm))
  have ecc (z : V) : G.dist x z≤3 := by
    apply Classical.byContradiction
    intro far
    have d4 := distanceTwo_add_two_le_even_of_far hc (show 4≤G.dist x z by omega)
    have cap := even x
    omega
  refine ⟨ecc,?_⟩
  intro z zd zp
  have xz : x≠z := fun e=>disjoint_left.mp (shore_disjoint cd) xc (e.symm ▸ zd)
  have d3 : G.dist x z=3 := by
    have lo := hc.one_lt_dist_of_ne_of_not_adj xz (cross zd)
    have hi := ecc z
    have n2 : G.dist x z ≠ 2 := fun h=>zp (eq.symm ▸ (show z∈DistanceTwo G x by simp [DistanceTwo,h]))
    omega
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist z x
  have len : p.length=3 := by rw [hp,dist_comm,d3]
  have middle {u v : V} (q : G.Walk u v) (l : q.length=3) (metric : G.dist v u=3) :
      ∃ w,G.Adj u w ∧ G.dist v w=2 := by
    cases q with
    | nil => simp at l
    | @cons u w v e q =>
      refine ⟨w,e,?_⟩
      have near := G.dist_le q.reverse
      simp only [length_reverse] at near
      have tri := hc.dist_triangle (u:=v) (v:=w) (w:=u)
      have step := dist_eq_one_iff_adj.mpr e.symm
      simp only [length_cons] at l
      omega
  obtain ⟨w,zw,w2⟩ := middle p len d3
  exact ⟨w,eq.symm ▸ (show w∈DistanceTwo G x by simp [DistanceTwo,w2]),zw⟩

#print axioms saturated_common_foreign_port_domination
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
