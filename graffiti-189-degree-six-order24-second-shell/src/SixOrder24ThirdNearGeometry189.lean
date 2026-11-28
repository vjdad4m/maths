import SixJointNearOrder24Radius189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private distance_on_geodesic lengths_take_drop mem_distanceTwo from SmallSeparator189
variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

namespace RadiusFiveNearEquality

theorem selected_degree_le_six_of_nonadj
    (hc : G.Connected) {x : V} (dx : G.degree x≤6)
    (Q : RadiusFiveNearEquality G x) {a b : V} (aT : a∈Q.T) (bT : b∈Q.T)
    (ab : a≠b) (no : ¬G.Adj a b) :
    G.degree a≤6 := by
  classical
  let A := Shell G x 1
  have a1 := mem_shell.mp (Q.near aT)
  have a6 : A.card≤6 := by
    have eq : A=G.neighborFinset x := by
      ext z
      change z∈Shell G x 1 ↔ _
      rw [mem_shell,G.mem_neighborFinset,dist_eq_one_iff_adj]
    rw [eq,G.card_neighborFinset_eq_degree]
    exact dx
  have ae : ((A.erase a).erase b).card≤4 := by
    have ha : a∈A := Q.near aT
    have hb : b∈A.erase a := mem_erase.mpr ⟨ab.symm,Q.near bT⟩
    rw [card_erase_of_mem hb,card_erase_of_mem ha]
    omega
  have sub : G.neighborFinset a⊆insert x (insert (Q.rep a) ((A.erase a).erase b)) := by
    intro z zm
    have az := (G.mem_neighborFinset ..).mp zm
    have o := dist_eq_one_iff_adj.mpr az
    have d := hc.dist_triangle (u:=x) (v:=a) (w:=z)
    have cases : G.dist x z=0 ∨ G.dist x z=1 ∨ G.dist x z=2 := by omega
    rcases cases with h|h|h
    · exact mem_insert.mpr (.inl ((hc.dist_eq_zero_iff.mp h).symm))
    · have zb : z≠b := fun e=>no (e ▸ az)
      exact mem_insert.mpr (.inr (mem_insert.mpr (.inr
        (mem_erase.mpr ⟨zb,mem_erase.mpr ⟨az.ne.symm,mem_shell.mpr h⟩⟩))))
    · obtain ⟨j,jt,je⟩ := Q.rep_cover z (mem_shell.mpr h)
      have aj : a=j := by
        by_contra ne
        exact Q.private_rep j jt a aT ne (je.symm ▸ az)
      subst j
      exact mem_insert.mpr (.inr (mem_insert.mpr (.inl je.symm)))
  have l := (card_le_card sub).trans (card_insert_le x (insert (Q.rep a) ((A.erase a).erase b)))
  have k := card_insert_le (Q.rep a) ((A.erase a).erase b)
  rw [G.card_neighborFinset_eq_degree] at l
  omega

/-- At maximum order, every fourth-layer vertex has a neighbor
in the fourth-size third-layer group of every selector. -/
theorem fourth_meets_full_group
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x : V} (dx : G.degree x≤6) (n : 24≤Fintype.card V)
    (Q : RadiusFiveNearEquality G x) {a d : V} (aT : a∈Q.T) (full : (JointFarGroup G x a).card=4) (d4 : d∈Shell G x 4) :
    Q.Active d a := by
  have a1 := mem_shell.mp (Q.near aT)
  have d4' := mem_shell.mp d4
  have adlo := hc.dist_triangle (u:=x) (v:=a) (w:=d)
  have ad4 : G.dist a d≤4 := by
    by_cases lo : G.degree a≤6
    · exact eccentricity_le_four_of_order_ge_twenty_four_at_degree_six hc cap conn high lo n d
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x d
    have len := hp.trans d4'
    let b := p.getVert 2
    let c := p.getVert 3
    have x2 : b∈Shell G x 2 := mem_shell.mpr (distance_on_geodesic hc p hp 2 (by omega))
    have bc : G.Adj b c := p.adj_getVert_succ (i:=2) (by omega)
    have cd : G.Adj c d := by
      have e := p.adj_getVert_succ (i:=3) (by omega)
      have ed : p.getVert 4=d := by rw [←len,getVert_length]
      simpa only [ed] using e
    obtain ⟨i,iT,ir⟩ := Q.rep_cover b x2
    have ib : G.Adj i b := ir ▸ Q.adj i iT
    have q := hc.dist_triangle (u:=b) (v:=c) (w:=d)
    have r := hc.dist_triangle (u:=i) (v:=b) (w:=d)
    have one := dist_eq_one_iff_adj.mpr ib
    have two := dist_eq_one_iff_adj.mpr bc
    have three := dist_eq_one_iff_adj.mpr cd
    have id : G.dist i d≤3 := by omega
    by_cases ai : a=i
    · rw [ai]
      omega
    have ia : G.Adj a i := by
      by_contra na
      exact lo (selected_degree_le_six_of_nonadj hc dx Q aT iT ai na)
    have o := dist_eq_one_iff_adj.mpr ia
    have t := hc.dist_triangle (u:=a) (v:=i) (w:=d)
    omega
  have not4 : G.dist a d≠4 := by
    intro h
    have b := Q.fourth_charge hc aT {d} (singleton_subset_iff.mpr d4)
      (fun u um=>by have e := mem_singleton.mp um; simpa [e] using h)
    rw [card_singleton,full] at b
    omega
  exact Q.active_of_dist_three hc aT d4 (by omega)

end RadiusFiveNearEquality

#print axioms RadiusFiveNearEquality.fourth_meets_full_group
end Graffiti189LongestPath
