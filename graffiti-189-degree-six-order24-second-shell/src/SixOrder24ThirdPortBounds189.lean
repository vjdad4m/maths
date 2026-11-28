import SixOrder24ThirdRepCharge189

namespace Graffiti189LongestPath
open SimpleGraph Finset
variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

namespace RadiusFiveNearEquality

theorem selected_degree_le_two_add_spares_add_partners (hc : G.Connected)
    {x a : V} (Q : RadiusFiveNearEquality G x)
    (aT : a∈Q.T) :
    G.degree a≤2+((Shell G x 1)\Q.T).card+(Q.nearPartners a).card := by
  classical
  let A := Shell G x 1
  let R := A\Q.T
  let J := Q.nearPartners a
  have a1 := mem_shell.mp (Q.near aT)
  have sub : G.neighborFinset a⊆insert x (insert (Q.rep a) (R∪J)) := by
    intro z zm
    have az := (G.mem_neighborFinset ..).mp zm
    have o := dist_eq_one_iff_adj.mpr az
    have d := hc.dist_triangle (u:=x) (v:=a) (w:=z)
    have cases : G.dist x z=0 ∨ G.dist x z=1 ∨ G.dist x z=2 := by omega
    apply mem_insert.mpr
    rcases cases with h|h|h
    · exact Or.inl ((hc.dist_eq_zero_iff.mp h).symm)
    · right
      apply mem_insert.mpr
      right
      by_cases zT : z∈Q.T
      · exact mem_union_right _ (mem_filter.mpr ⟨zT,az⟩)
      · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_shell.mpr h,zT⟩)
    · obtain ⟨j,jt,je⟩ := Q.rep_cover z (mem_shell.mpr h)
      have aj : a=j := by
        by_contra ne
        exact Q.private_rep j jt a aT ne (je.symm ▸ az)
      subst j
      exact Or.inr (mem_insert.mpr (.inl je.symm))
  have l := (card_le_card sub).trans (card_insert_le x (insert (Q.rep a) (R∪J)))
  have q := card_insert_le (Q.rep a) (R∪J)
  have k := card_union_le R J
  rw [G.card_neighborFinset_eq_degree] at l
  change G.degree a≤2+R.card+J.card
  omega

noncomputable def thirdPorts {x : V} (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) :=
  (Shell G x 4).filter (G.Adj z)

theorem third_degree_bound_of_group
    (hc : G.Connected) {x a z : V} (Q : RadiusFiveNearEquality G x)
    (_aT : a∈Q.T) (zg : z∈JointFarGroup G x a)
    (none : Shell G x 5=∅)
    (unique : ∀ b∈Q.T,z∈JointFarGroup G x b → a=b)
    (F : Finset V)
    (f : ∀ w∈Shell G x 3,w∉JointFarGroup G x a → G.Adj z w → w∈F) :
    G.degree z ≤ (JointFarGroup G x a).card + F.card + (thirdPorts (x:=x) G z).card := by
  classical
  let W := JointFarGroup G x a
  let P := thirdPorts (x:=x) G z
  have z3 := mem_shell.mp (radius_four_group_sub_third none zg)
  have sub : G.neighborFinset z⊆insert (Q.rep a) ((W.erase z∪F)∪P) := by
    intro w wm
    have zw := (G.mem_neighborFinset ..).mp wm
    have o := dist_eq_one_iff_adj.mpr zw
    have oo := dist_eq_one_iff_adj.mpr zw.symm
    have r := hc.dist_triangle (u:=x) (v:=z) (w:=w)
    have t := hc.dist_triangle (u:=x) (v:=w) (w:=z)
    have dep : G.dist x w=2 ∨ G.dist x w=3 ∨ G.dist x w=4 := by omega
    apply mem_insert.mpr
    rcases dep with d|d|d
    · obtain ⟨b,bT,br⟩ := Q.rep_cover w (mem_shell.mpr d)
      have zB := Q.third_of_rep_adj hc bT (mem_shell.mpr z3) (br.symm ▸ zw.symm)
      have ab := unique b bT zB
      subst b
      exact Or.inl br.symm
    · right
      apply mem_union_left
      by_cases wW : w∈W
      · exact mem_union_left _ (mem_erase.mpr ⟨zw.ne.symm,wW⟩)
      · exact mem_union_right _ (f w (mem_shell.mpr d) wW zw)
    · exact Or.inr (mem_union_right _ (mem_filter.mpr ⟨mem_shell.mpr d,zw⟩))
  have v := (card_le_card sub).trans (card_insert_le (Q.rep a) ((W.erase z∪F)∪P))
  have u := card_union_le (W.erase z∪F) P
  have w := card_union_le (W.erase z) F
  rw [G.card_neighborFinset_eq_degree] at v
  have e := card_erase_add_one zg
  change (W.erase z).card+1=W.card at e
  change G.degree z≤W.card+F.card+P.card
  omega

theorem third_degree_bound_of_unique_group
    (hc : G.Connected) {x a z : V} (Q : RadiusFiveNearEquality G x)
    (aT : a∈Q.T) (zg : z∈JointFarGroup G x a)
    (none : Shell G x 5=∅)
    (unique : ∀ b∈Q.T,z∈JointFarGroup G x b → a=b) :
    G.degree z ≤ (JointFarGroup G x a).card + (Q.foreignThird a).card +
      (thirdPorts (x:=x) G z).card :=
  Q.third_degree_bound_of_group hc aT zg none unique _ (fun _w w3 nW adj=>
    mem_filter.mpr ⟨w3,nW,z,zg,adj⟩)

theorem third_ports_of_no_cross
    (hc : G.Connected) {x a z : V} (Q : RadiusFiveNearEquality G x)
    (aT : a∈Q.T) (zg : z∈JointFarGroup G x a) (high : 6≤G.degree z)
    (none : Shell G x 5=∅)
    (unique : ∀ b∈Q.T,z∈JointFarGroup G x b → a=b)
    (no : ∀ w∈Shell G x 3,w∉JointFarGroup G x a → ¬G.Adj z w) :
    6≤(JointFarGroup G x a).card+(thirdPorts (x:=x) G z).card := by
  have h := Q.third_degree_bound_of_group hc aT zg none unique ∅
    (fun w w3 nW adj=>False.elim (no w w3 nW adj))
  rw [card_empty] at h
  omega

end RadiusFiveNearEquality

#print axioms RadiusFiveNearEquality.third_degree_bound_of_group
#print axioms RadiusFiveNearEquality.selected_degree_le_two_add_spares_add_partners
end Graffiti189LongestPath
