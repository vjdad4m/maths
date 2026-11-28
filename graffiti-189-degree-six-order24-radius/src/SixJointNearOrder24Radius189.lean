import SixJointNearDispatcher189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private distance_on_geodesic from SmallSeparator189
open private order_sum_odd_shells_of_radius_six from SixThreeRadiusFive189
variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- All fourth-layer vertices with a forward neighbor are an actual
separator as soon as the fifth layer is nonempty. -/
theorem fourth_forward_sites_separate_fifth
    (hc : G.Connected) {x e : V} (e5 : e∈Shell G x 5) :
    ¬(G.induce (↑((Shell G x 4).filter
      (fun d=>∃ y∈Shell G x 5,G.Adj d y)) : Set V)ᶜ).Connected := by
  classical
  let W := (Shell G x 4).filter (fun d=>∃ y∈Shell G x 5,G.Adj d y)
  let S : Set V := (↑W : Set V)ᶜ
  have xW : x∉W := fun h=>by
    have d : G.dist x x=4 := mem_shell.mp (mem_filter.mp h).1
    rw [dist_self] at d
    omega
  have eW : e∉W := fun h=>by
    have d := mem_shell.mp (mem_filter.mp h).1
    have q := mem_shell.mp e5
    omega
  intro conn
  obtain ⟨p⟩ := conn.preconnected (⟨x,xW⟩ : S) (⟨e,eW⟩ : S)
  have walk {a b : S} (q : (G.induce S).Walk a b) :
      G.dist x a.val≤4 → G.dist x b.val≤4 := by
    induction q with
    | nil => exact id
    | @cons a z b aZ p ih =>
      intro h
      apply ih
      by_contra! no
      change G.Adj a.val z.val at aZ
      have o := dist_eq_one_iff_adj.mpr aZ
      have t := hc.dist_triangle (u:=x) (v:=a.val) (w:=z.val)
      have aa : a.val∈Shell G x 4 := mem_shell.mpr (by omega)
      have zz : z.val∈Shell G x 5 := mem_shell.mpr (by omega)
      exact a.property (mem_filter.mpr ⟨aa,z.val,zz,aZ⟩)
  have q := walk p (by simp only [dist_self]; decide : G.dist x x≤4)
  have z := mem_shell.mp e5
  change G.dist x e≤4 at q
  omega

theorem eccentricity_le_four_of_order_ge_twenty_four_at_degree_six
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x : V} (dx : G.degree x≤6) (n : 24≤Fintype.card V) :
    ∀ y,G.dist x y≤4 := by
  classical
  intro y
  by_contra! far
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
  let e := p.getVert 5
  let d := p.getVert 4
  have e5 : e∈Shell G x 5 := mem_shell.mpr (distance_on_geodesic hc p hp 5 (by omega))
  have d4 : d∈Shell G x 4 := mem_shell.mpr (distance_on_geodesic hc p hp 4 (by omega))
  have de : G.Adj d e := p.adj_getVert_succ (i:=4) (by omega)
  have b := shell_card_of_far hc 3 conn (x:=x) (y:=y) (i:=2) (by decide) (by omega)
  have f := shell_card_of_far hc 3 conn (x:=x) (y:=y) (i:=4) (by decide) (by omega)
  have ef := shell_two_four_le_of_even (cap x)
  have b3 : (Shell G x 2).card=3 := by omega
  have rad := diameter_bound_from_inner_even_layers hc 6 3 2 cap conn (by decide)
  have s := order_sum_odd_shells_of_radius_six cap x dx (rad x)
  have loose : 11≤(Shell G x 3).card+(Shell G x 5).card := by omega
  have dj : Disjoint (Shell G x 3) (Shell G x 5) := by
    apply disjoint_left.mpr
    intro k k3 k5
    have a := mem_shell.mp k3
    have b := mem_shell.mp k5
    omega
  have lo : 11≤(Shell G x 3∪Shell G x 5).card := by rwa [card_union_of_disjoint dj]
  obtain ⟨Q⟩ := radius_five_near_equality hc cap x dx b3 loose
  by_cases full : ∀ a∈Q.T,(JointFarGroup G x a).card=4
  · exact Q.no_fifth_support_when_full hc high dx d4 e5 de lo full
  push_neg at full
  obtain ⟨a,aT,an⟩ := full
  have bd := Q.far_card a aT
  have asmall : (JointFarGroup G x a).card<4 := by omega
  let W := (Shell G x 4).filter (fun r=>∃ u∈Shell G x 5,G.Adj r u)
  have wD : W⊆Shell G x 4 := filter_subset _ _
  have all : ∀ r∈W,G.dist a r=4 := by
    intro r rw
    obtain ⟨r4,z,z5,rz⟩ := mem_filter.mp rw
    exact Q.fourth_dist_to_deficient_if_fifth_support hc high dx r4 z5 rz lo aT asmall
  have cnt := Q.fourth_charge hc aT W wD all
  have k : (JointFarGroup G x a).card=3 :=
    (near_cover_deficient_members Q.T (JointFarGroup G x) (Shell G x 3∪Shell G x 5)
      Q.t3 Q.far_cover lo Q.far_card aT asmall).1
  have ws : W.card<3 := by omega
  exact fourth_forward_sites_separate_fifth hc e5 (conn W ws)

#print axioms fourth_forward_sites_separate_fifth
#print axioms eccentricity_le_four_of_order_ge_twenty_four_at_degree_six
end Graffiti189LongestPath
