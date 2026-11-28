import SixJointEquality189
import SixTripleCutBasics189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private distance_on_geodesic lengths_take_drop from SmallSeparator189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem distance_depth_difference (hc : G.Connected) {x y z : V} :
    G.dist x z ≤ G.dist x y + G.dist y z :=
  hc.dist_triangle

theorem mem_nonself_even_of_distance (a z : V)
    (ne : z≠a) (even : Even (G.dist a z)) : z∈(EvenFrom G a).erase a := by
  classical
  exact mem_erase.mpr ⟨ne,mem_filter.mpr ⟨mem_univ _,even⟩⟩

namespace RadiusFiveEquality

theorem no_fourth_at_distance_four
    {x : V} (Q : RadiusFiveEquality G x) {a d : V} (atT : a∈Q.T)
    (d4 : d∈Shell G x 4) : G.dist a d ≠ 4 := by
  intro h
  have aa := mem_shell.mp (Q.near atT)
  have dd := mem_shell.mp d4
  have ne : d≠a := by intro e; rw [e] at dd; omega
  have m := mem_nonself_even_of_distance (G:=G) a d ne (by rw [h]; decide)
  rcases Q.saturated a atT d m with hf|⟨b,bm,eq⟩
  · rcases mem_union.mp hf with j|j
    · have k := mem_shell.mp (mem_inter.mp j).1
      omega
    · have k := mem_shell.mp (mem_inter.mp j).1
      omega
  · have bt := (mem_erase.mp bm).2
    by_cases ab : G.Adj a b
    · rw [if_pos ab] at eq
      rw [eq] at dd
      have k := mem_shell.mp (Q.middle b bt)
      omega
    · rw [if_neg ab] at eq
      rw [eq] at dd
      have k := mem_shell.mp (Q.near bt)
      omega

theorem third_of_rep_adj
    (hc : G.Connected) {x : V} (Q : RadiusFiveEquality G x) {a c : V}
    (atT : a∈Q.T) (c3 : c∈Shell G x 3) (ac : G.Adj (Q.rep a) c) :
    c∈JointFarGroup G x a := by
  have aa := mem_shell.mp (Q.near atT)
  have cc := mem_shell.mp c3
  have ne : a≠c := by intro e; rw [e] at aa; omega
  have na : ¬G.Adj a c := by
    intro e
    have z := dist_eq_one_iff_adj.mpr e
    have t := hc.dist_triangle (u:=x) (v:=a) (w:=c)
    omega
  exact mem_union_left _ (mem_inter.mpr ⟨c3,
    Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne na (Q.adj a atT) ac⟩)

theorem same_group_of_shared_fifth_parent
    (hc : G.Connected) {x : V} (Q : RadiusFiveEquality G x) {e d : V}
    (e5 : e∈Shell G x 5) (de : G.Adj d e)
    {a b c s : V} (atT : a∈Q.T) (btT : b∈Q.T)
    (c3 : c∈Shell G x 3) (s3 : s∈Shell G x 3)
    (ac : G.Adj (Q.rep a) c) (bs : G.Adj (Q.rep b) s)
    (cd : G.Adj c d) (sd : G.Adj s d) : a=b := by
  have close (k : V) (kt : k∈Q.T) (v : V)
      (_v3 : v∈Shell G x 3) (kv : G.Adj (Q.rep k) v) (vd : G.Adj v d) :
      e∈JointFarGroup G x k := by
    have aa := mem_shell.mp (Q.near kt)
    have ee := mem_shell.mp e5
    have one := dist_eq_one_iff_adj.mpr (Q.adj k kt)
    have two := dist_eq_one_iff_adj.mpr kv
    have three := dist_eq_one_iff_adj.mpr vd
    have four := dist_eq_one_iff_adj.mpr de
    have ts := hc.dist_triangle (u:=k) (v:=Q.rep k) (w:=v)
    have tt := hc.dist_triangle (u:=v) (v:=d) (w:=e)
    have tr := hc.dist_triangle (u:=k) (v:=v) (w:=e)
    have tb := hc.dist_triangle (u:=x) (v:=k) (w:=e)
    have ew : G.dist k e=4 := by omega
    exact mem_union_right _ (mem_inter.mpr ⟨e5,mem_shell.mpr ew⟩)
  by_contra different
  exact disjoint_left.mp (Q.far_dis a atT b btT different)
    (close a atT c c3 ac cd) (close b btT s s3 bs sd)

theorem dist_fifth_support_of_different_selection
    (hc : G.Connected) {x : V} (Q : RadiusFiveEquality G x) {e d c a b : V}
    (e5 : e∈Shell G x 5) (d4 : d∈Shell G x 4) (c3 : c∈Shell G x 3)
    (cd : G.Adj c d) (de : G.Adj d e)
    (atT : a∈Q.T) (btT : b∈Q.T) (ab : a≠b) (ac : G.Adj (Q.rep a) c) :
    5≤G.dist b d := by
  have b1 := mem_shell.mp (Q.near btT)
  have d4' := mem_shell.mp d4
  have lo := hc.dist_triangle (u:=x) (v:=b) (w:=d)
  have not4 := Q.no_fourth_at_distance_four btT d4
  have not3 : G.dist b d≠3 := by
    intro bd
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist b d
    have p3 := hp.trans bd
    let u := p.getVert 1
    let v := p.getVert 2
    have depths (i : ℕ) (ip : i≤p.length) : G.dist x (p.getVert i)=i+1 := by
      obtain ⟨take,drop⟩ := lengths_take_drop p i ip
      have q := G.dist_le (p.take i)
      have r := G.dist_le (p.drop i)
      have s := hc.dist_triangle (u:=x) (v:=b) (w:=p.getVert i)
      have t := hc.dist_triangle (u:=x) (v:=p.getVert i) (w:=d)
      omega
    have u2 : u∈Shell G x 2 := mem_shell.mpr (depths 1 (by omega))
    have v3 : v∈Shell G x 3 := mem_shell.mpr (depths 2 (by omega))
    have bu : G.Adj b u := by
      simpa [u] using p.adj_getVert_succ (i:=0) (by omega)
    have uv : G.Adj u v := p.adj_getVert_succ (i:=1) (by omega)
    have vd : G.Adj v d := by
      have s := p.adj_getVert_succ (i:=2) (by omega)
      have t : p.getVert 3=d := by rw [←p3,getVert_length]
      simpa only [t] using s
    obtain ⟨j,jt,jr⟩ := Q.rep_cover u u2
    have bj : b=j := by
      by_contra ne
      exact Q.private_rep j jt b btT ne (jr.symm ▸ bu)
    subst j
    exact ab (Q.same_group_of_shared_fifth_parent hc e5 de atT btT c3 v3 ac
      (jr.symm ▸ uv) cd vd)
  omega

end RadiusFiveEquality

#print axioms RadiusFiveEquality.dist_fifth_support_of_different_selection
end Graffiti189LongestPath
