import SixJointNearCover189
import SixJointEqualityGeometry189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private lengths_take_drop mem_distanceTwo from SmallSeparator189
variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

namespace RadiusFiveNearEquality

theorem full_saturated {x a : V} (Q : RadiusFiveNearEquality G x)
    (aT : a∈Q.T) (full : (JointFarGroup G x a).card=4)
    (z : V) (ze : z∈(EvenFrom G a).erase a) :
    z∈JointFarGroup G x a ∨ ∃ b∈Q.T.erase a,z=(if G.Adj a b then Q.rep b else b) := by
  classical
  by_cases zg : z∈JointFarGroup G x a
  · exact Or.inl zg
  right
  by_contra! no
  have h := Q.extra a aT {z} (singleton_subset_iff.mpr ze)
    (by exact disjoint_left.mpr (fun w wm wg=>zg ((mem_singleton.mp wm) ▸ wg)))
    (fun w wm b bm=>by have we := mem_singleton.mp wm; subst w; exact no b bm)
  rw [card_singleton,full] at h
  omega

def Active {x : V} (Q : RadiusFiveNearEquality G x) (d a : V) : Prop :=
  ∃ c∈Shell G x 3,G.Adj (Q.rep a) c ∧ G.Adj c d

theorem dist_le_three_of_active (hc : G.Connected)
    {x a d : V} (Q : RadiusFiveNearEquality G x) (aT : a∈Q.T)
    (live : Q.Active d a) : G.dist a d≤3 := by
  obtain ⟨c,_,bc,cd⟩ := live
  have one := dist_eq_one_iff_adj.mpr (Q.adj a aT)
  have two := dist_eq_one_iff_adj.mpr bc
  have three := dist_eq_one_iff_adj.mpr cd
  have t := hc.dist_triangle (u:=a) (v:=Q.rep a) (w:=d)
  have q := hc.dist_triangle (u:=Q.rep a) (v:=c) (w:=d)
  omega

theorem active_of_dist_three (hc : G.Connected)
    {x a d : V} (Q : RadiusFiveNearEquality G x) (aT : a∈Q.T)
    (d4 : d∈Shell G x 4) (h : G.dist a d=3) : Q.Active d a := by
  have a1 := mem_shell.mp (Q.near aT)
  have d4' := mem_shell.mp d4
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a d
  have p3 := hp.trans h
  let u := p.getVert 1
  let v := p.getVert 2
  have depths (i : ℕ) (ip : i≤p.length) : G.dist x (p.getVert i)=i+1 := by
    obtain ⟨take,drop⟩ := lengths_take_drop p i ip
    have q := G.dist_le (p.take i)
    have r := G.dist_le (p.drop i)
    have s := hc.dist_triangle (u:=x) (v:=a) (w:=p.getVert i)
    have t := hc.dist_triangle (u:=x) (v:=p.getVert i) (w:=d)
    omega
  have u2 : u∈Shell G x 2 := mem_shell.mpr (depths 1 (by omega))
  have v3 : v∈Shell G x 3 := mem_shell.mpr (depths 2 (by omega))
  have au : G.Adj a u := by simpa [u] using p.adj_getVert_succ (i:=0) (by omega)
  have uv : G.Adj u v := p.adj_getVert_succ (i:=1) (by omega)
  have vd : G.Adj v d := by
    have s := p.adj_getVert_succ (i:=2) (by omega)
    have t : p.getVert 3=d := by rw [←p3,getVert_length]
    simpa only [t] using s
  obtain ⟨j,jt,jr⟩ := Q.rep_cover u u2
  have aj : a=j := by
    by_contra ne
    exact Q.private_rep j jt a aT ne (jr.symm ▸ au)
  subst j
  exact ⟨v,v3,jr.symm ▸ uv,vd⟩

theorem fifth_mem_of_active (hc : G.Connected)
    {x a d e : V} (Q : RadiusFiveNearEquality G x) (aT : a∈Q.T)
    (de : G.Adj d e) (e5 : e∈Shell G x 5) (live : Q.Active d a) :
    e∈JointFarGroup G x a := by
  have r := Q.dist_le_three_of_active hc aT live
  have a1 := mem_shell.mp (Q.near aT)
  have dst := hc.dist_triangle (u:=a) (v:=d) (w:=e)
  have lo := hc.dist_triangle (u:=x) (v:=a) (w:=e)
  have one := dist_eq_one_iff_adj.mpr de
  have e5' := mem_shell.mp e5
  exact mem_union_right _ (mem_inter.mpr ⟨e5,mem_shell.mpr (by omega)⟩)

theorem fourth_charge (_hc : G.Connected)
    {x a : V} (Q : RadiusFiveNearEquality G x) (aT : a∈Q.T)
    (W : Finset V) (w4 : W⊆Shell G x 4) (dist4 : ∀ d∈W,G.dist a d=4) :
    W.card+(JointFarGroup G x a).card≤4 := by
  have a1 := mem_shell.mp (Q.near aT)
  apply Q.extra a aT W
  · intro d dm
    have z := dist4 d dm
    have d4 := mem_shell.mp (w4 dm)
    have ne : d≠a := by intro e; rw [e] at d4; omega
    exact mem_nonself_even_of_distance a d ne (by rw [z]; decide)
  · apply disjoint_left.mpr
    intro d dm dg
    have d4 := mem_shell.mp (w4 dm)
    rcases mem_union.mp dg with h|h
    · have e := mem_shell.mp (mem_inter.mp h).1
      omega
    · have e := mem_shell.mp (mem_inter.mp h).1
      omega
  · intro d dm b bm eq
    have d4 := mem_shell.mp (w4 dm)
    have bt := (mem_erase.mp bm).2
    by_cases edge : G.Adj a b
    · rw [if_pos edge] at eq
      rw [eq] at d4
      have r := mem_shell.mp (Q.middle b bt)
      omega
    · rw [if_neg edge] at eq
      rw [eq] at d4
      have r := mem_shell.mp (Q.near bt)
      omega

theorem far_of_full_inactive (hc : G.Connected)
    {x a d : V} (Q : RadiusFiveNearEquality G x) (aT : a∈Q.T)
    (full : (JointFarGroup G x a).card=4)
    (d4 : d∈Shell G x 4) (inactive : ¬Q.Active d a) : 5≤G.dist a d := by
  have a1 := mem_shell.mp (Q.near aT)
  have dd := mem_shell.mp d4
  have lo := hc.dist_triangle (u:=x) (v:=a) (w:=d)
  have n3 : G.dist a d≠3 := fun h=>inactive (Q.active_of_dist_three hc aT d4 h)
  have n4 : G.dist a d≠4 := by
    intro h
    have b := Q.fourth_charge hc aT {d} (singleton_subset_iff.mpr d4)
      (fun u um=>by have e := mem_singleton.mp um; simpa [e] using h)
    rw [card_singleton,full] at b
    omega
  omega

theorem adj_extra_near
    (hc : G.Connected) {x : V} (Q : RadiusFiveNearEquality G x)
    {a z : V} (aT : a∈Q.T) (full : (JointFarGroup G x a).card=4) (z1 : z∈Shell G x 1) (zT : z∉Q.T) :
    G.Adj a z := by
  by_contra nz
  have ne : a≠z := fun e=>zT (e ▸ aT)
  have ax := (dist_eq_one_iff_adj.mp (mem_shell.mp (Q.near aT))).symm
  have xz := dist_eq_one_iff_adj.mp (mem_shell.mp z1)
  have zd := Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne nz ax xz
  have ze := mem_nonself_even_of_distance (G:=G) a z ne.symm (by rw [mem_distanceTwo.mp zd]; decide)
  rcases Q.full_saturated aT full z ze with zf|⟨b,bm,eq⟩
  · rcases mem_union.mp zf with h|h
    · have v := mem_shell.mp (mem_inter.mp h).1
      have j := mem_shell.mp z1
      omega
    · have v := mem_shell.mp (mem_inter.mp h).1
      have j := mem_shell.mp z1
      omega
  · have bt := (mem_erase.mp bm).2
    by_cases ab : G.Adj a b
    · rw [if_pos ab] at eq
      have v := mem_shell.mp (Q.middle b bt)
      rw [←eq] at v
      have j := mem_shell.mp z1
      omega
    · rw [if_neg ab] at eq
      exact zT (eq.symm ▸ bt)

theorem no_rep_at_distance_two_if_nonadj
    (_hc : G.Connected) {x : V} (Q : RadiusFiveNearEquality G x)
    {a b : V} (aT : a∈Q.T) (bT : b∈Q.T) (full : (JointFarGroup G x b).card=4) (no : ¬G.Adj b a) :
    Q.rep a∉DistanceTwo G b := by
  intro md
  have rep2 := mem_shell.mp (Q.middle a aT)
  have b1 := mem_shell.mp (Q.near bT)
  have ne : Q.rep a≠b := by intro e; rw [e] at rep2; omega
  have ee := mem_nonself_even_of_distance (G:=G) b (Q.rep a) ne
    (by rw [mem_distanceTwo.mp md]; decide)
  rcases Q.full_saturated bT full (Q.rep a) ee with zf|⟨j,jm,eq⟩
  · rcases mem_union.mp zf with h|h
    · have v := mem_shell.mp (mem_inter.mp h).1
      omega
    · have v := mem_shell.mp (mem_inter.mp h).1
      omega
  · have jt := (mem_erase.mp jm).2
    by_cases bj : G.Adj b j
    · rw [if_pos bj] at eq
      by_cases aj : a=j
      · exact no (aj.symm ▸ bj)
      exact Q.private_rep j jt a aT aj (eq ▸ Q.adj a aT)
    · rw [if_neg bj] at eq
      have v := mem_shell.mp (Q.near jt)
      rw [←eq] at v
      omega

end RadiusFiveNearEquality

#print axioms RadiusFiveNearEquality.far_of_full_inactive
end Graffiti189LongestPath
