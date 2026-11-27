import ForcedCredit180
import ActiveContacts180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals PairRepair
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The selected-parity edges meet the protected star whenever the entire
independent marking belongs to that parity and its degree bound is sharp. -/
theorem selected_edges_hit (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A)
    (sat : G.degree a=allowance G r p A+2) (sub : A⊆parity G r p)
    {x y : V} (xp : x∈parity G r p) (yp : y∈parity G r p) (ed : G.Adj x y) :
    G.Adj a x ∨ G.Adj a y := by
  have d := eq_dist G gc r x y p ed (iff_of_true xp yp)
  have xr : x≠r := by
    intro e;subst x
    have pos := gc.pos_dist_of_ne ed.ne.symm
    rw [dist_self] at d;omega
  have yr : y≠r := by
    intro e;subst y
    have pos := gc.pos_dist_of_ne ed.ne
    rw [dist_self] at d;omega
  by_cases xm : x∈A
  · exact Or.inr (parity_covered G gc hn r a ar p A ai am sat sub yp yr (fun ym => ai x xm y ym ed.ne ed))
  · exact Or.inl (parity_covered G gc hn r a ar p A ai am sat sub xp xr xm)

/-- At saturation, any two nonadjacent neighbors of a in the opposite
parity can be kept. Delete all other neighbors of a, and color by the
original distance parity. This works in every degree, and requires only
the stated cover of the selected-parity edges. -/
theorem star_repair (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A)
    (ap : a∈parity G r p) (sat : G.degree a=allowance G r p A+2)
    (hit : ∀ x∈parity G r p,∀ y∈parity G r p,G.Adj x y → G.Adj a x ∨ G.Adj a y)
    (u v : V) (ne : u≠v) (na : ¬G.Adj u v) (au : G.Adj a u) (av : G.Adj a v)
    (up : u∉parity G r p) (vp : v∉parity G r p) : Protected G r p A := by
  classical
  let J : Finset V := {u,v}
  let M := G.neighborFinset a\J
  let Z := univ\M
  have pair : J⊆G.neighborFinset a := insert_subset ((G.mem_neighborFinset ..).mpr au)
    (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr av))
  have inside {x : V} (m : x∈Z) (ed : G.Adj a x) : x∈J := by
    by_contra no
    exact (mem_sdiff.mp m).2 (mem_sdiff.mpr ⟨(G.mem_neighborFinset ..).mpr ed,no⟩)
  have off {x : V} (m : x∈J) : x∉parity G r p := by
    rcases mem_insert.mp m with e | n
    · exact e ▸ up
    · exact (mem_singleton.mp n) ▸ vp
  have ind : Indep G J := by
    intro x xm y ym xy ed
    have split {w : V} (m : w∈J) : w=u ∨ w=v := (mem_insert.mp m).imp_right mem_singleton.mp
    rcases split xm with rfl|rfl <;> rcases split ym with rfl|rfl <;> first | exact xy rfl | exact na ed | exact na ed.symm
  have col : TwoColor G Z := by
    apply (color_function ..).mpr
    refine ⟨fun w => decide (w∈parity G r p),fun x xm y ym ed same => ?_⟩
    have iff : x∈parity G r p ↔ y∈parity G r p := by simpa using same
    by_cases xp : x∈parity G r p
    · have yp := iff.mp xp
      rcases hit x xp y yp ed with ax|ay
      · exact off (inside xm ax) xp
      · exact off (inside ym ay) yp
    · have yp := mt iff.mpr xp
      obtain ⟨ax,ay⟩ := opposite_edges_confined G gc hn r a ar p A ai am ap sat ed xp yp
      exact ind x (inside xm ax) y (inside ym ay) ed.ne ed
  apply (protected_iff G gc hn r p A ai).mpr
  refine ⟨Z,col,?_,?_⟩
  · intro x xm
    exact mem_sdiff.mpr ⟨mem_univ _,fun m => by
      have ed := (G.mem_neighborFinset a x).mp (mem_sdiff.mp m).1
      exact ai a am x (mem_inter.mp xm).1 ed.ne ed⟩
  · have cnt := card_sdiff_add_card_eq_card pair
    change M.card+({u,v}:Finset V).card=(G.neighborFinset a).card at cnt
    rw [card_pair ne,card_neighborFinset_eq_degree] at cnt
    have rem := card_sdiff_add_card_eq_card (subset_univ M)
    change Z.card+M.card=Fintype.card V at rem;omega

/-- A failure of the common terminal color costs at least three when
each separated active region contains an opposite-parity contact and
the independent marking lies in the selected parity. -/
theorem incompatible_forces_three (G : SimpleGraph V) (gc : G.Connected)
    (r a b : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A)
    (sub : A⊆parity G r p) (ab : a≠b) (na : ¬G.Adj a b) (deg : G.degree a=4)
    (bi : TwoColor G (univ\{a,b})) (C D O : Finset V) (h : TwoRegions G a b C D O)
    (c : V→Bool) (cp : ProperOn G (univ\{a,b}) c) (lc : MixedAt G a C c) (rc : MixedAt G a D c)
    (left : ∃ u∈C,G.Adj a u ∧ u∉parity G r p) (right : ∃ v∈D,G.Adj a v ∧ v∉parity G r p)
    (bad : ¬∃ t : Bool,DropCheck G a b (A∩insert r (parity G r p)) C c t ∧
       DropCheck G a b (A∩insert r (parity G r p)) D c t) : 3≤allowance G r p A := by
  classical
  have hi := G.degree_lt_card_verts a
  have hn : 2<Fintype.card V := by omega
  have ap := sub am
  have paid := protected_degree G gc hn r a p A ai (mem_inter.mpr ⟨am,mem_insert_of_mem ap⟩)
  by_contra! small
  have two : allowance G r p A=2 := by omega
  have sat : G.degree a=allowance G r p A+2 := by omega
  obtain ⟨u,uc,au,up⟩ := left
  obtain ⟨v,vd,av,vp⟩ := right
  have ne : u≠v := fun e => disjoint_left.mp h.apart uc (e ▸ vd)
  have good := star_repair G gc (by omega) r a ar p A ai am ap sat
    (fun _ xp _ yp ed => selected_edges_hit G gc (by omega) r a ar p A ai am sat sub xp yp ed)
    u v ne (h.cross u uc v vd) au av up vp
  exact bad ((active_contacts_iff G gc (by omega) r p A ai a b ab na bi am ap deg two C D O h c cp lc rc).mp good)

#print axioms selected_edges_hit
#print axioms star_repair
#print axioms incompatible_forces_three
end Minimal180.OppositeGain
