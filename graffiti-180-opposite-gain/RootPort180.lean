import ParityRepair180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A root marked only by the independent set has degree one when the
degree bound of a different doubly marked vertex is saturated. -/
theorem single_root_degree (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A) (ap : a∈parity G r p)
    (ra : r∈A) (rp : r∉parity G r p) (sat : G.degree a=allowance G r p A+2) : G.degree r=1 := by
  classical
  have no : ¬G.Adj a r := ai a am r ra ar
  have odd := (mem_parity G r a p).mp ap
  have rpar : ¬G.dist r r%2=p.toNat := fun e => rp ((mem_parity ..).mpr e)
  rw [dist_self] at rpar
  have far : 2<G.dist a r := by
    have pos := gc.pos_dist_of_ne ar
    have neq : G.dist a r≠1 := mt dist_eq_one_iff_adj.mp no
    cases p
    · exact (rpar rfl).elim
    · change G.dist a r%2=1 at odd
      omega
  let F := G.neighborFinset r
  have nr (x : V) (m : x∈F) : G.Adj r x := (G.mem_neighborFinset ..).mp m
  have src (x : V) (m : x∈F) : x≠r ∧ ¬G.Adj a x ∧ x≠a ∧ G.Adj x r := by
    have rx := nr x m
    refine ⟨rx.ne.symm,?_,fun eq => no (eq ▸ rx.symm),rx.symm⟩
    intro ax
    have d := gc.dist_triangle (u:=a) (v:=x) (w:=r)
    rw [dist_eq_one_iff_adj.mpr ax,dist_eq_one_iff_adj.mpr rx.symm] at d;omega
  obtain ⟨T,q,k,sub,tree,down,take,deg,pres,pay⟩ := star_parents G gc r a r ar p A ai am F src
    (fun x _ => Or.inl (show G.dist r r≤G.dist x r by rw [dist_self];exact Nat.zero_le _)) (fun x m both => (ai r ra x (mem_inter.mp both).1 (nr x m).ne (nr x m)).elim)
  have rootInc : F⊆T.neighborFinset r := by
    intro x mem
    exact (T.mem_neighborFinset ..).mpr ((pres x mem) ▸ (take x (nr x mem).ne.symm).symm)
  have rootDeg : G.degree r≤T.degree r := by simpa only [F,card_neighborFinset_eq_degree] using card_le_card rootInc
  have cost := parent_gain_with_root G T gc hn sub tree r p A ai q k down take pay ∅ (by simp)
  have rm : r∈(A∪parity G r p)\(A∩parity G r p) := mem_sdiff.mpr
    ⟨mem_union_left _ ra,fun m => rp (mem_inter.mp m).2⟩
  rw [if_pos rm,card_empty,add_zero] at cost
  have aa : a∈(A∪parity G r p).erase r := mem_erase.mpr ⟨ar,mem_union_left _ am⟩
  have bound := single_le_sum (f:=fun x => T.degree x-2) (fun _ _ => Nat.zero_le _) aa
  change T.degree a-2≤∑ v∈(A∪parity G r p).erase r,(T.degree v-2) at bound
  have pos := (G.degree_pos_iff_exists_adj r).mpr (exists_adj G gc hn r)
  omega

/-- A selected-parity edge missed by the star forces a nonroot
off-parity independent mark one layer closer to the root. Its endpoint
outside the independent marking sees only independent-mark predecessors. -/
theorem missed_edge_parent (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A) (ap : a∈parity G r p)
    (sat : G.degree a=allowance G r p A+2) {x y : V} (xp : x∈parity G r p) (yp : y∈parity G r p)
    (ed : G.Adj x y) (xa : x∉A) (ax : ¬G.Adj a x) :
    ∃ z,z≠r ∧ z∈A ∧ z∉parity G r p ∧ G.Adj x z ∧ G.dist x r=G.dist z r+1 ∧
      ∀ w,G.Adj x w → G.dist x r=G.dist w r+1 → w∈A := by
  classical
  have d := eq_dist G gc r x y p ed (iff_of_true xp yp)
  have xr : x≠r := by
    intro eq;subst x;rw [dist_self] at d;have := gc.pos_dist_of_ne ed.ne.symm;omega
  have preds := fun w (edge : G.Adj x w) (dw : G.dist x r=G.dist w r+1) =>
    outside_predecessors_marked G gc hn r a ar p A ai am sat xr ax xp xa edge dw
  obtain ⟨z,ez,dz⟩ := Graffiti169.exists_predecessor G gc r x xr
  have za := preds z ez dz
  have zp : z∉parity G r p := fun m => by have e := eq_dist G gc r x z p ez (iff_of_true xp m);omega
  refine ⟨z,?_,za,zp,ez,dz,preds⟩
  intro eq;subst z
  have small := single_root_degree G gc hn r a ar p A ai am ap za zp sat
  rw [dist_self] at dz
  have ey : G.Adj y r := dist_eq_one_iff_adj.mp (by omega)
  have sub : ({x,y}:Finset V)⊆G.neighborFinset r := insert_subset ((G.mem_neighborFinset ..).mpr ez.symm)
    (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr ey.symm))
  have ct := card_le_card sub
  rw [card_pair ed.ne,card_neighborFinset_eq_degree] at ct;omega

#print axioms single_root_degree
#print axioms missed_edge_parent
end Minimal180.OppositeGain
