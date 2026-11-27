import TwoStars180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals PairRepair
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every failure in the single-protected, nonroot pair case produces
a selected-parity edge in a different layer, missing the whole star.
At a singly marked endpoint all shortest predecessors are independently
marked. One such nonroot predecessor either has degree at most two,
or the edge is exactly two layers beyond the protected tip. -/
theorem remote_obstruction (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a b : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A)
    (ab : a≠b) (bi : TwoColor G (univ\{a,b})) (ak : a∈A∩insert r (parity G r p))
    (bk : b∉A∩insert r (parity G r p)) (bad : ¬Protected G r p A) :
    ∃ x y z,G.Adj x y ∧ x∈parity G r p ∧ y∈parity G r p ∧ x∉A ∧ ¬G.Adj a x ∧ ¬G.Adj a y ∧
      G.dist x r=G.dist y r ∧ G.dist x r≠G.dist a r ∧ z≠r ∧ z∈A ∧ z∉parity G r p ∧
      G.Adj x z ∧ G.dist x r=G.dist z r+1 ∧ (∀ w,G.Adj x w → G.dist x r=G.dist w r+1 → w∈A) ∧
      (G.degree z≤2 ∨ (G.dist x r=G.dist a r+2 ∧ ∃ v,G.Adj a v ∧ G.Adj z v)) := by
  classical
  have ap := (mem_insert.mp (mem_inter.mp ak).2).resolve_left ar
  have am := (mem_inter.mp ak).1
  obtain ⟨deg,two,_⟩ := solo_rigidity G gc hn r p A ai bad a b ab bi ak bk
  have high : 2<Fintype.card V := by have := G.degree_lt_card_verts a;omega
  have sat : G.degree a=allowance G r p A+2 := by omega
  have na := (pair_obstruction G gc hn r p A ai bad a b ab bi).1
  have ns : G.neighborFinset a⊆univ\{a,b} := by
    intro x xm
    have ed := (G.mem_neighborFinset ..).mp xm
    refine mem_sdiff.mpr ⟨mem_univ _,fun m => ?_⟩
    rcases mem_insert.mp m with h|h
    · exact ed.ne h.symm
    · exact na ((mem_singleton.mp h) ▸ ed)
  obtain ⟨c,cp⟩ := (color_function ..).mp bi
  have nbi : TwoColor G (G.neighborFinset a) := (color_function ..).mpr
    ⟨c,fun i im j jm => cp i (ns im) j (ns jm)⟩
  have uncovered : ¬∀ x∈parity G r p,∀ y∈parity G r p,G.Adj x y → G.Adj a x ∨ G.Adj a y :=
    fun hit => bad (repair_of_cover G gc high r a ar p A ai am ap sat nbi hit)
  push_neg at uncovered
  obtain ⟨i,ip,j,jp,ij,ni,nj⟩ := uncovered
  have labeled : ∃ x y,x∈parity G r p ∧ y∈parity G r p ∧ G.Adj x y ∧ ¬G.Adj a x ∧ ¬G.Adj a y ∧ x∉A := by
    by_cases m : i∈A
    · exact ⟨j,i,jp,ip,ij.symm,nj,ni,fun n => ai i m j n ij.ne ij⟩
    · exact ⟨i,j,ip,jp,ij,ni,nj,m⟩
  obtain ⟨x,y,xp,yp,ed,ax,ay,xa⟩ := labeled
  have dx := eq_dist G gc r x y p ed (iff_of_true xp yp)
  have diff : G.dist x r≠G.dist a r := fun eq =>
    ax (((saturated_layer G gc high r a p A ai ar am ap sat).2 x eq).mp xa)
  obtain ⟨z,zr,za,zp,xz,dz,allPred⟩ := missed_edge_parent G gc hn r a ar p A ai am ap sat xp yp ed xa ax
  refine ⟨x,y,z,ed,xp,yp,xa,ax,ay,dx,diff,zr,za,zp,xz,dz,allPred,?_⟩
  by_cases low : G.degree z≤2
  · exact Or.inl low
  · have near : ∃ v,G.Adj a v ∧ G.Adj z v := by
      by_contra! apart
      have bound := two_stars_gain G gc hn r a z ar zr (fun eq => zp (eq ▸ ap)) p A ai am za apart
      omega
    obtain ⟨v,av,zv⟩ := near
    have va := gc.dist_triangle (u:=a) (v:=v) (w:=r)
    have vz := gc.dist_triangle (u:=z) (v:=v) (w:=r)
    have av' := gc.dist_triangle (u:=v) (v:=a) (w:=r)
    have zv' := gc.dist_triangle (u:=v) (v:=z) (w:=r)
    rw [dist_eq_one_iff_adj.mpr av] at va
    rw [dist_eq_one_iff_adj.mpr zv] at vz
    rw [dist_eq_one_iff_adj.mpr av.symm] at av'
    rw [dist_eq_one_iff_adj.mpr zv.symm] at zv'
    have xp' := (mem_parity ..).mp xp
    have ap' := (mem_parity ..).mp ap
    exact Or.inr ⟨by omega,⟨v,av,zv⟩⟩

/-- Three alternatives suffice for every one- or two-component configuration.
In the third it suffices to check the degrees of off-parity, nonroot
independent marks; the prohibited horizontal level is exactly d(a)+2. -/
def RepairScope (G : SimpleGraph V) (r a : V) (p : Bool) (A : Finset V) : Prop :=
  A⊆insert r (parity G r p) ∨
    (∀ x∈parity G r p,∀ y∈parity G r p,G.Adj x y → G.dist x r=G.dist a r) ∨
    ((∀ z∈A,z≠r → z∉parity G r p → 3≤G.degree z) ∧
      ∀ x∈parity G r p,∀ y∈parity G r p,G.Adj x y → G.dist x r≠G.dist a r+2)

theorem solo_scope (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a b : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A)
    (ab : a≠b) (bi : TwoColor G (univ\{a,b})) (ak : a∈A∩insert r (parity G r p))
    (bk : b∉A∩insert r (parity G r p)) (scope : RepairScope G r a p A) : Protected G r p A := by
  by_contra bad
  obtain ⟨x,y,z,ed,xp,yp,_,_,_,_,diff,zr,za,zp,_,_,_,alt⟩ := remote_obstruction G gc hn r a b ar p A ai ab bi ak bk bad
  rcases scope with sub | layer | ⟨degrees,levels⟩
  · exact zp ((mem_insert.mp (sub za)).resolve_left zr)
  · exact diff (layer x xp y yp ed)
  · rcases alt with lo | ⟨far,_⟩
    · have := degrees z za zr zp;omega
    · exact levels x xp y yp ed far

/-- A graph-wide specialization of the third alternative. -/
theorem solo_outer_layers (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a b : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A)
    (ab : a≠b) (bi : TwoColor G (univ\{a,b})) (ak : a∈A∩insert r (parity G r p))
    (bk : b∉A∩insert r (parity G r p)) (dg : ∀ v,3≤G.degree v)
    (dist : ∀ v,G.dist v r≤G.dist a r+1) : Protected G r p A :=
  solo_scope G gc hn r a b ar p A ai ab bi ak bk (Or.inr (Or.inr
    ⟨fun z _ _ _ => dg z,fun x _ _ _ _ => by have := dist x;omega⟩))

#print axioms remote_obstruction
#print axioms solo_scope
#print axioms solo_outer_layers
end Minimal180.OppositeGain
