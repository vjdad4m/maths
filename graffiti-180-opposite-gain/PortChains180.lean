import RemoteLayer180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals PairRepair
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem common_port (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a z : V) (ar : a≠r) (zr : z≠r) (az : a≠z) (p : Bool) (A : Finset V) (ai : Indep G A)
    (am : a∈A) (zm : z∈A) (sat : G.degree a=allowance G r p A+2) (hi : 3≤G.degree z) :
    ∃ w,G.Adj a w ∧ G.Adj z w := by
  by_contra! apart
  have bound := two_stars_gain G gc hn r a z ar zr az p A ai am zm apart
  omega

/-- From an off-parity independent mark one level beyond a, a common
neighbor w with a is horizontal. Its ascending edge to z occupies its
only outside vertical position. Every predecessor of w is therefore
also a neighbor of a, supplying a second, lower port in the same wing. -/
theorem paired_ports (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a z : V) (ar : a≠r) (zr : z≠r) (p : Bool) (A : Finset V) (ai : Indep G A)
    (am : a∈A) (ap : a∈parity G r p) (zm : z∈A) (zp : z∉parity G r p)
    (sat : G.degree a=allowance G r p A+2) (hi : 3≤G.degree z) (dz : G.dist z r=G.dist a r+1) :
    ∃ w u,G.Adj a w ∧ G.Adj z w ∧ w∈parity G r p ∧ G.dist w r=G.dist a r ∧
      G.Adj a u ∧ G.Adj w u ∧ G.dist a r=G.dist u r+1 := by
  classical
  have az : a≠z := fun e => zp (e ▸ ap)
  have nz : ¬G.Adj a z := ai a am z zm az
  obtain ⟨w,aw,zw⟩ := common_port G gc hn r a z ar zr az p A ai am zm sat hi
  have wp : w∈parity G r p := by
    by_contra no
    exact nz (opposite_edges_confined G gc hn r a ar p A ai am ap sat zw zp no).1
  have dw := eq_dist G gc r w a p aw.symm (iff_of_true wp ap)
  have wr : w≠r := by
    intro e;subst w;rw [dist_self] at dw;exact ar (gc.dist_eq_zero_iff.mp dw.symm)
  obtain ⟨u,wu,du⟩ := Graffiti169.exists_predecessor G gc r w wr
  have up : u∉parity G r p := fun hit => by have e := eq_dist G gc r w u p wu (iff_of_true wp hit);omega
  have au : G.Adj a u := by
    by_contra no
    have small := horizontal_port G gc hn r a w ar p A ai am ap aw wp sat
    have eq := card_le_one.mp small z (mem_filter.mpr ⟨(G.mem_neighborFinset ..).mpr zw.symm,zp,nz⟩)
      u (mem_filter.mpr ⟨(G.mem_neighborFinset ..).mpr wu,up,no⟩)
    rw [eq] at dz;omega
  exact ⟨w,u,aw,zw,wp,dw,au,wu,by omega⟩

/-- A nonroot independently marked predecessor can have at most one
non-double successor outside the full protected star under saturation. -/
theorem unique_successor (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a z x y : V) (ar : a≠r) (zr : z≠r) (az : a≠z) (p : Bool) (A : Finset V) (ai : Indep G A)
    (am : a∈A) (zm : z∈A) (sat : G.degree a=allowance G r p A+2)
    (xa : x∉A) (ya : y∉A) (ax : ¬G.Adj a x) (ay : ¬G.Adj a y) (xz : G.Adj x z) (yz : G.Adj y z)
    (dx : G.dist x r=G.dist z r+1) (dy : G.dist y r=G.dist z r+1) : x=y := by
  classical
  have src {t : V} (m : t∈({x,y}:Finset V)) : t≠r ∧ ¬G.Adj a t ∧ t≠a ∧ G.Adj t z ∧
      t∉A ∧ G.dist t r=G.dist z r+1 := by
    rcases mem_insert.mp m with eq|e
    · subst t
      exact ⟨fun e => by rw [e,dist_self] at dx;omega,ax,fun e => xa (e ▸ am),xz,xa,dx⟩
    · obtain rfl := mem_singleton.mp e
      exact ⟨fun e => by rw [e,dist_self] at dy;omega,ay,fun e => ya (e ▸ am),yz,ya,dy⟩
  have bound := second_branch G gc hn r a z ar p A ai am az.symm zr (mem_union_left _ zm) {x,y}
    (fun _ m => ⟨(src m).1,(src m).2.1,(src m).2.2.1,(src m).2.2.2.1⟩)
    (fun _ m => Or.inl (Nat.le_of_lt (by rw [(src m).2.2.2.2.2];omega)))
    (fun _ m im => (src m).2.2.2.2.1 (mem_inter.mp im).1)
  by_contra ne
  rw [card_pair ne] at bound;omega

#print axioms common_port
#print axioms paired_ports
#print axioms unique_successor
end Minimal180.OppositeGain
