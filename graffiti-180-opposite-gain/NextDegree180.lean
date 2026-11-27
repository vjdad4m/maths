import TwoWingGain180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals PairRepair
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- With a degree-four saturated tip, an independent mark one layer
beyond it has at most two lower neighbors and one higher neighbor.
It has no neighbors in its own parity. -/
theorem next_degree (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (r a z : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A)
    (am : a∈A) (ap : a∈parity G r p) (zm : z∈A) (deg : G.degree a=4)
    (sat : G.degree a=allowance G r p A+2) (dz : G.dist z r=G.dist a r+1) : G.degree z≤3 := by
  classical
  let P := parity G r p
  let H := alternating G P
  let J := G.neighborFinset a\H.neighborFinset a
  let N := G.neighborFinset z
  let L := N.filter (fun v => G.dist v r=G.dist a r)
  let U := N\L
  have zp : z∉P := by
    intro hit
    have d := (mem_parity ..).mp hit
    have k := (mem_parity ..).mp ap
    omega
  have az : a≠z := fun e => zp (e ▸ ap)
  have zr : z≠r := fun e => by rw [e,dist_self] at dz;omega
  have rule := saturated_layer G gc hn r a p A ai ar am ap sat
  have gi : H.neighborFinset a⊆G.neighborFinset a := fun x xm =>
    (G.mem_neighborFinset ..).mpr ((H.mem_neighborFinset ..).mp xm).1
  have sum := card_sdiff_add_card_eq_card gi
  change J.card+(H.neighborFinset a).card=(G.neighborFinset a).card at sum
  have ch : (H.neighborFinset a).card=H.degree a := card_neighborFinset_eq_degree ..
  have cg : (G.neighborFinset a).card=4 := (card_neighborFinset_eq_degree G a).trans deg
  have lo := rule.1
  change 2≤H.degree a at lo
  have jcap : J.card≤2 := by omega
  have spec {v : V} (m : v∈N) : G.Adj z v ∧ v∉A ∧ v∈P := by
    have e := (G.mem_neighborFinset ..).mp m
    refine ⟨e,fun ma => ai z zm v ma e.ne e,?_⟩
    by_contra no
    exact ai a am z zm az (opposite_edges_confined G gc (by omega) r a ar p A ai am ap sat e zp no).1
  have ls : L⊆J := by
    intro v m
    have h := spec (mem_filter.mp m).1
    have av := (rule.2 v (mem_filter.mp m).2).mp h.2.1
    exact mem_sdiff.mpr ⟨(G.mem_neighborFinset ..).mpr av,fun hm => ((H.mem_neighborFinset ..).mp hm).2.mp ap h.2.2⟩
  have upward {v : V} (m : v∈U) : v∉A ∧ G.Adj v z ∧ ¬G.Adj a v ∧ G.dist v r=G.dist z r+1 := by
    obtain ⟨vn,vl⟩ := mem_sdiff.mp m
    have data := spec vn
    have neq : G.dist v r≠G.dist a r := fun h => vl (mem_filter.mpr ⟨vn,h⟩)
    have f := gc.dist_triangle (u:=v) (v:=z) (w:=r)
    have g := gc.dist_triangle (u:=z) (v:=v) (w:=r)
    rw [dist_eq_one_iff_adj.mpr data.1.symm] at f
    rw [dist_eq_one_iff_adj.mpr data.1] at g
    have dv := (mem_parity ..).mp data.2.2
    have da := (mem_parity ..).mp ap
    exact ⟨data.2.1,data.1.symm,fun av => neq (eq_dist G gc r v a p av.symm (iff_of_true data.2.2 ap)),by omega⟩
  have ucap : U.card≤1 := card_le_one.mpr (by
    intro x xm y ym
    obtain ⟨xa,xz,ax,dx⟩ := upward xm
    obtain ⟨ya,yz,ay,dy⟩ := upward ym
    exact unique_successor G gc (by omega) r a z x y ar zr az p A ai am zm sat xa ya ax ay xz yz dx dy)
  have lcap := (card_le_card ls).trans jcap
  have total := card_sdiff_add_card_eq_card (show L⊆N from filter_subset ..)
  change U.card+L.card=N.card at total
  have gdeg : N.card=G.degree z := card_neighborFinset_eq_degree ..;omega

#print axioms next_degree
end Minimal180.OppositeGain
