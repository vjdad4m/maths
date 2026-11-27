import LayerBonus180
import SaturatedLayer180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals PairRepair
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A saturated protected vertex with a bipartite neighborhood has two
nonadjacent neighbors of the opposite distance parity. The independent
marking may meet both distance parities. -/
theorem independent_ports (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (r a : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A) (ap : a∈parity G r p)
    (sat : G.degree a=allowance G r p A+2) (bi : TwoColor G (G.neighborFinset a)) :
    ∃ u v,u≠v ∧ ¬G.Adj u v ∧ G.Adj a u ∧ G.Adj a v ∧ u∉parity G r p ∧ v∉parity G r p := by
  classical
  let P := parity G r p
  let N := G.neighborFinset a
  let H := alternating G P
  let U := H.neighborFinset a
  let Y := ((A∪P)\(A∩P)).filter (fun x => G.dist x r=G.dist a r)
  have spec (x : V) : x∈U ↔ G.Adj a x ∧ x∉P := by
    change x∈H.neighborFinset a ↔ _
    rw [H.mem_neighborFinset];change (G.Adj a x ∧ (a∈P ↔ x∉P)) ↔ _
    simp [show a∈P from ap]
  have inc : U⊆N := fun x m => (G.mem_neighborFinset ..).mpr ((spec x).mp m).1
  have large := (saturated_layer G gc hn r a p A ai ar am ap sat).1
  change 2≤H.degree a at large
  have sz : 2≤U.card := by simpa only [U,card_neighborFinset_eq_degree] using large
  by_contra fail
  have clique {x y : V} (xm : x∈U) (ym : y∈U) (ne : x≠y) : G.Adj x y := by
    by_contra no
    exact fail ⟨x,y,ne,no,((spec x).mp xm).1,((spec y).mp ym).1,((spec x).mp xm).2,((spec y).mp ym).2⟩
  obtain ⟨c,cp⟩ := (color_function ..).mp bi
  have inj : Set.InjOn c (↑U) := by
    intro x xm y ym eq
    by_contra ne
    exact cp x (inc xm) y (inc ym) (clique xm ym ne) eq
  have count := card_le_univ (U.image c)
  rw [card_image_of_injOn inj] at count
  change U.card≤2 at count
  obtain ⟨u,um,v,vm,ne⟩ := one_lt_card.mp (show 1<U.card by omega)
  have outside {x : V} (xm : x∈U) : x∉A∪P := by
    obtain ⟨ed,np⟩ := (spec x).mp xm
    exact fun m => (mem_union.mp m).elim (fun ma => ai a am x ma ed.ne ed) np
  have bonus := layer_bonus G gc hn r a ar p A ai am ap u v (clique um vm ne) (outside um) (outside vm)
  change Y.card+1≤allowance G r p A at bonus
  have hit : N\U⊆Y := by
    intro x xm
    obtain ⟨inN,off⟩ := mem_sdiff.mp xm
    have ed := (G.mem_neighborFinset ..).mp inN
    have xp : x∈P := by by_contra no;exact off ((spec x).mpr ⟨ed,no⟩)
    have xa : x∉A := fun m => ai a am x m ed.ne ed
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_union_right _ xp,fun m => xa (mem_inter.mp m).1⟩,
      eq_dist G gc r x a p ed.symm (iff_of_true xp ap)⟩
  have cap := card_le_card hit
  have ct := card_sdiff_add_card_eq_card inc
  change (N\U).card+U.card=(G.neighborFinset a).card at ct
  have dg : (G.neighborFinset a).card=allowance G r p A+2 :=
    (card_neighborFinset_eq_degree G a).trans sat
  omega

/-- A vertex whose degree saturates the available deletion allowance
settles the protected test whenever its neighborhood is bipartite and
meets every edge internal to the selected parity. -/
theorem repair_of_cover (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (r a : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A) (ap : a∈parity G r p)
    (sat : G.degree a=allowance G r p A+2) (bi : TwoColor G (G.neighborFinset a))
    (hit : ∀ x∈parity G r p,∀ y∈parity G r p,G.Adj x y → G.Adj a x ∨ G.Adj a y) :
    Protected G r p A := by
  obtain ⟨u,v,ne,na,au,av,up,vp⟩ := independent_ports G gc hn r a ar p A ai am ap sat bi
  exact star_repair G gc (by omega) r a ar p A ai am ap sat hit u v ne na au av up vp

/-- The single-protected nonroot marking for a size-two transversal is
settled for every number of active components if the independent marking
lies in the selected parity, or all edges internal to that parity occur
at the distance of a. -/
theorem solo_parity_repair (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a b : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A)
    (ab : a≠b) (bi : TwoColor G (univ\{a,b})) (ak : a∈A∩insert r (parity G r p))
    (bk : b∉A∩insert r (parity G r p))
    (hyp : A⊆parity G r p ∨
      ∀ x∈parity G r p,∀ y∈parity G r p,G.Adj x y → G.dist x r=G.dist a r) :
    Protected G r p A := by
  classical
  by_contra bad
  obtain ⟨deg,two,_⟩ := solo_rigidity G gc hn r p A ai bad a b ab bi ak bk
  have high : 2<Fintype.card V := by have := G.degree_lt_card_verts a;omega
  have pm := (mem_insert.mp (mem_inter.mp ak).2).resolve_left ar
  have am := (mem_inter.mp ak).1
  have na := (pair_obstruction G gc hn r p A ai bad a b ab bi).1
  have sat : G.degree a=allowance G r p A+2 := by omega
  obtain ⟨c,cp⟩ := (color_function ..).mp bi
  have ns : G.neighborFinset a⊆univ\{a,b} := by
    intro x xm
    have edge := (G.mem_neighborFinset ..).mp xm
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    rintro m;rcases mem_insert.mp m with h|h
    · exact edge.ne h.symm
    · exact na ((mem_singleton.mp h) ▸ edge)
  apply bad
  apply repair_of_cover G gc high r a ar p A ai am pm sat ((color_function ..).mpr
    ⟨c,fun x xm y ym => cp x (ns xm) y (ns ym)⟩)
  intro x xp y yp ed
  rcases hyp with sub|layer
  · exact selected_edges_hit G gc hn r a ar p A ai am sat sub xp yp ed
  · have rule := (saturated_layer G gc high r a p A ai ar am pm sat).2
    by_cases xm : x∈A
    · exact Or.inr ((rule y (layer y yp x xp ed.symm)).mp (fun ym => ai x xm y ym ed.ne ed))
    · exact Or.inl ((rule x (layer x xp y yp ed)).mp xm)

#print axioms independent_ports
#print axioms repair_of_cover
#print axioms solo_parity_repair
end Minimal180.OppositeGain
