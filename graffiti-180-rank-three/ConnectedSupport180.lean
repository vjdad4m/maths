import SupportRank180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Graffiti318 Graffiti180 Rooted180 Converse180 Assembly180
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Compress a nonempty connected subset to one component representative. -/
theorem connected_components_bound (G : SimpleGraph V) (W S : Finset V) (inc : W⊆S)
    (cw : Con G W) : compCount G S+W.card≤S.card+1 := by
  classical
  let H := G.induce (S : Set V)
  letI : Finite H.ConnectedComponent := Finite.of_surjective H.connectedComponentMk (fun c => Quot.exists_rep c)
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  obtain ⟨w⟩ := cw.nonempty
  let Z := insert w.val (S\W)
  have zs : Z⊆S := insert_subset (inc w.property) sdiff_subset
  let f (v : ↥Z) : H.ConnectedComponent := H.connectedComponentMk ⟨v.val,zs v.property⟩
  have onto : Function.Surjective f := by
    intro c
    obtain ⟨x,xh⟩ := Quot.exists_rep c
    change H.connectedComponentMk x=c at xh
    by_cases xw : x.val∈W
    · refine ⟨⟨w.val,mem_insert_self ..⟩,?_⟩
      rw [←xh]
      apply ConnectedComponent.sound
      let m := (G.induceHomOfLE (show (W : Set V)⊆(S : Set V) from inc)).toHom
      exact (cw w ⟨x.val,xw⟩).map m
    · exact ⟨⟨x.val,mem_insert_of_mem (mem_sdiff.mpr ⟨x.property,xw⟩)⟩,xh⟩
  have count := Fintype.card_le_of_surjective f onto
  have k : compCount G S=Fintype.card H.ConnectedComponent := Nat.card_eq_fintype_card
  have z : Z.card=(S\W).card+1 := card_insert_of_not_mem (fun h => (mem_sdiff.mp h).2 w.property)
  rw [Fintype.card_coe,z] at count
  have n := card_sdiff_add_card_eq_card inc
  omega

/-- C is any connected set of even vertices and N any set of odd
neighbors of C. A failure bounds how many odd vertices C can reach. -/
theorem odd_neighborhood_obstruction (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 1<Fintype.card V) (r : V) (C N : Finset V) (connected : Con G C)
    (dis : Disjoint (oddSet G r) C) (odd : N⊆oddSet G r)
    (touch : ∀ x∈N,∃ y∈C,G.Adj x y)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r) :
    bipartiteNum G+secondDegree G+N.card≤Fintype.card V+C.card := by
  classical
  let Q := oddSet G r
  have wc : Con G (C∪N) := con_of_neighbors G connected subset_union_left (by
    intro x xm xn
    exact touch x ((mem_union.mp xm).resolve_left xn))
  have inc : C∪N⊆Q∪C := by
    intro x hx
    exact (mem_union.mp hx).elim (mem_union_right _) (fun h => mem_union_left _ (odd h))
  have cb := connected_components_bound G (C∪N) (Q∪C) inc wc
  rw [card_union_of_disjoint (dis.symm.mono_right odd),card_union_of_disjoint dis] at cb
  change compCount G (Q∪C)+(C.card+N.card)≤Q.card+C.card+1 at cb
  have res := (support_obstruction G hc hn r bad C).2
  change _<evenCount G r+C.card+compCount G (Q∪C) at res
  have eq := odd_partition G r
  change evenCount G r+Q.card=Fintype.card V at eq
  omega

/-- For example every root with degree d and maximizing even count proves
ordinary #180 when its degree and the second smallest degree sum to at
least the odd-cycle transversal number plus two. -/
theorem conjecture180_of_root_degree (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 1<Fintype.card V) (r : V) (mx : evenCount G r=maxEven G)
    (pay : Fintype.card V+2≤bipartiteNum G+secondDegree G+G.degree r) :
    1+independence G+maxEven G≤maxLeaves G+bipartiteNum G := by
  classical
  rw [←mx]
  by_contra! bad
  have dis : Disjoint (oddSet G r) {r} := disjoint_left.mpr (by
    rintro x hx h; obtain rfl := mem_singleton.mp h; simp [oddSet,dist_self] at hx)
  have sub : G.neighborFinset r⊆oddSet G r := by
    intro x hx
    have d := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset r x).mp hx).symm
    simp [oddSet,d]
  have cap := odd_neighborhood_obstruction G hc hn r {r} (G.neighborFinset r) (con_single G r) dis sub
    (fun x hx => ⟨r,mem_singleton_self _,((G.mem_neighborFinset r x).mp hx).symm⟩) bad
  rw [card_singleton,card_neighborFinset_eq_degree] at cap
  omega

#print axioms connected_components_bound
#print axioms odd_neighborhood_obstruction
#print axioms conjecture180_of_root_degree
end Minimal180.HigherRank
