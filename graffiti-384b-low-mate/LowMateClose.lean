import PoolRank
namespace Graffiti384b.PendantClose
open Finset SimpleGraph LowSample
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A degree-two vertex with at most one high neighbor settles diversity 29
when exactly 27 vertices have degree at least three. -/
theorem at_most_one_high (t : (types G).card=29) (h : (high G).card=27) {e : V}
    (de : G.degree e=2) (sparse : ((high G).filter (G.Adj e)).card≤1) :
    gamma G≤Fintype.card V-15 := by
  classical
  let S := (high G).filter (G.Adj e)
  obtain ⟨w,wh,one⟩ : ∃w∈high G,S⊆{w} := by
    by_cases non : S.Nonempty
    · obtain ⟨w,ws⟩ := non
      exact ⟨w,(mem_filter.mp ws).1,fun v vm => mem_singleton.mpr (card_le_one.mp sparse v vm w ws)⟩
    · obtain ⟨w,wh⟩ := card_pos.mp (show 0<(high G).card by omega)
      exact ⟨w,wh,fun v vm => (non ⟨v,vm⟩).elim⟩
  let X := (high G).erase w
  have sz : X.card=26 := by rw [show X=(high G).erase w from rfl,card_erase_of_mem wh,h]
  have sub : X⊆high G := erase_subset ..
  obtain ⟨inj,rich,_,_⟩ := Repair.maximal_diversity G (by omega)
  apply exact_frame G (X:=X) (e:=e)
  refine ⟨sz,sub,inj.mono sub,fun v vm => rich v (sub vm),?_,?_,de.ge⟩
  · intro em
    have highdeg := (mem_filter.mp (sub em)).2
    omega
  · intro v vm ev
    exact (mem_erase.mp vm).1 (mem_singleton.mp (one (mem_filter.mpr ⟨sub vm,ev⟩)))

/-- Includes the pendant triangle, a leaf adjacent to an ear, and adjacent
ears with different high roots. The other edge incident to the ear is arbitrary. -/
theorem low_mate (t : (types G).card=29) (h : (high G).card=27) {e v : V}
    (de : G.degree e=2) (ev : G.Adj e v) (low : G.degree v≤2) : gamma G≤Fintype.card V-15 := by
  apply at_most_one_high G t h de
  have sub : (high G).filter (G.Adj e)⊆(G.neighborFinset e).erase v := by
    intro a am
    obtain ⟨ah,ea⟩ := mem_filter.mp am
    have d := (mem_filter.mp ah).2
    exact mem_erase.mpr ⟨fun eq => by rw [eq] at d; omega,(G.mem_neighborFinset ..).mpr ea⟩
  have ct := card_le_card sub
  rwa [card_erase_of_mem ((G.mem_neighborFinset ..).mpr ev),card_neighborFinset_eq_degree,de] at ct

/-- In either residual nonleaf quota the ears have only high neighbors.
Every set of k ears uses at least 2k−1 distinct anchors. In particular
two ears need three anchors, and three ears need five. -/
theorem residual_anchors (t : (types G).card=29) (q : 29≤(nonleaves G).card) (fail : bound G<gamma G) :
    (high G).card=27 ∧ ((nonleaves G).card=29 ∧ (twos G).card=2 ∨
      (nonleaves G).card=30 ∧ (twos G).card=3) ∧
    (∀e∈twos G,G.neighborFinset e⊆high G) ∧
    (∀e∈twos G,∀v∈twos G,¬G.Adj e v) ∧
    (∀S⊆twos G,2*S.card≤(S.biUnion (fun v => G.neighborFinset v)).card+1) := by
  classical
  obtain ⟨h,profiles,_⟩ := Remaining29.residual G t q fail
  have neighbors (e : V) (et : e∈twos G) : G.neighborFinset e⊆high G := by
    intro v vm
    apply Classical.byContradiction
    intro no
    have large : ¬3≤G.degree v := fun ge => no (mem_filter.mpr ⟨mem_univ _,ge⟩)
    have low : G.degree v≤2 := by omega
    have sol := low_mate G t h (LowSample.two_degree G et) ((G.mem_neighborFinset ..).mp vm) low
    unfold bound at fail
    rw [t] at fail
    omega
  have independent (e : V) (et : e∈twos G) (v : V) (vt : v∈twos G) : ¬G.Adj e v :=
    fun ev => (mem_sdiff.mp vt).2 (neighbors e et ((G.mem_neighborFinset ..).mpr ev))
  refine ⟨h,profiles,neighbors,independent,?_⟩
  intro S sub
  have eq : (high G).filter (fun z => ∃v∈S,G.Adj v z)=S.biUnion (fun v => G.neighborFinset v) := by
    ext z
    constructor
    · intro m
      obtain ⟨v,vs,vz⟩ := (mem_filter.mp m).2
      exact mem_biUnion.mpr ⟨v,vs,(G.mem_neighborFinset ..).mpr vz⟩
    · intro m
      obtain ⟨v,vs,vz⟩ := mem_biUnion.mp m
      exact mem_filter.mpr ⟨neighbors v (sub vs) vz,v,vs,(G.mem_neighborFinset ..).mp vz⟩
  apply Classical.byContradiction
  intro small
  apply (not_lt_of_ge (Repair.exact_of_low_support G S
    (disjoint_left.mpr (fun _ vs => (mem_sdiff.mp (sub vs)).2))
    (fun _ vs => (LowSample.two_degree G (sub vs)).ge)
    (fun v vs w ws => independent v (sub vs) w (sub ws)) ?_)) fail
  rw [eq,t,h]
  omega

end Graffiti384b.PendantClose
#print axioms Graffiti384b.PendantClose.at_most_one_high
#print axioms Graffiti384b.PendantClose.low_mate
#print axioms Graffiti384b.PendantClose.residual_anchors
