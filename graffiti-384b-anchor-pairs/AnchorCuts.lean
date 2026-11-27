import FourFrontier
namespace Graffiti384b.AnchorPairs
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A degree-two vertex and a set of two-contact vertices can be put on the
same side of a protected cut. A failure leaves a particular anchor uncovered. -/
theorem uncovered_anchor (t : (types G).card=31) (q : (nonleaves G).card=31)
    (bad : bound G<gamma G) {e f : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2) :
    let A := G.neighborFinset e∪G.neighborFinset f
    let D := ((high G)\A).filter (fun v => 2≤nbr G v A)
    ∃ a∈A,∀ v∈D,¬G.Adj a v := by
  classical
  let A := G.neighborFinset e∪G.neighborFinset f
  let X := high G\A
  let D := X.filter (fun v => 2≤nbr G v A)
  let E : Finset V := {e,f}
  let L := E∪D
  change ∃ a∈A,∀ v∈D,¬G.Adj a v
  by_contra! allHit
  have highPins : A⊆high G := union_subset (TwoEars.high_anchors G t q bad de) (TwoEars.high_anchors G t q bad df)
  have low (v : V) (vm : v∈E) : G.degree v=2 := (mem_insert.mp vm).elim (fun h => h ▸ de) (fun h => mem_singleton.mp h ▸ df)
  have off (v : V) (vm : v∈E) : v∉high G := by intro vh; have := (mem_filter.mp vh).2; rw [low v vm] at this; omega
  have nbrs (v : V) (vm : v∈E) : G.neighborFinset v⊆A := by
    rcases mem_insert.mp vm with rfl|h
    · exact subset_union_left
    · rw [mem_singleton.mp h]; exact subset_union_right
  have fr : EarFrame33.Frame G L A := by
    refine ⟨disjoint_left.mpr ?_,?_,?_⟩
    · intro v vl va; exact (mem_union.mp vl).elim (fun ve => off v ve (highPins va))
        (fun vd => (mem_sdiff.mp (mem_filter.mp vd).1).2 va)
    · intro v vl; rcases mem_union.mp vl with ve|vd
      · have inc : G.neighborFinset v⊆A.filter (G.Adj v) := fun w m =>
          mem_filter.mpr ⟨nbrs v ve m,(G.mem_neighborFinset ..).mp m⟩
        have h := card_le_card inc; rwa [card_neighborFinset_eq_degree,low v ve] at h
      · exact (mem_filter.mp vd).2
    · intro a am; obtain ⟨v,vd,av⟩ := allHit a am
      have vh := (mem_sdiff.mp (mem_filter.mp vd).1).1
      have step {u : V} (ue : u∈E) (ua : G.Adj u a) : 2≤nbr G a L :=
        PinnedColor34.two G (fun (eq : u=v) => off u ue (eq.symm ▸ vh)) ua.symm av (mem_union_left _ ue) (mem_union_right _ vd)
      exact (mem_union.mp am).elim (fun ea => step (mem_insert_self ..) ((G.mem_neighborFinset ..).mp ea))
        (fun fa => step (mem_insert_of_mem (mem_singleton_self _)) ((G.mem_neighborFinset ..).mp fa))
  exact ef (Squares29.sparse G bad _ _ fr e (mem_union_left _ (mem_union_left _ (mem_insert_self ..))) f
    (mem_union_left _ (mem_union_left _ (mem_insert_of_mem (mem_singleton_self _)))) de df)

/-- There is an isolated vertex in the bipartite graph of cross edges between
the two pairs of anchors. Otherwise place the ears on opposite sides. -/
theorem missing_cross (t : (types G).card=31) (q : (nonleaves G).card=31)
    (bad : bound G<gamma G) {e f : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2) :
    (∃ a∈G.neighborFinset e,∀ b∈G.neighborFinset f,¬G.Adj a b) ∨
    (∃ b∈G.neighborFinset f,∀ a∈G.neighborFinset e,¬G.Adj b a) := by
  classical
  by_contra! contact
  let A := G.neighborFinset e
  let B := G.neighborFinset f
  let P := insert e B
  let Q := insert f A
  have dis := disjoint_anchors G t q bad ef de df
  have off {w v : V} (dw : G.degree w=2) (dv : G.degree v=2) (wm : w∈G.neighborFinset v) : False := by
    have h := TwoEars.high_anchors G t q bad dv wm
    have := (mem_filter.mp h).2; omega
  have ear (w : V) (d : G.degree w=2) (T : Finset V) (sub : G.neighborFinset w⊆T) : 2≤nbr G w T := by
    have inc : G.neighborFinset w⊆T.filter (G.Adj w) := fun i im => mem_filter.mpr ⟨sub im,(G.mem_neighborFinset ..).mp im⟩
    have ct := card_le_card inc; rwa [card_neighborFinset_eq_degree,d] at ct
  have fr : EarFrame33.Frame G P Q := by
    refine ⟨disjoint_left.mpr ?_,?_,?_⟩
    · intro v vp vq; rcases mem_insert.mp vp with rfl|bm
      · exact (mem_insert.mp vq).elim ef (off de de)
      · rcases mem_insert.mp vq with rfl|am
        · exact off df df bm
        · exact disjoint_left.mp dis am bm
    · intro v vp; rcases mem_insert.mp vp with rfl|bv
      · exact ear v de Q (subset_insert ..)
      · obtain ⟨a,am,va⟩ := contact.2 v bv
        exact PinnedColor34.two G (fun (eq : f=a) => off df de (eq.symm ▸ am)) ((G.mem_neighborFinset ..).mp bv).symm va
          (mem_insert_self ..) (mem_insert_of_mem am)
    · intro v vq; rcases mem_insert.mp vq with rfl|av
      · exact ear v df P (subset_insert ..)
      · obtain ⟨b,bm,vb⟩ := contact.1 v av
        exact PinnedColor34.two G (fun (eq : e=b) => off de df (eq.symm ▸ bm)) ((G.mem_neighborFinset ..).mp av).symm vb
          (mem_insert_self ..) (mem_insert_of_mem bm)
  exact ef (Squares29.sparse G bad _ _ fr e (mem_union_left _ (mem_insert_self ..)) f
    (mem_union_right _ (mem_insert_self ..)) de df)

end Graffiti384b.AnchorPairs
#print axioms Graffiti384b.AnchorPairs.uncovered_anchor
#print axioms Graffiti384b.AnchorPairs.missing_cross
