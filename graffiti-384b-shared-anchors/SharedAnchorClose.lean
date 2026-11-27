import SharedBudget

namespace Graffiti384b.Shared29
open Finset SimpleGraph Donor JointRank LowSample
open private Shared29.adjusted from SharedBudget
open private LowSample.two_degree from LowSample384b
open private Remaining29.account from Remaining29
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At diversity 29 and nonleaf quota at least 29, sharing a neighbor
between two distinct degree-two vertices guarantees fifteen omissions. -/
theorem shared_anchor (t : (types G).card=29) (q : 29≤(nonleaves G).card)
    {e f w : V} (et : e∈twos G) (ft : f∈twos G) (ne : e≠f)
    (ew : G.Adj e w) (fw : G.Adj f w) : gamma G≤Fintype.card V-15 := by
  classical
  by_contra! fail
  have bad : bound G<gamma G := by simpa only [bound,t] using fail
  obtain ⟨h,_,neighbors,independent,ports⟩ := PendantClose.residual_anchors G t q bad
  obtain ⟨inj,rich,_,_⟩ := Repair.maximal_diversity G (by omega)
  let E : Finset V := {e,f}
  let W := G.neighborFinset e ∪ G.neighborFinset f
  let X := high G\W
  have es : E⊆twos G := insert_subset et (singleton_subset_iff.mpr ft)
  have two : E.card=2 := card_pair ne
  have wh : W⊆high G := union_subset (neighbors e et) (neighbors f ft)
  have ws : W.card=3 := by
    have lo := ports E es
    have eq : E.biUnion (fun v => G.neighborFinset v)=W := by simp [E,W]
    rw [eq,two] at lo
    have add := card_union_add_card_inter (G.neighborFinset e) (G.neighborFinset f)
    rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,LowSample.two_degree G et,LowSample.two_degree G ft] at add
    have common : 0<(G.neighborFinset e ∩ G.neighborFinset f).card := card_pos.mpr
      ⟨w,mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr ew,(G.mem_neighborFinset ..).mpr fw⟩⟩
    change W.card+_=2+2 at add
    omega
  have xh : X⊆high G := sdiff_subset
  have xs : X.card=24 := by dsimp [X]; rw [card_sdiff wh,h,ws]
  have outside (z : V) (ze : z∈E) : G.neighborFinset z⊆W := by
    rcases mem_insert.mp ze with rfl|zf
    · exact subset_union_left
    · rw [mem_singleton.mp zf]
      exact subset_union_right
  have frame : Frame G X E := ⟨by omega,xh,inj.mono xh,fun v vm => rich v (xh vm),
    disjoint_left.mpr (fun _ ze zx => (mem_sdiff.mp (es ze)).2 (xh zx)),
    fun z ze v vx zv => (mem_sdiff.mp vx).2 (outside z ze ((G.mem_neighborFinset ..).mpr zv)),
    fun z ze u ue => independent z (es ze) u (es ue),fun z ze => (LowSample.two_degree G (es ze)).ge⟩
  apply (not_lt_of_ge (pool_budget G frame xs two ?_)) fail
  intro v vm
  let i := rank X (trianglesAt G) v
  let m := min (exposed G X).card 6
  change 2+Shared29.adjusted m i≤trianglesAt G v
  unfold Shared29.adjusted
  split
  · rename_i jump
    have actual : m=(exposed G X).card := by dsimp [m] at *; omega
    have cap (a : V) (aw : a∈W) : trianglesAt G a≤(m+2).choose 2+2 := by
      rw [actual]
      exact anchor_cap G W ws a aw (ear_multiplicity G ports a)
    have gap := rank_gap (trianglesAt G) inj rich xh wh (disjoint_left.mpr (fun _ vx => (mem_sdiff.mp vx).2))
      ws _ cap vm jump.2
    change i+5≤trianglesAt G v at gap
    omega
  · exact rank_lower X (trianglesAt G) (inj.mono xh) 2 frame.scores vm

/-- For the requested 27-high profile the existence of the two ears already
implies the required nonleaf quota. -/
theorem shared_at_27 (t : (types G).card=29) (h : (high G).card=27)
    {e f w : V} (de : G.degree e=2) (df : G.degree f=2) (ne : e≠f)
    (ew : G.Adj e w) (fw : G.Adj f w) : gamma G≤bound G := by
  classical
  have ear {v : V} (dv : G.degree v=2) : v∈twos G := by simp [twos,nonleaves,high,dv]
  have sub : ({e,f}:Finset V)⊆twos G := insert_subset (ear de) (singleton_subset_iff.mpr (ear df))
  have size := card_le_card sub
  rw [card_pair ne] at size
  have total := Remaining29.account G
  simpa only [bound,t] using shared_anchor G t (by omega) (ear de) (ear df) ne ew fw

/-- Every remaining failure at these quotas has pairwise disjoint two-element
neighborhoods, so the two/three ears use exactly four/six high anchors. -/
theorem residual_distinct (t : (types G).card=29) (q : 29≤(nonleaves G).card)
    (fail : bound G<gamma G) :
    (high G).card=27 ∧
    (∀e∈twos G,G.neighborFinset e⊆high G) ∧
    (∀e∈twos G,∀f∈twos G,e≠f → Disjoint (G.neighborFinset e) (G.neighborFinset f)) ∧
    (((nonleaves G).card=29 ∧ (twos G).card=2 ∧ ((twos G).biUnion (fun e => G.neighborFinset e)).card=4) ∨
     ((nonleaves G).card=30 ∧ (twos G).card=3 ∧ ((twos G).biUnion (fun e => G.neighborFinset e)).card=6)) := by
  classical
  obtain ⟨h,profiles,nbrs,_,_⟩ := PendantClose.residual_anchors G t q fail
  have dis (e : V) (et : e∈twos G) (f : V) (ft : f∈twos G) (ne : e≠f) :
      Disjoint (G.neighborFinset e) (G.neighborFinset f) := by
    apply disjoint_left.mpr
    intro w ew fw
    have sol := shared_anchor G t q et ft ne ((G.mem_neighborFinset ..).mp ew) ((G.mem_neighborFinset ..).mp fw)
    simp only [bound,t] at fail
    omega
  have exactSize : ((twos G).biUnion (fun e => G.neighborFinset e)).card=(twos G).card*2 := by
    rw [card_biUnion (fun e et f ft ne => dis e et f ft ne)]
    calc
      _ = ∑_e∈twos G,2 := sum_congr rfl (fun e et => (card_neighborFinset_eq_degree ..).trans (LowSample.two_degree G et))
      _ = _ := by simp
  refine ⟨h,nbrs,dis,?_⟩
  rcases profiles with ⟨nq,ct⟩|⟨nq,ct⟩
  · exact Or.inl ⟨nq,ct,by omega⟩
  · exact Or.inr ⟨nq,ct,by omega⟩

end Graffiti384b.Shared29
#print axioms Graffiti384b.Shared29.shared_anchor
#print axioms Graffiti384b.Shared29.shared_at_27
#print axioms Graffiti384b.Shared29.residual_distinct
