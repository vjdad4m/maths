import FourPrices
import SeparatedAnchors

namespace Graffiti384b.AnchorPairs
open Finset SimpleGraph
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At diversity 31 and 31 nonleaves, every failure has four distinct high
anchors. Among the other 25 high vertices at most 14 touch these anchors. -/
theorem four_anchor_frontier (t : (types G).card=31) (q : (nonleaves G).card=31)
    (bad : bound G<gamma G) {e f : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2) :
    let A := G.neighborFinset e∪G.neighborFinset f
    let X := high G\A
    let m := (X.filter (fun v => 0<nbr G v A)).card
    let b := (X.filter (fun v => 2≤nbr G v A)).card
    Disjoint (G.neighborFinset e) (G.neighborFinset f) ∧ A⊆high G ∧ A.card=4 ∧
      X.card=25 ∧ m≤14 ∧ (m=14 → b≤5) ∧ (m=13 → b≤9) := by
  classical
  dsimp only
  let A := G.neighborFinset e∪G.neighborFinset f
  let X := high G\A
  let E := LowSample.twos G
  have dis := disjoint_anchors G t q bad ef de df
  have ah : A⊆high G := union_subset (TwoEars.high_anchors G t q bad de) (TwoEars.high_anchors G t q bad df)
  obtain ⟨hs,es⟩ := TwoEars.profile G t q bad
  have ac : A.card=4 := by dsimp [A]; rw [card_union_of_disjoint dis,card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,de,df]
  have xs : X.card=25 := by dsimp [X]; rw [card_sdiff ah,hs,ac]
  have mE {v : V} (d : G.degree v=2) : v∈E := mem_sdiff.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  have eq : ({e,f}:Finset V)=E := eq_of_subset_of_card_le (insert_subset (mE de) (singleton_subset_iff.mpr (mE df)))
    (by rw [card_pair ef]; exact es.le)
  have xa : Disjoint X A := disjoint_left.mpr (fun _ xm => (mem_sdiff.mp xm).2)
  have xe : Disjoint X E := disjoint_left.mpr (fun _ xm em => (mem_sdiff.mp em).2 (mem_sdiff.mp xm).1)
  have none (i : V) (ix : i∈X) (w : V) (we : w∈E) (iw : G.Adj i w) : False := by
    have wm := (G.mem_neighborFinset ..).mpr iw.symm
    rw [←eq,mem_insert,mem_singleton] at we
    apply (mem_sdiff.mp ix).2
    exact we.elim (fun h => mem_union_left _ (h ▸ wm)) (fun h => mem_union_right _ (h ▸ wm))
  have ind (i : V) (im : i∈E) (j : V) (jm : j∈E) (ij : G.Adj i j) : False :=
    (mem_sdiff.mp jm).2 (TwoEars.high_anchors G t q bad (LowSample.two_degree G im) ((G.mem_neighborFinset ..).mpr ij))
  obtain ⟨inj,lo,_,_⟩ := Repair.maximal_diversity G (by omega)
  refine ⟨dis,ah,ac,xs,?_⟩
  apply incidence G X E A xs es xe xa sdiff_subset (fun _ h => LowSample.two_degree G h) ind none
    (inj.mono (show (X:Set V)⊆high G from sdiff_subset)) (fun i h => lo i (mem_sdiff.mp h).1)
  rw [bound,t] at bad; omega

end Graffiti384b.AnchorPairs
#print axioms Graffiti384b.AnchorPairs.four_anchor_frontier
