import CoreFrontier28
import ProtectedPair28

namespace Graffiti384b.Core28
open Finset SimpleGraph
open private OneEar.trim_scores from OneEarFinish384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In a half-tight positive distinct core, the two cubic scores cannot
have two common neighbors, whether or not there is a five-clique. -/
theorem common_cap (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (hf : Fintype.card V≤2*gamma G)
    {u s : V} (du : (triangleEdges G).degree u=3) (su : trianglesAt (triangleEdges G) u=2)
    (ds : (triangleEdges G).degree s=3) (ss : trianglesAt (triangleEdges G) s=3) :
    ((triangleEdges G).neighborFinset u∩(triangleEdges G).neighborFinset s).card≤1 := by
  classical
  let J := triangleEdges G
  obtain ⟨_,eq,_,⟨e,a,b,_,ab,nb,unique⟩,_⟩ := profile G n pos fi hf
  have jp (v : V) : 0<trianglesAt J v := (OneEar.trim_scores G v) ▸ pos v
  have ji : Function.Injective (trianglesAt J) := fun v w vs => fi
    ((OneEar.trim_scores G v).symm.trans (vs.trans (OneEar.trim_scores G w)))
  have tight : CliquePivot33.Tight J ∅ := by
    intro D rel
    have dom : TwoDominates J D := fun v out => by simpa using rel v out
    have up : gamma J≤D.card := Nat.sInf_le ⟨D,dom,rfl⟩
    change gamma J=14 at eq
    omega
  have ea : J.Adj e a := (J.mem_neighborFinset ..).mp (nb ▸ mem_insert_self _ _)
  have eb : J.Adj e b := (J.mem_neighborFinset ..).mp (nb ▸ mem_insert_of_mem (mem_singleton_self _))
  have de := (unique e).mpr rfl
  apply card_le_one.mpr
  intro p pm q qm
  by_contra different
  obtain ⟨up,sp⟩ := mem_inter.mp pm
  obtain ⟨uq,sq⟩ := mem_inter.mp qm
  have hit (C : Finset V) (cl : J.IsNClique 5 C) : p∈C ∨ q∈C :=
    ForcedCubics.shared_transversal J de ea eb ab jp ji du su ds ss different
      ((J.mem_neighborFinset ..).mp up) ((J.mem_neighborFinset ..).mp uq)
      ((J.mem_neighborFinset ..).mp sp) ((J.mem_neighborFinset ..).mp sq) tight cl
  have save := CorePair28.shared_saving J n du su ds ss different
    ((J.mem_neighborFinset ..).mp up) ((J.mem_neighborFinset ..).mp uq)
    ((J.mem_neighborFinset ..).mp sp) ((J.mem_neighborFinset ..).mp sq) jp ji hit
  change gamma J=14 at eq
  omega

/-- In the five-clique branch the two forced cubics share at most one
neighbor in the connected triangle-edge graph. -/
theorem at_most_one (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (hf : Fintype.card V≤2*gamma G)
    (five : ∃ C,(triangleEdges G).IsNClique 5 C) :
    let J := triangleEdges G
    ∃ u s,J.degree u=3 ∧ trianglesAt J u=2 ∧ J.degree s=3 ∧ trianglesAt J s=3 ∧
      (J.neighborFinset u∩J.neighborFinset s).card≤1 ∧
      ∀ C,J.IsNClique 5 C → 3≤(C∩(J.neighborFinset u∪J.neighborFinset s)).card ∧ ∃ x∈C,J.Adj s x := by
  obtain ⟨u,s,du,su,ds,ss,cover⟩ := clique_contacts G n pos fi hf five
  exact ⟨u,s,du,su,ds,ss,common_cap G n pos fi hf du su ds ss,cover⟩

theorem original_clique (t : (types G).card=29) (q : (nonleaves G).card=28) (bad : bound G<gamma G) :
    let P := nonleaves G
    let H := G.induce (P:Set V)
    let J := triangleEdges H
    (∃ C,J.IsNClique 5 C) →
    ∃ u s,J.degree u=3 ∧ trianglesAt J u=2 ∧ J.degree s=3 ∧ trianglesAt J s=3 ∧
      (J.neighborFinset u∩J.neighborFinset s).card≤1 ∧
      ∀ C,J.IsNClique 5 C → 3≤(C∩(J.neighborFinset u∪J.neighborFinset s)).card ∧ ∃ x∈C,J.Adj s x := by
  let P := nonleaves G
  let H := G.induce (P:Set V)
  have nc : Fintype.card P=28 := (Fintype.card_coe _).trans q
  obtain ⟨pos,fi,eq,_⟩ := Quota29.minimum G t q bad
  exact at_most_one H nc pos fi (by change Fintype.card P≤2*gamma H; change gamma H=14 at eq; omega)

/-- Two common neighbors of the two specified cubics suffice for the
catalogue inequality on the original graph. -/
theorem exact_of_shared_pair (t : (types G).card=29) (q : (nonleaves G).card=28) :
    let H := G.induce (nonleaves G:Set V)
    let J := triangleEdges H
    ∀ u s,J.degree u=3 → trianglesAt J u=2 → J.degree s=3 → trianglesAt J s=3 →
      2≤(J.neighborFinset u∩J.neighborFinset s).card → gamma G≤bound G := by
  dsimp only
  intro u s du su ds ss two
  by_contra! bad
  let P := nonleaves G
  let H := G.induce (P:Set V)
  have nc : Fintype.card P=28 := (Fintype.card_coe _).trans q
  obtain ⟨pos,fi,eq,_⟩ := Quota29.minimum G t q bad
  have half : Fintype.card P≤2*gamma H := by change gamma H=14 at eq; omega
  exact (Nat.not_succ_le_self 1) (two.trans (common_cap H nc pos fi half du su ds ss))

end Graffiti384b.Core28
#print axioms Graffiti384b.Core28.at_most_one
#print axioms Graffiti384b.Core28.original_clique
#print axioms Graffiti384b.Core28.common_cap
#print axioms Graffiti384b.Core28.exact_of_shared_pair

