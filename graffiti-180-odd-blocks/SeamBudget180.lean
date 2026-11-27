import WingRank180

set_option warningAsError true
namespace Minimal180.OddBlock
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Weighted leaf optima add exactly across a proper seam, after removing
the seam from both eligibility sets. -/
theorem seam_leaves {J : SimpleGraph V} {w : V} {S T : Finset V} (s : Split J w S T)
    (jc : J.Connected) (U : Finset V) :
    weightedLeaves J U =
      weightedLeaves (side J S) (pull (fun v : ↥S => v.val) (U.erase w)) +
      weightedLeaves (side J T) (pull (fun v : ↥T => v.val) (U.erase w)) := by
  classical
  apply le_antisymm _ (s.leaf_join jc U)
  obtain ⟨M,mj,tr,opt⟩ := tree_opt J jc U
  let q : Split M w S T := ⟨s.cover,s.meet,fun e => s.edges (mj e),s.smallL,s.smallR⟩
  have inside {Q R : Finset V} (t : Split M w Q R) : (side M Q).IsTree := by
    refine ⟨t.connectedL tr.isConnected,?_⟩
    let f : side M Q ↪g M := Embedding.induce _
    exact fun _ p hp => tr.IsAcyclic (p.map f.toHom) (hp.map f.injective)
  have wl : w∉leaves M := by
    intro leaf
    obtain ⟨a,wa⟩ := exists_adj (side M S) (q.connectedL tr.isConnected) q.largeL ⟨w,q.both.1⟩
    obtain ⟨b,wb⟩ := exists_adj (side M T) (q.flip.connectedL tr.isConnected) q.flip.largeL ⟨w,q.both.2⟩
    have same : a.val=b.val := leaf_unique M leaf wa wb
    have eq : a.val=w := q.common a.property (same ▸ b.property)
    exact (show M.Adj w a.val from wa).ne eq.symm
  have score {Q R : Finset V} (t : Split M w Q R) :
      (pull (fun v : ↥Q => v.val) (U∩leaves M)).card ≤
      weightedLeaves (side J Q) (pull (fun v : ↥Q => v.val) (U.erase w)) := by
    let K := side M Q
    let E := pull (fun v : ↥Q => v.val) (U.erase w)
    have sub : K≤side J Q := fun _ _ e => mj e
    have valid : ∀ v : ↥Q, v.val∈U∩leaves M → v∈E∩leaves K := by
      intro v hv
      obtain ⟨vu,vl⟩ := mem_inter.mp hv
      refine mem_inter.mpr ⟨mem_pull.mpr (mem_erase.mpr ⟨fun h => wl (h ▸ vl),vu⟩),?_⟩
      apply leaf_of_unique K (t.connectedL tr.isConnected) t.largeL
      exact fun e f => Subtype.ext (leaf_unique M vl e f)
    have inc : pull (fun v : ↥Q => v.val) (U∩leaves M)⊆E∩leaves K :=
      fun v h => valid v (mem_pull.mp h)
    exact (card_le_card inc).trans (le_sup (s:=univ.filter (fun H : SimpleGraph ↥Q => H≤side J Q ∧ H.IsTree))
      (f:=fun H => (E∩leaves H).card) (mem_filter.mpr ⟨mem_univ K,sub,inside t⟩))
  have tally := s.tally (U∩leaves M)
  have miss : w∉U∩leaves M := fun h => wl (mem_inter.mp h).2
  rw [weight,if_neg miss,Nat.add_zero,opt] at tally
  exact tally ▸ Nat.add_le_add (score q) (score q.flip)

/-- The exact lower equality can be tested using only the two lower sides.
A and P may be arbitrary finite marks and U any fixed eligibility set. -/
theorem seam_tight_iff {J : SimpleGraph V} (jc : J.Connected) {x y w : V} {S T : Finset V}
    (s : Split J w S T) (xs : x∈S) (ys : y∉S) (xy : x≠y)
    (drop : bipartiteNum (J⊔edge x y)<bipartiteNum J) (A P U : Finset V) :
    let score (Q : Finset V) := weightedLeaves (side J Q) (pull (fun v : ↥Q => v.val) (U.erase w))+
      bipartiteNum (side J Q)
    let target (Q : Finset V) := 1+(pull (fun v : ↥Q => v.val) A).card+
      (pull (fun v : ↥Q => v.val) P).card
    weightedLeaves J U+bipartiteNum J=1+A.card+P.card ↔
      score S+score T+weight w A+weight w P=target S+target T := by
  dsimp only
  obtain ⟨B,b,h⟩ := optB J
  have pin := (locked_seam s xs ys xy drop ⟨b,h⟩).2.1
  have rank := (exact_wing_scores s ⟨b,h⟩ pin).2.2
  have leaf := seam_leaves s jc U
  have ta := s.tally A
  have tp := s.tally P
  omega

#print axioms seam_leaves
#print axioms seam_tight_iff
end Minimal180.OddBlock
