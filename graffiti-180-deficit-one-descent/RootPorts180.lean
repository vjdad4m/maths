import RankTwoRoot180

set_option warningAsError true
namespace Minimal180.DescentOne
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The rank-two upper theorem gives strict gain after any tight one-unit
rank drop meeting its root condition. No shape for the lower graph or for
the added edges is required. -/
theorem transition_gain (J G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (block : NoCut G) (order : 2<Fintype.card V) (one : bipartiteNum J+1=Fintype.card V)
    (drop : bipartiteNum J=bipartiteNum G+1) (r : V) (odd : Bool) (A : Finset V)
    (ind : Indep G A) :
    let P := parity G r odd
    let U := eligible A P r
    weightedLeaves J U+bipartiteNum J=1+A.card+P.card →
      (3≤G.degree r ∨ (r∈A ↔ r∈P)) → weightedLeaves J U<weightedLeaves G U := by
  intro P U tight root
  have bound := rank_two_root G gc block order (by omega) r odd A ind root
  change 1+A.card+P.card≤weightedLeaves G U+bipartiteNum G at bound
  omega

/-- With an independence-only root, a failed marking forces every
independent subset of the eligible set to be smaller than A. -/
theorem FailedTwo.independence_only {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) :
    let P := parity G r odd
    let U := eligible A P r
    r∉P → ∀ Q⊆U, Indep G Q → Q.card<A.card := by
  classical
  intro P U rp Q qu qi
  have ru : r∉U := by
    intro mem
    obtain ⟨_,alt⟩ := eligible_iff.mp mem
    exact rp ((alt.resolve_left (not_not.mpr rfl)).2)
  have rq : r∉Q := fun m => ru (qu m)
  have bound := rank_two_root G h.connected h.block h.order h.rank r odd Q qi (Or.inr ⟨fun z => (rq z).elim,fun z => (rp z).elim⟩)
  change 1+Q.card+P.card≤weightedLeaves G (eligible Q P r)+bipartiteNum G at bound
  have inc : eligible Q P r⊆U := by
    intro i mem
    obtain ⟨mark,ok⟩ := eligible_iff.mp mem
    rcases mark with q|p
    · exact qu q
    · exact eligible_iff.mpr ⟨Or.inr p,Or.inl (fun eq => rp (eq ▸ p))⟩
  have cap := eligible_mono G inc
  have bad := h.bad
  change weightedLeaves G U+bipartiteNum G<1+A.card+P.card at bad
  omega

/-- With a parity-only root, a failed marking forces every independent
set of eligible nonneighbors of the root to be smaller than A. -/
theorem FailedTwo.parity_only {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) :
    let P := parity G r odd
    let U := eligible A P r
    r∈P → ∀ Q⊆U, Indep G Q → (∀ i∈Q,¬G.Adj r i) → Q.card<A.card := by
  classical
  intro P U rp Q qu qi safe
  have miss := h.root_disagreement
  change r∈(A∪P)\(A∩P) at miss
  have ra : r∉A := fun z => (mem_sdiff.mp miss).2 (mem_inter.mpr ⟨z,rp⟩)
  have ru : r∉U := fun mem => ra (((eligible_iff.mp mem).2.resolve_left (not_not.mpr rfl)).1)
  have rq : r∉Q := fun m => ru (qu m)
  let B := insert r Q
  have bi : Indep G B := by
    intro i im j jm ne edge
    rcases mem_insert.mp im with ir|iq <;> rcases mem_insert.mp jm with jr|jq
    · exact ne (ir.trans jr.symm)
    · exact safe j jq (ir ▸ edge)
    · exact safe i iq (jr ▸ edge.symm)
    · exact qi i iq j jq ne edge
  have bound := rank_two_root G h.connected h.block h.order h.rank r odd B bi
    (Or.inr ⟨fun _ => rp,fun _ => mem_insert_self ..⟩)
  change 1+B.card+P.card≤weightedLeaves G (eligible B P r)+bipartiteNum G at bound
  have off : (eligible B P r)\U⊆{r} := by
    intro i mem
    obtain ⟨marked,notu⟩ := mem_sdiff.mp mem
    apply mem_singleton.mpr
    apply Classical.byContradiction
    intro nr
    rcases (eligible_iff.mp marked).1 with ib|ip
    · exact notu (qu ((mem_insert.mp ib).resolve_left nr))
    · exact notu (eligible_iff.mpr ⟨Or.inr ip,Or.inl nr⟩)
  have cap := card_le_card off
  rw [card_singleton] at cap
  have le := restrict_leaves G (eligible B P r) U
  have size : B.card=Q.card+1 := card_insert_of_not_mem rq
  have bad := h.bad
  change weightedLeaves G U+bipartiteNum G<1+A.card+P.card at bad
  omega

#print axioms transition_gain
#print axioms FailedTwo.independence_only
#print axioms FailedTwo.parity_only
end Minimal180.DescentOne
