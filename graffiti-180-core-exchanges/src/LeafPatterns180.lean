import CoreSplit180
set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

structure LeafPattern (V : Type*) where
  need : Finset V
  a : V
  b : V
  side : Finset V

def LeafPattern.valid (p : LeafPattern V) (E : List (V×V)) : Prop :=
  if p.a=p.b then p.a∈p.need ∧ ∀ e∈E,(e.1=p.a → e.2∈p.need) ∧ (e.2=p.a → e.1∈p.need)
  else p.a∈p.side ∧ p.b∉p.side ∧ ∀ e∈E, e.1∉p.need → e.2∉p.need → (e.1∈p.side ↔ e.2∈p.side)

def LeafPattern.hits (p : LeafPattern V) (K : Finset V) : Prop :=
  p.need⊆K ∧ (p.a=p.b ∨ (p.a∉K ∧ p.b∉K))

theorem LeafPattern.blocks (p : LeafPattern V) (J : SimpleGraph V) (E : List (V×V))
    (given : ∀ {a b}, J.Adj a b → (a,b)∈E ∨ (b,a)∈E)
    (valid : p.valid E) (K : Finset V) (hit : p.hits K)
    (conn : Con J (univ\K)) (dom : ∀ q∈K,Dominates J (univ\K) q) : False := by
  by_cases eq : p.a=p.b
  · rw [LeafPattern.valid,if_pos eq] at valid
    obtain ⟨t,ht,edge⟩ := dom p.a (hit.1 valid.1)
    apply (mem_sdiff.mp ht).2
    apply hit.1
    rcases given edge with e|e
    · exact (valid.2 _ e).1 rfl
    · exact (valid.2 _ e).2 rfl
  · rw [LeafPattern.valid,if_neg eq] at valid
    obtain ⟨oa,ob⟩ := hit.2.resolve_left eq
    let f (i:V) := decide (i∈p.side)
    have stable : OnEdges J (univ\K) f := by
      intro a ha b hb edge
      have an : a∉p.need := fun h => (mem_sdiff.mp ha).2 (hit.1 h)
      have bn : b∉p.need := fun h => (mem_sdiff.mp hb).2 (hit.1 h)
      have same : a∈p.side ↔ b∈p.side := by
        rcases given edge with e|e
        · exact valid.2.2 _ e an bn
        · exact (valid.2.2 _ e bn an).symm
      exact decide_eq_decide.mpr same
    have both := ((connected_cuts _ _).mp conn).2 f stable p.a (by simp [oa]) p.b (by simp [ob])
    simp [f,valid.1,valid.2.1] at both

theorem weighted_le_of_patterns (J : SimpleGraph V) (jc : J.Connected) (hn : 2<Fintype.card V)
    (U : Finset V) (k : ℕ) (E : List (V×V)) (patterns : List (LeafPattern V))
    (given : ∀ {a b}, J.Adj a b → (a,b)∈E ∨ (b,a)∈E)
    (valid : ∀ p∈patterns,p.valid E)
    (covered : ∀ K∈U.powersetCard (k+1),∃ p∈patterns,p.hits K) :
    weightedLeaves J U≤k := by
  by_contra! bad
  obtain ⟨T,sub,tr,score⟩ := tree_opt J jc U
  obtain ⟨K,small,size⟩ := exists_subset_card_eq (show k+1≤(U∩leaves T).card by omega)
  obtain ⟨p,hp,hit⟩ := covered K (mem_powersetCard.mpr ⟨small.trans inter_subset_left,size⟩)
  obtain ⟨conn,dom⟩ := leaf_core J T sub tr hn K (small.trans inter_subset_right)
  exact p.blocks J E given (valid p hp) K hit conn dom

#print axioms weighted_le_of_patterns
end Minimal180
