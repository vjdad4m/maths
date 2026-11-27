import EdgeExchange180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u

/-- Only edges within one distance layer are tested. The sparser graph
must attain equality at the same root, parity and independent set. -/
def HorizontalExchange : Prop := ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → 1<Fintype.card V → NoCut G → ∀ r, SparseAt G r → ∀ odd A, Indep G A →
    ∀ a b, G.Adj a b → G.dist a r=G.dist b r →
    let J := G.deleteEdges {s(a,b)}
    let P := parity G r odd
    let U := eligible A P r
    bipartiteNum J=bipartiteNum G+1 →
    weightedLeaves J U+bipartiteNum J=1+A.card+P.card →
    weightedLeaves J U<weightedLeaves G U

/-- Universal #180 is exactly equivalent to a weighted-leaf gain when a
single within-layer edge is restored to a tight instance and costs one
bipartite vertex. Only sparse biconnected final graphs need to be tested. -/
theorem universal_iff_horizontal : Universal.{u} ↔ HorizontalExchange.{u} := by
  classical
  constructor
  · intro all V _ _ G hc hn noc r _ odd A ai a b _ _
    dsimp only
    intro rank equality
    have ok := universal_iff_blocks.mp all V G hc hn noc r odd A ai
    omega
  · intro exchange
    apply universal_iff_blocks.mpr
    have result {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
        (hc : H.Connected) (hn : 1<Fintype.card W) :
        ∀ r odd, localBound H r (parity H r odd) := by
      generalize eq : Fintype.card W=n at *
      induction n using Nat.strong_induction_on generalizing W with
      | h n ih =>
        intro r odd
        apply Classical.byContradiction
        intro failure
        let fails (M : SimpleGraph W) := M.Connected ∧ ¬localBound M r (parity M r odd)
        obtain ⟨G,_,small⟩ := {M : SimpleGraph W | fails M}.toFinite.exists_minimal_le
          (show fails H from ⟨hc,failure⟩)
        obtain ⟨gc,no⟩ := small.prop
        have noc : NoCut G := by
          by_contra cut
          obtain ⟨c,S,T,s⟩ := split_of_cut cut
          have next {X Y} (q : Split G c X Y) : ∀ (a : ↥X) p, localBound (side G X) a (parity (side G X) a p) := by
            exact ih (Fintype.card ↥X) (by rw [Fintype.card_coe,← eq]; exact q.smallL)
              _ (q.connectedL gc) rfl q.largeL
          apply no
          rcases s.either r with h|h
          · exact s.parity_join gc ⟨r,h⟩ odd (next s) (next s.flip)
          · exact s.flip.parity_join gc ⟨r,h⟩ odd (next s.flip) (next s)
        have less : ∀ a b, G.Adj a b → let J := G.deleteEdges {s(a,b)}
            J.Connected → localBound J r (parity J r odd) := by
          intro a b e
          dsimp only
          intro connected
          apply Classical.byContradiction
          intro bad
          have strict : G.deleteEdges {s(a,b)} < G := by
            refine lt_of_le_of_ne (G.deleteEdges_le _) ?_
            intro same
            have absent : ¬(G.deleteEdges {s(a,b)}).Adj a b := by simp
            rw [same] at absent
            exact absent e
          exact small.not_prop_of_lt strict (show fails _ from ⟨connected,bad⟩)
        change ¬∀ A : Finset W, Indep G A → _ at no
        push_neg at no
        obtain ⟨A,ai,bad⟩ := no
        have sp : SparseAt G r := by
          intro a b e ab ba
          exact (edge_tight G gc r odd A ai bad less a b e ab ba).1
        have sameLayer : ∃ a b, G.Adj a b ∧ G.dist a r=G.dist b r := by
          apply Classical.byContradiction
          intro noEdge
          have bip := by_layers G gc r univ (fun a _ b _ e same => noEdge ⟨a,b,e,same⟩)
          have w := weighted_bipartite G gc (eq ▸ hn) bip r odd.toNat A ai
          change A.card+(parity G r odd).card+1≤bipartiteNum G+weightedLeaves G (eligible A (parity G r odd) r) at w
          omega
        obtain ⟨a,b,e,d⟩ := sameLayer
        have ab : ¬Arc G r a b := fun z => by have := z.2.1; omega
        have ba : ¬Arc G r b a := fun z => by have := z.2.1; omega
        obtain ⟨rank,leaf,tight,_⟩ := edge_tight G gc r odd A ai bad less a b e ab ba
        have gain := exchange W G gc (eq ▸ hn) noc r sp odd A ai a b e d rank tight
        exact (Nat.ne_of_lt gain) leaf
    intro W _ _ H hc hn _
    exact result H hc hn

#print axioms universal_iff_horizontal
end Minimal180
