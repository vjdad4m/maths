import RankTwoAssembly180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 OddBlock CutGain
universe u
variable {V W : Type u} [Fintype V] [DecidableEq V]

/-- An induced biconnected subgraph of order at least three, with
bipartization deficit at least three and a failed rooted marking. -/
def ResidualBlock (G : SimpleGraph V) : Prop :=
  ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
    Nonempty (H ↪g G) ∧ H.Connected ∧ 2<Fintype.card W ∧ NoCut H ∧
    bipartiteNum H+2<Fintype.card W ∧ ∃ r p, ¬localBound H r (parity H r p)

omit [Fintype V] [DecidableEq V] in
theorem ResidualBlock.lift {H : SimpleGraph W} {G : SimpleGraph V}
    (e : H ↪g G) (res : ResidualBlock H) : ResidualBlock G := by
  obtain ⟨X,ft,de,K,⟨f⟩,data⟩ := res
  exact ⟨X,ft,de,K,⟨e.comp f⟩,data⟩

/-- Absence of an induced residual block proves the rooted inequality for
the whole connected graph. -/
theorem rooted_of_no_residual (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (none : ¬ResidualBlock G) : ∀ r p,localBound G r (parity G r p) := by
  classical
  generalize eq : Fintype.card V=n at *
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases block : NoCut G
    · by_cases rk : Fintype.card V≤bipartiteNum G+2
      · exact (family_of_rank G gc (by omega) rk).rooted
      · have large : 2<Fintype.card V := by omega
        intro r p
        apply Classical.byContradiction
        intro bad
        exact none ⟨V,inferInstance,inferInstance,G,⟨SimpleGraph.Embedding.refl⟩,gc,large,block,by omega,r,p,bad⟩
    · obtain ⟨c,S,T,cut⟩ := split_of_cut block
      have smaller {X Y} (q : Split G c X Y) : ∀ r p,localBound (side G X) r (parity (side G X) r p) :=
        ih (Fintype.card ↥X) (by rw [Fintype.card_coe,←eq]; exact q.smallL) _ (q.connectedL gc)
          (fun res => none (res.lift (SimpleGraph.Embedding.induce (X : Set V)))) rfl q.largeL
      intro r p
      rcases cut.either r with rs|rt
      · exact cut.parity_join gc ⟨r,rs⟩ p (smaller cut) (smaller cut.flip)
      · exact cut.flip.parity_join gc ⟨r,rt⟩ p (smaller cut.flip) (smaller cut)

/-- Any counterexample to ordinary #180 contains an induced biconnected
graph with a failed rooted marking and bipartization deficit at least three. -/
theorem counterexample_has_residual (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (fail : maxLeaves G+bipartiteNum G<1+independence G+maxEven G) : ResidualBlock G := by
  classical
  apply Classical.byContradiction
  intro none
  haveI : Nonempty V := gc.nonempty
  obtain ⟨r,_,re⟩ := exists_mem_eq_sup (s:=univ) (f:=evenCount G) univ_nonempty
  obtain ⟨A,ha,ae⟩ := exists_mem_eq_sup (s:=univ.filter (Indep G)) (f:=card)
    ⟨∅,mem_filter.mpr ⟨mem_univ _,by simp [Indep]⟩⟩
  have bound := rooted_of_no_residual G gc hn none r false A (mem_filter.mp ha).2
  have le : weightedLeaves G (eligible A (parity G r false) r)≤maxLeaves G := by
    rw [←weighted_all]
    exact (restrict_leaves G _ univ).trans (by simp)
  change maxEven G=evenCount G r at re
  change independence G=A.card at ae
  rw [ae,re,even_equiv] at fail
  omega

#print axioms ResidualBlock.lift
#print axioms rooted_of_no_residual
#print axioms counterexample_has_residual
end Minimal180.RootEar
