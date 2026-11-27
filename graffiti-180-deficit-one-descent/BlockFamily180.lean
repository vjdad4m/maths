import RankTwoRoot180

set_option warningAsError true
namespace Minimal180.DescentOne
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 OddBlock CutGain
open Classical
universe u

/-- Finite assemblies along cut vertices. The base pieces can be
nontrivial connected bipartite graphs, deficit-at-most-one blocks,
or deficit-at-most-two blocks of minimum degree at least three. -/
inductive BlockFamily : {V : Type u} → [Fintype V] → [DecidableEq V] → SimpleGraph V → Prop where
  | bip {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hc : G.Connected)
      (hn : 1<Fintype.card V) (col : TwoColor G univ) : BlockFamily G
  | block {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hc : G.Connected)
      (hn : 2<Fintype.card V) (nc : NoCut G) (rk : Fintype.card V≤bipartiteNum G+2)
      (extra : Fintype.card V≤bipartiteNum G+1 ∨ ∀ r,3≤G.degree r) : BlockFamily G
  | split {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {c : V} {S T : Finset V}
      (hc : G.Connected) (cut : Split G c S T) (near : BlockFamily (side G S))
      (far : BlockFamily (side G T)) : BlockFamily G

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem BlockFamily.rooted (proof : BlockFamily G) : ∀ r p, localBound G r (parity G r p) := by
  classical
  induction proof with
  | @bip W _ _ H hc hn col =>
    intro r p A ind
    let P := parity H r p
    have b := weighted_bipartite H hc hn col r p.toNat A ind
    change A.card+P.card+1≤bipartiteNum H+weightedLeaves H (eligible A P r) at b
    change 1+A.card+P.card≤weightedLeaves H (eligible A P r)+bipartiteNum H
    omega
  | @block W _ _ H hc hn nc rk extra =>
    intro r p A ind
    rcases extra with low|high
    · exact rank_one_rooted H hc (by omega) r (block_neighbors H hc hn nc r) low p A ind
    · exact rank_two_root H hc nc hn rk r p A ind (Or.inl (high r))
  | split hc s _ _ l r =>
    intro v p
    rcases s.either v with vs|vt
    · exact s.parity_join hc ⟨v,vs⟩ p l r
    · exact s.flip.parity_join hc ⟨v,vt⟩ p r l

/-- Ordinary, unweighted Graffiti.pc #180 on every graph in the
stated cut-vertex assembly class. No limit on the number of blocks. -/
theorem conjecture180_on_family (proof : BlockFamily G) :
    1+independence G+maxEven G≤maxLeaves G+bipartiteNum G := by
  classical
  have hc : G.Connected := by cases proof <;> assumption
  haveI : Nonempty V := hc.nonempty
  obtain ⟨r,_,re⟩ := exists_mem_eq_sup (s:=univ) (f:=evenCount G) univ_nonempty
  obtain ⟨A,ha,ae⟩ := exists_mem_eq_sup (s:=univ.filter (Indep G)) (f:=card)
    ⟨∅,mem_filter.mpr ⟨mem_univ _,by simp [Indep]⟩⟩
  have bd := proof.rooted r false A (mem_filter.mp ha).2
  have le : weightedLeaves G (eligible A (parity G r false) r)≤maxLeaves G := by
    rw [←weighted_all]
    exact (restrict_leaves G _ univ).trans (by simp)
  change maxEven G=evenCount G r at re
  change independence G=A.card at ae
  rw [re,ae,even_equiv]
  omega

#print axioms BlockFamily.rooted
#print axioms conjecture180_on_family
end Minimal180.DescentOne
