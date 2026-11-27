import RankTwoBlock180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 OddBlock CutGain
open Classical
universe u

/-- Finite assemblies along cut vertices. The base pieces can be
nontrivial connected bipartite graphs or biconnected graphs with
bipartization deficit at most two, without a degree restriction. -/
inductive RankTwoFamily : {V : Type u} → [Fintype V] → [DecidableEq V] → SimpleGraph V → Prop where
  | bip {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hc : G.Connected)
      (hn : 1<Fintype.card V) (col : TwoColor G univ) : RankTwoFamily G
  | block {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hc : G.Connected)
      (hn : 2<Fintype.card V) (nc : NoCut G) (rk : Fintype.card V≤bipartiteNum G+2) : RankTwoFamily G
  | split {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {c : V} {S T : Finset V}
      (hc : G.Connected) (cut : Split G c S T) (near : RankTwoFamily (side G S))
      (far : RankTwoFamily (side G T)) : RankTwoFamily G

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem RankTwoFamily.rooted (proof : RankTwoFamily G) : ∀ r p, localBound G r (parity G r p) := by
  classical
  induction proof with
  | @bip W _ _ H hc hn col =>
    intro r p A ind
    let P := parity H r p
    have b := weighted_bipartite H hc hn col r p.toNat A ind
    change A.card+P.card+1≤bipartiteNum H+weightedLeaves H (eligible A P r) at b
    change 1+A.card+P.card≤weightedLeaves H (eligible A P r)+bipartiteNum H
    omega
  | @block W _ _ H hc hn nc rk => exact rank_two_block H hc nc hn rk
  | split hc s _ _ l r =>
    intro v p
    rcases s.either v with vs|vt
    · exact s.parity_join hc ⟨v,vs⟩ p l r
    · exact s.flip.parity_join hc ⟨v,vt⟩ p r l

/-- Ordinary, unweighted Graffiti.pc #180 on every graph in the
stated cut-vertex assembly class. No limit on the number of blocks. -/
theorem conjecture180_on_family (proof : RankTwoFamily G) :
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

/-- Restricting to an induced subgraph cannot increase the minimum
number of deletions needed to obtain a bipartite graph. -/
theorem deficit_induced (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    (rank : Fintype.card V≤bipartiteNum G+k) :
    Fintype.card ↥S≤bipartiteNum (side G S)+k := by
  classical
  obtain ⟨B,hb,maximal⟩ := optB G
  let X := pull (fun z : ↥S => z.val) B
  have ok : TwoColor (side G S) X := restrict_color _ _ _ Subtype.val_injective (fun e => e) hb
  have cap := size_bip _ ok
  have inter : X.card=(B∩S).card := by
    have eq := congrArg Finset.card (push_pull S B)
    simpa only [push,card_map] using eq
  have size := card_union_add_card_inter B S
  have all : (B∪S).card≤Fintype.card V := card_le_univ _
  rw [Fintype.card_coe]
  omega

/-- The assembly class contains every nontrivial connected graph whose
global bipartization deficit is at most two. -/
theorem family_of_rank (G : SimpleGraph V) (hc : G.Connected) (hn : 1<Fintype.card V)
    (rank : Fintype.card V≤bipartiteNum G+2) : RankTwoFamily G := by
  classical
  generalize eq : Fintype.card V=n at *
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases block : NoCut G
    · by_cases order : 2<Fintype.card V
      · exact .block hc order block (eq ▸ rank)
      · obtain ⟨a,b,ab⟩ := Fintype.one_lt_card_iff.mp (show 1<Fintype.card V by omega)
        have un : ({a,b}:Finset V)=univ := eq_univ_of_card _ (by rw [card_pair ab]; omega)
        apply RankTwoFamily.bip hc (by omega)
        apply (color_function G _).mpr
        refine ⟨fun z => decide (z=a),fun x _ y _ e => ?_⟩
        have only (z : V) : z=a ∨ z=b := by have m : z∈({a,b}:Finset V) := un ▸ mem_univ z; simpa only [mem_insert,mem_singleton] using m
        rcases only x with rfl|rfl <;> rcases only y with rfl|rfl <;> simp_all [ne_comm]
    · obtain ⟨c,S,T,s⟩ := split_of_cut block
      have smaller {X Y} (q : Split G c X Y) : RankTwoFamily (side G X) :=
        ih (Fintype.card ↥X) (by rw [Fintype.card_coe,←eq]; exact q.smallL) _ (q.connectedL hc) rfl q.largeL
          (deficit_induced G X 2 (eq ▸ rank))
      exact .split hc s (smaller s) (smaller s.flip)

/-- Ordinary Graffiti.pc 180 for every nontrivial finite connected graph
that becomes bipartite after deleting at most two vertices. -/
theorem conjecture180_deficit_two (G : SimpleGraph V) (hc : G.Connected) (hn : 1<Fintype.card V)
    (rank : Fintype.card V≤bipartiteNum G+2) :
    1+independence G+maxEven G≤maxLeaves G+bipartiteNum G :=
  conjecture180_on_family (family_of_rank G hc hn rank)

/-- Strict gain in unrestricted eligible leaves after a tight lower
equality and a strict bipartite-order drop at an upper block of deficit
at most two. -/
theorem rank_two_gain (J G : SimpleGraph V) (gc : G.Connected) (block : NoCut G)
    (hn : 2<Fintype.card V) (rank : Fintype.card V≤bipartiteNum G+2)
    (drop : bipartiteNum G<bipartiteNum J) (r : V) (odd : Bool) (A : Finset V) (ai : Indep G A) :
    let P := parity G r odd
    let U := eligible A P r
    weightedLeaves J U+bipartiteNum J=1+A.card+P.card → weightedLeaves J U<weightedLeaves G U := by
  intro P U equality
  have lower := rank_two_block G gc block hn rank r odd A ai
  change 1+A.card+P.card≤weightedLeaves G U+bipartiteNum G at lower
  omega

#print axioms deficit_induced
#print axioms family_of_rank
#print axioms conjecture180_deficit_two
#print axioms rank_two_gain
#print axioms RankTwoFamily.rooted
#print axioms conjecture180_on_family
end Minimal180.RootEar
