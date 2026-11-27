import ResidualBlock180
import TwoCenters180
import DeepFork180
import Packing180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 CutGain RootEar
open Classical
universe u
variable {V W : Type u} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- The odd-cycle transversal number cannot increase on an embedded
subgraph. The backward edge implication of an induced embedding is unused. -/
theorem embedding_deficit {G : SimpleGraph V} {H : SimpleGraph W} (f : W→V)
    (inj : Function.Injective f) (map : ∀ {x y},H.Adj x y → G.Adj (f x) (f y))
    (k : ℕ) (bound : Fintype.card V≤bipartiteNum G+k) : Fintype.card W≤bipartiteNum H+k := by
  classical
  obtain ⟨B,col,eq⟩ := optB G
  let C := pull f B
  have lo := size_bip H (restrict_color H G f inj map col)
  change C.card≤bipartiteNum H at lo
  let e : W↪V := ⟨f,inj⟩
  have inc : (univ\C).map e⊆univ\B := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
    exact mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_sdiff.mp hx).2 (mem_pull.mpr h)⟩
  have cnt := card_le_card inc
  rw [card_map] at cnt
  have g := card_sdiff_add_card_eq_card (subset_univ B)
  have h := card_sdiff_add_card_eq_card (subset_univ C)
  rw [card_univ] at g h
  omega

/-- The outward fork profile of the actual marked vertices. -/
def ForkProfile (G : SimpleGraph V) (r : V) (Y : Finset V) : Prop :=
  let F (v : V) := outward G r {v}
  let Q := Fork G r Y
  (∀ v∈Y,(F v).card≤2) ∧
  (∀ u,Q u → ∀ v,Q v → G.dist u r=G.dist v r) ∧
  ((∃ z,∀ u,Q u → z∈F u) ∨ ∃ a b c : V,a≠b ∧ a≠c ∧ b≠c ∧
      (∃ u,Q u ∧ F u={a,b}) ∧ (∃ u,Q u ∧ F u={b,c}) ∧ (∃ u,Q u ∧ F u={a,c}) ∧
      ∀ u,Q u → F u={a,b} ∨ F u={b,c} ∨ F u={a,c})

/-- A counterexample of global deficit at most three would induce a block
of exact deficit three with a genuine failed marking. The fork profile
and all local center tests refer to that same marking and root. -/
theorem rank_three_residual (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (rk : Fintype.card V≤bipartiteNum G+3)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+maxEven G) :
    ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
    Nonempty (H ↪g G) ∧ H.Connected ∧ 2<Fintype.card W ∧ NoCut H ∧
    bipartiteNum H+3=Fintype.card W ∧ ∃ (r : W) (p : Bool) (A : Finset W),
    let P := parity H r p
    let X := A∪P
    let D := X\(A∩P)
    Indep H A ∧ weightedLeaves H (eligible A P r)+bipartiteNum H<1+A.card+P.card ∧
    ForkProfile H r (X.erase r) ∧
    ∀ B⊆X.erase r, bipartiteNum H+baseScore H r D X+(children H r D B).card<Fintype.card W+B.card := by
  classical
  obtain ⟨W,ft,de,H,⟨f⟩,hc,ord,block,high,r,p,fail⟩ := counterexample_has_residual G gc hn bad
  let P := parity H r p
  change ¬∀ A,Indep H A → 1+A.card+P.card≤weightedLeaves H (eligible A P r)+bipartiteNum H at fail
  push_neg at fail
  obtain ⟨A,ai,wrong⟩ := fail
  have low := embedding_deficit (H:=H) (G:=G) f f.injective (fun e => f.map_adj_iff.mpr e) 3 rk
  have two := block_neighbors H hc ord block r
  have shape := rank_three_forks H hc (by omega) r two p A ai low wrong
  let X := A∪P
  let D := X\(A∩P)
  refine ⟨W,ft,de,H,⟨f⟩,hc,ord,block,by omega,r,p,A,ai,wrong,shape,?_⟩
  intro B inc
  by_contra! enough
  have yes : LayerTest H r A P := by
    refine ⟨B,inc,?_⟩
    change Fintype.card W+B.card≤bipartiteNum H+(if r∈D then 1 else 0)+
      (if r∈X then H.degree r-2 else 0)+score H r D B
    rw [score_formula]
    change Fintype.card W+B.card≤bipartiteNum H+baseScore H r D X+(children H r D B).card at enough
    unfold baseScore at enough
    omega
  exact (Nat.not_le.mpr wrong) (rooted_of_layer_test H hc (by omega) r two p A ai yes)

#print axioms embedding_deficit
#print axioms rank_three_residual
end Minimal180.HigherRank
