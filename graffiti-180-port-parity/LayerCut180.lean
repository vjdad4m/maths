import OddCutBudget180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Graffiti318 Graffiti180 Rooted180 Converse180 Assembly180 HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All surviving vertices remain joined to the root along descending
paths if each has a predecessor outside S. -/
theorem descending_core (G : SimpleGraph V) (r : V) (S : Finset V) (rs : r∉S)
    (pred : ∀ v∉S,v≠r → ∃ w,w∉S ∧ G.Adj v w ∧ G.dist v r=G.dist w r+1) :
    Con (alternating G (parity G r false)) (univ\S) := by
  classical
  let D := univ\S
  let H := alternating G (parity G r false)
  let K := H.induce (D : Set V)
  have rr : r∈D := mem_sdiff.mpr ⟨mem_univ _,rs⟩
  apply (connected_iff_exists_forall_reachable K).mpr
  refine ⟨⟨r,rr⟩,fun z => Reachable.symm ?_⟩
  induction h : G.dist z.val r using Nat.strong_induction_on generalizing z with
  | h n ih =>
    by_cases zr : z.val=r
    · exact (Subtype.ext zr : z=⟨r,rr⟩) ▸ Reachable.refl _
    obtain ⟨w,ws,zw,eq⟩ := pred z.val (mem_sdiff.mp z.property).2 zr
    let u : ↥(D:Set V) := ⟨w,mem_sdiff.mpr ⟨mem_univ _,ws⟩⟩
    have edge : K.Adj z u := by
      refine ⟨zw,?_⟩
      change (z.val∈parity G r false ↔ w∉parity G r false)
      simp only [mem_parity,Bool.toNat_false]
      omega
    exact edge.reachable.trans (ih (G.dist w r) (by omega) u rfl)

noncomputable def layer (G : SimpleGraph V) (r : V) (j : ℕ) : Finset V := by
  classical exact univ.filter (fun v => G.dist v r=j)

/-- Any set of odd levels may be tested together, pairing each such
level with the immediately following even level. A failure requires
the total excess width to be less than the deficit minus second degree. -/
theorem widths_budget (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (J : Finset ℕ) (odd : ∀ j∈J,j%2=1) :
    let X := univ.filter (fun v => G.dist v r∈J)
    let Y := univ.filter (fun v => ∃ j∈J,G.dist v r=j+1)
    bipartiteNum G+secondDegree G+1+X.card≤Fintype.card V+Y.card := by
  classical
  intro X Y
  let p (v : V) := if h : v=r then r else (Graffiti169.exists_predecessor G gc r v h).choose
  have spec (v : V) (vr : v≠r) : G.Adj v (p v) ∧ G.dist v r=G.dist (p v) r+1 := by
    simpa only [p,dif_neg vr] using (Graffiti169.exists_predecessor G gc r v vr).choose_spec
  let B := Y.image p
  let S := X\B
  have dis : Disjoint S (parity G r false) := by
    apply disjoint_left.mpr
    intro x xs ev
    have j := odd _ (mem_filter.mp (mem_sdiff.mp xs).1).2
    simp only [mem_parity,Bool.toNat_false] at ev
    omega
  have rs : r∉S := fun h => disjoint_left.mp dis h (by simp [dist_self])
  have con := descending_core G r S rs (by
    intro v _ ne
    refine ⟨p v,?_,spec v ne⟩
    intro ps
    obtain ⟨px,out⟩ := mem_sdiff.mp ps
    have vy : v∈Y := mem_filter.mpr ⟨mem_univ _,_,(mem_filter.mp px).2,(spec v ne).2⟩
    exact out (mem_image.mpr ⟨v,vy,rfl⟩))
  have budget := removable_odds_budget G gc hn r bad S dis con
  have split := card_sdiff_add_card_inter X B
  have le : (X∩B).card≤Y.card := (card_le_card inter_subset_right).trans (card_image_le (s:=Y) (f:=p))
  change bipartiteNum G+secondDegree G+1+(X\B).card≤Fintype.card V at budget
  omega

/-- A single odd layer wider than its successor settles the borderline
case at any maximizing root, including an odd last layer. -/
theorem conjecture180_of_layer (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V) (mx : evenCount G r=maxEven G) (j : ℕ) (odd : j%2=1)
    (pay : Fintype.card V+(layer G r (j+1)).card≤bipartiteNum G+secondDegree G+(layer G r j).card) :
    1+independence G+maxEven G≤maxLeaves G+bipartiteNum G := by
  classical
  rw [←mx]; by_contra! bad
  have b := widths_budget G gc hn r bad {j} (by intro i h; simpa only [mem_singleton.mp h] using odd)
  simp only [mem_singleton,exists_eq_left] at b
  unfold layer at pay
  omega

#print axioms descending_core
#print axioms widths_budget
#print axioms conjecture180_of_layer
end Minimal180.PortParity
