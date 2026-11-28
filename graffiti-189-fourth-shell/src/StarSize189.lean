import FarReciprocity189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.OneSlack Graffiti189LongestPath.SingleStar
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.mem_omittedStar Graffiti189LongestPath.Rigidity.mem_external from Rigidity189
set_option warningAsError true
namespace Graffiti189LongestPath.StarSize
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A pin on a longest path bounds the entire omitted star, without
any hypothesis on connectivity strength, degree, or the number of pins. -/
theorem star_order_of_pin (hc : G.Connected) (d : Nat)
    (cap : ∀ v, (DistanceTwo G v).card≤d)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    {i : Nat} (hi : i∈Pins p x) :
    (OmittedStar p x).card≤2*d ∧
      (((OmittedStar p x).filter (G.Adj (p.getVert i))).card≤d) := by
  classical
  let A := OmittedStar p x
  let b := p.getVert i
  let f := p.getVert (i+1)
  have bb : G.Adj x b := (Graffiti189LongestPath.pin_data hi).2
  have bf : G.Adj b f := p.adj_getVert_succ (Graffiti189LongestPath.pin_data hi).1
  have ff : f∈FlankVertices p x := mem_image.mpr
    ⟨i+1,mem_union.mpr (Or.inr (mem_image.mpr ⟨i,hi,rfl⟩)),rfl⟩
  have fno := (mem_sdiff.mp (flanks_outside_boundary hc hp hx ff)).2
  have fa : f∉A := fun h => (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp h).1 (p.getVert_mem_support _)
  have ba : b∉A := fun h => (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp h).1 (p.getVert_mem_support _)
  let U := A.filter (G.Adj b)
  let W := A.filter (fun y => ¬G.Adj b y)
  have useU : U⊆DistanceTwo G f := by
    intro y hy
    obtain ⟨ya,by'⟩ := mem_filter.mp hy
    have no : ¬G.Adj f y := fun e => fno
      (Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨fa,y,ya,e.symm⟩)
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.dist_two hc (fun e => fa (e.symm ▸ ya)) no bf.symm by')
  have useW : W⊆DistanceTwo G b := by
    intro y hy
    obtain ⟨ya,no⟩ := mem_filter.mp hy
    rcases (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp ya).2 with eq|xy
    · exact (no (eq.symm ▸ bb.symm)).elim
    · exact Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc (fun e => ba (e.symm ▸ ya)) no bb.symm xy)
  have c : A⊆U∪W := by
    intro y hy
    by_cases e : G.Adj b y
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hy,e⟩))
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hy,e⟩))
  have uu : U.card≤d := (card_le_card useU).trans (cap f)
  have ww : W.card≤d := (card_le_card useW).trans (cap b)
  have cc := (card_le_card c).trans (card_union_le U W)
  change A.card≤2*d ∧ U.card≤d
  exact ⟨by omega,uu⟩
#print axioms star_order_of_pin
end Graffiti189LongestPath.StarSize
