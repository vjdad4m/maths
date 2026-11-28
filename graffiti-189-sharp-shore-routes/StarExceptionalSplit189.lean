import ExceptionalSplit189
import DefectRoutable189
import OffPathBoundaryBudget189
import Normalize189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.DefectRoutable Graffiti189LongestPath.ExceptionalSplit
open Graffiti189LongestPath.Normalize Graffiti189LongestPath.OffPathBoundaryBudget
open private Graffiti189LongestPath.Rigidity.mem_omittedStar from Rigidity189
set_option warningAsError true
set_option maxHeartbeats 2000000
namespace Graffiti189LongestPath.StarExceptionalSplit
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In the odd minimum-height split obstruction, one exceptional
incomplete cross-neighborhood is permitted on the independent side. -/
theorem separated_double_no_one_exception_split (hc : G.Connected) (k : Nat) (hk : 6≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ D : Finset V,D.card<k → (G.induce ((↑D : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    {a b x y : V} {p : G.Walk a b} (hp : EdgeMinAvoid (k+2) p)
    (hx : x∉p.support) (hy : y∉p.support) (xy : G.Adj x y)
    (high : k+2≤G.degree x)
    (double : (Pins p x).card=2) (sep : PairedPins p x=∅)
    (S L : Finset V) (part : S∪L=OmittedStar p x) (dis : Disjoint S L)
    (height : (OmittedStar p x).card=k+1)
    (eq : L.card=S.card+1)
    (e : V) (el : e∈L)
    (cross : ∀ s∈S,∀ l∈L,l≠e → G.Adj s l) (nz : 3≤(S.filter (G.Adj e)).card)
    (ind : ∀ u∈L,∀ v∈L,¬G.Adj u v) : False := by
  classical
  let A := OmittedStar p x
  change S∪L=A at part
  change A.card=k+1 at height
  have sc := congrArg Finset.card part
  rw [card_union_of_disjoint dis] at sc
  have lbig : 1<L.card := by omega
  obtain ⟨u,ul,v,vl,ne⟩ := one_lt_card.mp lbig
  have ex : ∃ w∈L,k+2≤G.degree w :=
    (deg u v ne).elim (fun h => ⟨u,ul,h⟩) (fun h => ⟨v,vl,h⟩)
  obtain ⟨w,wl,wh⟩ := ex
  have wa : w∈A := part ▸ mem_union.mpr (Or.inr wl)
  have wo := (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp wa).1
  let z : ↥(A : Set V) := ⟨w,wa⟩
  let J := G.induce (A : Set V)
  have pins : (Pins p w).card≤2 := by
    by_cases e : (Pins p w).card=0
    · omega
    obtain ⟨i,hi⟩ := card_pos.mp (by omega : 0<(Pins p w).card)
    have q := (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn
      hp wo wh i hi).1
    omega
  let N := (J.neighborFinset z).image Subtype.val
  have nc : N.card=J.degree z := by
    rw [←J.card_neighborFinset_eq_degree,card_image_of_injective _ Subtype.val_injective]
  have ns : N⊆S := by
    intro t ht
    obtain ⟨q,qn,rfl⟩ := mem_image.mp ht
    have e : G.Adj w q.val := (J.mem_neighborFinset _ _).mp qn
    have qa : q.val∈S∪L := by rw [part]; exact q.property
    exact (mem_union.mp qa).elim id (fun ql => (ind w wl q.val ql e).elim)
  have nh := card_le_card ns
  rw [nc] at nh
  have budget := degree_le_shore_and_ports hp.1.1 A z wo
  change G.degree w≤J.degree z+(Pins p w).card+(External G A\p.support.toFinset).card at budget
  have pay : S.card≤(External G A\p.support.toFinset).card := by omega
  have part' : S∪L=OmittedStar p x := part
  apply one_defect_double_branch_impossible hc k hk cap conn hp.1.1 hx hy xy high double sep S pay
  · intro t ht
    rw [←part'] at ht ⊢
    exact one_exception_outer S L e el dis eq cross nz ht
  · intro a ha b hb ne
    rw [←part'] at ha hb ⊢
    exact one_exception_routes S L e el dis eq cross nz ha hb ne

#print axioms separated_double_no_one_exception_split
end Graffiti189LongestPath.StarExceptionalSplit
