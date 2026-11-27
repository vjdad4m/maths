import RootBonus180
import ColorRepair180
import DeletionClass180
import RankTwoAssembly180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

theorem pinned_of_low_marks (G : SimpleGraph V) (r : V) (p : Bool) (A : Finset V) (ai : Indep G A)
    (low : ∀ x∈A∩parity G r p,G.degree x≤3) (ordinary : localBound G r (parity G r p)) :
    Pinned G r p A (A∩parity G r p) := by
  obtain ⟨Z,col,mx,inc⟩ := pin_low_degree G (A∩parity G r p)
    (fun x xm y ym => ai x (mem_inter.mp xm).1 y (mem_inter.mp ym).1) low
  exact ⟨Z,col,inc,mx.symm ▸ ordinary A ai⟩

theorem odd_of_low_marks (G : SimpleGraph V) (r : V) (I : Finset V) (ii : Indep G I) (ir : r∈I)
    (low : ∀ x∈insert r (I∩parity G r true),G.degree x≤3) (ordinary : localBound G r (parity G r true)) :
    OddRootTest G r I := by
  let Q := parity G r true
  let D := insert r (I∩Q)
  have sub : D⊆I := insert_subset ir inter_subset_left
  obtain ⟨Z,col,mx,inc⟩ := pin_low_degree G D (fun x xm y ym => ii x (sub xm) y (sub ym)) low
  refine ⟨Z,col,inc,?_⟩
  have ok := ordinary I ii
  change 1+I.card+Q.card≤weightedLeaves G (eligible I Q r)+bipartiteNum G at ok
  change 1+I.card+Q.card≤weightedLeaves G (eligible I Q r)+Z.card+bonus G r Z
  omega

/-- Arbitrary bags can replace the degree-at-most-three indices; other
bags may be arbitrary nonempty cliques. There is no deficit bound upstairs.
The quotient belongs to the checked rank-two cut assembly class. -/
theorem Bags.lowRankFamily {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B} (h : Bags H G f)
    (gc : G.Connected) (hn : 1<Fintype.card B) (family : RootEar.RankTwoFamily G)
    (low : ∀ i,NonCliqueBag H f i → G.degree i≤3) :
    (∀ r p,localBound H r (parity H r p)) ∧
      1+independence H+Graffiti318.maxEven H≤maxLeaves H+bipartiteNum H := by
  have rooted (r : V) (p : Bool) := h.lowDegreeRooted low gc hn r p (family.rooted (f r) p)
  exact ⟨rooted,ordinary_of_rooted H (h.connected gc hn) rooted⟩

theorem Bags.lowRankTwo {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B} (h : Bags H G f)
    (gc : G.Connected) (hn : 1<Fintype.card B) (rank : Fintype.card B≤bipartiteNum G+2)
    (low : ∀ i,NonCliqueBag H f i → G.degree i≤3) :
    1+independence H+Graffiti318.maxEven H≤maxLeaves H+bipartiteNum H :=
  (h.lowRankFamily gc hn (RootEar.family_of_rank G gc hn rank) low).2

#print axioms pinned_of_low_marks
#print axioms odd_of_low_marks
#print axioms Bags.lowRankFamily
#print axioms Bags.lowRankTwo
end Minimal180.Substitution
