import Graph

namespace CubicRainbow791
open Finset SimpleGraph

def leftSites : Finset V := {0,1,2}
def rightSites : Finset V := {3,4,5,6,7}
def leftCores : Finset V := {8,9,10,11}
def rightCores : Finset V := {12,13,14,15,16,17,19}

/-- Each internal core represents an edge of one side of the auxiliary
multigraph. The last pair joins the two sides by core 18, or ends at 6,7
through core 19. Entries for sites and for core 18 are unused. -/
def tailV : V → V := ![0,0,0,0,0,0,0,0,0,0,1,1,3,3,4,4,5,5,0,6]
def headV : V → V := ![0,0,0,0,0,0,0,0,1,2,2,2,4,5,6,7,6,7,3,7]

/-- Distinct chosen tails occupy all but at least one of the touched sites.
The greatest touched site cannot be a tail, since each head is larger. -/
private theorem count_side (Z D A : Finset V) (ind : ∀ x ∈ Z, ∀ y ∈ Z, ¬g.Adj x y)
    (ends : ∀ x ∈ D, tailV x ∈ A ∧ headV x ∈ A ∧ tailV x < headV x ∧
      g.Adj x (tailV x) ∧ g.Adj x (headV x))
    (collision : ∀ x ∈ D, ∀ y ∈ D, tailV x=tailV y → x=y ∨ g.Adj x y) :
    (D ∩ Z).card ≤ (A \ Z).card ∧
    ((A \ Z).Nonempty → (D ∩ Z).card < (A \ Z).card) := by
  classical
  have facts {x : V} (hx : x ∈ D ∩ Z) :
      tailV x ∈ A \ Z ∧ headV x ∈ A \ Z ∧ tailV x < headV x := by
    obtain ⟨d,z⟩ := mem_inter.mp hx
    obtain ⟨a,b,lt,at',ah⟩ := ends x d
    exact ⟨mem_sdiff.mpr ⟨a,fun h => ind x z _ h at'⟩,
      mem_sdiff.mpr ⟨b,fun h => ind x z _ h ah⟩,lt⟩
  have inject : Set.InjOn tailV ↑(D ∩ Z) := by
    intro x hx y hy eq
    obtain ⟨xd,xz⟩ := mem_inter.mp hx
    obtain ⟨yd,yz⟩ := mem_inter.mp hy
    exact (collision x xd y yd eq).resolve_right (ind x xz y yz)
  refine ⟨card_le_card_of_injOn tailV (fun _ h => (facts h).1) inject,?_⟩
  intro h
  let m := (A \ Z).max' h
  have image {x} (hx : x ∈ D ∩ Z) : tailV x ∈ (A \ Z).erase m := by
    obtain ⟨a,b,lt⟩ := facts hx
    exact mem_erase.mpr ⟨(lt.trans_le (le_max' _ _ b)).ne,a⟩
  have cap := card_le_card_of_injOn tailV (fun _ hx => image hx) inject
  exact cap.trans_lt (card_erase_lt_of_mem (max'_mem _ h))

/-- The eight sites are the unique independent set of size at least eight. -/
theorem independent_rigid (Z : Finset V) (ind : ∀ x ∈ Z, ∀ y ∈ Z, ¬g.Adj x y)
    (large : 8 ≤ Z.card) : Z = leftSites ∪ rightSites := by
  classical
  have left := count_side Z leftCores leftSites ind (by decide) (by decide)
  have right := count_side Z rightCores rightSites ind (by decide) (by decide)
  let T : Finset V := if 18 ∈ Z then {18} else ∅
  have sub : Z ⊆ (((leftSites ∩ Z ∪ rightSites ∩ Z) ∪ (leftCores ∩ Z)) ∪ (rightCores ∩ Z)) ∪ T := by
    intro x hx
    have partition : ∀ x : V, x ∈ leftSites ∨ x ∈ rightSites ∨ x ∈ leftCores ∨ x ∈ rightCores ∨ x=18 := by decide
    rcases partition x with h|h|h|h|h <;> simp_all [T]
  have cap : Z.card ≤ (leftSites ∩ Z).card+(rightSites ∩ Z).card+
      (leftCores ∩ Z).card+(rightCores ∩ Z).card+T.card :=
    (card_le_card sub).trans <| (card_union_le _ _).trans <| Nat.add_le_add_right
      ((card_union_le _ _).trans <| Nat.add_le_add_right
        ((card_union_le _ _).trans <| Nat.add_le_add_right (card_union_le _ _) _) _) _
  have lsum := card_inter_add_card_sdiff leftSites Z
  have rsum := card_inter_add_card_sdiff rightSites Z
  have ls : leftSites.card=3 := by decide
  have rs : rightSites.card=5 := by decide
  have same (emptyL : ¬(leftSites \ Z).Nonempty) (emptyR : ¬(rightSites \ Z).Nonempty)
      (bridge : 18 ∉ Z) : Z = leftSites ∪ rightSites := by
    have l0 : (leftSites \ Z).card=0 := by rw [not_nonempty_iff_eq_empty.mp emptyL]; rfl
    have r0 : (rightSites \ Z).card=0 := by rw [not_nonempty_iff_eq_empty.mp emptyR]; rfl
    have eL : leftCores ∩ Z = ∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero (left.1.trans_eq l0))
    have eR : rightCores ∩ Z = ∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero (right.1.trans_eq r0))
    have only : Z ⊆ leftSites ∪ rightSites := by
      intro x hx
      have h := sub hx
      simpa [T,bridge,eL,eR,mem_union,mem_inter,hx] using h
    have eq : (leftSites ∪ rightSites).card = 8 := by decide
    exact eq_of_subset_of_card_le only (eq.trans_le large)
  by_cases bridge : 18 ∈ Z
  · have l : (leftSites \ Z).Nonempty := ⟨0,mem_sdiff.mpr ⟨by decide,fun h => ind 18 bridge 0 h (by decide)⟩⟩
    have r : (rightSites \ Z).Nonempty := ⟨3,mem_sdiff.mpr ⟨by decide,fun h => ind 18 bridge 3 h (by decide)⟩⟩
    have a := left.2 l
    have b := right.2 r
    have t : T.card=1 := by simp [T,bridge]
    omega
  · have t : T.card=0 := by simp [T,bridge]
    by_cases l : (leftSites \ Z).Nonempty
    · have a := left.2 l
      omega
    by_cases r : (rightSites \ Z).Nonempty
    · have b := right.2 r
      omega
    exact same l r bridge

end CubicRainbow791
