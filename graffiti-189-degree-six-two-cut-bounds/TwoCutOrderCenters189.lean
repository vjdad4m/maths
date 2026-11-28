import AdjacentCutFiveActual189
import OddPortsCut189
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Graffiti189LongestPath.CrossSaturation.TwoCutOrder
open SimpleGraph Finset
open private CutGraph from AdjacentCutFiveActual189
open private left_boundary right_boundary odd_equal from AdjacentCutFiveBound189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem positive_even_cap {d : ℕ} {x : V} (hx : (EvenFrom G x).card≤d+1) :
    (PositiveEven G x).card≤d := by
  classical
  have h : x∈EvenFrom G x := by simp [EvenFrom,dist_self]
  have k := card_erase_of_mem h
  change ((EvenFrom G x).erase x).card ≤ d
  omega

private theorem card_of_centers (d k : ℕ) (cap : ∀ z,(EvenFrom G z).card≤d+1)
    (K : Finset V) (nK : K.card≤k)
    (cover : ∀ z : V,z≠a → z≠b → ∃ w∈K,z∈PositiveEven G w) :
    Fintype.card V≤k*d+2 := by
  classical
  let S := K.biUnion (PositiveEven G)
  have cnt : S.card≤K.card*d :=
    card_biUnion_le_card_mul _ _ _ (fun w _=>positive_even_cap (cap w))
  have sub : (univ : Finset V)⊆insert a (insert b S) := by
    intro z _
    by_cases za : z=a
    · simp [za]
    by_cases zb : z=b
    · simp [zb]
    obtain ⟨w,wK,h⟩ := cover z za zb
    exact mem_insert_of_mem (mem_insert_of_mem (mem_biUnion.mpr ⟨w,wK,h⟩))
  have n := card_le_card sub
  rw [card_univ] at n
  have n₁ := card_insert_le a (insert b S)
  have n₂ := card_insert_le b S
  have m := Nat.mul_le_mul_right d nK
  omega

private theorem near_port_even {x z a b : V} (L : Finset V)
    (hc : G.Connected) (xl : x∈L) (zn : z∉L)
    (edge : ∀ u∈L,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈L)
    (xb : x≠b) (ax : G.Adj a x) (lo : G.dist a z≤G.dist b z)
    (odd : ¬Even (G.dist a z)) : z∈PositiveEven G x := by
  classical
  have m := cross_metric L hc xl zn edge
  have a1 := dist_eq_one_iff_adj.mpr ax.symm
  have b1 := hc.pos_dist_of_ne xb
  have q : G.dist x z=G.dist a z+1 := by omega
  have e : Even (G.dist x z) := by
    rw [q]
    simp only [Nat.even_iff] at odd ⊢
    omega
  exact mem_erase.mpr ⟨fun h=>zn (h.symm ▸ xl),mem_filter.mpr ⟨mem_univ _,e⟩⟩

private theorem both_sides (ab : a≠b)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (cut : 2≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent) :
    ∃ S : CrossSaturation.Split G a b, ∃ x y u v : V,
      x∈S.L ∧ y∈S.L ∧ u∈S.R ∧ v∈S.R ∧
      G.Adj a x ∧ G.Adj b y ∧ G.Adj a u ∧ G.Adj b v := by
  obtain ⟨S,ra,rb⟩ := FiveAdjacent.actual_split ab conn cut
  obtain ⟨x,xL,ax⟩ := S.leftA
  obtain ⟨y,yL,by'⟩ := S.leftB
  obtain ⟨u,uR,au⟩ := ra
  obtain ⟨v,vR,bv⟩ := rb
  exact ⟨S,x,y,u,v,xL,yL,uR,vR,ax,by',au,bv⟩

/-- If deleting a pair disconnects a graph that remains connected on deleting
any one vertex, an even-distance bound d+1 bounds the graph's order by 6d+2. -/
theorem order_le_six_mul_add_two (hc : G.Connected) (ab : a≠b) (d : ℕ)
    (cap : ∀ z,(EvenFrom G z).card≤d+1)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (cut : 2≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent) :
    Fintype.card V≤6*d+2 := by
  classical
  obtain ⟨S,x,y,u,v,xL,yL,uR,vR,ax,by',au,bv⟩ := both_sides ab conn cut
  let K : Finset V := [a,b,x,y,u,v].toFinset
  have nK : K.card≤6 := List.toFinset_card_le _
  apply card_of_centers d 6 cap K nK
  intro z za zb
  by_cases ea : Even (G.dist a z)
  · exact ⟨a,by simp [K],mem_erase.mpr ⟨za,mem_filter.mpr ⟨mem_univ _,ea⟩⟩⟩
  by_cases eb : Even (G.dist b z)
  · exact ⟨b,by simp [K],mem_erase.mpr ⟨zb,mem_filter.mpr ⟨mem_univ _,eb⟩⟩⟩
  rcases S.cover z with h|h|zL|zR
  · exact (za h).elim
  · exact (zb h).elim
  · have zz : z∉S.R := fun h=>disjoint_left.mp S.dis zL h
    by_cases order : G.dist a z≤G.dist b z
    · exact ⟨u,by simp [K],near_port_even S.R hc uR zz (right_boundary S)
        (fun h=>S.rightOff.2 (h ▸ uR)) au order ea⟩
    exact ⟨v,by simp [K],near_port_even (a:=b) (b:=a) S.R hc vR zz
      (fun t tm w tw=>by simpa only [or_left_comm (a:=w=a) (b:=w=b)] using right_boundary S t tm w tw)
      (fun h=>S.rightOff.1 (h ▸ vR)) bv (by omega) eb⟩
  have zz : z∉S.L := fun h=>disjoint_left.mp S.dis h zR
  by_cases order : G.dist a z≤G.dist b z
  · exact ⟨x,by simp [K],near_port_even S.L hc xL zz (left_boundary S)
      (fun h=>S.leftOff.2 (h ▸ xL)) ax order ea⟩
  exact ⟨y,by simp [K],near_port_even (a:=b) (b:=a) S.L hc yL zz
    (fun t tm w tw=>by simpa only [or_left_comm (a:=w=a) (b:=w=b)] using left_boundary S t tm w tw)
    (fun h=>S.leftOff.1 (h ▸ yL)) by' (by omega) eb⟩

/-- The bound improves to 4d+2 for adjacent separators because any two odd
distances to the adjacent endpoints are equal. -/
theorem order_le_four_mul_add_two_of_adjacent (hc : G.Connected) (ab : G.Adj a b) (d : ℕ)
    (cap : ∀ z,(EvenFrom G z).card≤d+1)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (cut : 2≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent) :
    Fintype.card V≤4*d+2 := by
  classical
  obtain ⟨S,x,_,u,_,xL,_,uR,_,ax,_,au,_⟩ := both_sides ab.ne conn cut
  let K : Finset V := [a,b,x,u].toFinset
  have nK : K.card≤4 := List.toFinset_card_le _
  apply card_of_centers d 4 cap K nK
  intro z za zb
  by_cases ea : Even (G.dist a z)
  · exact ⟨a,by simp [K],mem_erase.mpr ⟨za,mem_filter.mpr ⟨mem_univ _,ea⟩⟩⟩
  by_cases eb : Even (G.dist b z)
  · exact ⟨b,by simp [K],mem_erase.mpr ⟨zb,mem_filter.mpr ⟨mem_univ _,eb⟩⟩⟩
  have order := (odd_equal hc ab ea eb).le
  rcases S.cover z with h|h|zL|zR
  · exact (za h).elim
  · exact (zb h).elim
  · exact ⟨u,by simp [K],near_port_even S.R hc uR (fun h=>disjoint_left.mp S.dis zL h)
      (right_boundary S) (fun h=>S.rightOff.2 (h ▸ uR)) au order ea⟩
  exact ⟨x,by simp [K],near_port_even S.L hc xL (fun h=>disjoint_left.mp S.dis h zR)
    (left_boundary S) (fun h=>S.leftOff.2 (h ▸ xL)) ax order ea⟩

theorem order_le_thirty_eight_at_six (hc : G.Connected) (ab : a≠b)
    (cap : ∀ z,(EvenFrom G z).card≤7)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (cut : 2≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent) :
    Fintype.card V≤38 :=
  order_le_six_mul_add_two hc ab 6 cap conn cut

#print axioms order_le_six_mul_add_two
#print axioms order_le_four_mul_add_two_of_adjacent
#print axioms order_le_thirty_eight_at_six
end Graffiti189LongestPath.CrossSaturation.TwoCutOrder
