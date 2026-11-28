import TwoCutOrderCenters189

namespace Graffiti189LongestPath.CrossSaturation.TwoCutOrder
open SimpleGraph Finset
open private CutGraph from AdjacentCutFiveActual189
open private left_boundary right_boundary from AdjacentCutFiveBound189
open private card_of_centers near_port_even both_sides from TwoCutOrderCenters189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem odd_both_across_even (L : Finset V) (hc : G.Connected)
    {x z : V} (xl : x∈L) (zn : z∉L)
    (closed : ∀ u∈L,∀ w,G.Adj u w → w=a ∨ w=b ∨ w∈L)
    (xa : ¬Even (G.dist a x)) (xb : ¬Even (G.dist b x))
    (za : ¬Even (G.dist a z)) (zb : ¬Even (G.dist b z)) : z∈PositiveEven G x := by
  classical
  have m := cross_metric L hc xl zn closed
  rw [dist_comm (u:=x) (v:=a),dist_comm (u:=x) (v:=b)] at m
  have even : Even (G.dist x z) := by
    rw [m]
    simp only [Nat.even_iff] at xa xb za zb ⊢
    omega
  exact mem_erase.mpr ⟨fun h=>zn (h.symm ▸ xl),mem_filter.mpr ⟨mem_univ _,even⟩⟩

private theorem four_centers_from_split (hc : G.Connected) (_ab : a≠b)
    (S : CrossSaturation.Split G a b)
    {la lb ra rb : V} (laL : la∈S.L) (lbL : lb∈S.L) (raR : ra∈S.R) (rbR : rb∈S.R)
    (ala : G.Adj a la) (blb : G.Adj b lb) (ara : G.Adj a ra) (brb : G.Adj b rb) :
    ∃ x y : V, ∀ z : V,z≠a → z≠b →
      z∈PositiveEven G a ∨ z∈PositiveEven G b ∨ z∈PositiveEven G x ∨ z∈PositiveEven G y := by
  classical
  let oddOdd (z : V) := ¬Even (G.dist a z) ∧ ¬Even (G.dist b z)
  have diffL {z : V} (zR : z∈S.R) : z∉S.L := fun h=>disjoint_left.mp S.dis h zR
  have diffR {z : V} (zL : z∈S.L) : z∉S.R := fun h=>disjoint_left.mp S.dis zL h
  have term {z : V} (za : z≠a) (zb : z≠b) :
      z∈PositiveEven G a ∨ z∈PositiveEven G b ∨ oddOdd z := by
    by_cases ea : Even (G.dist a z)
    · exact .inl (mem_erase.mpr ⟨za,mem_filter.mpr ⟨mem_univ _,ea⟩⟩)
    by_cases eb : Even (G.dist b z)
    · exact .inr (.inl (mem_erase.mpr ⟨zb,mem_filter.mpr ⟨mem_univ _,eb⟩⟩))
    exact .inr (.inr ⟨ea,eb⟩)
  have where' {z : V} (za : z≠a) (zb : z≠b) : z∈S.L ∨ z∈S.R := by
    rcases S.cover z with e|e|h|h
    · exact (za e).elim
    · exact (zb e).elim
    · exact .inl h
    exact .inr h
  by_cases oL : ∃ x∈S.L,oddOdd x
  · by_cases oR : ∃ y∈S.R,oddOdd y
    · obtain ⟨x,xL,xo⟩ := oL
      obtain ⟨y,yR,yo⟩ := oR
      refine ⟨x,y,fun z za zb=>?_⟩
      rcases term za zb with h|h|h
      · exact .inl h
      · exact .inr (.inl h)
      rcases where' za zb with L|R
      · exact .inr (.inr (.inr (odd_both_across_even S.R hc yR (diffR L) (right_boundary S)
          yo.1 yo.2 h.1 h.2)))
      exact .inr (.inr (.inl (odd_both_across_even S.L hc xL (diffL R) (left_boundary S)
        xo.1 xo.2 h.1 h.2)))
    refine ⟨ra,rb,fun z za zb=>?_⟩
    rcases term za zb with h|h|h
    · exact .inl h
    · exact .inr (.inl h)
    have zL : z∈S.L := (where' za zb).resolve_right (fun R=>oR ⟨z,R,h⟩)
    by_cases le : G.dist a z≤G.dist b z
    · exact .inr (.inr (.inl (near_port_even S.R hc raR (diffR zL) (right_boundary S)
        (fun e=>S.rightOff.2 (e ▸ raR)) ara le h.1)))
    exact .inr (.inr (.inr (near_port_even (a:=b) (b:=a) S.R hc rbR (diffR zL)
      (fun u um w uw=>by simpa only [or_left_comm (a:=w=a) (b:=w=b)] using right_boundary S u um w uw)
      (fun e=>S.rightOff.1 (e ▸ rbR)) brb (by omega) h.2)))
  refine ⟨la,lb,fun z za zb=>?_⟩
  rcases term za zb with h|h|h
  · exact .inl h
  · exact .inr (.inl h)
  have zR : z∈S.R := (where' za zb).resolve_left (fun L=>oL ⟨z,L,h⟩)
  by_cases le : G.dist a z≤G.dist b z
  · exact .inr (.inr (.inl (near_port_even S.L hc laL (diffL zR) (left_boundary S)
      (fun e=>S.leftOff.2 (e ▸ laL)) ala le h.1)))
  exact .inr (.inr (.inr (near_port_even (a:=b) (b:=a) S.L hc lbL (diffL zR)
    (fun u um w uw=>by simpa only [or_left_comm (a:=w=a) (b:=w=b)] using left_boundary S u um w uw)
    (fun e=>S.leftOff.1 (e ▸ lbL)) blb (by omega) h.2)))

/-- Four even-distance centers suffice at any actual two-separator:
no adjacency hypothesis or restriction on the number of shores is needed. -/
theorem order_le_four_mul_add_two_of_actual_two_cut (hc : G.Connected) (ab : a≠b) (d : ℕ)
    (cap : ∀ x,(EvenFrom G x).card≤d+1)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (cut : 2≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent) :
    Fintype.card V≤4*d+2 := by
  classical
  obtain ⟨S,la,lb,ra,rb,laL,lbL,raR,rbR,ala,blb,ara,brb⟩ := both_sides ab conn cut
  obtain ⟨x,y,h⟩ := four_centers_from_split hc ab S laL lbL raR rbR ala blb ara brb
  let K : Finset V := [a,b,x,y].toFinset
  have k : K.card≤4 := List.toFinset_card_le _
  apply card_of_centers d 4 cap K k
  intro z za zb
  rcases h z za zb with p|p|p|p
  · exact ⟨a,by simp [K],p⟩
  · exact ⟨b,by simp [K],p⟩
  · exact ⟨x,by simp [K],p⟩
  exact ⟨y,by simp [K],p⟩

theorem order_le_twenty_six_at_six (hc : G.Connected) (ab : a≠b)
    (cap : ∀ x,(EvenFrom G x).card≤7)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (cut : 2≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent) : Fintype.card V≤26 :=
  order_le_four_mul_add_two_of_actual_two_cut hc ab 6 cap conn cut

#print axioms order_le_four_mul_add_two_of_actual_two_cut
#print axioms order_le_twenty_six_at_six
end Graffiti189LongestPath.CrossSaturation.TwoCutOrder
