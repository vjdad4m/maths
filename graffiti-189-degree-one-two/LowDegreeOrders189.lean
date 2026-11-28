import SmallSeparator189

open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open private Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two
  Graffiti189LongestPath.distance_on_geodesic from SmallSeparator189

namespace Graffiti189LongestPath.LowDegreeOrders
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem predecessor (hc : G.Connected) {v z : V} {i : ℕ}
    (di : G.dist v z=i+1) : ∃ y,G.dist v y=i ∧ G.Adj y z := by
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist v z
  have step := p.adj_getVert_succ (i:=i) (by omega)
  have li : p.length=i+1 := pl.trans di
  have endAt : p.getVert (i+1)=z := by rw [←li,getVert_length]
  rw [endAt] at step
  exact ⟨p.getVert i,Graffiti189LongestPath.distance_on_geodesic hc p pl i (by omega),step⟩

private theorem order_three_shells (hc : G.Connected) (v : V)
    (rad : ∀ y,G.dist v y≤3) :
    Fintype.card V≤1+G.degree v+(Shell G v 2).card+(Shell G v 3).card := by
  classical
  let A := G.neighborFinset v
  let B := Shell G v 2
  let C := Shell G v 3
  have sub : (univ:Finset V)⊆insert v (A∪B∪C) := by
    intro y _
    have b := rad y
    have e : G.dist v y=0 ∨ G.dist v y=1 ∨ G.dist v y=2 ∨ G.dist v y=3 := by omega
    rcases e with e|e|e|e
    · exact mem_insert.mpr (Or.inl (hc.dist_eq_zero_iff.mp e).symm)
    · exact mem_insert.mpr (Or.inr (mem_union_left _ (mem_union_left _
        ((G.mem_neighborFinset _ _).mpr (dist_eq_one_iff_adj.mp e)))))
    · exact mem_insert.mpr (Or.inr (mem_union_left _ (mem_union_right _ (mem_shell.mpr e))))
    · exact mem_insert.mpr (Or.inr (mem_union_right _ (mem_shell.mpr e)))
  have cc := card_le_card sub
  rw [card_univ] at cc
  have ins := card_insert_le v (A∪B∪C)
  have u := card_union_le A B
  have uu := card_union_le (A∪B) C
  have aa := G.card_neighborFinset_eq_degree v
  change A.card=G.degree v at aa
  change Fintype.card V≤1+G.degree v+B.card+C.card
  omega

/-- Degree-one root and parity threshold one force order at most four. -/
theorem order_le_four_of_even_two (hc : G.Connected) (v : V) (low : G.degree v≤1)
    (cap : ∀ u,(EvenFrom G u).card≤2) : Fintype.card V≤4 := by
  classical
  have c2 (u : V) := distanceTwo_le_of_even 1 u (cap u)
  have rad (u : V) : G.dist v u≤3 := by
    by_contra! h
    obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist v u
    have z := Graffiti189LongestPath.distance_on_geodesic hc p pl 2 (by omega)
    have low : 1≤(DistanceTwo G v).card := card_pos.mpr ⟨p.getVert 2,Graffiti189LongestPath.mem_distanceTwo.mpr z⟩
    have b := distanceTwo_add_to_even_along_geodesic hc 1 (x:=v) (y:=u) (by omega)
    have hi := cap v
    omega
  have n := order_three_shells hc v rad
  have a := c2 v
  have b := third_shell_le hc 1 c2 v
  rw [shell_two] at n b
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem two_from_steps (hc : G.Connected) {v a b c : V}
    (a1 : G.dist v a=1) (c3 : G.dist v c=3) (ab : G.Adj a b) (bc : G.Adj b c) :
    G.dist a c=2 := by
  have tri1 := hc.dist_triangle (u:=v) (v:=a) (w:=c)
  have tri2 := hc.dist_triangle (u:=a) (v:=b) (w:=c)
  have d1 := dist_eq_one_iff_adj.mpr ab
  have d2 := dist_eq_one_iff_adj.mpr bc
  omega

/-- A robust graph with threshold-two parity budget and a degree-at-most-two
root has at most seven vertices. -/
theorem order_le_seven_of_even_three (hc : G.Connected) (v : V) (low : G.degree v≤2)
    (cap : ∀ u,(EvenFrom G u).card≤3)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S:Set V)ᶜ)).Connected) :
    Fintype.card V≤7 := by
  classical
  let B := Shell G v 2
  let C := Shell G v 3
  have c2 (u : V) := distanceTwo_le_of_even 2 u (cap u)
  have rad (u : V) : G.dist v u≤3 := by
    by_contra! far
    have lo := shell_card_of_far hc 2 conn (x:=v) (y:=u) (i:=2) (by decide) (by omega)
    rw [shell_two] at lo
    have b := distanceTwo_add_to_even_along_geodesic hc 1 (x:=v) (y:=u) (by omega)
    have hi := cap v
    omega
  have upper := order_three_shells hc v rad
  have bUp : B.card≤2 := c2 v
  have cUp : C.card≤2 := by
    by_contra! over
    obtain ⟨z,zC⟩ := card_pos.mp (show 0<C.card by omega)
    have z3 := mem_shell.mp zC
    have bLow : 2≤B.card := shell_card_of_far hc 2 conn (x:=v) (y:=z)
      (i:=2) (by decide) (by omega)
    obtain ⟨b1,b2,neq,bEq⟩ := card_eq_two.mp (show B.card=2 by omega)
    have b1m : b1∈B := by rw [bEq]; simp
    have b2m : b2∈B := by rw [bEq]; simp
    have pb1 : G.dist v b1=1+1 := mem_shell.mp b1m
    have pb2 : G.dist v b2=1+1 := mem_shell.mp b2m
    have predC (w : V) (wC : w∈C) : ∃ y∈B,G.Adj y w := by
      obtain ⟨b,d,ed⟩ := predecessor hc (i:=2) (mem_shell.mp wC)
      exact ⟨b,mem_shell.mpr d,ed⟩
    have cannot (a : V) (a1 : G.dist v a=1) (e1 : G.Adj a b1) (e2 : G.Adj a b2) : False := by
      have sub : C⊆DistanceTwo G a := by
        intro w wC
        obtain ⟨b,bB,bw⟩ := predC w wC
        rw [bEq,mem_insert,mem_singleton] at bB
        exact Graffiti189LongestPath.mem_distanceTwo.mpr (two_from_steps hc a1 (mem_shell.mp wC)
          (bB.elim (fun e => e.symm ▸ e1) (fun e => e.symm ▸ e2)) bw)
      have t := (card_le_card sub).trans (c2 a)
      omega
    obtain ⟨a1,a1d,a1b1⟩ := predecessor hc (i:=1) pb1
    obtain ⟨a2,a2d,a2b2⟩ := predecessor hc (i:=1) pb2
    have not12 : ¬G.Adj a1 b2 := fun e => cannot a1 a1d a1b1 e
    have not21 : ¬G.Adj a2 b1 := fun e => cannot a2 a2d e a2b2
    have aNe : a1≠a2 := fun e => not12 (e.symm ▸ a2b2)
    have Csplit (w : V) (wC : w∈C) :
        G.Adj b1 w ∨ G.Adj b2 w := by
      obtain ⟨b,bB,bw⟩ := predC w wC
      rw [bEq,mem_insert,mem_singleton] at bB
      exact bB.elim (fun e => Or.inl (e ▸ bw)) (fun e => Or.inr (e ▸ bw))
    have charge (a b t : V) (a1 : G.dist v a=1) (ab : G.Adj a b)
        (tN : t∈DistanceTwo G a) (tOut : G.dist v t≠3) :
        (C.filter (G.Adj b)).card≤1 := by
      have sub : C.filter (G.Adj b)⊆(DistanceTwo G a).erase t := by
        intro w hw
        obtain ⟨h3,bw⟩ := mem_filter.mp hw
        have d3 := mem_shell.mp h3
        exact mem_erase.mpr ⟨fun e => tOut (e ▸ d3),
          Graffiti189LongestPath.mem_distanceTwo.mpr (two_from_steps hc a1 d3 ab bw)⟩
      have out := card_le_card sub
      have er := card_erase_add_one tN
      have c := c2 a
      omega
    have qs : (C.filter (G.Adj b1)).card≤1 ∧ (C.filter (G.Adj b2)).card≤1 := by
      by_cases edge : G.Adj a1 a2
      · have ne1 : a1≠b2 := fun e => by rw [e] at a1d; omega
        have ne2 : a2≠b1 := fun e => by rw [e] at a2d; omega
        exact ⟨charge a1 b1 b2 a1d a1b1
          (Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc ne1 not12 edge a2b2)) (by omega),
          charge a2 b2 b1 a2d a2b2
          (Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc ne2 not21 edge.symm a1b1)) (by omega)⟩
      · have e1 := (dist_eq_one_iff_adj.mp a1d)
        have e2 := (dist_eq_one_iff_adj.mp a2d)
        exact ⟨charge a1 b1 a2 a1d a1b1
          (Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc aNe edge e1.symm e2)) (by omega),
          charge a2 b2 a1 a2d a2b2
          (Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc (Ne.symm aNe) (fun e => edge e.symm) e2.symm e1))
          (by omega)⟩
    have sub : C⊆C.filter (G.Adj b1)∪C.filter (G.Adj b2) := by
      intro w wC
      exact (Csplit w wC).elim (fun e => mem_union_left _ (mem_filter.mpr ⟨wC,e⟩))
        (fun e => mem_union_right _ (mem_filter.mpr ⟨wC,e⟩))
    have out := (card_le_card sub).trans (card_union_le _ _)
    have z := qs.1
    have w := qs.2
    omega
  change Fintype.card V≤1+G.degree v+B.card+C.card at upper
  omega

#print axioms order_le_four_of_even_two
#print axioms order_le_seven_of_even_three
end Graffiti189LongestPath.LowDegreeOrders
