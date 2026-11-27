import SmallSeparator189

namespace Graffiti189LongestPath.Order
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
private theorem dist_two {a b c : V} (hconn : G.Connected)
    (hac : a ≠ c) (hna : ¬G.Adj a c) (hab : G.Adj a b) (hbc : G.Adj b c) :
    G.dist a c = 2 := by
  have hu := hconn.one_lt_dist_of_ne_of_not_adj hac hna
  have hl := G.dist_le (Walk.cons hab (Walk.cons hbc .nil))
  simp at hl
  omega



private theorem mem_distanceTwo {x y : V} :
    y ∈ DistanceTwo G x ↔ G.dist x y = 2 := by
  classical
  simp [DistanceTwo]



omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private lemma lengths_take_drop {x y : V} (p : G.Walk x y) (n : ℕ) (hn : n ≤ p.length) :
    (p.take n).length = n ∧ (p.drop n).length = p.length - n := by
  induction p generalizing n with
  | nil =>
    have : n=0 := by simpa using hn
    subst n
    exact ⟨rfl,rfl⟩
  | @cons a b c h p ih =>
    cases n with
    | zero => simp [Walk.take,Walk.drop]
    | succ n =>
      have hh : n ≤ p.length := by
        simp only [length_cons] at hn
        omega
      obtain ⟨h₁,h₂⟩ := ih n hh
      simp [Walk.take,Walk.drop,h₁,h₂,Nat.add_sub_add_right]



omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private lemma distance_on_geodesic (hc : G.Connected) {x y : V} (p : G.Walk x y)
    (hp : p.length = G.dist x y) (i : ℕ) (hi : i ≤ p.length) :
    G.dist x (p.getVert i) = i := by
  obtain ⟨h₁,h₂⟩ := lengths_take_drop p i hi
  have upper := G.dist_le (p.take i)
  have lower := hc.dist_triangle (u:=x) (v:=p.getVert i) (w:=y)
  have suffix := G.dist_le (p.drop i)
  omega



private theorem predecessor_on_geodesic (hc : G.Connected) {x z : V} (pos : 0 < G.dist x z) :
    ∃ y, G.Adj y z ∧ G.dist x y + 1 = G.dist x z := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x z
  let t := p.length-1
  have ht : t+1=p.length := by omega
  have a := p.adj_getVert_succ (i:=t) (by omega)
  rw [ht,getVert_length] at a
  have b := distance_on_geodesic hc p hp t (by omega)
  exact ⟨p.getVert t,a,by omega⟩

/-- A degree-at-most-d root and the even cap d+1 force order at most
(d+1)², with no restriction on vertex connectivity or diameter. -/
theorem order_at_most_square (hc : G.Connected) (d : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ d+1)
    {root : V} (small : G.degree root ≤ d) :
    Fintype.card V ≤ d*d+2*d+1 := by
  classical
  let E := (EvenFrom G root).erase root
  let N := G.neighborFinset root
  let child (z : V) := (univ : Finset V).filter fun w =>
    G.Adj z w ∧ G.dist root w = G.dist root z+1
  have e_pos {z : V} (hz : z∈E) : 0<G.dist root z := by
    have nz := (mem_erase.mp hz).1
    exact hc.pos_dist_of_ne nz.symm
  have ecard : E.card ≤ d := by
    have rE : root ∈ EvenFrom G root := by simp [EvenFrom,SimpleGraph.dist_self]
    have c := card_erase_add_one rE
    have b := bound root
    change E.card+1=(EvenFrom G root).card at c
    omega
  have kids (z : V) (hz : z∈E) : (child z).card≤d := by
    obtain ⟨y,yz,yd⟩ := predecessor_on_geodesic hc (e_pos hz)
    apply (card_le_card (t:=DistanceTwo G y) ?_).trans (distanceTwo_le_of_even d y (bound y))
    intro w hw
    have ⟨zw,wd⟩ := (mem_filter.mp hw).2
    have ynw : y≠w := by
      intro eq
      rw [←eq] at wd
      omega
    have no : ¬G.Adj y w := by
      intro e
      have dist := dist_eq_one_iff_adj.mpr e
      have tri := hc.dist_triangle (u:=root) (v:=y) (w:=w)
      omega
    exact mem_distanceTwo.mpr (dist_two hc ynw no yz zw)
  let O := E.biUnion child
  have oc : O.card≤E.card*d := card_biUnion_le_card_mul E child d kids
  have cover : (univ : Finset V) ⊆ insert root (N ∪ (E ∪ O)) := by
    intro z _
    by_cases eq : z=root
    · exact mem_insert.mpr (Or.inl eq)
    apply mem_insert.mpr
    apply Or.inr
    by_cases adj : G.Adj root z
    · exact mem_union.mpr (Or.inl ((G.mem_neighborFinset _ _).mpr adj))
    apply mem_union.mpr
    apply Or.inr
    by_cases ez : Even (G.dist root z)
    · exact mem_union.mpr (Or.inl (mem_erase.mpr ⟨eq,by simp [EvenFrom,ez]⟩))
    apply mem_union.mpr
    apply Or.inr
    have dist_pos : 0 < G.dist root z := hc.pos_dist_of_ne (fun e => eq e.symm)
    have dist_not_one : G.dist root z≠1 := fun e => adj (dist_eq_one_iff_adj.mp e)
    have odd := Nat.not_even_iff.mp ez
    obtain ⟨y,yz,yd⟩ := predecessor_on_geodesic hc dist_pos
    have e_g : Even (G.dist root y) := Nat.even_iff.mpr (by omega)
    have ny : y≠root := by
      intro ey
      rw [ey,SimpleGraph.dist_self] at yd
      omega
    have y_in : y∈E := mem_erase.mpr ⟨ny,by simp [EvenFrom,e_g]⟩
    exact mem_biUnion.mpr ⟨y,y_in,mem_filter.mpr ⟨mem_univ _,yz,yd.symm⟩⟩
  have c := card_le_card cover
  rw [card_univ] at c
  have c₁ := card_insert_le root (N ∪ (E ∪ O))
  have c₂ := card_union_le N (E ∪ O)
  have c₃ := card_union_le E O
  have cm := Nat.mul_le_mul_right d ecard
  have nC : N.card ≤ d := by simpa [N,card_neighborFinset_eq_degree] using small
  omega

#print axioms order_at_most_square

/-- At d=4 and connectivity at least two, the positive-even budget
forces diameter at most five. -/
theorem diameter_five_of_even_five (hc : G.Connected)
    (bound : ∀ x, (EvenFrom G x).card≤5)
    (conn : ∀ S : Finset V, S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected) :
    ∀ x y, G.dist x y ≤ 5 := by
  classical
  intro x y
  by_contra! far
  let A := Shell G x 2
  let B := Shell G x 4
  have cA : 2≤A.card := shell_card_of_far hc 2 conn (x:=x) (y:=y) (by decide) (by omega)
  have cB : 2≤B.card := shell_card_of_far hc 2 conn (x:=x) (y:=y) (by decide) (by omega)
  obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist x y
  let z := q.getVert 6
  have dz : G.dist x z = 6 := distance_on_geodesic hc q ql 6 (by omega)
  have dAB : Disjoint A B := by
    rw [disjoint_left]
    intro w ha hb
    have a : G.dist x w=2 := mem_shell.mp ha
    have b : G.dist x w=4 := mem_shell.mp hb
    omega
  have zAB : z ∉ A ∪ B := by
    intro e
    rcases mem_union.mp e with h|h
    · have d : G.dist x z=2 := mem_shell.mp h; omega
    · have d : G.dist x z=4 := mem_shell.mp h; omega
  have xAB : x ∉ insert z (A ∪ B) := by
    intro e
    rcases mem_insert.mp e with h|h
    · rw [←h,SimpleGraph.dist_self] at dz
      omega
    · rcases mem_union.mp h with e|e
      · have d : G.dist x x=2 := mem_shell.mp e
        rw [SimpleGraph.dist_self] at d
        omega
      · have d : G.dist x x=4 := mem_shell.mp e
        rw [SimpleGraph.dist_self] at d
        omega
  have sub : insert x (insert z (A ∪ B)) ⊆ EvenFrom G x := by
    intro w hw
    rcases mem_insert.mp hw with rfl|h
    · simp [EvenFrom,SimpleGraph.dist_self]
    · rcases mem_insert.mp h with rfl|h
      · simp only [EvenFrom,mem_filter,mem_univ,true_and,dz]
        decide
      · rcases mem_union.mp h with h|h
        · simp [EvenFrom,(show G.dist x w=2 from mem_shell.mp h),even_two]
        · simp only [EvenFrom,mem_filter,mem_univ,true_and,(show G.dist x w=4 from mem_shell.mp h)]
          decide
  have cb := card_le_card sub
  rw [card_insert_of_not_mem xAB,card_insert_of_not_mem zAB,card_union_of_disjoint dAB] at cb
  have up := bound x
  omega

/-- A distance-five endpoint has exactly two vertices in each of its
positive even-distance layers. -/
theorem shells_two_and_four_of_ecc_five (hc : G.Connected)
    (bound : ∀ x, (EvenFrom G x).card≤5)
    (conn : ∀ S : Finset V, S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {x y : V} (far : G.dist x y=5) :
    (Shell G x 2).card=2 ∧ (Shell G x 4).card=2 := by
  have c₂ : 2 ≤ (Shell G x 2).card := shell_card_of_far hc 2 conn (x:=x) (y:=y) (by decide) (by omega)
  have c₄ : 2 ≤ (Shell G x 4).card := shell_card_of_far hc 2 conn (x:=x) (y:=y) (by decide) (by omega)
  have bg := shell_two_four_le_of_even (x:=x) (d:=4) (bound x)
  omega

#print axioms diameter_five_of_even_five
#print axioms shells_two_and_four_of_ecc_five
end Graffiti189LongestPath.Order
