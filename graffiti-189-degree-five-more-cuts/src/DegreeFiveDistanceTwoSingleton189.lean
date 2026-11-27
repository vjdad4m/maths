import DegreeFiveDistanceTwoComponents189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_closed shore_disjoint shore_nonempty shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private d2 from CrossSaturation189
open private singleton_shore_is_low from DegreeFiveDistanceTwoComponents189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- A degree-two vertex with nonadjacent neighbors and at least four vertices
at distance two imposes order at most sixteen under the degree-five parity budget. -/
theorem order_le_sixteen_of_degree_two_root
    {r a b : V} (hc : G.Connected) (two : G.dist a b=2)
    (ra : G.Adj r a) (rb : G.Adj r b)
    (nbr : ∀ x,G.Adj r x → x=a ∨ x=b)
    (four : 4≤(DistanceTwo G r).card)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected) :
    Fintype.card V≤16 := by
  classical
  let A := (DistanceTwo G a).erase b
  let B := (DistanceTwo G b).erase a
  have ab : b∈DistanceTwo G a := by simp [DistanceTwo,two]
  have ba : a∈DistanceTwo G b := by simp only [DistanceTwo,mem_filter,mem_univ,true_and]; rwa [SimpleGraph.dist_comm]
  have ca := distanceTwo_le_of_even 5 a (even a)
  have cb := distanceTwo_le_of_even 5 b (even b)
  have Ac : A.card≤4 := by
    dsimp [A]
    rw [card_erase_of_mem ab]
    omega
  have Bc : B.card≤4 := by
    dsimp [B]
    rw [card_erase_of_mem ba]
    omega
  have budget := shell_two_four_le_of_even (x:=r) (d:=5) (even r)
  rw [shell_two] at budget
  have rad (z : V) : G.dist r z≤4 := by
    apply Classical.byContradiction
    intro h
    have hh : 4<G.dist r z := by omega
    have lo := shell_card_of_far hc 2 conn (x:=r) (y:=z) (i:=4) (by decide) hh
    omega
  have layer (z : V) (z3 : G.dist r z=3) : z∈A∪B := by
    obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist r z
    have l : p.length=3 := pl.trans z3
    cases p with
    | nil => simp at l
    | @cons _ x _ e q =>
      have le := G.dist_le q
      have xa : G.dist r x=1 := dist_eq_one_iff_adj.mpr e
      have dl := hc.dist_triangle (u:=r) (v:=x) (w:=z)
      simp only [length_cons] at l
      have eq : G.dist x z=2 := by omega
      have xz : z∈DistanceTwo G x := by simp [DistanceTwo,eq]
      rcases nbr x e with rfl|rfl
      · exact mem_union_left _ (mem_erase.mpr ⟨fun zb=>by subst z; have := dist_eq_one_iff_adj.mpr rb; omega,xz⟩)
      · exact mem_union_right _ (mem_erase.mpr ⟨fun za=>by subst z; have := dist_eq_one_iff_adj.mpr ra; omega,xz⟩)
  let T := ({r,a,b} : Finset V) ∪ DistanceTwo G r ∪ A ∪ B ∪ Shell G r 4
  have sub : (univ : Finset V)⊆T := by
    intro y _
    have bound := rad y
    by_cases h0 : G.dist r y=0
    · have e := hc.dist_eq_zero_iff.mp h0
      simp [T,←e]
    by_cases h1 : G.dist r y=1
    · rcases nbr y (dist_eq_one_iff_adj.mp h1) with rfl|rfl <;> simp [T]
    by_cases h2 : G.dist r y=2
    · simp [T,DistanceTwo,h2]
    by_cases h3 : G.dist r y=3
    · rcases mem_union.mp (layer y h3) with h|h <;> simp [T,h]
    have h4 : G.dist r y=4 := by omega
    exact mem_union_right _ (mem_shell.mpr h4)
  have total := card_le_card sub
  rw [card_univ] at total
  have first : ({r,a,b} : Finset V).card≤3 :=
    (card_insert_le r {a,b}).trans (Nat.add_le_add_right
      ((card_insert_le a {b}).trans (by simp)) 1)
  have c1 := card_union_le ({r,a,b} : Finset V) (DistanceTwo G r)
  have c2 := card_union_le (({r,a,b} : Finset V)∪DistanceTwo G r) A
  have c3 := card_union_le (({r,a,b} : Finset V)∪DistanceTwo G r∪A) B
  have c4 := card_union_le (({r,a,b} : Finset V)∪DistanceTwo G r∪A∪B) (Shell G r 4)
  change T.card≤_ at c4
  omega

theorem order_le_sixteen_of_three_shores_one_singleton
    {a b : V} (hc : G.Connected) (two : G.dist a b=2)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (three : 3≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent)
    (singleton : ∃ C : (CutGraph (G:=G) a b).ConnectedComponent,(Shore C).card=1) :
    Fintype.card V≤16 := by
  classical
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  obtain ⟨C,hC⟩ := singleton
  obtain ⟨r,rs⟩ := card_eq_one.mp hC
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have rm : r∈Shore C := by simp [rs]
  have nbr (x : V) (rx : G.Adj r x) : x=a ∨ x=b := by
    rcases shore_closed C r rm x rx with h|h|h
    · exact .inl h
    · exact .inr h
    have e : x=r := by simpa [rs] using h
    exact (rx.ne e.symm).elim
  obtain ⟨x,xm,ax⟩ := shore_hit_a ab conn C
  obtain ⟨y,ym,by'⟩ := shore_hit_b ab conn C
  have xr : x=r := by simpa [rs] using xm
  have yr : y=r := by simpa [rs] using ym
  have ra : G.Adj r a := xr ▸ ax.symm
  have rb : G.Adj r b := yr ▸ by'.symm
  apply order_le_sixteen_of_degree_two_root hc two ra rb nbr _ even conn
  let T := (univ : Finset J.ConnectedComponent).erase C
  have tc : 2≤T.card := by
    change 3≤Nat.card J.ConnectedComponent at three
    rw [Nat.card_eq_fintype_card] at three
    dsimp [T]
    rw [card_erase_of_mem (mem_univ _),card_univ]
    omega
  let P := cutPorts (G:=G) (a:=a) (b:=b)
  have closed : T.biUnion P ⊆ DistanceTwo G r := by
    intro z zp
    obtain ⟨D,dt,zd⟩ := mem_biUnion.mp zp
    have dc := (mem_erase.mp dt).1
    obtain ⟨zs,h⟩ := mem_filter.mp zd
    have rz : r≠z := fun e=>disjoint_left.mp (shore_disjoint dc) zs (e ▸ rm)
    have no : ¬G.Adj r z := fun e=>(nbr z e).elim
      (fun eq=>(shore_off D).1 (eq ▸ zs)) (fun eq=>(shore_off D).2 (eq ▸ zs))
    rcases h with az|bz
    · exact d2 hc rz no ra az
    exact d2 hc rz no rb bz
  have pairDis : (↑T : Set _).PairwiseDisjoint P := by
    intro D _ E _ de
    exact (shore_disjoint de).mono (filter_subset _ _) (filter_subset _ _)
  have each : ∀ D∈T, 2≤(P D).card := by
    intro D dt
    apply two_ports_of_nonsingleton ab conn
    apply Classical.byContradiction
    intro h
    have nz := card_pos.mpr (shore_nonempty D)
    obtain ⟨w,ws⟩ := card_eq_one.mp (show (Shore D).card=1 by omega)
    have wm : w∈Shore D := by simp [ws]
    have dc := (mem_erase.mp dt).1
    have rw' : r≠w := fun e=>disjoint_left.mp (shore_disjoint dc) wm (e ▸ rm)
    exact (degree r w rw').elim (fun high=>by have := singleton_shore_is_low rs; omega)
      (fun high=>by have := singleton_shore_is_low ws; omega)
  have total := card_le_card closed
  rw [card_biUnion pairDis] at total
  have lo : 2*T.card≤∑ D∈T,(P D).card := by
    simpa [sum_const,nsmul_eq_mul,Nat.mul_comm] using sum_le_sum each
  have m := lo.trans total
  omega

#print axioms order_le_sixteen_of_degree_two_root
#print axioms order_le_sixteen_of_three_shores_one_singleton
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
