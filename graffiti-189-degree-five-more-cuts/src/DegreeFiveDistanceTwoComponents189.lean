import DegreeFiveActualCut189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore mem_shore shore_off shore_nonempty shore_disjoint shore_closed
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

noncomputable def cutPorts (C : (CutGraph (G:=G) a b).ConnectedComponent) : Finset V := by
  classical
  exact (Shore C).filter (fun x=>G.Adj a x ∨ G.Adj b x)

theorem two_ports_of_nonsingleton (ab : a≠b)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (C : (CutGraph (G:=G) a b).ConnectedComponent) (many : 1<(Shore C).card) :
    2≤(cutPorts C).card := by
  classical
  by_contra! low
  obtain ⟨x,xs,ax⟩ := shore_hit_a ab conn C
  have xp : x∈cutPorts C := mem_filter.mpr ⟨xs,.inl ax⟩
  let A := (Shore C).erase x
  have xn : x∉A := by simp [A]
  have an : a∉A := fun h=>(shore_off C).1 (mem_erase.mp h).2
  have bound (u : V) (ua : u∈A) (v : V) (uv : G.Adj u v) : v=a ∨ v=x ∨ v∈A := by
    have ⟨ux,us⟩ := mem_erase.mp ua
    rcases shore_closed C u us v uv with rfl|rfl|vs
    · exact .inl rfl
    · have up : u∈cutPorts C := mem_filter.mpr ⟨us,.inr uv.symm⟩
      exact (ux (card_le_one.mp (by omega) u up x xp)).elim
    by_cases vx : v=x
    · exact .inr (.inl vx)
    exact .inr (.inr (mem_erase.mpr ⟨vx,vs⟩))
  have nonempty : A.Nonempty := by
    apply card_pos.mp
    rw [show A=(Shore C).erase x from rfl,card_erase_of_mem xs]
    omega
  have xa : x≠a := fun e=>(shore_off C).1 (e ▸ xs)
  obtain ⟨y,ya,ay⟩ := side_hits_first_after_deleting_second xa.symm A nonempty an xn
    bound (conn {x} (by simp))
  obtain ⟨yx,ys⟩ := mem_erase.mp ya
  have yp : y∈cutPorts C := mem_filter.mpr ⟨ys,.inl ay⟩
  exact yx (card_le_one.mp (by omega) y yp x xp)

private theorem singleton_shore_is_low
    {C : (CutGraph (G:=G) a b).ConnectedComponent} {x : V}
    (single : Shore C={x}) : G.degree x≤2 := by
  classical
  have xs : x∈Shore C := by simp [single]
  have sub : G.neighborFinset x⊆({a,b} : Finset V) := by
    intro y hy
    have xy := (mem_neighborFinset G x y).mp hy
    rcases shore_closed C x xs y xy with rfl|rfl|ys
    · simp
    · simp
    have e : y=x := by simpa [single] using ys
    exact (xy.ne e.symm).elim
  have n := card_le_card sub
  rw [card_neighborFinset_eq_degree] at n
  exact n.trans ((card_insert_le _ _).trans (by simp))

theorem foreign_ports_le_five_at_common (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤6)
    {C : (CutGraph (G:=G) a b).ConnectedComponent} {x : V}
    (xs : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    {T : Finset (CutGraph (G:=G) a b).ConnectedComponent} (out : C∉T) :
    (∑ D∈T, (cutPorts (G:=G) (a:=a) (b:=b) D).card)≤5 := by
  classical
  have pd : (↑T : Set _).PairwiseDisjoint (cutPorts (G:=G) (a:=a) (b:=b)) := by
    intro D _ E _ ne
    exact (shore_disjoint ne).mono (filter_subset _ _) (filter_subset _ _)
  have sub : T.biUnion (cutPorts (G:=G) (a:=a) (b:=b)) ⊆ DistanceTwo G x := by
    intro y hp
    obtain ⟨D,dt,yp⟩ := mem_biUnion.mp hp
    obtain ⟨ys,ay|by'⟩ := mem_filter.mp yp
    all_goals
      have dx : D≠C := fun h=>out (h ▸ dt)
      have no : y∉Shore C := disjoint_left.mp (shore_disjoint dx) ys
      have xy : x≠y := fun h=>no (h ▸ xs)
      have na : ¬G.Adj x y := by
        intro e
        rcases shore_closed C x xs y e with rfl|rfl|yc
        · exact (shore_off D).1 ys
        · exact (shore_off D).2 ys
        exact no yc
    · exact d2 hc xy na ax.symm ay
    · exact d2 hc xy na bx.symm by'
  have c := card_le_card sub
  rw [card_biUnion pd] at c
  exact c.trans (distanceTwo_le_of_even 5 x (even x))

/-- In the degree-five setting, a distance-two cut has at most three shores. -/
theorem component_card_le_three_at_five_distance_two (hc : G.Connected)
    (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v) :
    Nat.card (CutGraph (G:=G) a b).ConnectedComponent≤3 := by
  classical
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent≤3
  rw [Nat.card_eq_fintype_card]
  by_contra! many
  have ab : a≠b := by intro h; rw [h,SimpleGraph.dist_self] at two; omega
  have impossible {C : J.ConnectedComponent} {x : V} (xs : x∈Shore C)
      (ax : G.Adj a x) (bx : G.Adj b x) (others : ∀ D : J.ConnectedComponent,
        D≠C → 1<(Shore D).card) : False := by
    let T := (univ : Finset J.ConnectedComponent).erase C
    have size : 3≤T.card := by
      dsimp [T]
      rw [card_erase_of_mem (mem_univ _),card_univ]
      omega
    have cap := foreign_ports_le_five_at_common hc even xs ax bx (T:=T) (by simp [T])
    have each : ∀ D∈T,2≤(cutPorts D).card := by
      intro D dt
      exact two_ports_of_nonsingleton ab conn D (others D (mem_erase.mp dt).1)
    have lo : 2*T.card ≤ ∑ D∈T, (cutPorts (G:=G) (a:=a) (b:=b) D).card := by
      simpa [sum_const,nsmul_eq_mul,Nat.mul_comm] using sum_le_sum each
    have z : 2*T.card≤5 := lo.trans cap
    omega
  by_cases sing : ∃ C : J.ConnectedComponent,(Shore C).card=1
  · obtain ⟨C,s⟩ := sing
    obtain ⟨x,hx⟩ := card_eq_one.mp s
    have xs : x∈Shore C := by simp [hx]
    obtain ⟨p,ps,ap⟩ := shore_hit_a ab conn C
    obtain ⟨q,qs,bq⟩ := shore_hit_b ab conn C
    have px : p=x := by simpa [hx] using ps
    have qx : q=x := by simpa [hx] using qs
    have others (D : J.ConnectedComponent) (dc : D≠C) : 1<(Shore D).card := by
      apply Classical.byContradiction
      intro h
      have p := card_pos.mpr (shore_nonempty D)
      obtain ⟨y,hy⟩ := card_eq_one.mp (show (Shore D).card=1 by omega)
      have ys : y∈Shore D := by simp [hy]
      have xy : x≠y := fun h=>disjoint_left.mp (shore_disjoint dc.symm) xs (h.symm ▸ ys)
      have xd := singleton_shore_is_low hx
      have yd := singleton_shore_is_low hy
      exact (degree x y xy).elim (by omega) (by omega)
    exact impossible xs (px ▸ ap) (qx ▸ bq) others
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨x,ax,xb⟩ := two_walk_middle p (pl.trans two)
  have xa := ax.ne.symm
  let C : J.ConnectedComponent := (CutGraph (G:=G) a b).connectedComponentMk ⟨x,xa,xb.ne⟩
  have xs : x∈Shore C := mem_shore.mpr ⟨⟨xa,xb.ne⟩,rfl⟩
  exact impossible xs ax xb.symm (fun D _=>by
    have p := card_pos.mpr (shore_nonempty D)
    have n : (Shore D).card≠1 := fun h=>sing ⟨D,h⟩
    omega)

#print axioms two_ports_of_nonsingleton
#print axioms foreign_ports_le_five_at_common
#print axioms component_card_le_three_at_five_distance_two
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
