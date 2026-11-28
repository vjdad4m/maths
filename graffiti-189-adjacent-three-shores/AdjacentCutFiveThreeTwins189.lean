import AdjacentCutFiveThreeShape189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_hit_a shore_disjoint shore_closed shore_nonempty from AdjacentCutFiveActual189
open private Vis vis_sub vis_card_ge_two sum_subset_card positive_cap degree_le_shore_add_one
  from AdjacentCutFiveComponents189
open private mem_positive twins_dist_le from AdjacentCutFiveBound189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
open scoped BigOperators

theorem three_components_impossible_at_adjacent_twin_cut (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (three : Nat.card (CutGraph (G := G) a b).ConnectedComponent = 3)
    (twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z)) : False := by
  classical
  have noSingleton := three_components_no_singleton_at_adjacent_cut hc ab even conn degree three
  obtain ⟨D,d5,_,_⟩ := exists_high_shore_five_to_seven_of_three_at_adjacent_cut
    hc ab even conn degree three
  let J := CutGraph (G := G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent = 3 at three
  rw [Nat.card_eq_fintype_card] at three
  let T : Finset J.ConnectedComponent := univ.erase D
  have t2 : T.card=2 := by simp [T,three]
  obtain ⟨C,E,ce,tEq⟩ := card_eq_two.mp t2
  have cd : C≠D := (mem_erase.mp (show C∈T by simp [tEq])).1
  have ed : E≠D := (mem_erase.mp (show E∈T by simp [tEq])).1
  have allFour (K : J.ConnectedComponent) : 4≤(Shore K).card := by
    obtain ⟨x,xc⟩ := shore_nonempty K
    have Cpos := card_pos.mpr (shore_nonempty K)
    have n1 := noSingleton K
    have k := card_erase_add_one xc
    obtain ⟨y,ym⟩ : ((Shore K).erase x).Nonempty := card_pos.mp (by omega)
    rcases degree y x (mem_erase.mp ym).1 with dy|dx
    · have h := degree_le_shore_add_one K (mem_erase.mp ym).2
      omega
    · have h := degree_le_shore_add_one K xc
      omega
  have twindist {K : J.ConnectedComponent} {z : V} (zk : z∈Shore K) :
      G.dist a z = G.dist b z := by
    have za : z≠a := fun h=>(shore_off K).1 (by simpa only [h] using zk)
    have zb : z≠b := fun h=>(shore_off K).2 (by simpa only [h] using zk)
    have e1 := twins_dist_le hc za.symm (fun v vb av=> (twin v av.ne.symm vb).mp av)
    have e2 := twins_dist_le hc zb.symm (fun v va bv=> (twin v va bv.ne.symm).mpr bv)
    omega
  let O (K : J.ConnectedComponent) := (Shore K).filter (fun v => ¬Even (G.dist a v))
  let P (K : J.ConnectedComponent) := (Shore K).filter (fun v => Even (G.dist a v))
  have part (K : J.ConnectedComponent) : (O K).card + (P K).card = (Shore K).card := by
    have dis : Disjoint (O K) (P K) := disjoint_left.mpr
      (fun _ h j => (mem_filter.mp h).2 (mem_filter.mp j).2)
    rw [←card_union_of_disjoint dis]
    congr 1
    ext z
    by_cases e : Even (G.dist a z) <;>
      simp only [mem_union,O,P,mem_filter,e,not_true,not_false,and_true,and_false,false_or,or_false]; simp
  have odd2 (K : J.ConnectedComponent) : 2≤(O K).card := by
    have sub : Vis K ⊆ O K := by
      intro z zm
      obtain ⟨zk,port⟩ := mem_filter.mp zm
      have da : G.dist a z = 1 := by
        rcases port with az|bz
        · exact dist_eq_one_iff_adj.mpr az
        · exact (twindist zk).trans (dist_eq_one_iff_adj.mpr bz)
      exact mem_filter.mpr ⟨zk,by rw [da]; decide⟩
    exact (vis_card_ge_two ab.ne conn K (by have q:=allFour K; omega)).trans (card_le_card sub)
  have pcap : (P C).card + (P E).card + (P D).card ≤ 5 := by
    let U : Finset J.ConnectedComponent := {C,E,D}
    have raw := sum_subset_card U P (fun _ _ => filter_subset _ _) (PositiveEven G a) (by
      intro K _ z zm
      obtain ⟨zk,ze⟩ := mem_filter.mp zm
      exact mem_positive.mpr ⟨fun e=>(shore_off K).1 (by simpa only [e] using zk),ze⟩)
    simp [U,ce,cd,ed] at raw
    have cap := positive_cap a even
    omega
  have pair {K L M : J.ConnectedComponent} (kl : K≠L) (km : K≠M) (lm : L≠M) :
      (O L).card + (O M).card ≤ 5 := by
    obtain ⟨x,xk,ax⟩ := shore_hit_a ab.ne conn K
    have x1 := dist_eq_one_iff_adj.mpr ax
    have xb1 := (twindist xk).symm.trans x1
    have subK {Z : J.ConnectedComponent} (ne : K≠Z) : O Z ⊆ PositiveEven G x := by
      intro z zo
      obtain ⟨zz,odd⟩ := mem_filter.mp zo
      have zo' : z∉Shore K := fun e=>disjoint_left.mp (shore_disjoint ne) e zz
      have nz : z≠x := fun h=>zo' (by simpa only [←h] using xk)
      have form := cross_metric (Shore K) hc xk zo' (shore_closed K)
      rw [dist_comm (G:=G) (u:=x) (v:=a),dist_comm (G:=G) (u:=x) (v:=b),
        x1,xb1,←twindist zz,min_self] at form
      refine mem_positive.mpr ⟨nz,?_⟩
      rw [form]
      simp only [Nat.even_iff] at odd ⊢
      omega
    have sub : O L ∪ O M ⊆ PositiveEven G x := by
      intro v h
      exact (mem_union.mp h).elim (fun ho=>subK kl ho) (fun ho=>subK km ho)
    have dis := (shore_disjoint lm).mono (show O L ⊆ Shore L from filter_subset _ _)
      (show O M ⊆ Shore M from filter_subset _ _)
    have c := card_le_card sub
    rw [card_union_of_disjoint dis] at c
    exact c.trans (positive_cap x even)
  have oce := pair cd.symm ed.symm ce
  have ocd := pair ce.symm ed cd
  have oed := pair ce cd ed
  have cc := part C
  have ee := part E
  have dd := part D
  have c4 := allFour C
  have e4 := allFour E
  omega

#print axioms three_components_impossible_at_adjacent_twin_cut
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
