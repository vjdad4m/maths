import DegreeFiveEightLabels189
import DegreeFiveEightTerminalOre189
import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair Graffiti189EightTerminal
open private left_boundary from AdjacentCut189
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Split G a b)
set_option linter.unusedSectionVars false

/-- The eight-vertex route transferred to the original induced shore.
The replacement graph is used only inside the two-terminal closure proof. -/
theorem terminal_route_of_eight_balanced_exclusive_shore
    (eight : S.L.card=8)
    (two : (S.L.filter (G.Adj a)).card=2)
    (three : (S.L.filter (G.Adj b)).card=3)
    (high : ∀ v∈S.L,5 ≤ G.degree v)
    (none : ∀ v∈S.L,¬(G.Adj a v ∧ G.Adj b v)) :
    ∃ u∈S.L,∃ v∈S.L,G.Adj a u ∧ G.Adj b v ∧ RouteOn G S.L u v := by
  classical
  let U := ↑(↑S.L : Set V)
  let J := G.induce (↑S.L : Set V)
  let A := (univ : Finset U).filter (fun u => G.Adj a u.val)
  let B := (univ : Finset U).filter (fun u => G.Adj b u.val)
  have count (c : V) :
      ((univ : Finset U).filter (fun u => G.Adj c u.val)).card = (S.L.filter (G.Adj c)).card := by
    apply card_bij (fun u _ => u.val)
    · intro u m
      exact mem_filter.mpr ⟨u.property,(mem_filter.mp m).2⟩
    · intro u _ v _ e
      exact Subtype.ext e
    · intro v vm
      obtain ⟨vl,cv⟩ := mem_filter.mp vm
      exact ⟨⟨v,vl⟩,mem_filter.mpr ⟨mem_univ _,cv⟩,rfl⟩
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro u au bu
    exact none u.val u.property ⟨(mem_filter.mp au).2,(mem_filter.mp bu).2⟩
  have sz : Fintype.card U=8 := (Fintype.card_coe S.L).trans eight
  obtain ⟨e,col⟩ := exists_terminal_labels A B ((count a).trans two)
    ((count b).trans three) sz dis
  have portHigh (i : Fin 8) (_ : i.val<5) : 4 ≤ J.degree (e i) := by
    let x := e i
    let N := inside G S.L x.val
    have core (c d : V) (notd : ¬G.Adj d x.val) (ord : (c=a ∧ d=b) ∨ (c=b ∧ d=a)) :
        G.neighborFinset x.val ⊆ insert c N := by
      intro y ym
      have xy := (mem_neighborFinset G _ _).mp ym
      rcases left_boundary S x.val x.property y xy with ea|eb|yl
      · rcases ord with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact mem_insert.mpr (.inl ea)
        exact (notd (ea ▸ xy.symm)).elim
      · rcases ord with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact (notd (eb ▸ xy.symm)).elim
        exact mem_insert.mpr (.inl eb)
      exact mem_insert_of_mem (mem_filter.mpr ⟨yl,xy⟩)
    have cap : G.degree x.val  ≤  N.card+1 := by
      by_cases ax : G.Adj a x.val
      · have sub := core a b (fun bx=>none _ x.property ⟨ax,bx⟩) (.inl ⟨rfl,rfl⟩)
        have k := (card_le_card sub).trans (card_insert_le _ _)
        rwa [card_neighborFinset_eq_degree] at k
      have sub := core b a ax (.inr ⟨rfl,rfl⟩)
      have k := (card_le_card sub).trans (card_insert_le _ _)
      rwa [card_neighborFinset_eq_degree] at k
    have deg := high _ x.property
    change 4  ≤  (G.induce (↑S.L : Set V)).degree x
    rw [←inside_card_eq_degree_induce (G:=G) S.L x]
    change 4  ≤  N.card
    omega
  have nonHigh (i : Fin 8) (h : 5 ≤ i.val) : 5 ≤ J.degree (e i) := by
    let x := e i
    have na : ¬ G.Adj a x.val := by
      intro ax
      have q := (col i).1.mp (mem_filter.mpr ⟨mem_univ _,ax⟩)
      omega
    have nb : ¬ G.Adj b x.val := by
      intro bx
      have q := (col i).2.mp (mem_filter.mpr ⟨mem_univ _,bx⟩)
      omega
    have sub : G.neighborFinset x.val ⊆ inside G S.L x.val := by
      intro y ym
      have xy := (mem_neighborFinset G _ _).mp ym
      rcases left_boundary S x.val x.property y xy with rfl|rfl|yl
      · exact (na xy.symm).elim
      · exact (nb xy.symm).elim
      exact mem_filter.mpr ⟨yl,xy⟩
    have k := card_le_card sub
    rw [card_neighborFinset_eq_degree,inside_card_eq_degree_induce (G:=G) S.L x] at k
    exact (high _ x.property).trans k
  obtain ⟨u,v,ul,vl,vu,p,hp,ps⟩ := terminal_walk_at_eight (J:=J) e portHigh nonHigh
  exact ⟨(e u).val,(e u).property,(e v).val,(e v).property,
    (mem_filter.mp ((col u).1.mpr ul)).2,(mem_filter.mp ((col v).2.mpr ⟨vl,vu⟩)).2,
    lift_side_path S.L p hp ps⟩

#print axioms terminal_route_of_eight_balanced_exclusive_shore
end Graffiti189LongestPath.CrossSaturation.Split.Five
