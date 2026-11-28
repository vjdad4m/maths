import AdjacentCutFiveFourteenSingletonPartial189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_disjoint from AdjacentCutFiveActual189
open private degree_le_shore_add_one from AdjacentCutFiveComponents189
open private classSet prof from AdjacentCutFiveTopProfiles189
open private key_a_port key_b_port from AdjacentCutFiveTopFlatten189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

/-- A singleton shore is the allowed low vertex. Both terminals therefore
have at least three neighbors in the other shore, and that shore is all high. -/
theorem adjacent_singleton_terminal_count
    (ab : G.Adj a b) (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (one : (Shore C).card=1) :
    3≤((Shore D).filter (G.Adj a)).card ∧
    3≤((Shore D).filter (G.Adj b)).card ∧
    ∀ z∈Shore D,5≤G.degree z := by
  classical
  obtain ⟨s,eq⟩ := card_eq_one.mp one
  have sm : s∈Shore C := by simp [eq]
  have sd := degree_le_shore_add_one C sm
  rw [one] at sd
  have ss : s∉Shore D := fun h=>disjoint_left.mp (shore_disjoint cd) sm h
  have run {u w : V} (_uw : G.Adj u w) (uOff : u∉Shore C)
      (cov : ∀ {z : V}, z≠u → z≠w → z∈Shore C ∨ z∈Shore D) :
      3≤((Shore D).filter (G.Adj u)).card := by
    let N := (Shore D).filter (G.Adj u)
    have h := (degree u s (fun e=>uOff (e.symm ▸ sm))).resolve_right (by omega)
    have sub : G.neighborFinset u⊆insert w (insert s N) := by
      intro z zm
      have uz := (mem_neighborFinset G u z).mp zm
      by_cases e : z=w
      · exact mem_insert.mpr (.inl e)
      rcases cov uz.ne.symm e with c|d
      · have zs : z=s := by simpa [eq] using c
        exact mem_insert_of_mem (mem_insert.mpr (.inl zs))
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨d,uz⟩))
    have c := card_le_card sub
    rw [card_neighborFinset_eq_degree] at c
    have i := card_insert_le w (insert s N)
    have j := card_insert_le s N
    change 3≤N.card
    omega
  exact ⟨run ab (shore_off C).1 cover,run ab.symm (shore_off C).2 (fun hb ha=>cover ha hb),
    fun z zm=>(degree z s (fun e=>ss (e ▸ zm))).resolve_right (by omega)⟩

theorem adjacent_singleton_terminal_profile_bounds
    (hc : G.Connected) (ab : G.Adj a b) (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (one : (Shore C).card=1) :
    3≤(prof D).oa+(prof D).oc ∧ 3≤(prof D).ob+(prof D).oc := by
  classical
  obtain ⟨hA,hB,_⟩ := adjacent_singleton_terminal_count ab degree cd cover one
  have al : (Shore D).filter (G.Adj a) ⊆ classSet D 3 ∪ classSet D 5 := by
    intro v vm
    obtain ⟨vd,av⟩ := mem_filter.mp vm
    have vb : v≠b := fun e=>(shore_off D).2 (e ▸ vd)
    rcases key_a_port hc ab vb av with h|h
    · exact mem_union_left _ (mem_filter.mpr ⟨vd,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨vd,h⟩)
  have be : (Shore D).filter (G.Adj b) ⊆ classSet D 4 ∪ classSet D 5 := by
    intro v vm
    obtain ⟨vd,bv⟩ := mem_filter.mp vm
    have va : v≠a := fun e=>(shore_off D).1 (e ▸ vd)
    rcases key_b_port hc ab va bv with h|h
    · exact mem_union_left _ (mem_filter.mpr ⟨vd,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨vd,h⟩)
  exact ⟨hA.trans ((card_le_card al).trans (card_union_le _ _)),
         hB.trans ((card_le_card be).trans (card_union_le _ _))⟩

#print axioms adjacent_singleton_terminal_count
#print axioms adjacent_singleton_terminal_profile_bounds
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
