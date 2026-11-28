import PosaCrossSplice189
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.PosaSpine Graffiti189LongestPath.PosaOrderedPair
open Graffiti189LongestPath.PosaSpliceCommon Graffiti189LongestPath.PosaSameSplice
open Graffiti189LongestPath.PosaCrossSplice
set_option warningAsError true
set_option maxHeartbeats 6000000
namespace Graffiti189LongestPath.PosaMaxCover
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

noncomputable def covered {a b : V} {p : G.Walk a b} (R : OrderedPair p) : Finset Nat := by
  classical
  exact (range (p.length+1)).filter (Hits R)

omit [DecidableEq V] in
theorem mem_covered {a b : V} {p : G.Walk a b} (R : OrderedPair p) (i : Nat) :
    i∈covered R ↔ i≤p.length ∧ Hits R i := by
  classical
  rw [covered,mem_filter,mem_range,Nat.lt_succ_iff]

omit [DecidableEq V] in
theorem exists_max_covered {a b : V} {p : G.Walk a b} (w : Nonempty (OrderedPair p)) :
    ∃ R : OrderedPair p, ∀ T : OrderedPair p,(covered T).card≤(covered R).card := by
  classical
  let K := (range (p.length+2)).filter (fun n => ∃ R : OrderedPair p,(covered R).card=n)
  have lim (R : OrderedPair p) : (covered R).card<p.length+2 := by
    have d := card_le_card (filter_subset (Hits R) (range (p.length+1)))
    change (covered R).card≤(range (p.length+1)).card at d
    rw [card_range] at d
    omega
  have has (R : OrderedPair p) : (covered R).card∈K :=
    mem_filter.mpr ⟨mem_range.mpr (lim R),R,rfl⟩
  obtain ⟨W⟩ := w
  have hn : K.Nonempty := ⟨_,has W⟩
  obtain ⟨n,hn,hmax⟩ := exists_max_image K id hn
  obtain ⟨R,rfl⟩ := (mem_filter.mp hn).2
  exact ⟨R,fun T => hmax _ (has T)⟩

/-- Every missed neighbor of the initial endpoint permits an
enlargement of the covered-spine set without losing any covered index. -/
theorem augment_missing_left_neighbor {a b : V} {p : G.Walk a b} (hp : p.IsPath)
    (R : OrderedPair p) (i : Nat) (ip : 0<i) (il : i<p.length)
    (edge : G.Adj a (p.getVert i)) (no : ¬Hits R i) :
    ∃ T : OrderedPair p, Hits T i ∧ ∀ j≤p.length,Hits R j → Hits T j := by
  classical
  let C := covered R
  let L := C.filter (fun j => j<i)
  let H := C.filter (fun j => i<j)
  have zero : 0∈C := (mem_covered R 0).mpr ⟨by omega,
    Or.inl (p.getVert_zero.symm ▸ R.left.start_mem_support)⟩
  have last : p.length∈C := (mem_covered R _).mpr ⟨by omega,
    Or.inl (p.getVert_length.symm ▸ R.left.end_mem_support)⟩
  have ln : L.Nonempty := ⟨0,mem_filter.mpr ⟨zero,ip⟩⟩
  have hn : H.Nonempty := ⟨p.length,mem_filter.mpr ⟨last,il⟩⟩
  let g := L.max' ln
  let h := H.min' hn
  have gm : g∈L := max'_mem _ _
  have hm : h∈H := min'_mem _ _
  have gi := (mem_filter.mp gm).2
  have ih := (mem_filter.mp hm).2
  obtain ⟨gl,gHit⟩ := (mem_covered R g).mp (mem_filter.mp gm).1
  obtain ⟨hl,hHit⟩ := (mem_covered R h).mp (mem_filter.mp hm).1
  have gap : ∀ j,g<j → j<h → ¬Hits R j := by
    intro j gj jh hit
    have jc : j∈C := (mem_covered _ _).mpr ⟨by omega,hit⟩
    by_cases ji : j<i
    · have jl : j∈L := mem_filter.mpr ⟨jc,ji⟩
      exact (not_le_of_gt gj) (le_max' _ _ jl)
    by_cases ij : i<j
    · have jh' : j∈H := mem_filter.mpr ⟨jc,ij⟩
      exact (not_le_of_gt jh) (min'_le _ _ jh')
    have eq : j=i := by omega
    exact no (eq ▸ hit)
  have swap_in (j : Nat) : Hits R j → Hits (OrderedPair.swap R) j :=
    fun h => h.elim Or.inr Or.inl
  have swap_out (j : Nat) : Hits (OrderedPair.swap R) j → Hits R j :=
    fun h => h.elim Or.inr Or.inl
  have sgap (j : Nat) (gj : g<j) (jh : j<h) : ¬Hits (OrderedPair.swap R) j :=
    fun h' => gap j gj jh (swap_out j h')
  rcases gHit with gL|gR <;> rcases hHit with hL|hR
  · exact augment_same_route p hp R g i h gi ih hl gL hL gap
  · exact augment_cross_routes p hp R g i h gi ih hl gL hR edge gap
  · obtain ⟨T,hit,keep⟩ := augment_cross_routes p hp (OrderedPair.swap R)
      g i h gi ih hl gR hL edge sgap
    exact ⟨T,hit,fun j jN h' => keep j jN (swap_in j h')⟩
  · obtain ⟨T,hit,keep⟩ := augment_same_route p hp (OrderedPair.swap R)
      g i h gi ih hl gR hR sgap
    exact ⟨T,hit,fun j jN h' => keep j jN (swap_in j h')⟩

theorem optimal_left {a b : V} {p : G.Walk a b} (hp : p.IsPath) (R : OrderedPair p)
    (max : ∀ T : OrderedPair p,(covered T).card≤(covered R).card)
    (i : Nat) (ip : 0<i) (il : i<p.length)
    (edge : G.Adj a (p.getVert i)) : Hits R i := by
  apply Classical.byContradiction
  intro no
  obtain ⟨T,hit,keep⟩ := augment_missing_left_neighbor hp R i ip il edge no
  have sub : covered R⊆covered T := by
    intro j h
    obtain ⟨jN,old⟩ := (mem_covered R j).mp h
    exact (mem_covered T j).mpr ⟨jN,keep j jN old⟩
  have eq := eq_of_subset_of_card_le sub (max T)
  have h : i∈covered T := (mem_covered T i).mpr ⟨by omega,hit⟩
  exact no ((mem_covered R i).mp (eq.symm ▸ h)).2

#print axioms exists_max_covered
#print axioms augment_missing_left_neighbor
#print axioms optimal_left
end Graffiti189LongestPath.PosaMaxCover
