import DegreeFiveOneFourShapes189
import CapOreFill189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_off shore_closed from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}

/-- At a one/four-port distance-two two-cut, the graph has at most
eleven vertices and all but the singleton shore have degree at least
five. Complete the high vertices by the unrooted Ore threshold. -/
theorem traceable_of_actual_five_one_four_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (one : (cutPorts C).card=1) (four : (cutPorts D).card=4) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨r,ce,ar,br,_,small⟩ := one_four_shore_shape hc two even conn degree cd cover one four
  have ab : a≠b := by intro e; rw [e,dist_self] at two; omega
  have rc : r∈Shore C := by simp [ce]
  have rlow : ¬5≤G.degree r := by
    have sub : G.neighborFinset r ⊆ ({a,b} : Finset V) := by
      intro z hz
      have rz := (G.mem_neighborFinset r z).mp hz
      rcases shore_closed C r rc z rz with h|h|h
      · simp [h]
      · simp [h]
      have eq : z=r := by simpa [ce] using h
      exact (rz.ne eq.symm).elim
    have q := card_le_card sub
    rw [G.card_neighborFinset_eq_degree,card_pair ab] at q
    omega
  have upper : Fintype.card V≤11 := by
    have sub : (univ : Finset V) ⊆ insert a (insert b (insert r (Shore D))) := by
      intro z _
      have c := cover z
      simp only [ce,mem_singleton] at c
      simpa only [mem_insert] using c
    have c := card_le_card sub
    rw [card_univ] at c
    have d₁ := card_insert_le a (insert b (insert r (Shore D)))
    have d₂ := card_insert_le b (insert r (Shore D))
    have d₃ := card_insert_le r (Shore D)
    omega
  let S : Finset V := univ.erase r
  let H := fillAcross G S S
  have hi (u : V) (us : u∈S) : 5≤G.degree u :=
    (degree u r (mem_erase.mp us).1).resolve_right rlow
  have cl : CompleteOn H S := fun _ us _ vs ne => .inr ⟨ne,.inl ⟨us,vs⟩⟩
  have as : a∈S := mem_erase.mpr ⟨ar.ne,mem_univ _⟩
  have bs : b∈S := mem_erase.mpr ⟨br.ne,mem_univ _⟩
  obtain ⟨q,qp,qs⟩ := path_between_in_clique S cl as bs ab
  have route : RouteOn H S a b := ⟨q,qp,qs⟩
  have rp := route.prefix (show H.Adj r a from .inl ar.symm) (fun h => (mem_erase.mp h).1 rfl)
  have rt : Graffiti189Ore.Traceable H := by
    obtain ⟨w,wp,ws⟩ := rp
    refine ⟨r,b,w,wp,fun z => (ws z).mpr ?_⟩
    by_cases zr : z=r
    · exact mem_insert.mpr (.inl zr)
    · exact mem_insert.mpr (.inr (mem_erase.mpr ⟨zr,mem_univ _⟩))
  apply Graffiti189Ore.traceable_closure (fillAcross_mono G S S) _ rt
  intro u v h n
  obtain ⟨_,pair⟩ := h.resolve_left n
  have both : u∈S ∧ v∈S := pair.elim id And.symm
  have uh := hi u both.1
  have vh := hi v both.2
  omega

#print axioms traceable_of_actual_five_one_four_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
