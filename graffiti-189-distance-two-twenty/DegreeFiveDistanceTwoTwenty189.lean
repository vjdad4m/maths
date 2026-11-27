import DegreeFiveActualCut189
import DegreeFiveTwoCutEvenCover189
import DegreeFiveSharedPortCount189
import DegreeFiveExclusiveGateway189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private CutGraph Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem order_le_twenty_of_actual_five_distance_two_cut {a b : V}
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (comp : Nat.card (CutGraph (G:=G) a b).ConnectedComponent=2)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v) :
    Fintype.card V≤20 := by
  classical
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent=2 at comp
  rw [Nat.card_eq_fintype_card] at comp
  have ab : a≠b := by intro eq; rw [eq,SimpleGraph.dist_self] at two; omega
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨x,ax,xb⟩ := two_walk_middle p (pl.trans two)
  let C := J.connectedComponentMk ⟨x,ax.ne.symm,xb.ne⟩
  have xC : x∈Shore C := mem_shore.mpr ⟨⟨ax.ne.symm,xb.ne⟩,rfl⟩
  let T := (univ : Finset J.ConnectedComponent).erase C
  have tc : T.card=1 := by
    dsimp [T]
    rw [card_erase_of_mem (mem_univ _),card_univ,comp]
  obtain ⟨D,hD⟩ := card_eq_one.mp tc
  have dt : D∈T := by simp [hD]
  have DC : D≠C := (mem_erase.mp dt).1
  have dis : Disjoint (Shore C) (Shore D) := shore_disjoint DC.symm
  have cover (u : V) : u=a ∨ u=b ∨ u∈Shore C ∨ u∈Shore D := by
    by_cases ua : u=a
    · exact .inl ua
    by_cases ub : u=b
    · exact .inr (.inl ub)
    let E := J.connectedComponentMk ⟨u,ua,ub⟩
    have eu : u∈Shore E := mem_shore.mpr ⟨⟨ua,ub⟩,rfl⟩
    by_cases ec : E=C
    · exact .inr (.inr (.inl (ec ▸ eu)))
    have et : E∈T := mem_erase.mpr ⟨ec,mem_univ _⟩
    rw [hD] at et
    exact .inr (.inr (.inr (mem_singleton.mp et ▸ eu)))
  have cross (u : V) (uC : u∈Shore C) (v : V) (vD : v∈Shore D) : ¬G.Adj u v := by
    intro uv
    rcases shore_closed C u uC v uv with rfl|rfl|vC
    · exact (shore_off D).1 vD
    · exact (shore_off D).2 vD
    exact disjoint_left.mp dis vC vD
  let S : Split G a b :=
    ⟨Shore C,Shore D,dis,shore_off C,shore_off D,shore_connected C,cross,
      shore_hit_a ab conn C,shore_hit_b ab conn C,cover⟩
  by_cases both : ∃ y∈Shore D,G.Adj a y ∧ G.Adj b y
  · obtain ⟨y,yD,ay,by'⟩ := both
    exact Split.Five.order_le_twenty_at_distance_two_with_common_on_both S hc two even
      xC ax xb.symm yD ay by'
  have none (y : V) (yD : y∈Shore D) : ¬(G.Adj a y ∧ G.Adj b y) :=
    fun e=>both ⟨y,yD,e⟩
  by_cases p : 4≤(cutPorts D).card
  · exact (Split.Five.order_le_nineteen_of_exclusive_four_foreign S hc two even conn
      (shore_connected D) (shore_hit_a ab conn D) (shore_hit_b ab conn D) none
      xC ax xb.symm p).trans (by decide)
  exact (order_le_sixteen_at_three_or_fewer_exclusive_ports hc two even conn degree DC.symm
    cover xC ax xb.symm none (by omega)).trans (by decide)

#print axioms order_le_twenty_of_actual_five_distance_two_cut
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
