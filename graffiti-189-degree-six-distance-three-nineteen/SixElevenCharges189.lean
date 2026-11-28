import SixElevenGeometry189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_disjoint shore_off shore_hit_a shore_hit_b shore_closed from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private no_common_far from SixDistanceThreeShort189
open private each_foreign_port_is_distance_two from SixCutHighShore189
open private positive_even_cap from TwoCutOrderCenters189
open private in_positive_even_of_dist_two from TwoCutDistanceCaps189
open FiveAdjacent (cross_metric)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}

theorem mem_cutSeen {S : Finset V} {r x : V} :
    x∈cutSeen G S r ↔ x∈S ∧ G.dist r x=2 := by
  simp [cutSeen,DistanceTwo]

theorem even_budget_three (even : ∀ x,(EvenFrom G x).card≤7) (u : V)
    (F H T : Finset V) (fh : Disjoint F H) (ft : Disjoint F T) (ht : Disjoint H T)
    (fs : F⊆PositiveEven G u) (hs : H⊆PositiveEven G u) (ts : T⊆PositiveEven G u) :
    F.card+H.card+T.card≤6 := by
  classical
  have d : Disjoint (F∪H) T := by rw [disjoint_union_left]; exact ⟨ft,ht⟩
  have sub : (F∪H)∪T⊆PositiveEven G u := union_subset (union_subset fs hs) ts
  have c := (card_le_card sub).trans (positive_even_cap (d:=6) (even u))
  rwa [card_union_of_disjoint d,card_union_of_disjoint fh] at c

theorem port_even_eleven (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤7) {C D : Cmp G a b} (cd : C≠D)
    (eleven : (Shore D).card=11) {u : V} (ud : u∈Shore D) (au : G.Adj a u) (uh : 6≤G.degree u)
    (H T : Finset V)
    (loc : ∀ x∈H,x∈Shore D ∧ 6≤G.degree x ∧ x≠u ∧ ¬G.Adj u x)
    (tC : Disjoint T (Shore C)) (tD : Disjoint T (Shore D)) (t2 : T⊆DistanceTwo G u) :
    (cutPorts G (Shore C) a).card+H.card+T.card≤6 := by
  classical
  have hsub : H⊆Shore D := fun x hx=>(loc x hx).1
  have psub : cutPorts G (Shore C) a⊆Shore C := filter_subset _ _
  apply even_budget_three even u _ H T
    ((shore_disjoint cd).mono psub hsub) (tC.symm.mono_left psub) (tD.symm.mono_left hsub)
  · intro x xx
    have h : x∈DistanceTwo G u :=
      each_foreign_port_is_distance_two hc cd.symm (mem_filter.mpr ⟨ud,au⟩) xx
    exact in_positive_even_of_dist_two (mem_filter.mp h).2
  · intro x xx
    obtain ⟨xd,xh,ne,no⟩ := loc x xx
    exact in_positive_even_of_dist_two ((mem_filter.mp
      (eleven_nonedge_charges hc far eleven ud xd ne.symm no uh xh)).2)
  · intro x xx
    exact in_positive_even_of_dist_two ((mem_filter.mp (t2 xx)).2)

theorem dark_one_even_eleven (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ x,(EvenFrom G x).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D) (six : (Shore C).card=6)
    (eleven : (Shore D).card=11) {u : V} (ud : u∈Shore D) (uh : 6≤G.degree u)
    (ua : G.dist a u=2) (ub : 3≤G.dist b u)
    (H : Finset V) (loc : ∀ x∈H,x∈Shore D ∧ 6≤G.degree x ∧ G.Adj b x) :
    (cutPorts G (Shore C) b).card+H.card+1≤6 := by
  classical
  obtain ⟨r,rc,ar⟩ := shore_hit_a ab conn C
  have clique := cut_shore_six_clique far C six degree
  have hsub : H⊆Shore D := fun x hx=>(loc x hx).1
  have psub : cutPorts G (Shore C) b⊆Shore C := filter_subset _ _
  have aoffC : Disjoint (cutPorts G (Shore C) b) ({a}:Finset V) :=
    disjoint_left.mpr (fun x xp xe=>(shore_off C).1 ((mem_singleton.mp xe) ▸ psub xp))
  have aoffD : Disjoint H ({a}:Finset V) :=
    disjoint_left.mpr (fun x xp xe=>(shore_off D).1 ((mem_singleton.mp xe) ▸ hsub xp))
  have q := even_budget_three even u (cutPorts G (Shore C) b) H {a}
    ((shore_disjoint cd).mono psub hsub) aoffC aoffD ?_ ?_ ?_
  · rwa [card_singleton] at q
  · intro z zp
    obtain ⟨zc,bz⟩ := mem_filter.mp zp
    have az : ¬G.Adj a z := fun h=>no_common_far far ⟨h,bz⟩
    have rz : r≠z := fun eq=>az (eq ▸ ar)
    have za : z≠a := fun eq=>(shore_off C).1 (eq ▸ zc)
    have seen : G.dist a z=2 :=
      (mem_cutSeen.mp (visible_of_adj_port (S:=Shore C) hc za zc ar (clique r rc z zc rz) az)).2
    have zb := dist_eq_one_iff_adj.mpr bz
    have out : z∉Shore D := fun zd=>disjoint_left.mp (shore_disjoint cd) zc zd
    have dist := cross_metric (Shore D) hc ud out (shore_closed D)
    have ub' : 3≤G.dist u b := by rwa [dist_comm]
    have ua' : G.dist u a=2 := by rwa [dist_comm]
    have d4 : G.dist u z=4 := by rw [dist,ua',seen,zb]; omega
    have zu : z≠u := fun e=>out (e.symm ▸ ud)
    exact mem_erase.mpr ⟨zu,mem_filter.mpr ⟨mem_univ _,by rw [d4]; decide⟩⟩
  · intro z zh
    obtain ⟨zd,hd,bz⟩ := loc z zh
    have pos : u≠z := fun e=>by rw [e,dist_eq_one_iff_adj.mpr bz] at ub; omega
    have no : ¬G.Adj u z := by
      intro yes
      have du := G.dist_le (Walk.cons bz (Walk.cons yes.symm .nil))
      simp at du
      omega
    exact in_positive_even_of_dist_two ((mem_filter.mp
      (eleven_nonedge_charges hc far eleven ud zd pos no uh hd)).2)
  · intro z zz
    rw [mem_singleton.mp zz]
    apply in_positive_even_of_dist_two
    rwa [dist_comm]

theorem unseen_nonport_dist_ge_three (hc : G.Connected) {D : Finset V} {u r : V}
    (ud : u∈D) (ne : r≠u) (no : ¬G.Adj r u) (ns : u∉cutSeen G D r) :
    3≤G.dist r u := by
  have n0 := dist_ne_zero_iff_ne_and_reachable.mpr ⟨ne,hc r u⟩
  have n1 : G.dist r u≠1 := fun h=>no (dist_eq_one_iff_adj.mp h)
  have n2 : G.dist r u≠2 := fun h=>ns (mem_cutSeen.mpr ⟨ud,h⟩)
  omega

#print axioms port_even_eleven
#print axioms dark_one_even_eleven
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
