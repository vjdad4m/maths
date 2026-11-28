import SixTwoShoreTen189
import TwoCutDistanceCaps189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_disjoint shore_off shore_hit_a shore_hit_b shore_closed from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private no_common_far shore_inside_five from SixDistanceThreeShort189
open private d2 from CrossSaturation189
open private each_foreign_port_is_distance_two from SixCutHighShore189
open private aPorts bPorts from SixCutFar189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open private positive_even_cap from TwoCutOrderCenters189
open private in_positive_even_of_dist_two from TwoCutDistanceCaps189
open FiveAdjacent (shore_swapCut cross_metric)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}

def cutPorts (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (r : V) : Finset V :=
  S.filter (G.Adj r)

noncomputable def cutSeen (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (r : V) : Finset V :=
  S ∩ DistanceTwo G r

theorem visible_of_adj_port (hc : G.Connected) {S : Finset V} {r u v : V}
    (vr : v≠r) (vs : v∈S) (ur : G.Adj r u) (uv : G.Adj u v) (no : ¬G.Adj r v) :
    v∈cutSeen G S r :=
  mem_inter.mpr ⟨vs,d2 hc vr.symm no ur uv⟩

theorem inside_subset_erase (S : Finset V) (x : V) :
    inside G S x⊆S.erase x := by
  intro y h
  have e := mem_filter.mp h
  exact mem_erase.mpr ⟨e.2.ne.symm,e.1⟩

/-- At threshold six, the six-vertex shore of a distance-three pair is a clique. -/
theorem cut_shore_six_clique (far : 3≤G.dist a b) (C : Cmp G a b)
    (six : (Shore C).card=6) (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v) :
    ∀ x∈Shore C,∀ y∈Shore C,x≠y → G.Adj x y := by
  have all (x : V) (xh : x∈Shore C) (xd : 6≤G.degree x) :
      inside G (Shore C) x=(Shore C).erase x := by
    refine eq_of_subset_of_card_le (inside_subset_erase _ _) ?_
    rw [card_erase_of_mem xh,six]
    exact shore_inside_five far C xh xd
  intro x xm y ym xy
  rcases degree x y xy with xd|yd
  · have k : y∈inside G (Shore C) x := by
      rw [all x xm xd]
      exact mem_erase.mpr ⟨xy.symm,ym⟩
    exact (mem_filter.mp k).2
  · have k : x∈inside G (Shore C) y := by
      rw [all y ym yd]
      exact mem_erase.mpr ⟨xy,xm⟩
    exact (mem_filter.mp k).2.symm

theorem cut_dark_degree (C : Cmp G a b) {x : V} (xc : x∈Shore C)
    (noa : ¬G.Adj a x) (nob : ¬G.Adj b x) : G.degree x+1≤(Shore C).card := by
  have h : G.neighborFinset x⊆(Shore C).erase x := by
    intro y hy
    have ad := (G.mem_neighborFinset _ _).mp hy
    rcases shore_closed C x xc y ad with rfl|rfl|s
    · exact (noa ad.symm).elim
    · exact (nob ad.symm).elim
    · exact mem_erase.mpr ⟨ad.ne.symm,s⟩
  have c := card_le_card h
  rw [G.card_neighborFinset_eq_degree,card_erase_of_mem xc] at c
  have pos := card_pos.mpr ⟨x,xc⟩
  omega

theorem cut_shore_six_terminal_data (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ x,(EvenFrom G x).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D) (six : (Shore C).card=6)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D) :
    0<(cutPorts G (Shore C) a).card ∧ (cutSeen G (Shore D) a).card≤(cutPorts G (Shore C) a).card ∧
    (cutPorts G (Shore D) a).card≤5 ∧ 6≤(cutPorts G (Shore C) a).card+(cutPorts G (Shore D) a).card := by
  classical
  let P := cutPorts G (Shore C) a
  let Q := cutPorts G (Shore D) a
  let X := cutSeen G (Shore D) a
  have clique := cut_shore_six_clique far C six degree
  obtain ⟨u,uc,au⟩ := shore_hit_a ab conn C
  obtain ⟨w,wc,bw⟩ := shore_hit_b ab conn C
  have wu : w≠u := fun eq=> no_common_far far ⟨au,eq ▸ bw⟩
  obtain ⟨v,vd,av⟩ := shore_hit_a ab conn D
  have ppos : 0<P.card := card_pos.mpr ⟨u,mem_filter.mpr ⟨uc,au⟩⟩
  have psub : P⊆Shore C := filter_subset _ _
  have dis : Disjoint (Shore C \ P) X := (shore_disjoint cd).mono sdiff_subset inter_subset_left
  have memX : X⊆DistanceTwo G a := inter_subset_right
  have memC : Shore C \ P⊆DistanceTwo G a := by
    intro x hx
    obtain ⟨xc,xp⟩ := mem_sdiff.mp hx
    have no : ¬G.Adj a x := fun e=>xp (mem_filter.mpr ⟨xc,e⟩)
    have e : u≠x := fun e=>no (e ▸ au)
    exact d2 hc (fun eq=>(shore_off C).1 (eq ▸ xc)) no au (clique u uc x xc e)
  have budget := (card_le_card (union_subset memC memX)).trans (distanceTwo_le_of_even 6 a (even a))
  rw [card_union_of_disjoint dis,card_sdiff psub,six] at budget
  have pp := card_le_card psub
  rw [six] at pp
  have xcap : X.card≤P.card := by omega
  have Q2 : Q⊆DistanceTwo G u := fun _ h=>
    each_foreign_port_is_distance_two hc cd (mem_filter.mpr ⟨uc,au⟩) h
  have b2 : b∈DistanceTwo G u := d2 hc (fun eq=>(shore_off C).2 (eq.symm ▸ uc))
    (fun ub=> no_common_far far ⟨au,ub.symm⟩) (clique u uc w wc wu.symm) bw.symm
  have qcap0 := (card_le_card (insert_subset b2 Q2)).trans (distanceTwo_le_of_even 6 u (even u))
  have bq : b∉Q := fun x=>(shore_off D).2 (mem_filter.mp x).1
  rw [card_insert_of_not_mem bq] at qcap0
  have noab : ¬G.Adj a b := fun h=>by have z := dist_eq_one_iff_adj.mpr h; omega
  have dega : G.degree a=P.card+Q.card := by
    have eq : G.neighborFinset a=P∪Q := by
      ext x
      rw [G.mem_neighborFinset,mem_union]
      constructor
      · intro ax
        have xa : x≠a := ax.ne.symm
        have xb : x≠b := fun e=>noab (e ▸ ax)
        exact (cover xa xb).imp (fun xc=>mem_filter.mpr ⟨xc,ax⟩) (fun xd=>mem_filter.mpr ⟨xd,ax⟩)
      · exact fun e=>e.elim (fun h=>(mem_filter.mp h).2) (fun h=>(mem_filter.mp h).2)
    have dPQ : Disjoint P Q := (shore_disjoint cd).mono (filter_subset _ _) (filter_subset _ _)
    rw [←G.card_neighborFinset_eq_degree,eq,card_union_of_disjoint dPQ]
  have higha : 6≤G.degree a := by
    by_contra! lo
    have va : v≠a := fun e=>(shore_off D).1 (e ▸ vd)
    have highv := (degree a v va.symm).resolve_left (by omega)
    have sub : G.neighborFinset v⊆insert a ((Q.erase v)∪X) := by
      intro z zn
      have vz := (G.mem_neighborFinset _ _).mp zn
      rcases shore_closed D v vd z vz with rfl|rfl|zD
      · exact mem_insert_self _ _
      · exact (no_common_far far ⟨av,vz.symm⟩).elim
      by_cases az : G.Adj a z
      · exact mem_insert_of_mem (mem_union_left _ (mem_erase.mpr ⟨vz.ne.symm,mem_filter.mpr ⟨zD,az⟩⟩))
      · exact mem_insert_of_mem (mem_union_right _ (visible_of_adj_port hc
          (fun e=>(shore_off D).1 (e ▸ zD)) zD av vz az))
    have d := card_le_card sub
    have d₁ := card_insert_le a ((Q.erase v)∪X)
    have d₂ := card_union_le (Q.erase v) X
    rw [card_erase_of_mem (show v∈Q from mem_filter.mpr ⟨vd,av⟩)] at d₂
    have qpos := card_pos.mpr (show Q.Nonempty from ⟨v,mem_filter.mpr ⟨vd,av⟩⟩)
    rw [G.card_neighborFinset_eq_degree] at d
    omega
  change 0<P.card ∧ X.card≤P.card ∧ Q.card≤5 ∧ 6≤P.card+Q.card
  exact ⟨ppos,xcap,by omega,dega ▸ higha⟩

theorem eleven_nonedge_charges (hc : G.Connected) (far : 3≤G.dist a b)
    {D : Cmp G a b} (eleven : (Shore D).card=11) {x y : V}
    (xd : x∈Shore D) (yd : y∈Shore D) (xy : x≠y) (no : ¬G.Adj x y)
    (hx : 6≤G.degree x) (hy : 6≤G.degree y) :
    y∈DistanceTwo G x := by
  classical
  let X := inside G (Shore D) x
  let Y := inside G (Shore D) y
  have x5 : 5≤X.card := shore_inside_five far D xd hx
  have y5 : 5≤Y.card := shore_inside_five far D yd hy
  obtain ⟨z,zx,zy⟩ : ∃ z∈X,z∈Y := by
    by_contra h
    have dis : Disjoint X Y := disjoint_left.mpr (fun z zx zy=>h ⟨z,zx,zy⟩)
    have sub : X∪Y ⊆ ((Shore D).erase x).erase y := by
      intro z hz
      rcases mem_union.mp hz with a|b
      · obtain ⟨zd,xz⟩ := mem_filter.mp a
        exact mem_erase.mpr ⟨fun e=>no (e ▸ xz),mem_erase.mpr ⟨xz.ne.symm,zd⟩⟩
      · obtain ⟨zd,yz⟩ := mem_filter.mp b
        exact mem_erase.mpr ⟨yz.ne.symm,mem_erase.mpr ⟨fun e=>no ((e ▸ yz).symm),zd⟩⟩
    have q := card_le_card sub
    rw [card_union_of_disjoint dis,card_erase_of_mem (mem_erase.mpr ⟨xy.symm,yd⟩),
      card_erase_of_mem xd,eleven] at q
    omega
  exact d2 hc xy no (mem_filter.mp zx).2 (mem_filter.mp zy).2.symm

#print axioms cut_shore_six_terminal_data
#print axioms eleven_nonedge_charges
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
