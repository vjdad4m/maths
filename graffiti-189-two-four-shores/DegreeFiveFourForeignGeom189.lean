import DegreeFiveThreeFiveDom189
import DegreeFiveBothFourOrFiveUnsat189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- The distance-two and four shells share at most five slots. -/
theorem four_layer_add_distance_two_le_five
    (even : ∀ x,(EvenFrom G x).card≤6) (x : V) :
    (DistanceTwo G x).card+(univ.filter (fun z=>G.dist x z=4)).card≤5 := by
  classical
  let A := DistanceTwo G x
  let B := univ.filter (fun z=>G.dist x z=4)
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro w wa wb
    have p : G.dist x w=2 := by simpa [A,DistanceTwo] using wa
    have q := (mem_filter.mp wb).2
    omega
  have no : x∉A∪B := by simp [A,B,DistanceTwo,dist_self]
  have sub : insert x (A∪B)⊆EvenFrom G x := by
    intro w wm
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases mem_insert.mp wm with h|h
    · rw [h,dist_self]
      decide
    rcases mem_union.mp h with ha|hb
    · have eq : G.dist x w=2 := by simpa [A,DistanceTwo] using ha
      rw [eq]
      decide
    have eq := (mem_filter.mp hb).2
    rw [eq]
    decide
  have card := (card_le_card sub).trans (even x)
  rw [card_insert_of_not_mem no,card_union_of_disjoint dis] at card
  change A.card+B.card≤5
  omega

/-- With four foreign contacts, all local vertices are within distance
two of the common porter. Across the cut, at most one nonporter fails
to be adjacent to an actual cut porter. -/
theorem four_foreign_near_with_exception
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (D4 : (cutPorts D).card=4)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    ((secondShore C x).card≤1 ∧ ∀ v∈Shore C,G.dist x v≤2) ∧
    (∀ z,G.dist x z≤4) ∧
    ((univ.filter (fun z=>G.dist x z=4)).card + (secondShore C x).card≤1) ∧
    (∀ z∈Shore D,z∉cutPorts D → G.dist x z=4 ∨ ∃ y∈cutPorts D,G.Adj z y) := by
  classical
  have ab : a≠b := by intro e; rw [e,dist_self] at two; omega
  have cross {u v : V} (uc : u∈Shore C) (vd : v∈Shore D) : ¬G.Adj u v := by
    intro e
    rcases shore_closed C u uc v e with rfl|rfl|vc
    · exact (shore_off D).1 vd
    · exact (shore_off D).2 vd
    exact disjoint_left.mp (shore_disjoint cd) vc vd
  let S : Split G a b := ⟨Shore C,Shore D,shore_disjoint cd,shore_off C,shore_off D,
    shore_connected C,(fun _ uc _ vd=>cross uc vd),shore_hit_a ab conn C,shore_hit_b ab conn C,cover⟩
  have near := Split.Five.near_universal_at_four_foreign S hc even conn xc ax bx
    (show 4≤(cutPorts D).card by omega)
  have farSub : cutPorts D⊆DistanceTwo G x := by
    intro z zp
    obtain ⟨zd,hit⟩ := mem_filter.mp zp
    have ne : x≠z := fun e=>disjoint_left.mp (shore_disjoint cd) xc (e.symm ▸ zd)
    exact hit.elim (fun h=>d2 hc ne (cross xc zd) ax.symm h)
      (fun h=>d2 hc ne (cross xc zd) bx.symm h)
  have dis : Disjoint (cutPorts D) (secondShore C x) :=
    (shore_disjoint cd.symm).mono (filter_subset _ _) inter_subset_left
  have card := card_le_card (union_subset farSub
    (show secondShore C x⊆DistanceTwo G x from inter_subset_right))
  rw [card_union_of_disjoint dis,D4] at card
  have cap := four_layer_add_distance_two_le_five even x
  have ecc (z : V) : G.dist x z≤4 := by
    apply Classical.byContradiction
    intro far
    have layer : 2≤(univ.filter (fun w=>G.dist x w=4)).card :=
      layer_card_of_connectivity hc 2 conn (x:=x) (y:=z) 4
        (by decide) (by omega) (inferInstance)
    omega
  refine ⟨near,ecc,by omega,?_⟩
  intro z zd zp
  by_cases far : G.dist x z=4
  · exact .inl far
  apply Or.inr
  have ne : x≠z := fun e=>disjoint_left.mp (shore_disjoint cd) xc (e.symm ▸ zd)
  have not2 : G.dist x z≠2 := by
    intro h
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x z
    obtain ⟨w,xw,wz⟩ := two_walk_middle p (hp.trans h)
    rcases shore_closed C x xc w xw with rfl|rfl|wc
    · exact zp (mem_filter.mpr ⟨zd,.inl wz⟩)
    · exact zp (mem_filter.mpr ⟨zd,.inr wz⟩)
    exact cross wc zd wz
  have hz : G.dist x z=3 := by
    have h := hc.one_lt_dist_of_ne_of_not_adj ne (cross xc zd)
    have e := ecc z
    omega
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist z x
  have len : p.length=3 := by rw [hp,dist_comm,hz]
  have middle {u v : V} (q : G.Walk u v) (l : q.length=3) (metric : G.dist v u=3) :
      ∃ w,G.Adj u w ∧ G.dist v w=2 := by
    cases q with
    | nil => simp at l
    | @cons u w v e q =>
      refine ⟨w,e,?_⟩
      have near := G.dist_le q.reverse
      simp only [length_reverse] at near
      have tri := hc.dist_triangle (u:=v) (v:=w) (w:=u)
      have step := dist_eq_one_iff_adj.mpr e.symm
      simp only [length_cons] at l
      omega
  obtain ⟨w,zw,wx⟩ := middle p len hz
  have wd : w∈Shore D := by
    rcases shore_closed D z zd w zw with rfl|rfl|h
    · exact (zp (mem_filter.mpr ⟨zd,.inl zw.symm⟩)).elim
    · exact (zp (mem_filter.mpr ⟨zd,.inr zw.symm⟩)).elim
    exact h
  obtain ⟨q,hq⟩ := hc.exists_walk_length_eq_dist x w
  obtain ⟨t,xq,qw⟩ := two_walk_middle q (hq.trans wx)
  refine ⟨w,?_,zw⟩
  rcases shore_closed C x xc t xq with rfl|rfl|qc
  · exact mem_filter.mpr ⟨wd,.inl qw⟩
  · exact mem_filter.mpr ⟨wd,.inr qw⟩
  exact (cross qc wd qw).elim

#print axioms four_layer_add_distance_two_le_five
#print axioms four_foreign_near_with_exception
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
