import SixTwelveBudget189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_disjoint shore_off shore_closed from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private no_common_far shore_inside_five from SixDistanceThreeShort189
open private neighbor_subset_of_dark from SixTenRegular189
open private degree_two_from_one_deletion from AdjacentCutFiveTwinThreeGeom189
open private d2 from CrossSaturation189
open Graffiti189LongestPath.SixTwelveSat (Profile Model color seen external floor)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {C D : Cmp G a b}

abbrev WingVertex := Fin 12

theorem dark_role_not_adj_when_ge4 {u : V} {i : Fin 8} (hi : (4:ℕ) ≤ i.val)
    (us : sixClassSpec G a b u i) : ¬G.Adj a u ∧ ¬G.Adj b u := by
  fin_cases i <;> first | exact ⟨us.1,us.2.1⟩ | simp at hi

theorem role_terminal_spec (far : 3≤G.dist a b) {u : V} {i : Fin 8}
    (us : sixClassSpec G a b u i) :
    (color i false ↔ G.Adj a u) ∧ (color i true ↔ G.Adj b u) ∧
    (seen i false ↔ G.dist a u=2) ∧ (seen i true ↔ G.dist b u=2) := by
  have no : ¬(G.Adj a u ∧ G.Adj b u) := no_common_far far
  have ba : G.Adj a u → G.dist a u≠2 := fun h e=>by have k := dist_eq_one_iff_adj.mpr h; omega
  have bb : G.Adj b u → G.dist b u≠2 := fun h e=>by have k := dist_eq_one_iff_adj.mpr h; omega
  fin_cases i <;> simp [color,seen,sixClassSpec] at * <;> tauto

theorem visible_has_local_mark (hc : G.Connected) (far : 3≤G.dist a b) {u : V} (ud : u∈Shore D)
    {r : V} (rt : r=a∨r=b) (dr : G.dist r u=2) :
    ∃ v∈Shore D,G.Adj r v ∧ G.Adj u v := by
  obtain ⟨w,wl⟩ := hc.exists_walk_length_eq_dist r u
  have len : w.length=2 := wl.trans dr
  obtain ⟨v,rv,vu⟩ : ∃ v,G.Adj r v ∧ G.Adj v u := by
    cases w with
    | nil => simp at len
    | @cons _ v _ rv path =>
      cases path with
      | nil => simp at len
      | @cons _ z _ vz tail =>
        have tl : tail.length=0 := by simpa using len
        have zU := (Walk.exists_length_eq_zero_iff.mp ⟨tail,tl⟩)
        subst z
        exact ⟨v,rv,vz⟩
  have vd : v∈Shore D := by
    rcases shore_closed D u ud v vu.symm with h|h|h
    · subst v
      rcases rt with h|h
      · subst r; exact (G.loopless _ rv).elim
      · subst r
        have n := dist_eq_one_iff_adj.mpr rv
        rw [dist_comm] at n
        omega
    · subst v
      rcases rt with h|h
      · subst r
        have n := dist_eq_one_iff_adj.mpr rv
        omega
      · subst r; exact (G.loopless _ rv).elim
    · exact h
  exact ⟨v,vd,rv,vu.symm⟩

noncomputable def wingGraph (G : SimpleGraph V) (S : Finset V) (lab : WingVertex ≃ (↑S : Set V)) :
    SimpleGraph WingVertex := G.comap (fun i=>(lab i).val)

instance (S : Finset V) (lab : WingVertex ≃ (↑S : Set V)) :
    DecidableRel (wingGraph G S lab).Adj :=
  fun i j=>inferInstanceAs (Decidable (G.Adj (lab i).val (lab j).val))

theorem wing_degree_eq (lab : WingVertex ≃ (↑(Shore D) : Set V)) (i : WingVertex) :
    (wingGraph G (Shore D) lab).degree i=(inside G (Shore D) (lab i).val).card := by
  classical
  let H := wingGraph G (Shore D) lab
  let e : WingVertex ↪ V := lab.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
  have k : (H.neighborFinset i).map e = inside G (Shore D) (lab i).val := by
    ext v
    constructor
    · intro mm
      obtain ⟨j,jm,eq⟩ := mem_map.mp mm
      change (lab j).val=v at eq
      subst v
      exact mem_filter.mpr ⟨(lab j).property,(H.mem_neighborFinset _ _).mp jm⟩
    · intro mm
      obtain ⟨vs,adj⟩ := mem_filter.mp mm
      let j := lab.symm ⟨v,vs⟩
      have je : lab j=(⟨v,vs⟩ : ↑(↑(Shore D):Set V)) := lab.apply_symm_apply _
      have aj : H.Adj i j := by change G.Adj (lab i).val (lab j).val; rwa [je]
      exact mem_map.mpr ⟨j,(H.mem_neighborFinset _ _).mpr aj,congrArg Subtype.val je⟩
  have h := congrArg Finset.card k
  rw [card_map,H.card_neighborFinset_eq_degree] at h
  exact h

theorem model_of_label (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ x,(EvenFrom G x).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cd : C≠D) (six : (Shore C).card=6)
    (P : Profile) (lab : WingVertex ≃ (↑(Shore D) : Set V))
    (ha : P.p=(cutPorts G (Shore C) a).card) (hb : P.q=(cutPorts G (Shore C) b).card)
    (hr : ∀ i,sixClass G a b (lab i).val=P.role i)
    (h7 : ∀ i,(P.role i).val<7)
    (hl : ∀ i,P.low≠some i → 6≤G.degree (lab i).val) :
    Model P (wingGraph G (Shore D) lab) (fun i j=>G.dist (lab i).val (lab j).val=2) := by
  classical
  let w (i : WingVertex) := (lab i).val
  have spec (i : WingVertex) : sixClassSpec G a b (w i) (P.role i) := by
    have no : ¬(G.Adj a (w i)∧G.Adj b (w i)) := no_common_far far
    exact (class_spec no _).mp (hr i)
  have sha (i : WingVertex) : w i∈Shore D := (lab i).property
  have na (i : WingVertex) : w i≠a := by
    intro e
    have s := sha i
    rw [e] at s
    exact (shore_off D).1 s
  have nb (i : WingVertex) : w i≠b := by
    intro e
    have s := sha i
    rw [e] at s
    exact (shore_off D).2 s
  have winj : Function.Injective w := fun _ _ e=>lab.injective (Subtype.ext e)
  have term (i : WingVertex) := role_terminal_spec far (spec i)
  constructor
  · intro i j h
    rwa [dist_comm]
  · intro i j ad
    exact six_role_of_edge hc far (na i) (nb i) (na j) (nb j) ad (spec i) (spec j)
  · intro i z vis
    have one : ∃ v∈Shore D,G.Adj (if z then b else a) v ∧ G.Adj (w i) v := by
      cases z
      · exact visible_has_local_mark hc far (sha i) (.inl rfl) ((term i).2.2.1.mp vis)
      · exact visible_has_local_mark hc far (sha i) (.inr rfl) ((term i).2.2.2.mp vis)
    obtain ⟨u,ud,ru,iu⟩ := one
    let j := lab.symm ⟨u,ud⟩
    have je : w j=u := congrArg Subtype.val (lab.apply_symm_apply ⟨u,ud⟩)
    refine ⟨j,?_,?_⟩
    · cases z
      · exact (term j).1.mpr (by rwa [je])
      · exact (term j).2.1.mpr (by rwa [je])
    · change G.Adj (w i) (w j)
      rwa [je]
  · intro i j k ne ik kj no
    exact (mem_filter.mp (d2 hc (fun eq=>ne (winj eq)) no ik kj)).2
  · intro i j z ne ic jc no
    cases z
    · exact (mem_filter.mp (d2 hc (fun eq=>ne (winj eq)) no ((term i).1.mp ic).symm ((term j).1.mp jc))).2
    · exact (mem_filter.mp (d2 hc (fun eq=>ne (winj eq)) no ((term i).2.1.mp ic).symm ((term j).2.1.mp jc))).2
  · intro i
    rw [wing_degree_eq]
    change floor P i≤(inside G (Shore D) (w i)).card
    by_cases k : P.low=some i
    · by_cases ip : (P.role i).val<4
      · simpa [floor,k,ip] using shore_inside_one_of_two_connected far conn (sha i)
      · have mn := dark_role_not_adj_when_ge4 (Nat.le_of_not_gt ip) (spec i)
        have l := degree_two_from_one_deletion conn (na i) (fun h=>mn.1 h.symm)
        have sub := card_le_card (neighbor_subset_of_dark D (sha i) mn.1 mn.2)
        rw [G.card_neighborFinset_eq_degree] at sub
        simpa [floor,k,ip] using l.trans sub
    · by_cases ip : (P.role i).val<4
      · simpa [floor,k,ip] using shore_inside_five far D (sha i) (hl i k)
      · obtain ⟨na,nb⟩ := dark_role_not_adj_when_ge4 (Nat.le_of_not_gt ip) (spec i)
        simpa [floor,k,ip] using dark_inside_six (sha i) na nb (hl i k)
  · intro i s caps
    let e : WingVertex ↪ V := ⟨w,winj⟩
    have loc : s.map e⊆Shore D := by
      intro x hx
      obtain ⟨j,js,eq⟩ := mem_map.mp hx
      exact eq ▸ sha j
    have tw : s.map e⊆DistanceTwo G (w i) := by
      intro x hx
      obtain ⟨j,js,eq⟩ := mem_map.mp hx
      exact mem_filter.mpr ⟨mem_univ _,eq ▸ caps j js⟩
    have l := k6_profile_budget hc far ab conn even degree cd six (sha i) (h7 i) (spec i) _ loc tw
    rw [card_map] at l
    simpa [external,ha,hb] using l

#print axioms model_of_label
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
